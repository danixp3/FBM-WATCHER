"""
Monitor de anuncios de Facebook Marketplace con Playwright.

Cómo detecta cambios
--------------------
1. Al terminar, guarda en estado_motos.json un objeto por cada URL: título, precio,
   disponible, si la lectura fue válida, etc.
2. La siguiente vez que ejecutes, carga ese JSON y compara cada URL con lo nuevo.
3. Solo compara precio/disponibilidad cuando la lectura actual y la anterior son válidas
   (se considera que realmente viste el anuncio, no login ni banner de cookies).
4. Si antes leías bien y ahora no (login/cookies), envía un aviso distinto para que revises.

Facebook suele exigir iniciar sesión para ver anuncios del Marketplace. Una vez ejecuta:
  python monitor_motos.py --guardar-sesion
(inicia sesión en la ventana que se abre) y se guardará la sesión en playwright_storage.json.

Velocidad: varias URLs en paralelo (por defecto 4). Ajusta con --concurrencia o MW_CONCURRENCY.
"""

from __future__ import annotations

import argparse
import asyncio
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlparse

from playwright.async_api import async_playwright, TimeoutError as PlaywrightTimeout

BASE_DIR = Path(__file__).resolve().parent
try:
    from dotenv import load_dotenv

    load_dotenv(BASE_DIR / ".env")
except ImportError:
    pass

# --- Telegram: .env local (no subir) o variables de entorno / secretos en GitHub Actions ---
TELEGRAM_BOT_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")
URLS_FILE = BASE_DIR / "urls_motos.txt"
STATE_FILE = BASE_DIR / "estado_motos.json"
DEBUG_DIR = BASE_DIR / "debug_captures"
# Cookies aceptadas una vez; en siguientes ejecuciones Facebook suele no mostrar el diálogo.
PLAYWRIGHT_STORAGE_FILE = BASE_DIR / "playwright_storage.json"

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)

VIEWPORT = {"width": 1920, "height": 1080}
NAV_TIMEOUT_MS = int(os.environ.get("MW_NAV_TIMEOUT_MS", "60000"))
POST_LOAD_WAIT_MS = int(os.environ.get("MW_POST_WAIT_MS", "900"))
DEFAULT_CONCURRENCY = int(os.environ.get("MW_CONCURRENCY", "4"))


EXTRACT_SCRIPT = """
() => {
  const itemId = ((location.pathname || '').match(/\\/marketplace\\/item\\/(\\d+)/) || [])[1] || '';

  function decodeJsonEscapes(s) {
    if (!s) return '';
    return s.replace(/\\\\u([0-9a-fA-F]{4})/g, (_, h) => String.fromCharCode(parseInt(h, 16)));
  }

  function extractPriceFromEmbeddedJson(html, id) {
    if (!id || !html) return '';
    let winStart = -1;
    const routeMarker = '"props":{"isCrawler":false';
    let from = 0;
    while (true) {
      const p = html.indexOf(routeMarker, from);
      if (p < 0) break;
      const head = html.slice(p, p + 900);
      if (head.indexOf('"id":"' + id + '"') >= 0) {
        winStart = p;
        break;
      }
      from = p + 1;
    }
    if (winStart < 0) {
      const needle = '"id":"' + id + '"';
      winStart = html.indexOf(needle);
      if (winStart < 0) return '';
    }
    const win = html.slice(winStart, winStart + 45000);
    const re = /"listing_price"\\s*:\\s*\\{([^}]*)\\}/g;
    let m;
    while ((m = re.exec(win)) !== null) {
      const blk = m[1];
      const amtM = blk.match(/"amount"\\s*:\\s*"([^"]+)"/);
      if (!amtM) continue;
      const v = parseFloat(amtM[1]);
      if (!(v > 0)) continue;
      const fmtM = blk.match(/"formatted_amount_zeros_stripped"\\s*:\\s*"([^"]*)"/);
      if (fmtM && fmtM[1]) return decodeJsonEscapes(fmtM[1]);
      const curM = blk.match(/"currency"\\s*:\\s*"([^"]*)"/);
      return (curM && curM[1]) ? (amtM[1] + ' ' + curM[1]) : amtM[1];
    }
    return '';
  }

  function firstPlausibleEuroFromText(text) {
    if (!text) return '';
    const re = /\\d{1,3}(?:\\.\\d{3})*(?:,\\d{2})?\\s*€|€\\s*\\d{1,3}(?:\\.\\d{3})*(?:,\\d{2})?/g;
    let m;
    while ((m = re.exec(text)) !== null) {
      const raw = m[0].replace(/€/g, '').replace(/\\s/g, '').replace(/\\./g, '').replace(',', '.');
      const v = parseFloat(raw);
      if (v > 0 && v < 100000000) return m[0].trim();
    }
    return '';
  }

  const ogTitle = document.querySelector('meta[property="og:title"]')?.getAttribute('content') || '';
  const ogDesc = document.querySelector('meta[property="og:description"]')?.getAttribute('content') || '';
  const ogType = document.querySelector('meta[property="og:type"]')?.getAttribute('content') || '';
  let titulo = ogTitle.trim() || document.title.replace(/\\s*-\\s*Facebook\\s*$/i, '').trim();
  titulo = titulo.replace(/^Marketplace:\\s*/i, '').replace(/\\s*\\|\\s*Facebook\\s*$/i, '').trim();

  const htmlDump = document.documentElement ? document.documentElement.innerHTML : '';
  let precio = extractPriceFromEmbeddedJson(htmlDump, itemId);

  if (!precio) {
    const amount = document.querySelector('meta[property="product:price:amount"]')?.getAttribute('content');
    const currency = document.querySelector('meta[property="product:price:currency"]')?.getAttribute('content');
    if (amount) precio = (currency ? amount + ' ' + currency : amount).trim();
  }
  if (!precio && ogDesc) {
    const firstLine = ogDesc.split(/\\n/)[0].trim();
    if (firstLine.length < 55 && /[€$£]|\\bEUR\\b/i.test(firstLine)) precio = firstLine;
  }

  const bodyRaw = (document.body && document.body.innerText) ? document.body.innerText : '';
  const body = bodyRaw.toLowerCase();
  const head = body.slice(0, 6000);

  const loginHints = [
    'you must log in',
    'debes iniciar sesión',
    'inicia sesión para continuar',
    'log in to facebook',
    'sign in to facebook',
    'enter your email',
    'email or phone',
    'contraseña de facebook'
  ];
  const blocked = loginHints.some(h => body.includes(h));

  const cookieHints = [
    'permitir el uso de cookies',
    'permitir todas las cookies',
    'allow all cookies',
    'reject optional cookies',
    'only allow essential cookies',
    'solo las cookies necesarias',
    'aceptar todas las cookies',
    'rechazar cookies opcionales',
    'configuración de cookies',
    'cookies esenciales',
    'manage cookie preferences',
    'cookie settings',
    'we use cookies',
    'utilizamos cookies',
    'cookies y publicidad'
  ];
  const cookieLikely = cookieHints.some(h => head.includes(h));

  const unavailablePhrases = [
    'sold',
    'vendido',
    'no longer available',
    'isn\\'t available',
    'is not available',
    'listing isn\\'t available',
    'this listing may have been removed',
    'ya no está disponible',
    'este anuncio no está disponible',
    'anuncio eliminado',
    'content not found'
  ];
  let disponible = true;
  for (const p of unavailablePhrases) {
    if (body.includes(p)) {
      disponible = false;
      break;
    }
  }

  let precioRegex = '';
  if (!precio) precioRegex = firstPlausibleEuroFromText(bodyRaw);

  return {
    titulo,
    precio,
    precioRegex,
    disponible,
    blocked,
    cookieLikely,
    ogType,
    pathname: location.pathname || '',
    url: location.href
  };
}
"""


def load_urls() -> list[str]:
    if not URLS_FILE.is_file():
        print(f"No existe {URLS_FILE}. Créalo con una URL por línea.", file=sys.stderr)
        sys.exit(1)
    lines = URLS_FILE.read_text(encoding="utf-8").splitlines()
    urls: list[str] = []
    for line in lines:
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if "facebook.com" not in line.lower() and "fb.com" not in line.lower():
            continue
        urls.append(line)
    if not urls:
        print(f"No hay URLs válidas en {URLS_FILE}.", file=sys.stderr)
        sys.exit(1)
    return urls


def load_state() -> dict:
    if not STATE_FILE.is_file():
        return {"urls": {}}
    try:
        data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
        if "urls" not in data or not isinstance(data["urls"], dict):
            return {"urls": {}}
        return data
    except (json.JSONDecodeError, OSError):
        return {"urls": {}}


def save_state(state: dict) -> None:
    STATE_FILE.write_text(
        json.dumps(state, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def send_telegram(message: str) -> None:
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        print("[Aviso] Telegram no configurado; mensaje no enviado:", message[:200], file=sys.stderr)
        return
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    payload = {
        "chat_id": TELEGRAM_CHAT_ID,
        "text": message,
        "disable_web_page_preview": True,
    }
    data = urllib.parse.urlencode(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            if resp.status != 200:
                print(f"Telegram HTTP {resp.status}", file=sys.stderr)
    except urllib.error.URLError as e:
        print(f"Error Telegram: {e}", file=sys.stderr)


def normalize_price(s: str) -> str:
    if not s:
        return ""
    s = s.lower().replace(" ", "")
    s = re.sub(r"[^\d.,]", "", s)
    return s


def classify_snapshot(data: dict, final_url: str) -> tuple[bool, str, str | None]:
    """
    Devuelve (lectura_valida, pagina_tipo, motivo).
    pagina_tipo: anuncio | login | cookies | no_item | vacio | desconocida
    """
    path = urlparse(final_url).path.lower()
    if "/marketplace/item/" not in path:
        return False, "no_item", "La URL no acabó en /marketplace/item/… (redirección o error)."

    titulo = (data.get("titulo") or "").strip()
    tl = titulo.lower()

    if data.get("blocked"):
        return (
            False,
            "login",
            "Facebook pide iniciar sesión. Ejecuta: python monitor_motos.py --guardar-sesion",
        )

    if "login" in final_url.lower() or "checkpoint" in final_url.lower():
        return (
            False,
            "login",
            "Redirección a login o verificación. Ejecuta: python monitor_motos.py --guardar-sesion",
        )

    if data.get("cookieLikely"):
        return False, "cookies", "Parece el diálogo o capa de cookies (revisa captura con --debug)."

    if len(titulo) < 4:
        return False, "vacio", "Sin título útil; probablemente no cargó el anuncio."

    if tl == "facebook" or tl.startswith("iniciar sesión") or "log in to facebook" in tl:
        return (
            False,
            "login",
            "Título de pantalla de acceso. Ejecuta: python monitor_motos.py --guardar-sesion",
        )

    og_type = (data.get("ogType") or "").lower()
    if og_type and og_type not in ("product", "article", "website"):
        pass

    return True, "anuncio", None


COOKIE_BUTTON_NAMES = (
    "Permitir todas las cookies",
    "Allow all cookies",
    "Accept all cookies",
    "Aceptar todas las cookies",
)


async def click_cookie_accept_if_present(page, timeout_ms: int = 6000) -> bool:
    """Pulsa el botón principal de aceptar cookies del diálogo de Facebook (ES/EN)."""
    for name in COOKIE_BUTTON_NAMES:
        loc = page.get_by_role("button", name=name, exact=True)
        try:
            if await loc.count() > 0:
                await loc.first.click(timeout=timeout_ms)
                return True
        except Exception:
            pass
    try:
        dialog = page.locator('[role="dialog"]')
        if await dialog.count() > 0:
            for name in COOKIE_BUTTON_NAMES:
                btn = dialog.get_by_role("button", name=name, exact=True)
                if await btn.count() > 0:
                    await btn.first.click(timeout=timeout_ms)
                    return True
    except Exception:
        pass
    return False


async def prime_facebook_cookie_consent(context) -> None:
    """
    Abre facebook.com una vez por ejecución y acepta cookies antes de cargar Marketplace
    en paralelo. Las cookies son de dominio .facebook.com y se reutilizan en todas las pestañas.
    """
    page = await context.new_page()
    try:
        await page.goto("https://www.facebook.com/", wait_until="domcontentloaded", timeout=NAV_TIMEOUT_MS)
        await page.wait_for_timeout(700)
        if await click_cookie_accept_if_present(page):
            await page.wait_for_timeout(900)
            await click_cookie_accept_if_present(page)
    except PlaywrightTimeout:
        pass
    finally:
        await page.close()
    try:
        await context.storage_state(path=str(PLAYWRIGHT_STORAGE_FILE))
    except OSError as e:
        print(f"[cookies] No se pudo guardar {PLAYWRIGHT_STORAGE_FILE}: {e}", file=sys.stderr)


async def guardar_sesion_facebook_interactiva() -> None:
    """
    Abre Chromium visible para que inicies sesión en Facebook manualmente y guarda
    cookies + almacenamiento en playwright_storage.json (mismo archivo que usa el monitor).
    """
    print(
        "Se abrirá una ventana de Chromium.\n"
        "1) Si aparece el aviso de cookies, acéptalo.\n"
        "2) Inicia sesión con tu cuenta (email/teléfono y contraseña; 2FA si aplica).\n"
        "3) Comprueba que ves tu cuenta o abre Marketplace.\n"
        "4) Vuelve a esta consola y pulsa Enter para guardar la sesión.\n"
    )
    async with async_playwright() as p:
        browser = await p.chromium.launch(
            headless=False,
            args=[
                "--disable-blink-features=AutomationControlled",
                "--no-sandbox",
            ],
        )
        ctx_kwargs: dict = {
            "user_agent": USER_AGENT,
            "viewport": VIEWPORT,
            "locale": "es-ES",
            "timezone_id": "Europe/Madrid",
            "extra_http_headers": {
                "Accept-Language": "es-ES,es;q=0.9,en;q=0.8",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
            },
        }
        if PLAYWRIGHT_STORAGE_FILE.is_file():
            ctx_kwargs["storage_state"] = str(PLAYWRIGHT_STORAGE_FILE)
            print(
                f"(Hay sesión previa en {PLAYWRIGHT_STORAGE_FILE.name}; "
                "se mantiene para no perder cookies hasta que guardes de nuevo.)\n"
            )
        context = await browser.new_context(**ctx_kwargs)
        page = await context.new_page()
        try:
            await page.goto(
                "https://www.facebook.com/login",
                wait_until="domcontentloaded",
                timeout=NAV_TIMEOUT_MS,
            )
            await page.wait_for_timeout(800)
            await click_cookie_accept_if_present(page)
        except PlaywrightTimeout:
            print("Aviso: la página de login tardó mucho; continúa en el navegador.", file=sys.stderr)

        loop = asyncio.get_running_loop()
        await loop.run_in_executor(
            None,
            lambda: input("Pulsa Enter cuando hayas iniciado sesión correctamente… "),
        )

        try:
            await context.storage_state(path=str(PLAYWRIGHT_STORAGE_FILE))
            print(f"\nSesión guardada en: {PLAYWRIGHT_STORAGE_FILE}")
            print("Ya puedes cerrar la ventana del navegador o dejarla; el monitor usará este archivo.")
        except OSError as e:
            print(f"No se pudo guardar la sesión: {e}", file=sys.stderr)
            sys.exit(1)
        finally:
            await browser.close()


async def fetch_listing(page, url: str, post_wait_ms: int, debug: bool) -> dict:
    result: dict = {
        "titulo": "",
        "precio": "",
        "disponible": True,
        "error": None,
        "blocked": False,
        "cookie_banner": False,
        "url_final": url,
        "lectura_valida": False,
        "pagina_tipo": "desconocida",
        "motivo_lectura": None,
    }
    try:
        resp = await page.goto(url, wait_until="domcontentloaded", timeout=NAV_TIMEOUT_MS)
        result["url_final"] = page.url
        if resp and resp.status >= 400:
            result["disponible"] = False
            result["error"] = f"HTTP {resp.status}"
            result["lectura_valida"] = False
            result["pagina_tipo"] = "no_item"
            result["motivo_lectura"] = f"HTTP {resp.status}"
            return result
    except PlaywrightTimeout:
        result["error"] = "timeout"
        result["pagina_tipo"] = "desconocida"
        result["motivo_lectura"] = "Timeout al cargar."
        return result
    except Exception as e:
        result["error"] = str(e)
        result["motivo_lectura"] = str(e)
        return result

    await page.wait_for_timeout(post_wait_ms)
    if await click_cookie_accept_if_present(page):
        await page.wait_for_timeout(500)

    try:
        data = await page.evaluate(EXTRACT_SCRIPT)
    except Exception as e:
        result["error"] = str(e)
        result["motivo_lectura"] = str(e)
        return result

    result["titulo"] = (data.get("titulo") or "").strip()
    raw_precio = (data.get("precio") or "").strip()
    prx = (data.get("precioRegex") or "").strip()
    if prx and (not raw_precio or len(raw_precio) > 80):
        result["precio"] = prx
    else:
        result["precio"] = raw_precio

    result["disponible"] = bool(data.get("disponible", True))
    result["blocked"] = bool(data.get("blocked", False))
    result["cookie_banner"] = bool(data.get("cookieLikely", False))

    valid, tipo, motivo = classify_snapshot(data, result["url_final"])
    result["lectura_valida"] = valid
    result["pagina_tipo"] = tipo
    result["motivo_lectura"] = motivo

    if result["blocked"] and not motivo:
        result["error"] = result["error"] or "posible_login"
    elif result["pagina_tipo"] == "cookies":
        result["error"] = result["error"] or "cookies"

    if debug:
        DEBUG_DIR.mkdir(exist_ok=True)
        safe = re.sub(r"[^\w.-]+", "_", urlparse(url).path)[-80:] or "page"
        stem = f"{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S')}_{safe}"
        try:
            await page.screenshot(path=str(DEBUG_DIR / f"{stem}.png"), full_page=True)
            html = await page.content()
            (DEBUG_DIR / f"{stem}.html").write_text(html, encoding="utf-8", errors="replace")
        except OSError as e:
            print(f"[debug] No se pudo guardar captura: {e}", file=sys.stderr)

    return result


def compare_and_notify(url: str, prev: dict | None, current: dict) -> None:
    if prev is None:
        return

    prev_ok = prev.get("lectura_valida", False)
    cur_ok = current.get("lectura_valida", False)

    if prev_ok and not cur_ok:
        send_telegram(
            "⚠️ Antes se leía el anuncio; ahora no (login, cookies o bloqueo).\n"
            f"{url}\n"
            f"Tipo: {current.get('pagina_tipo')}\n"
            f"Motivo: {current.get('motivo_lectura') or current.get('error') or '—'}"
        )
        return

    if not cur_ok:
        return

    if not prev_ok:
        return

    old_titulo = (prev.get("titulo") or "").strip()
    old_precio = (prev.get("precio") or "").strip()
    old_disp = prev.get("disponible", True)

    new_titulo = (current.get("titulo") or "").strip()
    new_precio = (current.get("precio") or "").strip()
    new_disp = current.get("disponible", True)

    messages: list[str] = []

    if old_disp and not new_disp:
        messages.append(
            f"🔴 Anuncio ya no disponible / vendido\n{url}\n"
            f"Título anterior: {old_titulo or '—'}\nPrecio anterior: {old_precio or '—'}"
        )
    elif not old_disp and new_disp and (new_titulo or new_precio):
        messages.append(
            f"🟢 Anuncio vuelve a aparecer como disponible\n{url}\n"
            f"Título: {new_titulo or '—'}\nPrecio: {new_precio or '—'}"
        )

    if old_precio and new_precio and normalize_price(old_precio) != normalize_price(new_precio):
        messages.append(
            f"💰 Cambio de precio\n{url}\n"
            f"Antes: {old_precio}\nAhora: {new_precio}\n"
            f"Título: {new_titulo or old_titulo or '—'}"
        )

    for msg in messages:
        send_telegram(msg)


def print_verification_row(url: str, snap: dict) -> None:
    ok = snap.get("lectura_valida")
    mark = "OK " if ok else "NO "
    tipo = snap.get("pagina_tipo", "?")
    tit = (snap.get("titulo") or "")[:55]
    pre = (snap.get("precio") or "")[:40]
    extra = snap.get("motivo_lectura") or snap.get("error") or ""
    print(f"{mark} | {tipo:8} | {tit:55} | {pre:40} | {url[:60]}…")
    if not ok and extra:
        print(f"     └─ {extra[:120]}")


async def run_checks(
    urls: list[str],
    *,
    concurrency: int,
    post_wait_ms: int,
    debug: bool,
    verificar: bool,
    url_map: dict[str, dict],
    now_iso: str,
) -> None:
    sem = asyncio.Semaphore(max(1, concurrency))

    async with async_playwright() as p:
        browser = await p.chromium.launch(
            headless=True,
            args=[
                "--disable-blink-features=AutomationControlled",
                "--no-sandbox",
            ],
        )
        ctx_kwargs: dict = {
            "user_agent": USER_AGENT,
            "viewport": VIEWPORT,
            "locale": "es-ES",
            "timezone_id": "Europe/Madrid",
            "extra_http_headers": {
                "Accept-Language": "es-ES,es;q=0.9,en;q=0.8",
                "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
            },
        }
        if PLAYWRIGHT_STORAGE_FILE.is_file():
            ctx_kwargs["storage_state"] = str(PLAYWRIGHT_STORAGE_FILE)
        else:
            print(
                "[Aviso] No existe playwright_storage.json. Si solo ves la pantalla de login, "
                "ejecuta primero: python monitor_motos.py --guardar-sesion",
                file=sys.stderr,
            )
        context = await browser.new_context(**ctx_kwargs)

        await prime_facebook_cookie_consent(context)

        async def one(url: str) -> tuple[str, dict]:
            async with sem:
                page = await context.new_page()
                try:
                    snap = await fetch_listing(page, url, post_wait_ms, debug)
                    return url, snap
                finally:
                    await page.close()

        results = await asyncio.gather(*(one(u) for u in urls))

        await browser.close()

    for url, snap in results:
        if verificar:
            print_verification_row(url, snap)
        else:
            ok = snap.get("lectura_valida")
            print(
                f"{'✓' if ok else '✗'} {snap.get('pagina_tipo', '?'):8} | "
                f"{(snap.get('titulo') or '')[:50]}"
            )

        entry = {
            "titulo": snap["titulo"],
            "precio": snap["precio"],
            "disponible": snap["disponible"],
            "ultima_revision": now_iso,
            "url_final": snap.get("url_final", url),
            "error": snap.get("error"),
            "blocked": snap.get("blocked", False),
            "cookie_banner": snap.get("cookie_banner", False),
            "lectura_valida": snap.get("lectura_valida", False),
            "pagina_tipo": snap.get("pagina_tipo"),
            "motivo_lectura": snap.get("motivo_lectura"),
        }

        prev = url_map.get(url)
        if not verificar:
            compare_and_notify(url, prev, entry)
        url_map[url] = entry


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Monitor Facebook Marketplace → estado_motos.json + Telegram")
    p.add_argument(
        "--verificar",
        action="store_true",
        help="Solo muestra por pantalla qué detectó por URL; no envía Telegram ni guarda JSON.",
    )
    p.add_argument(
        "--debug",
        action="store_true",
        help=f"Guarda PNG + HTML en {DEBUG_DIR} por cada URL (útil si dudas de login/cookies).",
    )
    p.add_argument(
        "--concurrencia",
        type=int,
        default=DEFAULT_CONCURRENCY,
        metavar="N",
        help=f"URLs en paralelo (default {DEFAULT_CONCURRENCY}; env MW_CONCURRENCY).",
    )
    p.add_argument(
        "--espera-ms",
        type=int,
        default=POST_LOAD_WAIT_MS,
        metavar="MS",
        help=f"Pausa tras domcontentloaded en ms (default {POST_LOAD_WAIT_MS}; env MW_POST_WAIT_MS). Más alto = más fiable, más lento.",
    )
    p.add_argument(
        "--guardar-sesion",
        action="store_true",
        help="Abre el navegador visible para iniciar sesión en Facebook y guardar playwright_storage.json (requerido para la mayoría de anuncios).",
    )
    return p.parse_args()


def main() -> None:
    args = parse_args()
    if args.guardar_sesion:
        asyncio.run(guardar_sesion_facebook_interactiva())
        return

    urls = load_urls()
    state = load_state()
    url_map: dict[str, dict] = state["urls"]
    now_iso = datetime.now(timezone.utc).isoformat()

    if args.verificar:
        print("OK = lectura considerada anuncio real | tipo = login|cookies|anuncio|…")
        print("-" * 120)

    asyncio.run(
        run_checks(
            urls,
            concurrency=args.concurrencia,
            post_wait_ms=args.espera_ms,
            debug=args.debug,
            verificar=args.verificar,
            url_map=url_map,
            now_iso=now_iso,
        )
    )

    if args.verificar:
        print("-" * 120)
        print("(Modo --verificar: no se ha guardado estado_motos.json ni Telegram.)")
        return

    save_state(state)
    print(f"Estado guardado en {STATE_FILE}")


if __name__ == "__main__":
    main()
