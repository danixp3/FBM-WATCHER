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
5. Al guardar, quita del JSON las URLs que ya no están en urls_motos.txt (el estado no crece con anuncios borrados).

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


def _env_strip(key: str) -> str:
    return (os.environ.get(key) or "").strip().strip("\ufeff")


def _telegram_secret(key: str) -> str:
    """Token/chat_id: quita espacios, BOM y comillas típicas de copiar/pegar."""
    v = _env_strip(key)
    if len(v) >= 2 and v[0] == v[-1] and v[0] in "\"'":
        v = v[1:-1].strip()
    return v


def _running_in_github_actions() -> bool:
    return os.environ.get("GITHUB_ACTIONS", "").lower() == "true"


# --- Telegram: .env local (no subir) o variables de entorno / secretos en GitHub Actions ---
TELEGRAM_BOT_TOKEN = _env_strip("TELEGRAM_BOT_TOKEN")
TELEGRAM_CHAT_ID = _env_strip("TELEGRAM_CHAT_ID")
TELEGRAM_STARTUP_MESSAGE = "¡Monitor de motos activado y buscando!"
URLS_FILE = BASE_DIR / "urls_motos.txt"
STATE_FILE = BASE_DIR / "estado_motos.json"
DEBUG_DIR = BASE_DIR / "debug_captures"
# Cookies aceptadas una vez; en siguientes ejecuciones Facebook suele no mostrar el diálogo.
PLAYWRIGHT_STORAGE_FILE = BASE_DIR / "playwright_storage.json"
PRECIO_SELECTOR_FILE = BASE_DIR / "precio_selector.txt"

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"
)

VIEWPORT = {"width": 1920, "height": 1080}
NAV_TIMEOUT_MS = int(os.environ.get("MW_NAV_TIMEOUT_MS", "60000"))
POST_LOAD_WAIT_MS = int(os.environ.get("MW_POST_WAIT_MS", "1500"))
DEFAULT_CONCURRENCY = int(os.environ.get("MW_CONCURRENCY", "4"))


EXTRACT_SCRIPT = """
() => {
  const itemId = ((location.pathname || '').match(/\\/marketplace\\/item\\/(\\d+)/) || [])[1] || '';

  function decodeJsonEscapes(s) {
    if (!s) return '';
    return s.replace(/\\\\u([0-9a-fA-F]{4})/g, (_, h) => String.fromCharCode(parseInt(h, 16)));
  }

  function collectListingPriceBlocks(segment) {
    const out = [];
    let from = 0;
    const key = '"listing_price"';
    while (true) {
      const i = segment.indexOf(key, from);
      if (i < 0) break;
      const j = segment.indexOf('{', i + key.length);
      if (j < 0) break;
      let depth = 0;
      let k = j;
      for (; k < segment.length; k++) {
        const c = segment[k];
        if (c === '{') depth++;
        else if (c === '}') {
          depth--;
          if (depth === 0) {
            out.push(segment.slice(j + 1, k));
            from = k + 1;
            break;
          }
        }
      }
      if (k >= segment.length) break;
    }
    return out;
  }

  function extractPriceFromEmbeddedJson(html, id) {
    if (!id || !html) return '';
    let winStart = -1;
    const routeMarker = '"props":{"isCrawler":false';
    let fr = 0;
    while (true) {
      const p = html.indexOf(routeMarker, fr);
      if (p < 0) break;
      const head = html.slice(p, p + 900);
      if (head.indexOf('"id":"' + id + '"') >= 0) {
        winStart = p;
        break;
      }
      fr = p + 1;
    }
    if (winStart < 0) {
      const needle = '"id":"' + id + '"';
      winStart = html.indexOf(needle);
      if (winStart < 0) return '';
    }
    const win = html.slice(winStart, winStart + 120000);
    const idTag = '"id":"' + id + '"';
    const idPos = win.indexOf(idTag);
    if (idPos < 0) return '';
    const local = win.slice(idPos, idPos + 35000);
    const blks = collectListingPriceBlocks(local);
    const parsed = [];
    for (const blk of blks) {
      const amtM = blk.match(/"amount"\\s*:\\s*"([^"]+)"/);
      if (!amtM) continue;
      const v = parseFloat(amtM[1]);
      if (!(v > 0)) continue;
      const fmtM = blk.match(/"formatted_amount_zeros_stripped"\\s*:\\s*"([^"]*)"/);
      const label = (fmtM && fmtM[1]) ? decodeJsonEscapes(fmtM[1]) : null;
      const curM = blk.match(/"currency"\\s*:\\s*"([^"]*)"/);
      const plain = (curM && curM[1]) ? (amtM[1] + ' ' + curM[1]) : amtM[1];
      parsed.push({ v, text: label || plain, hasFmt: !!(fmtM && fmtM[1]) });
    }
    if (parsed.length === 0) return '';
    let pool = parsed;
    if (parsed.some(p => p.v >= 15) && parsed.some(p => p.v === 1)) {
      pool = parsed.filter(p => p.v !== 1);
      if (pool.length === 0) pool = parsed;
    }
    const withFmt = pool.filter(p => p.hasFmt);
    const pick = (arr) => {
      arr.sort((a, b) => b.v - a.v);
      return arr[0].text;
    };
    if (withFmt.length > 0) return pick(withFmt);
    return pick(pool);
  }

  function firstPlausibleEuroFromText(text) {
    if (!text) return '';
    const re = /\\d{1,3}(?:\\.\\d{3})*(?:,\\d{2})?\\s*€|€\\s*\\d{1,3}(?:\\.\\d{3})*(?:,\\d{2})?/g;
    const found = [];
    let m;
    while ((m = re.exec(text)) !== null) {
      const raw = m[0].replace(/€/g, '').replace(/\\s/g, '').replace(/\\./g, '').replace(',', '.');
      const v = parseFloat(raw);
      if (v > 0 && v < 100000000) found.push({ v, s: m[0].trim() });
    }
    if (found.length === 0) return '';
    if (found.some(x => x.v >= 25) && found.some(x => x.v === 1)) {
      const f = found.filter(x => x.v !== 1);
      if (f.length > 0) return f[0].s;
    }
    return found[0].s;
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
  if (!precio) {
    const mainEl = document.querySelector('[role="main"]');
    if (mainEl) precio = firstPlausibleEuroFromText(mainEl.innerText.slice(0, 14000));
  }
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
  if (!precio) {
    const ariaCand = [];
    document.querySelectorAll('[aria-label]').forEach((el) => {
      const a = (el.getAttribute('aria-label') || '').trim();
      if (!a || a.length > 55) return;
      if (!/[€$]|EUR|USD/i.test(a) || !/\\d/.test(a)) return;
      const nums = a.replace(/[^\\d.,]/g, ' ').trim().split(/\\s+/).filter(Boolean);
      let best = 0;
      for (const n of nums) {
        const t = n.replace(/\\./g, '').replace(',', '.');
        const v = parseFloat(t);
        if (v > best) best = v;
      }
      if (best > 0) ariaCand.push({ v: best, a });
    });
    if (ariaCand.length) {
      ariaCand.sort((x, y) => y.v - x.v);
      precio = ariaCand[0].a;
    }
  }
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
    text = json.dumps(state, ensure_ascii=False, indent=2)
    tmp = STATE_FILE.with_suffix(".tmp")
    tmp.write_text(text, encoding="utf-8")
    tmp.replace(STATE_FILE)


def load_price_css_selector() -> str | None:
    if not PRECIO_SELECTOR_FILE.is_file():
        return None
    for line in PRECIO_SELECTOR_FILE.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        # Comentario: "# texto" pero no selector tipo #id o #mount_...
        if line.startswith("#") and not re.match(r"^#[A-Za-z0-9_-]{2,}(\s|[>,\[\(:]|$)", line):
            continue
        return line
    return None


def send_telegram(message: str) -> bool:
    """
    Lee token/chat del entorno en cada llamada (importante en GitHub Actions).
    Devuelve True si no hay credenciales (no es error) o si Telegram respondió ok.
    False si había credenciales pero la API falló.
    En GitHub Actions, credenciales vacías tras normalizar = error (evita job “verde” sin Telegram).
    """
    token = _telegram_secret("TELEGRAM_BOT_TOKEN")
    raw_chat = _telegram_secret("TELEGRAM_CHAT_ID")
    if not token or not raw_chat:
        if _running_in_github_actions():
            print(
                "::error::TELEGRAM_BOT_TOKEN o TELEGRAM_CHAT_ID vacíos o inválidos "
                "(revisa secretos: sin espacios extra, token del BotFather, chat_id numérico).",
                file=sys.stderr,
            )
            return False
        print("[Aviso] Telegram no configurado; mensaje no enviado:", message[:200], file=sys.stderr)
        return True
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    if re.fullmatch(r"-?\d+", raw_chat):
        chat: str | int = int(raw_chat)
    else:
        chat = raw_chat
    payload = {
        "chat_id": chat,
        "text": message,
        "disable_web_page_preview": True,
    }
    data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=data,
        headers={"Content-Type": "application/json; charset=utf-8"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            raw = resp.read().decode("utf-8")
            try:
                out = json.loads(raw)
            except json.JSONDecodeError:
                print(f"Telegram respuesta no JSON: {raw[:300]}", file=sys.stderr)
                return False
            if out.get("ok"):
                print("Telegram OK (mensaje enviado).", flush=True)
                return True
            print(f"Telegram API ok=false: {raw[:500]}", file=sys.stderr)
            return False
    except urllib.error.HTTPError as e:
        err_body = e.read().decode("utf-8", errors="replace")
        print(f"Error Telegram HTTP {e.code}: {e.reason}\n{err_body}", file=sys.stderr)
        if e.code == 400 and "chat not found" in err_body.lower():
            print(
                "\n→ El chat_id no es válido para este bot, o aún no has escrito al bot.\n"
                "  1) Abre Telegram, busca tu bot y envía /start (o cualquier mensaje).\n"
                "  2) Ejecuta: python monitor_motos.py --probar-telegram\n"
                "     y copia el chat_id que salga en TELEGRAM_CHAT_ID del .env\n",
                file=sys.stderr,
            )
        return False
    except urllib.error.URLError as e:
        print(f"Error Telegram: {e}", file=sys.stderr)
        return False


def normalize_price(s: str) -> str:
    if not s:
        return ""
    s = s.lower().replace(" ", "")
    s = re.sub(r"[^\d.,]", "", s)
    return s


def _url_points_at_marketplace_item(url: str) -> bool:
    """True si la URL pedida es la de un anuncio (aunque luego Facebook redirija)."""
    if not url:
        return False
    try:
        return "/marketplace/item/" in (urlparse(url).path or "").lower()
    except Exception:
        return False


def _looks_like_facebook_auth_redirect(final_url: str) -> bool:
    """Login, checkpoint o enlaces intermedios típicos (p. ej. l.php) antes del anuncio."""
    u = (final_url or "").lower()
    if not u:
        return False
    if "login" in u or "checkpoint" in u or "/oauth" in u:
        return True
    try:
        p = urlparse(final_url)
        path = (p.path or "").lower().rstrip("/")
        host = (p.netloc or "").lower()
    except Exception:
        return False
    if path in ("/login", "/login.php"):
        return True
    if "facebook.com" in host and (path == "/l.php" or path.startswith("/l.php")):
        return True
    return False


def classify_snapshot(data: dict, final_url: str, start_url: str = "") -> tuple[bool, str, str | None]:
    """
    Devuelve (lectura_valida, pagina_tipo, motivo).
    pagina_tipo: anuncio | login | cookies | no_item | vacio | desconocida
    (En fetch_listing, errores HTTP tempranos usan pagina_tipo "http_error".)

    Importante: hay que detectar login/redirección *antes* de exigir /marketplace/item/ en la
    URL final; si no, un 302 a login se etiquetaba como no_item y avisaba mal en Telegram.
    """
    path = urlparse(final_url or "").path.lower()

    if data.get("blocked"):
        return (
            False,
            "login",
            "Facebook pide iniciar sesión. Ejecuta: python monitor_motos.py --guardar-sesion",
        )

    if _looks_like_facebook_auth_redirect(final_url):
        return (
            False,
            "login",
            "Redirección a login, verificación o enlace intermedio de Facebook. "
            "Renueva la sesión (local: --guardar-sesión; CI: caché o PLAYWRIGHT_STORAGE_B64).",
        )

    if data.get("cookieLikely"):
        return False, "cookies", "Parece el diálogo o capa de cookies (revisa captura con --debug)."

    if "/marketplace/item/" not in path:
        if _url_points_at_marketplace_item(start_url):
            return (
                False,
                "login",
                "Facebook redirigió fuera del anuncio (sesión caducada o bloqueo en headless). "
                "Actualiza playwright_storage.json o el secreto PLAYWRIGHT_STORAGE_B64.",
            )
        return False, "no_item", "La URL no acabó en /marketplace/item/… (redirección o error)."

    titulo = (data.get("titulo") or "").strip()
    tl = titulo.lower()

    if len(titulo) < 4:
        return False, "vacio", "Sin título útil; probablemente no cargó el anuncio."

    if tl == "facebook" or tl.startswith("iniciar sesión") or "log in to facebook" in tl:
        return (
            False,
            "login",
            "Título de pantalla de acceso. Ejecuta: python monitor_motos.py --guardar-sesion",
        )

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
            result["pagina_tipo"] = "http_error"
            result["motivo_lectura"] = f"Respuesta HTTP {resp.status} al cargar la página."
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

    css_sel = load_price_css_selector()
    if css_sel:
        candidates = [css_sel.strip()]
        no_mount = re.sub(r"^#mount_[a-zA-Z0-9_]+\s*>\s*", "", css_sel.strip())
        if no_mount and no_mount != css_sel.strip():
            candidates.append(no_mount)
        for sel in candidates:
            try:
                loc = page.locator(sel).first
                if await loc.count() > 0:
                    txt = (await loc.inner_text()).strip()
                    if txt and (re.search(r"\d", txt) or "€" in txt or "EUR" in txt.upper()):
                        result["precio"] = txt
                        break
            except Exception:
                continue

    result["disponible"] = bool(data.get("disponible", True))
    result["blocked"] = bool(data.get("blocked", False))
    result["cookie_banner"] = bool(data.get("cookieLikely", False))

    valid, tipo, motivo = classify_snapshot(data, result["url_final"], url)
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

        raw_results = await asyncio.gather(*(one(u) for u in urls), return_exceptions=True)

        await browser.close()

    results: list[tuple[str, dict]] = []
    for url, res in zip(urls, raw_results):
        if isinstance(res, Exception):
            print(f"[error] {url}\n  {res!r}", file=sys.stderr)
            results.append(
                (
                    url,
                    {
                        "titulo": "",
                        "precio": "",
                        "disponible": True,
                        "error": str(res),
                        "blocked": False,
                        "cookie_banner": False,
                        "url_final": url,
                        "lectura_valida": False,
                        "pagina_tipo": "desconocida",
                        "motivo_lectura": str(res),
                    },
                )
            )
        else:
            results.append(res)

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

    # Quitar del JSON entradas de URLs que ya no están en urls_motos.txt (evita estado eternamente hinchado).
    keep = set(urls)
    for stale in [k for k in url_map if k not in keep]:
        del url_map[stale]


def cmd_probar_telegram() -> None:
    token = _telegram_secret("TELEGRAM_BOT_TOKEN")
    if not token:
        print("Falta TELEGRAM_BOT_TOKEN en .env o en el entorno.", file=sys.stderr)
        sys.exit(1)
    base = f"https://api.telegram.org/bot{token}/"
    try:
        with urllib.request.urlopen(base + "getMe", timeout=20) as r:
            me = json.loads(r.read().decode("utf-8"))
        if not me.get("ok"):
            print("getMe:", me, file=sys.stderr)
            sys.exit(1)
        b = me.get("result") or {}
        print(f"Bot @{b.get('username')} — token correcto.")
    except urllib.error.HTTPError as e:
        print("Token inválido o error API:", e.read().decode("utf-8", errors="replace"), file=sys.stderr)
        sys.exit(1)
    except urllib.error.URLError as e:
        print("Red:", e, file=sys.stderr)
        sys.exit(1)

    try:
        with urllib.request.urlopen(base + "getUpdates?limit=40", timeout=20) as r:
            up = json.loads(r.read().decode("utf-8"))
    except urllib.error.URLError as e:
        print("getUpdates:", e, file=sys.stderr)
        sys.exit(1)

    results = up.get("result") or []
    if not results:
        print(
            "\nNo hay conversaciones recientes con este bot.\n"
            "Abre Telegram → busca tu bot → envía /start (o hola).\n"
            "Después vuelve a ejecutar: python monitor_motos.py --probar-telegram\n"
        )
        return

    seen: set[tuple] = set()
    print("\nUsa uno de estos valores en TELEGRAM_CHAT_ID (chat privado = tu número):")
    for u in results:
        msg = u.get("message") or u.get("channel_post") or u.get("edited_message")
        if not msg:
            continue
        chat = msg.get("chat") or {}
        cid = chat.get("id")
        typ = chat.get("type")
        name = chat.get("title") or chat.get("username") or chat.get("first_name") or ""
        key = (cid, typ)
        if key in seen:
            continue
        seen.add(key)
        print(f"  TELEGRAM_CHAT_ID={cid}   (tipo: {typ}, {name})")
    print()


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Monitor Facebook Marketplace → estado_motos.json + Telegram")
    p.add_argument(
        "--probar-telegram",
        action="store_true",
        help="Comprueba el token (getMe) y muestra chat_id desde getUpdates (envía /start al bot antes).",
    )
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
    if args.probar_telegram:
        cmd_probar_telegram()
        return
    if args.guardar_sesion:
        asyncio.run(guardar_sesion_facebook_interactiva())
        return

    urls = load_urls()
    state = load_state()
    url_map: dict[str, dict] = state["urls"]
    now_iso = datetime.now(timezone.utc).isoformat()

    startup_telegram_ok = True
    # En GitHub Actions también se envía por defecto. Para desactivar: MW_SKIP_MONITOR_STARTUP=1
    if os.environ.get("MW_SKIP_MONITOR_STARTUP", "").lower() not in ("1", "true", "yes"):
        startup_telegram_ok = send_telegram(TELEGRAM_STARTUP_MESSAGE)
        if not startup_telegram_ok and not _running_in_github_actions():
            print("Fallo al enviar a Telegram con credenciales configuradas; abortando.", file=sys.stderr)
            sys.exit(1)

    if args.verificar:
        print("OK = lectura considerada anuncio real | tipo = login|cookies|anuncio|…")
        print("-" * 120)

    try:
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
    finally:
        if not args.verificar:
            save_state(state)
            print(f"Estado guardado en {STATE_FILE}", flush=True)

    if args.verificar:
        print("-" * 120)
        print("(Modo --verificar: no se guarda estado_motos.json.)")
        return

    if not startup_telegram_ok:
        print("Fallo el mensaje inicial a Telegram (revisa token, chat_id y que hayas escrito al bot).", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
