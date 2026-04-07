# -*- coding: utf-8 -*-
import asyncio
import json
import csv
import os
import sys
from datetime import datetime, timezone
from statistics import mean
import pandas as pd
import time  # Added for timestamps in orden_real and BLOQUE 5
import random  # Added for jitter in BLOQUE 1.3
import itertools  # For req_counter in api_call
import math
import importlib
import warnings

os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")

def _load_optional_module(name: str):
    try:
        if str(name) == "pygame":
            with warnings.catch_warnings():
                warnings.filterwarnings(
                    "ignore",
                    message="pkg_resources is deprecated as an API.*",
                    category=UserWarning,
                )
                return importlib.import_module(name)
        return importlib.import_module(name)
    except Exception:
        return None

websockets = _load_optional_module("websockets")
WEBSOCKETS_OK = websockets is not None

colorama = _load_optional_module("colorama")
if colorama is not None:
    Fore = colorama.Fore
    Back = colorama.Back
    Style = colorama.Style
    init = colorama.init
else:
    class _NoColor:
        def __getattr__(self, _name):
            return ""
    Fore = _NoColor()
    Back = _NoColor()
    Style = _NoColor()
    def init(*args, **kwargs):
        return None

pygame = _load_optional_module("pygame")
PYGAME_OK = pygame is not None

# === BLINDAJE: señales limpias ===
import signal
from contextlib import suppress
stop_event = asyncio.Event()

def handle_stop(sig, frame):
    # no tumbar de golpe; pedimos apagado ordenado
    if not stop_event.is_set():
        stop_event.set()

for _sig in (signal.SIGINT, signal.SIGTERM):
    with suppress(Exception):
        signal.signal(_sig, handle_stop)

# === /BLINDAJE ===

init(autoreset=True)

# Inicio de mixer blindado
try:
    if not pygame.mixer.get_init():
        pygame.mixer.init()
except Exception as _e:
    print("Audio deshabilitado (mixer.init):", _e)

# Forzar que siempre use la carpeta donde está el script
script_dir = os.path.dirname(os.path.abspath(__file__))
os.chdir(script_dir)

# === PATCH SFX: audio seguro, canales y rate-limit ===
AUDIO_ENABLED = False
try:
    # Si ya inicializaste mixer arriba, sólo validamos canales
    pygame.mixer.set_num_channels(6)  # margen para solapamientos
    AUDIO_ENABLED = True
except Exception as _e:
    print("Audio deshabilitado (pygame.mixer):", _e)
    AUDIO_ENABLED = False

SFX_FILES = {
    "FELICITACIONES": "ia_scifi_01_felicitaciones_ivan_dry.wav",
    "LO_SIENTO": "ia_scifi_02_losiento_ivan_dry.wav",
    "PASO_A_REAL": "ia_scifi_03_paso_a_real_dry.wav",
    "REINTENTA": "ia_scifi_05_reintenta_dry.wav",
    "NO_CONCLUYO": "ia_scifi_06_no_concluyo_dry.wav",
    "NO_PASAR_REAL": "ia_scifi_07_no_pasar_real_dry.wav",
}
SFX = {}
_SFX_LAST_TS = {}
_SFX_MIN_INTERVAL = {
    "FELICITACIONES": 4.0,
    "LO_SIENTO": 4.0,
    "PASO_A_REAL": 2.0,   # ✅ más sensible
    "REINTENTA": 6.0,
    "NO_CONCLUYO": 10.0,
    "NO_PASAR_REAL": 6.0,
}

def _sfx_load_all():
    if not AUDIO_ENABLED:
        return
    for k, fname in SFX_FILES.items():
        p = os.path.join(script_dir, fname)
        try:
            if os.path.exists(p):
                SFX[k] = pygame.mixer.Sound(p)
            else:
                # Silencioso si no existe, no rompemos nada
                SFX[k] = None
        except Exception as e:
            print(f"No se pudo cargar SFX {k}: {e}")
            SFX[k] = None

def play_sfx(key: str, vol: float = 0.9):
    # Respeta MODO_SILENCIOSO y modo_manual (definidos en tu código)
    if not AUDIO_ENABLED:
        return
    if key not in SFX:
        return
    if SFX.get(key) is None:
        return
    # Rate-limit
    now = time.time()
    last = _SFX_LAST_TS.get(key, 0.0)
    min_iv = _SFX_MIN_INTERVAL.get(key, 4.0)
    if now - last < min_iv:
        return
    # Si el usuario forzó silencio (MANUAL), no sonar
    manual = False
    try:
        manual = bool(estado_bot.get("modo_manual"))
    except NameError:
        manual = False
    # Si el usuario forzó silencio (MANUAL), no sonar...
    # ...PERO no silenciamos el "PASO_A_REAL" ni sonidos de resultado (clave para tu lógica).
    if 'MODO_SILENCIOSO' in globals() and MODO_SILENCIOSO and manual and key not in ("PASO_A_REAL", "FELICITACIONES", "LO_SIENTO"):
        return

    try:
        ch = pygame.mixer.find_channel(True)
        if ch:
            SFX[key].set_volume(max(0.0, min(1.0, vol)))
            ch.play(SFX[key])
            _SFX_LAST_TS[key] = now
    except Exception as e:
        # Nunca rompemos lógica por un sonido
        if _print_once(f"sfx-{key}-err", ttl=60.0):
            print(f"SFX falló ({key}): {e}")

# Carga diferida para evitar bloquear import
_sfx_load_all()

# === /PATCH SFX ===

# ==================== CONFIG BÁSICA ====================
NOMBRE_BOT = "fulll50"
ARCHIVO_CSV = f"registro_enriquecido_{NOMBRE_BOT}.csv"
ARCHIVO_TOKEN = "token_actual.txt"  # Fuente única de verdad (coincide con 5R6M)
DERIV_WS_URL = "wss://ws.derivws.com/websockets/v3?app_id=1089"
ACTIVOS = ["1HZ10V", "1HZ25V", "1HZ50V", "1HZ75V", "1HZ100V"]
MARTINGALA_DEMO = [1, 2, 4, 8]
MARTINGALA_REAL = [1, 2, 4, 8]
VELAS = 20
PAUSA_POST_OPERACION_S = 8  # Pausa uniforme tras cada operación con resultado definido (BLOQUE 1)
# ==================== VENTANA DE DECISIÓN IA ====================
# Objetivo: dar tiempo al MAESTRO + humano para decidir pasar a REAL ANTES del BUY.
# (0 para desactivar)
VENTANA_DECISION_IA_S = 30        # segundos (alineado con maestro)
VENTANA_DECISION_IA_POLL_S = 0.10 # granularidad de espera
# === Filtro avanzado (sin cambiar 13 features) ===
SCORE_MIN = 2.35            # score mínimo para aceptar un setup
SCORE_DROP_MAX = 0.70       # caída máxima tolerada al revalidar pre-buy
REVALIDAR_VELAS_N = 8       # velas mínimas para revalidación rápida
resultado_global = {"demo": 0.0, "real": 0.0}
ultimo_token = None
reinicio_forzado = asyncio.Event()
estado_bot = {
    "ciclo_en_progreso": False,
    "token_msg_mostrado": False,
    "intentos_saldo": 0,
    "interrumpir_ciclo": False,
    "ciclo_forzado": None,
    "reinicios_consecutivos": 0,
    "modo_manual": False,
    "barra_activa": False,
    "score_senal": None,
    "ciclo_actual": 1,
}  # Added modo_manual and barra_activa
racha_actual_bot = 0  # racha del bot: >0 = racha de GANANCIAS, <0 = racha de PÉRDIDAS

# === Handshake con 5R6M ===
primer_ingreso_real = False  # Sonido solo 1 vez por ventana

# Variables persistentes para saldos últimos válidos
saldo_demo_last = 0.0
saldo_real_last = 0.0
real_activado_en_bot = 0.0  # BLOQUE 5: Global for activation timestamp

# BLOQUE 2: Commit guard for REAL operations
REAL_COMMIT_WINDOW_S = 20
last_real_contract_id = None
real_buy_commit_until = 0.0

# Higiene de riesgo: al saltar a REAL, arrancar en C1 (aunque el maestro sugiera C2+)
RESET_CICLO_EN_ENTRADA_REAL = False

def commit_guard_active() -> bool:
    return (last_real_contract_id is not None) and (time.time() < real_buy_commit_until)

def commit_guard_set(contract_id: int):
    global last_real_contract_id, real_buy_commit_until
    last_real_contract_id = contract_id
    real_buy_commit_until = time.time() + REAL_COMMIT_WINDOW_S

def commit_guard_clear():
    global last_real_contract_id, real_buy_commit_until
    last_real_contract_id = None
    real_buy_commit_until = 0.0

# >>> PATCH 1 — Helpers de orden de ciclo
ORDEN_DIR = "orden_real"  # misma carpeta usada por el maestro
# === IA ACK (handshake maestro→bot) ===
IA_ACK_DIR = "ia_ack"
try:
    os.makedirs(IA_ACK_DIR, exist_ok=True)
except Exception:
    pass

def leer_ia_ack(bot: str):
    path = os.path.join(IA_ACK_DIR, f"{bot}.json")
    try:
        if not os.path.exists(path):
            return None
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None

MAX_CICLOS = len(MARTINGALA_REAL)
# ✅ Asegura carpeta de órdenes (evita rarezas si el maestro aún no la creó)
try:
    os.makedirs(ORDEN_DIR, exist_ok=True)
except Exception:
    pass


def leer_orden_real(bot: str):
    """
    Devuelve (ciclo, ts, quiet, src) si existe orden fresca, o (None, None, 0, None) si no.
    """
    ruta = os.path.join(ORDEN_DIR, f"{bot}.json")
    tmp = ruta + ".tmp"
    try:
        if os.path.exists(ruta):
            with open(ruta, "r", encoding="utf-8") as f, open(tmp, "w", encoding="utf-8") as t:
                t.write(f.read())
            with open(tmp, "r", encoding="utf-8") as f:
                data = json.load(f)
            os.remove(tmp)
            if data.get("bot") != bot:
                return None, None, 0, None
            cyc = int(data.get("ciclo", 1))
            ts = float(data.get("ts", 0.0))
            ttl = int(data.get("ttl", 120))
            quiet = 1 if int(data.get("quiet", 0)) == 1 else 0
            src = str(data.get("src", "") or "").upper() or None
            lim = max(30, min(ttl, 300))  # margen seguro
            if time.time() - ts > lim:
                return None, None, 0, None
            return max(1, min(cyc, MAX_CICLOS)), ts, quiet, src
        return None, None, 0, None
    except Exception:
        if os.path.exists(tmp):
            os.remove(tmp)
        return None, None, 0, None

# <<< PATCH 1

# >>> PATCH: WS robusto
WS_KW = dict(ping_interval=15, ping_timeout=10, close_timeout=5, max_queue=None)
# <<< PATCH

# >>> PATCH (cerca de tus globals) BLOQUE 10
MODO_SILENCIOSO = False
_last_log = {}

def _print_once(key: str, ttl: float = 25.0) -> bool:
    now = time.time()
    exp = _last_log.get(key, 0)
    if now < exp:
        return False
    _last_log[key] = now + ttl
    return True

async def _desactivar_silencioso_en(seg=90):
    await asyncio.sleep(seg)
    global MODO_SILENCIOSO
    MODO_SILENCIOSO = False

async def _silencio_temporal(seg=90, fuente=None):
    global MODO_SILENCIOSO
    MODO_SILENCIOSO = True
    estado_bot["modo_manual"] = (str(fuente).upper() == "MANUAL")
    try:
        await asyncio.sleep(seg)
    finally:
        MODO_SILENCIOSO = False
        estado_bot["modo_manual"] = False

# <<< PATCH

# >>> PATCH (globals) BLOQUE 3
_contratos_procesados = set()
# <<< PATCH

# >>> PATCH (globals) BLOQUE 3 y BLOQUE 4
csv_lock = asyncio.Lock()
# <<< PATCH

# >>> PATCH: cooldown antirrebote BLOQUE 2 y 9
COOLDOWN_REAL_S = 12
# <<< PATCH

# >>> PATCH BLOQUE 4 y 8
REFRESCO_SALDO = 12
_last_saldo_ts = 0.0
# <<< PATCH

# >>> BLOQUE A: Buffer de logs para no romper la barra
log_buffer = []

def _buffer_log(msg: str):
    log_buffer.append(msg)

def _flush_log_buffer():
    if not log_buffer:
        return
    print()
    for m in log_buffer:
        print(m)
    log_buffer.clear()

# <<< BLOQUE A

# >>> BLOQUE B: Key para commit notice
def _commit_notice_key():
    return f"commit-guard-{last_real_contract_id or 'cooldown'}"

# <<< BLOQUE B

# >>> BLOQUE C: Separadores limpios para consola
def sep_saldos():
    """Separador discreto para bloques de saldo."""
    print(Fore.GREEN + "─" * 60)

def sep_ciclo():
    """Separador discreto para inicio/fin de ciclos de martingala."""
    print(Fore.BLUE + "─" * 60)

# <<< BLOQUE C

# ==================== UTILIDADES ====================
# Header único para el CSV enriquecido (incluye racha_actual y es_rebote)
# === HEADER FINAL CORREGIDO (23 columnas exactas) ===
CSV_HEADER = [
    "fecha", "activo", "direction", "monto", "resultado", "ganancia_perdida",
    "rsi_9", "rsi_14", "sma_5", "sma_20",
    "cruce_sma", "breakout", "rsi_reversion", "racha_actual", "es_rebote", "ciclo_martingala",
    "payout_total",          # nuevo: USD total retornado (stake + profit)
    "payout_multiplier",     # nuevo: ratio total/stake (independiente del monto)
    "puntaje_estrategia",
    "result_bin",            # 1 o 0 solo en filas cerradas
    "trade_status",          # "PRE_TRADE" o "CERRADO"
    "epoch",
    "ts",
    "ia_prob_en_juego",
    "ia_prob_source",
    "ia_decision_id",
    "ia_gate_real",
    "ia_modo_ack",
    "ia_ready_ack"
]
CLOSE_SNAPSHOT_COLS = [f"close_{i}" for i in range(20)]
CSV_HEADER = CSV_HEADER + CLOSE_SNAPSHOT_COLS
# =============================================================================
# CSV — helpers robustos (evita columnas corridas + asegura puntaje 0..1)
# =============================================================================
def _to_float(x, default=0.0):
    try:
        if x is None:
            return default
        if isinstance(x, str):
            s = x.strip()
            if s == "":
                return default
            s = s.replace(",", ".")
            return float(s)
        return float(x)
    except Exception:
        return default

def _warn_close_snapshot_insuficiente(closes, total: int = 20, min_valid: int = 10, cooldown_s: float = 120.0):
    try:
        valid_closes = sum(1 for c in list(closes or []) if isinstance(c, (int, float)) and math.isfinite(float(c)) and float(c) > 0.0)
    except Exception:
        valid_closes = 0
    if valid_closes >= int(min_valid):
        return
    now = time.time()
    last = float(globals().get("_last_warn_close_snapshot_ts", 0.0) or 0.0)
    if (now - last) < float(cooldown_s):
        return
    globals()["_last_warn_close_snapshot_ts"] = now
    print(Fore.YELLOW + f"[WARN] close_snapshot insuficiente: {valid_closes}/{int(total)}")

def _extract_close_snapshot(velas, n: int = 20):
    closes = []
    try:
        seq = list(velas or [])
        if not seq:
            return [None] * int(n)
        seq = seq[-int(n):]
        seq = list(reversed(seq))  # close_0 = más reciente
        for v in seq:
            c = None
            if isinstance(v, dict):
                c = v.get("close", v.get("c"))
            elif isinstance(v, (int, float)) and not isinstance(v, bool):
                c = v
            else:
                c = None
            try:
                cf = float(c)
                closes.append(cf if math.isfinite(cf) else None)
            except Exception:
                closes.append(None)
        while len(closes) < int(n):
            closes.append(None)
    except Exception:
        closes = [None] * int(n)
    return closes[:int(n)]

def _norm_puntaje_01(condiciones, total_cond=3):
    """
    Acepta:
      - 0..1 ya normalizado
      - enteros 0..3
      - strings tipo "2/3"
    Devuelve float en [0,1].
    """
    try:
        if isinstance(condiciones, str) and "/" in condiciones:
            a, b = condiciones.split("/", 1)
            a = _to_float(a, 0.0)
            b = _to_float(b, float(total_cond))
            if b <= 0:
                return 0.0
            v = a / b
        else:
            v = _to_float(condiciones, 0.0)
            # si viene 2 o 3, lo llevamos a 2/3, 3/3
            if v > 1.0001 and total_cond > 0:
                v = v / float(total_cond)
        if v < 0.0:
            v = 0.0
        if v > 1.0:
            v = 1.0
        return float(v)
    except Exception:
        return 0.0

def _write_row_dict_atomic(archivo_csv: str, row_dict: dict):
    """
    Escribe SIEMPRE respetando el orden de CSV_HEADER.
    """
    row = [row_dict.get(col, "") for col in CSV_HEADER]
    write_csv_atomic(archivo_csv, row)

def _build_trade_uid(epoch_val, symbol, direccion, ciclo, token, ts_iso=None):
    try:
        ep = int(float(epoch_val or 0))
    except Exception:
        ep = int(time.time())
    cyc = int(ciclo) if ciclo is not None else 1
    sym = str(symbol or "").strip().upper()
    direc = str(direccion or "").strip().upper()
    tok = str(token or "NA").strip().upper()
    ts_part = str(ts_iso or "").strip()
    return f"{NOMBRE_BOT}|{ep}|C{cyc}|{sym}|{direc}|{tok}|{ts_part}"

def _trade_key_from_row(row: dict) -> str:
    rid = str((row or {}).get("ia_decision_id", "") or "").strip()
    if rid:
        return rid
    parts = [
        str((row or {}).get("activo", "") or "").strip().upper(),
        str((row or {}).get("direction", "") or "").strip().upper(),
        str((row or {}).get("epoch", "") or "").strip(),
        str((row or {}).get("ciclo_martingala", "") or "").strip(),
        str((row or {}).get("ts", "") or "").strip(),
    ]
    return "|".join(parts)

def _audit_csv_trade_metrics(archivo_csv: str) -> tuple[int, int, int]:
    try:
        rec = {}
        with open(archivo_csv, "r", encoding="utf-8", newline="") as fh:
            reader = csv.DictReader(fh)
            for row in reader:
                status = str(row.get("trade_status", "")).strip().upper()
                if status not in {"PRE_TRADE", "PENDIENTE", "CERRADO"}:
                    continue
                key = _trade_key_from_row(row)
                if not key:
                    continue
                cur = rec.get(key, {"has_pre": False, "has_close": False, "rb": "", "ts": ""})
                cur["has_pre"] = bool(cur["has_pre"] or status in {"PRE_TRADE", "PENDIENTE"})
                if status == "CERRADO":
                    cur["has_close"] = True
                    cur["rb"] = str(row.get("result_bin", "")).strip()
                cur["ts"] = str(row.get("ts", cur.get("ts", "")) or cur.get("ts", ""))
                rec[key] = cur

        total_cerrados = 0
        ganancias = 0
        pendientes = 0
        for v in rec.values():
            rb = str(v.get("rb", "")).strip()
            if bool(v.get("has_close", False)) and rb in {"0", "1"}:
                total_cerrados += 1
                if rb == "1":
                    ganancias += 1
            elif bool(v.get("has_pre", False)):
                pendientes += 1
        return int(total_cerrados), int(ganancias), int(pendientes)
    except Exception:
        return 0, 0, 0

# === FIN HEADER FINAL ===
def write_pretrade_snapshot(
    archivo_csv,
    symbol=None,
    direccion=None,
    monto=None,
    rsi9=None,
    rsi14=None,
    sma5=None,
    sma20=None,
    cruce=None,
    breakout=None,
    rsi_reversion=None,
    ciclo=None,
    payout=None,
    condiciones=None,
    racha_actual_bot=0,
    **kwargs
):
    """
    PRE_TRADE snapshot consistente y tolerante:
    - Acepta llamada POSICIONAL (old) y llamada por KW (new) como la tuya.
    - Detecta payout como multiplier (<=3.5) o payout_total (>3.5).
    - puntaje_estrategia SIEMPRE 0..1
    - RETORNA epoch_val para GateWin/ACK.
    """

    # -------------------------
    # Aliases (tu llamada usa nombres distintos)
    # -------------------------
    if symbol is None:
        symbol = kwargs.get("activo") or kwargs.get("symbol")
    if direccion is None:
        direccion = kwargs.get("direccion") or kwargs.get("direction")
    if monto is None:
        monto = kwargs.get("monto") or kwargs.get("amount")

    if rsi9 is None:
        rsi9 = kwargs.get("rsi_9")
    if rsi14 is None:
        rsi14 = kwargs.get("rsi_14")
    if sma5 is None:
        sma5 = kwargs.get("sma_5")
    if sma20 is None:
        sma20 = kwargs.get("sma_20")

    if cruce is None:
        cruce = kwargs.get("cruce_sma")
    if breakout is None:
        breakout = kwargs.get("breakout")
    if rsi_reversion is None:
        rsi_reversion = kwargs.get("rsi_reversion")

    if ciclo is None:
        ciclo = kwargs.get("ciclo_martingala") or kwargs.get("ciclo")

    # condiciones/score puede venir como "puntaje_estrategia"
    if condiciones is None:
        condiciones = kwargs.get("puntaje_estrategia") or kwargs.get("condiciones")

    # racha previa real (PRE-TRADE)
    racha_prev = kwargs.get("racha_actual", racha_actual_bot)
    try:
        racha_prev = int(float(racha_prev))
    except Exception:
        racha_prev = int(racha_actual_bot) if isinstance(racha_actual_bot, (int, float)) else 0

    # es_rebote puede venir ya calculado
    es_rebote_in = kwargs.get("es_rebote", None)
    if es_rebote_in is None:
        es_rebote_flag = 1 if (racha_prev <= -4) else 0
    else:
        try:
            es_rebote_flag = 1 if int(float(es_rebote_in)) == 1 else 0
        except Exception:
            es_rebote_flag = 1 if (racha_prev <= -4) else 0

    # -------------------------
    # monto float
    # -------------------------
    try:
        monto_f = float(monto or 0.0)
    except Exception:
        monto_f = 0.0

    # -------------------------
    # payout robusto
    # -------------------------
    payout_total_f = 0.0
    payout_mult_f = 0.0
    try:
        p = float(payout) if payout not in (None, "", "nan", "NaN") else 0.0
        # si NaN/inf, lo anulamos
        try:
            if not math.isfinite(p):
                p = 0.0
            if not math.isfinite(monto_f):
                monto_f = 0.0
        except Exception:
            pass

        if p > 0 and p <= 3.5:
            payout_mult_f = p
            payout_total_f = (monto_f * payout_mult_f) if monto_f > 0 else 0.0
        elif p > 3.5:
            payout_total_f = p
            payout_mult_f = (payout_total_f / monto_f) if monto_f > 0 else 0.0
    except Exception:
        payout_total_f = 0.0
        payout_mult_f = 0.0

    # -------------------------
    # puntaje 0..1
    # -------------------------
    try:
        puntaje01 = _norm_puntaje_01(condiciones)
    except Exception:
        puntaje01 = 0.0

    now = datetime.now(timezone.utc)
    epoch_val = int(now.timestamp())
    ts_val = now.isoformat()
    trade_uid = str(kwargs.get("trade_uid", "") or "").strip()
    if not trade_uid:
        trade_uid = _build_trade_uid(epoch_val, symbol, direccion, ciclo, kwargs.get("token", "NA"), ts_iso=ts_val)
    close_snapshot = kwargs.get("close_snapshot", None)
    closes = _extract_close_snapshot(close_snapshot, n=20)
    _warn_close_snapshot_insuficiente(closes)

    row_dict = {
        "fecha": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "activo": symbol,
        "direction": direccion,
        "monto": float(monto_f),
        "resultado": "PENDIENTE",
        "ganancia_perdida": "",
        "rsi_9": rsi9,
        "rsi_14": rsi14,
        "sma_5": sma5,
        "sma_20": sma20,
        "cruce_sma": int(cruce) if cruce is not None else "",
        "breakout": int(breakout) if breakout is not None else "",
        "rsi_reversion": int(rsi_reversion) if rsi_reversion is not None else "",
        "racha_actual": int(racha_prev),
        "es_rebote": int(es_rebote_flag),
        "ciclo_martingala": int(ciclo) if ciclo is not None else 1,
        "payout_total": float(round(payout_total_f, 2)),
        "payout_multiplier": float(round(payout_mult_f, 6)),
        "puntaje_estrategia": float(round(float(puntaje01), 6)),
        "result_bin": "",
        "trade_status": "PRE_TRADE",
        "epoch": int(epoch_val),
        "ts": ts_val,
        "ia_prob_en_juego": "",
        "ia_prob_source": "",
        "ia_decision_id": trade_uid,
        "ia_gate_real": "",
        "ia_modo_ack": "",
        "ia_ready_ack": "",
    }
    for i, c in enumerate(closes):
        row_dict[f"close_{i}"] = "" if c is None else float(c)

    _write_row_dict_atomic(archivo_csv, row_dict)
    return epoch_val

def write_token_atomic(path: str, content: str):
    """
    Escritura atómica robusta para tokens (ARCHIVO_TOKEN).
    - Reintenta en Windows si el archivo está bloqueado por otro proceso.
    - Limpia .tmp si queda colgado.
    """
    tmp = path + ".tmp"
    last_err = None

    # 1) escribir tmp
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(content)
            f.flush()
            os.fsync(f.fileno())
    except Exception as e:
        print(Fore.RED + f"⚠️ Token: no pude escribir tmp: {e}")
        return

    # 2) replace atómico con reintentos
    for attempt in range(10):
        try:
            os.replace(tmp, path)
            return
        except PermissionError as e:
            last_err = e
            time.sleep(0.06 + 0.04 * attempt)
        except Exception as e:
            last_err = e
            break

    print(Fore.RED + f"⚠️ Token: os.replace falló: {last_err}")
    try:
        if os.path.exists(tmp):
            os.remove(tmp)
    except Exception:
        pass
def release_real_token_if_owned():
    """
    Libera el token REAL solo si el archivo todavía dice REAL:<este bot>.
    Evita pisar al MAESTRO si ya reasignó REAL a otro bot.
    """
    expected = f"REAL:{NOMBRE_BOT}"
    try:
        with open(ARCHIVO_TOKEN, "r", encoding="utf-8", errors="replace") as f:
            cur = (f.read() or "").strip()
    except Exception:
        return False

    # CAS: solo escribo si sigo siendo el dueño
    if cur == expected:
        try:
            write_token_atomic(ARCHIVO_TOKEN, "REAL:none")
            return True
        except Exception:
            return False

    return False

def write_csv_atomic(path: str, row):
    """
    Escritura atómica + auto-reparación de filas inconsistentes (columnas corridas / len != header).
    Garantía:
      - Header final SIEMPRE = CSV_HEADER
      - Cada fila SIEMPRE se escribe con len(CSV_HEADER) columnas (pad/truncate)
      - Evita que un CSV roto haga que pandas luego "skip" filas.
    """
    import os, csv, time

    def _norm_len(r, target_len: int):
        if r is None:
            return [""] * target_len
        r = list(r)
        if len(r) < target_len:
            r = r + ([""] * (target_len - len(r)))
        elif len(r) > target_len:
            r = r[:target_len]
        return r

    # ---------- Lock cross-process (maestro/bot) ----------
    lock_path = path + ".lock"
    fd = None
    start = time.time()
    try:
        while time.time() - start < 5:
            try:
                fd = os.open(lock_path, os.O_CREAT | os.O_EXCL | os.O_RDWR)
                break
            except FileExistsError:
                time.sleep(0.05)
        # si no se pudo lockear, igual continuamos (no matamos al bot)
    except Exception:
        fd = None

    num_cols = len(CSV_HEADER)
    tmp = path + ".tmp"

    rows_to_write = []
    old_header = []
    data_rows = []
    file_exists = os.path.exists(path) and os.path.getsize(path) > 0

    needs_repair = False

    if file_exists:
        try:
            with open(path, "r", newline="", encoding="utf-8", errors="replace") as f:
                reader = csv.reader(f)
                old_header = next(reader, None) or []
                data_rows = [r for r in reader]

            # Detectar filas "mutantes" aun si header coincide
            if old_header == CSV_HEADER:
                for r in data_rows[:300]:
                    if len(r) != num_cols:
                        needs_repair = True
                        break

            # Normalizar filas respecto a header viejo para evitar IndexError
            if old_header:
                data_rows = [_norm_len(r, len(old_header)) for r in data_rows]

            if old_header == CSV_HEADER:
                # Header igual: solo normalizamos longitudes
                rows_to_write = [_norm_len(r, num_cols) for r in data_rows]
            else:
                # Header distinto: remapeo por nombre si se puede
                idx = {name: i for i, name in enumerate(old_header)} if old_header else {}
                remapped = []
                for r in data_rows:
                    new_r = [""] * num_cols
                    mapped_any = False
                    for j, col in enumerate(CSV_HEADER):
                        if col in idx and idx[col] < len(r):
                            new_r[j] = r[idx[col]]
                            mapped_any = True
                    if not mapped_any:
                        new_r = _norm_len(r, num_cols)
                    remapped.append(_norm_len(new_r, num_cols))
                rows_to_write = remapped
                needs_repair = True  # header cambiado implica reescritura correctiva
        except Exception:
            # Si está muy roto, no frenamos: recreamos desde cero con la fila nueva
            rows_to_write = []
            needs_repair = True

    new_row = _norm_len(row, num_cols)

    # Guard anti-duplicado:
    # - Si NO hace falta reparar, y la última fila coincide, salimos.
    # - Si SÍ hace falta reparar, igual reescribimos (sin re-agregar duplicado).
    append_new = True
    if rows_to_write and rows_to_write[-1] == new_row:
        if not needs_repair:
            # CSV ya está sano, no hagas nada
            if fd is not None:
                try: os.close(fd)
                except: pass
                try: os.remove(lock_path)
                except: pass
            return
        append_new = False  # reparo pero no duplico

    # Escritura atómica con retries (sin mover el original a .bak antes)
    last_err = None
    for _ in range(3):
        try:
            with open(tmp, "w", newline="", encoding="utf-8", errors="replace") as f:
                w = csv.writer(f)
                w.writerow(CSV_HEADER)
                for r in rows_to_write:
                    w.writerow(_norm_len(r, num_cols))
                if append_new:
                    w.writerow(new_row)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp, path)
            last_err = None
            break
        except Exception as e:
            last_err = e
            try:
                if os.path.exists(tmp):
                    os.remove(tmp)
            except Exception:
                pass
            time.sleep(0.05)

    # Fallback final: append directo
    if last_err is not None:
        try:
            file_exists = os.path.exists(path) and os.path.getsize(path) > 0
            with open(path, "a", newline="", encoding="utf-8", errors="replace") as f:
                w = csv.writer(f)
                if not file_exists:
                    w.writerow(CSV_HEADER)
                w.writerow(new_row)
                f.flush()
                os.fsync(f.fileno())
        except Exception:
            pass

    # release lock
    if fd is not None:
        try: os.close(fd)
        except: pass
        try: os.remove(lock_path)
        except: pass
# ============================================================================
# PATCH CSV (SOLO) — Completar es_rebote y ciclo_martingala si vienen vacíos
# - No toca estrategia, no toca trading, no toca IA.
# - Solo asegura que el CSV enriquecido SIEMPRE tenga estas 2 columnas completas.
# ============================================================================
_CSV_REPARADO_1VEZ = False

def _to_int(x, default=0):
    try:
        if x is None:
            return default
        if isinstance(x, str) and x.strip() == "":
            return default
        return int(float(x))
    except Exception:
        return default

def infer_ciclo_por_monto(monto):
    """
    Si ciclo_martingala viene vacío, lo inferimos por el monto comparando con
    MARTINGALA_REAL / MARTINGALA_DEMO. Si no calza, devolvemos 1.
    """
    try:
        m = float(monto)
    except Exception:
        return 1

    secuencias = []
    try:
        if isinstance(MARTINGALA_REAL, (list, tuple)) and len(MARTINGALA_REAL) > 0:
            secuencias.append(MARTINGALA_REAL)
    except Exception:
        pass
    try:
        if isinstance(MARTINGALA_DEMO, (list, tuple)) and len(MARTINGALA_DEMO) > 0:
            secuencias.append(MARTINGALA_DEMO)
    except Exception:
        pass

    # Match exacto
    for seq in secuencias:
        for i, v in enumerate(seq):
            try:
                if abs(m - float(v)) <= 1e-9:
                    return i + 1
            except Exception:
                continue

    # Tolerancia por redondeos
    for seq in secuencias:
        for i, v in enumerate(seq):
            try:
                if abs(m - float(v)) <= 0.01:
                    return i + 1
            except Exception:
                continue

    return 1

def reparar_csv_esrebote_ciclo(archivo):
    """
    Repara SOLO filas donde es_rebote o ciclo_martingala están vacíos.
    No recalcula nada más. No altera columnas existentes.
    """
    try:
        if not os.path.exists(archivo):
            return

        with open(archivo, "r", newline="", encoding="utf-8") as f:
            rows = list(csv.reader(f))

        if not rows:
            return

        header = rows[0]
        if ("es_rebote" not in header) or ("ciclo_martingala" not in header):
            return

        idx_es = header.index("es_rebote")
        idx_ci = header.index("ciclo_martingala")
        idx_monto = header.index("monto") if "monto" in header else None

        changed = False
        fixed = [header]

        for r in rows[1:]:
            if not r:
                continue

            # Normaliza largo (sin mover columnas)
            if len(r) < len(header):
                r = r + [""] * (len(header) - len(r))
            elif len(r) > len(header):
                r = r[:len(header)]

            # Completar es_rebote si vacío
            if isinstance(r[idx_es], str) and r[idx_es].strip() == "":
                r[idx_es] = "0"
                changed = True

            # Completar ciclo_martingala si vacío
            if isinstance(r[idx_ci], str) and r[idx_ci].strip() == "":
                ciclo = 1
                if idx_monto is not None:
                    ciclo = infer_ciclo_por_monto(r[idx_monto])
                r[idx_ci] = str(int(ciclo))
                changed = True

            fixed.append(r)

        if changed:
            tmp = archivo + ".tmp_fix"
            with open(tmp, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerows(fixed)
            os.replace(tmp, archivo)
            print(Fore.YELLOW + "🧽 CSV reparado: es_rebote/ciclo_martingala completados (solo columnas vacías).")

    except Exception as e:
        print(Fore.RED + f"⚠️ No se pudo reparar CSV ({archivo}): {e}")

def cargar_tokens():
    """
    tokens_usuario.txt:
        línea 1 = TOKEN_DEMO
        línea 2 = TOKEN_REAL
    """
    ruta = "tokens_usuario.txt"
    intento = 0
    while True:
        try:
            if not os.path.exists(ruta):
                intento += 1
                if intento % 3 == 1:
                    print("tokens_usuario.txt no existe. Esperando a que la GUI lo genere...")
                time.sleep(3)
                continue
            with open(ruta, "r", encoding="utf-8") as f:
                lineas = [ln.strip() for ln in f.readlines()]
            if len(lineas) < 2 or not lineas[0] or not lineas[1]:
                intento += 1
                if intento % 5 == 1:
                    print("tokens_usuario.txt inválido (faltan líneas o están vacías). Reintentando...")
                time.sleep(3)
                continue
            demo, real = lineas[0], lineas[1]
            print(f"Tokens cargados desde archivo: DEMO={demo[:4]}*** REAL={real[:4]}***")
            return demo, real
        except Exception as e:
            intento += 1
            if intento % 5 == 1:
                print(f"Error leyendo tokens_usuario.txt: {e}. Reintentando en 3s...")
            time.sleep(3)

TOKEN_DEMO, TOKEN_REAL = cargar_tokens()

def reset_csv_and_total():
    """
    Borra el CSV si existe, lo recrea con el encabezado actualizado y
    resetea el total acumulado de DEMO (no REAL).
    Solo úsalo manualmente si quieres empezar una sesión limpia.
    """
    if os.path.exists(ARCHIVO_CSV):
        os.remove(ARCHIVO_CSV)
    with open(ARCHIVO_CSV, "w", newline="", encoding="utf-8", errors="replace") as f:
        writer = csv.writer(f)
        writer.writerow(CSV_HEADER)
    resultado_global["demo"] = 0.0
    print(Fore.YELLOW + "CSV limpiado manualmente y total DEMO resetado para sesión nueva.")

# Crea el CSV si no existe (con header actualizado, sin borrar histórico existente)
if not os.path.exists(ARCHIVO_CSV):
    with open(ARCHIVO_CSV, "w", newline="", encoding="utf-8", errors="replace") as f:
        writer = csv.writer(f)
        writer.writerow(CSV_HEADER)

def leer_token_desde_archivo():
    """
    Lee ARCHIVO_TOKEN. Si contiene 'REAL:fulll45' -> autoriza con TOKEN_REAL, si no -> TOKEN_DEMO.
    """
    try:
        with open(ARCHIVO_TOKEN, "r", encoding="utf-8", errors="replace") as f:
            linea = f.read().strip()
            if linea == f"REAL:{NOMBRE_BOT}":
                return TOKEN_REAL
    except:
        pass
    return TOKEN_DEMO

def calcular_rsi(cierres, periodo=14):
    if len(cierres) < periodo + 1:
        return 50
    ganancias, perdidas = [], []
    for i in range(1, periodo + 1):
        delta = cierres[-i] - cierres[-i - 1]
        (ganancias if delta > 0 else perdidas).append(abs(delta))
    media_gan = mean(ganancias) if ganancias else 0.0001
    media_per = mean(perdidas) if perdidas else 0.0001
    rs = media_gan / media_per
    return round(100 - (100 / (1 + rs)), 2)

def evaluar_estrategia(velas):
    # Normaliza a float por si Deriv devuelve strings
    cierres = [float(v["close"]) for v in velas]
    open_ = float(velas[-1]["open"])
    close = float(velas[-1]["close"])

    sma5 = sum(cierres[-5:]) / 5
    if len(cierres) >= 20:
        sma20 = sum(cierres[-20:]) / 20
    else:
        sma20 = sum(cierres) / max(1, len(cierres))

    rsi9 = calcular_rsi(cierres, 9)
    rsi14 = calcular_rsi(cierres, 14)

    high_prev = float(velas[-2]["high"])
    low_prev = float(velas[-2]["low"])

    breakout = (close > high_prev) or (close < low_prev)
    cruce_sma = ((sma5 > sma20 and close > sma5) or (sma5 < sma20 and close < sma5))
    rsi_reversion = ((rsi14 < 30 and rsi9 > rsi14) or (rsi14 > 70 and rsi9 < rsi14))

    direccion = "CALL" if close > open_ else "PUT"
    condiciones = int(breakout) + int(cruce_sma) + int(rsi_reversion)

    # Importante: mantenemos el orden de retorno que tu bot ya espera
    return condiciones, direccion, rsi9, rsi14, sma5, sma20, breakout, cruce_sma, rsi_reversion


def puntuar_setups(condiciones, direccion, rsi9, rsi14, sma5, sma20, breakout, cruce_sma, rsi_reversion):
    """
    Score interno para elegir MEJOR activo entre candidatos válidos (sin cambiar 13 features).
    Mantiene la regla base (>=2/3), pero evita tomar el primer símbolo "aceptable".
    """
    try:
        score = float(condiciones)

        # Alineación de tendencia con la dirección sugerida
        tendencia_call = (sma5 > sma20)
        tendencia_put = (sma5 < sma20)
        alineado = (direccion == "CALL" and tendencia_call) or (direccion == "PUT" and tendencia_put)
        if alineado:
            score += 0.75

        # Fortaleza del cruce (distancia relativa entre medias)
        den = max(abs(float(sma20)), 1e-9)
        gap = abs(float(sma5) - float(sma20)) / den
        score += min(0.50, gap * 25.0)

        # Confirmaciones de setup
        if breakout:
            score += 0.35
        if rsi_reversion:
            score += 0.25

        # Penalización suave si RSI está en zona "gris" (menos edge)
        if 45.0 <= float(rsi14) <= 55.0:
            score -= 0.15

        return float(score)
    except Exception:
        return float(condiciones or 0)


def setup_pasa_filtro(score: float, condiciones: int) -> bool:
    """Gate de calidad: mantiene >=2/3 y exige score mínimo."""
    try:
        return (int(condiciones) >= 2) and (float(score) >= float(SCORE_MIN))
    except Exception:
        return False
# ==================== WS HELPERS ====================
# BLOQUE 1: api_call wrapper
_req_counter = itertools.count(1)

async def api_call(ws, payload: dict, expect_msg_type: str = None, timeout=10.0):
    """
    Envia payload con req_id y espera respuesta con el mismo req_id.
    Si expect_msg_type se especifica, valida msg_type (con aliases defensivos).
    Lanza RuntimeError ante errores del API Deriv.
    """
    rid = next(_req_counter)
    payload = dict(payload)
    payload["req_id"] = rid

    await ws.send(json.dumps(payload))

    aliases = {
        "candles": {"history"},
        "history": {"candles"},
    }

    deadline = time.time() + float(timeout)

    while True:
        remaining = deadline - time.time()
        if remaining <= 0:
            raise TimeoutError(f"Timeout esperando respuesta para req_id={rid}")

        raw = await asyncio.wait_for(ws.recv(), timeout=remaining)

        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            # Mensaje corrupto/partial: ignora y sigue escuchando
            continue

        # Errores explícitos del API
        if data.get("error"):
            err = data["error"]
            raise RuntimeError(f"API error: {err.get('code')} - {err.get('message')}")

        # Filtra por req_id
        if data.get("req_id") != rid:
            continue

        # Si espero un msg_type específico, valido (con aliases)
        if expect_msg_type:
            mt = data.get("msg_type")
            if mt != expect_msg_type and mt not in aliases.get(expect_msg_type, set()):
                continue

        return data

async def authorize_ws(ws, token: str, tries: int = 3, timeout: float = 8.0):
    """Authorize robusto: reintenta antes de rendirse (reduce timeouts)."""
    last = None
    for i in range(tries):
        try:
            await api_call(ws, {"authorize": token}, expect_msg_type=None, timeout=timeout)
            return
        except Exception as e:
            last = e
            await asyncio.sleep(0.4 + 0.4 * i + random.uniform(0.0, 0.3))
    raise last

# BLOQUE 2: obtener_velas con cooldown
_symbol_cooldown = {}  # symbol -> epoch hasta el que está en pausa

# Salud WS
_ws_fail_streak = 0  # cuántas 1006/errores seguidos en esta pasada
ws_reset_needed = asyncio.Event()  # señal para que el loop principal reabra WS

def _es_error_transitorio_ws(exc: Exception) -> bool:
    """Errores de red/WS que deben reintentarse sin tumbar el ciclo."""
    if isinstance(exc, (asyncio.TimeoutError, TimeoutError, websockets.exceptions.ConnectionClosed, OSError)):
        return True
    msg = str(exc).lower()
    return (
        "connectionclosed" in msg
        or "timeout" in msg
        or "timed out" in msg
        or "se agotó el tiempo" in msg
        or "winerror 121" in msg
    )

async def obtener_velas(ws, symbol, token, reintentos=4):
    global _ws_fail_streak
    # respeta cooldown por símbolo
    until = _symbol_cooldown.get(symbol, 0)
    if time.time() < until:
        return []
    delay = 0.8
    for intento in range(reintentos):
        try:
            data = await api_call(ws, {
                "ticks_history": symbol,
                "adjust_start_time": 1,
                "count": VELAS,
                "end": "latest",
                "start": 1,
                "style": "candles",
                "granularity": 60
            }, expect_msg_type="candles", timeout=12.0)
            candles = data.get("candles", [])
            # Éxito: resetea racha de fallas WS
            if candles:
                _ws_fail_streak = 0
            return candles or []
        except websockets.exceptions.ConnectionClosed as e:
            # 1006/close: marca cooldown corto al símbolo y sube racha global
            _symbol_cooldown[symbol] = time.time() + 20
            _ws_fail_streak += 1
            if _print_once(f"ws-obt-closed-{symbol}", ttl=8):
                print(Fore.YELLOW + f"WS cerrado ({getattr(e, 'code', '???')}) en {symbol}. Reintento {intento+1}/{reintentos}...")
        except (asyncio.TimeoutError, json.JSONDecodeError):
            if _print_once(f"ws-obt-timeout-{symbol}", ttl=8):
                print(Fore.YELLOW + f"Timeout/JSON en velas {symbol}. Reintentando...")
        except RuntimeError as api_e:
            msg = str(api_e)
            if "RateLimit" in msg or "market" in msg.lower():
                pass  # retry suave
            else:
                # error “duro”: enfría más tiempo y abandona
                _symbol_cooldown[symbol] = time.time() + 90
                if _print_once(f"cool-{symbol}", ttl=60):
                    print(Fore.YELLOW + f"{symbol} en cooldown 90s por error: {api_e}")
                return []
        except Exception as e:
            if _print_once(f"ws-obt-err-{symbol}", ttl=8):
                print(Fore.RED + f"Error velas {symbol}: {e}. Reintentando...")
        # Fallback: desde el 3er intento usa una conexión efímera dedicada
        if intento >= 2:
            try:
                async with websockets.connect(DERIV_WS_URL, **WS_KW) as ws2:
                    await authorize_ws(ws2, token, tries=2, timeout=6.0)
                    data2 = await api_call(ws2, {
                        "ticks_history": symbol,
                        "adjust_start_time": 1,
                        "count": VELAS,
                        "end": "latest",
                        "start": 1,
                        "style": "candles",
                        "granularity": 60
                    }, expect_msg_type="candles", timeout=12.0)
                    candles2 = data2.get("candles", [])
                    if candles2:
                        _ws_fail_streak = 0
                    return candles2 or []
            except Exception as e2:
                # si también falla, seguimos con backoff
                if _print_once(f"ws-efimera-{symbol}", ttl=8):
                    print(Fore.YELLOW + f"Fallback efímero falló en {symbol}: {e2}")
        await asyncio.sleep(delay + random.uniform(0.0, 0.5))  # Jitter para evitar rate-limits
        delay = min(delay * 1.5, 3.0)
    return []

async def check_token_and_reconnect(ws, current_token):
    global ultimo_token
    global primer_ingreso_real, real_activado_en_bot
    token_desde_archivo = leer_token_desde_archivo()
    if token_desde_archivo != current_token:
        # BLOQUE 2 y 9: Anti-rebote + commit guard
        if current_token == TOKEN_REAL and token_desde_archivo == TOKEN_DEMO:
            # SOLO ignorar "rebote a DEMO" si hay ciclo en progreso.
            if estado_bot.get("ciclo_en_progreso") and (commit_guard_active() or (time.time() - real_activado_en_bot < COOLDOWN_REAL_S)):
                key = _commit_notice_key()
                if not estado_bot.get("barra_activa", False) and _print_once(key, ttl=180):
                    print(Fore.YELLOW + "Commit REAL o cooldown activo: ignorando rebote a DEMO.")
                return ws, current_token

        if estado_bot["ciclo_en_progreso"]:
            # Corte en caliente: interrumpe el reloj YA
            if not estado_bot.get("token_msg_mostrado", False):
                if not (MODO_SILENCIOSO and estado_bot.get("modo_manual")):
                    print(Fore.MAGENTA + Style.BRIGHT + "Cambio de token detectado: cortando ciclo y aplicando de inmediato.")
                estado_bot["token_msg_mostrado"] = True
            estado_bot["interrumpir_ciclo"] = True
            reinicio_forzado.set()
            return ws, current_token  # dejar que esperar_resultado lo desprenda
        else:
            print(Fore.YELLOW + Style.BRIGHT + f"Token cambió a {'REAL' if token_desde_archivo == TOKEN_REAL else 'DEMO'}. Reconectando...")
            try:
                await ws.close()
            except:
                pass
            ws = await websockets.connect(DERIV_WS_URL, **WS_KW)  # BLOQUE 1.2
            await authorize_ws(ws, token_desde_archivo)
            await asyncio.sleep(0.6 + random.uniform(0.0, 0.5))  # BLOQUE 4: micro-cooldown
            if token_desde_archivo == TOKEN_REAL:
                # >>> PATCH 4 — Al entrar a REAL, preconfigura el ciclo forzado
                if not primer_ingreso_real:
                    print(Fore.LIGHTRED_EX + Back.WHITE + Style.BRIGHT + f"\n{NOMBRE_BOT.upper()} ENTRÓ EN CUENTA REAL {datetime.now().strftime('%H:%M:%S')}")
                    # SFX: PASO_A_REAL (reemplaza racha_detectada.wav)
                    try:
                        play_sfx("PASO_A_REAL", vol=0.9)
                    except Exception:
                        pass
                    primer_ingreso_real = True
                    real_activado_en_bot = time.time()  # BLOQUE 5 and 2: Set activation time
                    # Lee la orden del maestro y deja seteado el ciclo para la siguiente vuelta
                    cyc, _, quiet, src = leer_orden_real(NOMBRE_BOT)  # BLOQUE 7: Relee fresh
                    ciclo_objetivo = cyc if cyc else estado_bot.get("ciclo_forzado")
                    if ciclo_objetivo:
                        estado_bot["ciclo_forzado"] = int(max(1, min(int(ciclo_objetivo), MAX_CICLOS)))
                        if cyc:
                            print(Fore.YELLOW + f"Orden maestro detectada: arrancaré en ciclo #{estado_bot['ciclo_forzado']}.")
                    else:
                        estado_bot["ciclo_forzado"] = 1
                        if RESET_CICLO_EN_ENTRADA_REAL:
                            print(Fore.YELLOW + "Entrada REAL detectada: reinicio de martingala a C1 por seguridad.")

                    # Silenciar ruido guiado por maestro (BLOQUE 3)
                    if quiet or (str(src).upper() == "MANUAL"):
                        asyncio.create_task(_silencio_temporal(90, fuente=src))
                    else:
                        asyncio.create_task(_desactivar_silencioso_en(90))
                    reinicio_forzado.set()
                else:
                    if not (MODO_SILENCIOSO and estado_bot.get("modo_manual")) and not estado_bot.get("barra_activa", False):
                        if _print_once("rea-REAL", ttl=180):
                            print(Fore.YELLOW + "Reafirmación de REAL (sin reset de martingala)")
                    cyc, _, quiet, src = leer_orden_real(NOMBRE_BOT)  # BLOQUE 7: Relee fresh
                    ciclo_objetivo = cyc if cyc else estado_bot.get("ciclo_forzado")
                    if ciclo_objetivo:
                        estado_bot["ciclo_forzado"] = int(max(1, min(int(ciclo_objetivo), MAX_CICLOS)))
                    elif RESET_CICLO_EN_ENTRADA_REAL:
                        estado_bot["ciclo_forzado"] = 1

                    if quiet or (str(src).upper() == "MANUAL"):
                        asyncio.create_task(_silencio_temporal(90, fuente=src))
                    else:
                        asyncio.create_task(_desactivar_silencioso_en(90))
                # <<< PATCH 4
            else:
                # Saliste de REAL: prepara el sonido para la próxima ventana
                primer_ingreso_real = False
                reinicio_forzado.set()
            ultimo_token = token_desde_archivo  # mantén vigilante y lazo alineados
            return ws, token_desde_archivo
    else:
        if token_desde_archivo == TOKEN_REAL:
            # ✅ FIX: si el bot arranca/reconecta y ya está en REAL, igual debe "hablar" 1 vez
            if not primer_ingreso_real:
                if not estado_bot.get("barra_activa", False):
                    try:
                        print(
                            Fore.LIGHTRED_EX + Back.WHITE + Style.BRIGHT
                            + f"\n{NOMBRE_BOT.upper()} INICIÓ EN CUENTA REAL"
                            + Style.RESET_ALL
                        )
                    except Exception:
                        pass

                # Audio PASO_A_REAL (blindado)
                try:
                    play_sfx("PASO_A_REAL", vol=0.95)
                except Exception:
                    pass

                primer_ingreso_real = True
                try:
                    real_activado_en_bot = time.time()
                except Exception:
                        pass

            else:
                # Mantén tu mensaje de reafirmación como estaba (sin tocar otras lógicas)
                if not (MODO_SILENCIOSO and estado_bot.get("modo_manual")) and not estado_bot.get("barra_activa", False):
                    if _print_once("rea-REAL", ttl=180):
                        print(Fore.YELLOW + "Reafirmación de REAL (sin reset de martingala)")

        ultimo_token = token_desde_archivo  # mantén vigilante y lazo alineados
        return ws, current_token

async def vigilar_token():
    """Dispara reinicio cuando cambia el archivo token_actual.txt"""
    global ultimo_token
    while not stop_event.is_set():
        await asyncio.sleep(2)
        token_desde_archivo = leer_token_desde_archivo()
        if token_desde_archivo != ultimo_token:
            # BLOQUE 2 y 9: Anti-rebote + commit guard in watcher
            if ultimo_token == TOKEN_REAL and token_desde_archivo == TOKEN_DEMO:
                # SOLO ignorar "rebote a DEMO" si hay ciclo en progreso.
                if estado_bot.get("ciclo_en_progreso") and (commit_guard_active() or (time.time() - real_activado_en_bot < COOLDOWN_REAL_S)):
                    key = _commit_notice_key()
                    if not estado_bot.get("barra_activa", False) and _print_once(key, ttl=180):
                        print(Fore.YELLOW + "Commit REAL o cooldown activo: ignorando rebote a DEMO.")
                    continue
                        
            if estado_bot["ciclo_en_progreso"]:
                if not estado_bot.get("token_msg_mostrado", False):
                    if not (MODO_SILENCIOSO and estado_bot.get("modo_manual")):
                        print(Fore.MAGENTA + Style.BRIGHT + "Cambio de token detectado: cortando ciclo y aplicando de inmediato.")
                    estado_bot["token_msg_mostrado"] = True
                estado_bot["interrumpir_ciclo"] = True
                reinicio_forzado.set()
            else:
                ultimo_token = token_desde_archivo
                reinicio_forzado.set()

async def consultar_saldo_real(ws):
    global saldo_real_last
    try:
        data = await api_call(ws, {"balance": 1}, expect_msg_type="balance", timeout=6.0)
        b = data.get("balance", {}).get("balance")
        if b is not None:
            saldo_real_last = float(b)
            return saldo_real_last
        if _print_once("saldo-real-empty-main", ttl=20):
            print(Fore.YELLOW + "Balance REAL no disponible (respuesta vacía). Intento conexión dedicada...")
    except Exception as e:
        if _print_once("saldo-real-error-main", ttl=20):
            print(Fore.YELLOW + f"Balance por ws actual falló ({e}). Intento conexión dedicada...")
    # Conexión dedicada
    try:
        async with websockets.connect(DERIV_WS_URL, **WS_KW) as ws2:
            await authorize_ws(ws2, TOKEN_REAL, tries=2, timeout=6.0)
            data2 = await api_call(ws2, {"balance": 1}, expect_msg_type="balance", timeout=6.0)
            b2 = data2.get("balance", {}).get("balance")
            if b2 is not None:
                saldo_real_last = float(b2)
                return saldo_real_last
    except Exception as e2:
        if _print_once("saldo-real-error-dedicada", ttl=20):
            print(Fore.RED + Style.BRIGHT + f"[ERROR] al consultar saldo REAL (dedicada): {e2}")
    if _print_once("saldo-real-no-disponible-final", ttl=20):
        print(Fore.YELLOW + "Balance REAL no disponible. Uso último valor válido y **no compro** si no alcanza.")
    return saldo_real_last

# ==================== LÓGICA DE OPERACIÓN ====================
async def buscar_estrategia(ws, ciclo, token):
    print(Fore.MAGENTA + Style.BRIGHT + f"\nBuscando señal válida para Martingala #{ciclo}")
    for intento in range(1, 11):
        if reinicio_forzado.is_set():
            return "REINTENTAR", None, None, None, None, None, None, None, None, None, None
        if MODO_SILENCIOSO and estado_bot.get("modo_manual"):
            if intento in (1, 5, 10):
                print(Fore.YELLOW + f"Intento #{intento} (silencioso)...")
        else:
            print(Fore.YELLOW + f"Intento #{intento}...")
        errores_intento = []
        activos_invalidos = []
        mejores = []
        for symbol in ACTIVOS:
            velas = await obtener_velas(ws, symbol, token, reintentos=4)
            await asyncio.sleep(0.12 + random.uniform(0.0, 0.18))
            if reinicio_forzado.is_set():
                return "REINTENTAR", None, None, None, None, None, None, None, None, None, None
            try:
                if len(velas) < VELAS:
                    activos_invalidos.append(symbol)
                    continue
                condiciones, direccion, rsi9, rsi14, sma5, sma20, breakout, cruce, rsi_reversion = evaluar_estrategia(velas)
                if condiciones >= 2:
                    score = puntuar_setups(condiciones, direccion, rsi9, rsi14, sma5, sma20, breakout, cruce, rsi_reversion)
                    if setup_pasa_filtro(score, condiciones):
                        close_snapshot = _extract_close_snapshot(velas, n=20)
                        mejores.append((score, condiciones, symbol, direccion, rsi9, rsi14, sma5, sma20, breakout, cruce, rsi_reversion, close_snapshot))
                    else:
                        activos_invalidos.append(symbol)
                else:
                    activos_invalidos.append(symbol)
            except Exception as e:
                errores_intento.append(symbol)

        if mejores:
            # Prioridad: mayor score; desempate por más condiciones
            mejores.sort(key=lambda x: (x[0], x[1]), reverse=True)
            score, condiciones, symbol, direccion, rsi9, rsi14, sma5, sma20, breakout, cruce, rsi_reversion, close_snapshot = mejores[0]
            estado_bot["score_senal"] = float(score)
            print(Fore.GREEN + Style.BRIGHT + f"Estrategia válida en {symbol} | Dirección: {direccion} | Condiciones: {condiciones}/3 | Score={score:.3f}")
            return symbol, direccion, rsi9, rsi14, sma5, sma20, breakout, cruce, condiciones, rsi_reversion, close_snapshot

        if errores_intento:
            print(Fore.RED + f"Error WS en activos: {', '.join(errores_intento)} | Intento #{intento}")
        if activos_invalidos:
            msg_sil = (MODO_SILENCIOSO and estado_bot.get("modo_manual"))
            if not msg_sil:
                print(Fore.YELLOW + f"Ningún activo válido en intento #{intento}. Esperando 15s...")
            elif intento in (1, 5, 10):
                print(Fore.YELLOW + f"Sin activo válido (intento #{intento}, silencioso). Esperando 15s...")
        # Nueva lógica: si todos salieron inválidos y la racha de 1006 es alta, pide reconexión
        if len(activos_invalidos) == len(ACTIVOS) and _ws_fail_streak >= len(ACTIVOS):
            if _print_once("ws-reopen-needed", ttl=15):
                print(Fore.YELLOW + Style.BRIGHT + "Múltiples 1006 detectados en barrido. Señalando reconexión limpia del WS...")
            ws_reset_needed.set()
            # No seguimos martillando: pequeño respiro
            await asyncio.sleep(1.0 + random.uniform(0.0, 0.5))  # Jitter
        await asyncio.sleep(15 + random.uniform(0.0, 0.5))  # Jitter para pausas
    print(Fore.RED + Style.BRIGHT + f"No se encontró activo válido tras 10 intentos para Martingala #{ciclo}. Reintentando MISMO ciclo...")
    try:
        play_sfx("REINTENTA", vol=0.8)
    except Exception:
        pass
    await asyncio.sleep(30)
    return "REINTENTAR", None, None, None, None, None, None, None, None, None, None

async def esperar_resultado(ws, contract_id, symbol, direccion, monto, rsi9, rsi14, sma5, sma20, cruce, breakout, rsi_reversion, ciclo, payout, condiciones, token_usado_buy, epoch_pretrade=None, trade_uid=None, close_snapshot=None):
    # ✅ SIEMPRE cerramos/logueamos con el token real del BUY (aunque el maestro cambie token_actual.txt)
    token_antes = token_usado_buy
    print(Fore.CYAN + "=" * 80)
    estado_bot["barra_activa"] = True
    try:
        for i in range(60):
            # ¿Pediron corte inmediato? Desprendemos y liberamos YA.
            if estado_bot.get("interrumpir_ciclo"):
                remaining = 60 - i
                print(Fore.MAGENTA + Style.BRIGHT + "\nToken cambió: finalizo contrato en segundo plano y libero el ciclo.")
                # No reutilizar 'ws' para evitar choques de recv: usa una conexión propia
                asyncio.create_task(finalizar_contrato_bg(
                    contract_id, remaining, symbol, direccion, monto,
                    rsi9, rsi14, sma5, sma20, cruce, breakout, rsi_reversion,
                    ciclo, payout, condiciones, token_antes, epoch_pretrade=epoch_pretrade, trade_uid=trade_uid, close_snapshot=close_snapshot
                ))
                estado_bot["interrumpir_ciclo"] = False
                estado_bot["ciclo_en_progreso"] = False
                estado_bot["token_msg_mostrado"] = False
                return "INDEFINIDO", 0.0  # libera al loop para reautorizar ya
            if MODO_SILENCIOSO and estado_bot.get("modo_manual"):
                if i in (0, 29, 59):
                    barra = (
                        f"\r[{'█' * (i + 1)}{' ' * (59 - i)}] "
                        f"{i + 1:02d}s | C{ciclo} {symbol} {direccion} (silencioso)"
                    )
                    sys.stdout.write(barra)
                    sys.stdout.flush()
            else:
                barra = (
                    f"\r[{'█' * (i + 1)}{' ' * (59 - i)}] "
                    f"{i + 1:02d}s | C{ciclo} {symbol} {direccion}"
                )
                sys.stdout.write(barra)
                sys.stdout.flush()
            await asyncio.sleep(1 + random.uniform(0.0, 0.1))  # Pequeño jitter para stability
        print("\n" + "=" * 80)
        print(Fore.CYAN + Style.BRIGHT + "\nFinalizando contrato...")
        try:
            data = await api_call(ws, {"proposal_open_contract": 1, "contract_id": contract_id}, expect_msg_type="proposal_open_contract")
            poc = data.get("proposal_open_contract", {})
            profit = float(poc.get("profit", 0.0))
            resultado = "GANANCIA" if profit > 0 else "PÉRDIDA"
            # === PATCH SFX resultado principal ===
            try:
                if token_antes == TOKEN_REAL:
                    if resultado == "GANANCIA":
                        play_sfx("FELICITACIONES", vol=1.0)
                    else:
                        play_sfx("LO_SIENTO", vol=0.9)
            except Exception:
                pass
            # === /PATCH SFX ===
            color = Fore.GREEN if profit > 0 else Fore.RED
            print(color + Style.BRIGHT + f"{resultado}: {profit:.2f} USD")
            # >>> PATCH BLOQUE 3 y 5
            if contract_id in _contratos_procesados:
                return resultado, profit
            _contratos_procesados.add(contract_id)
            # <<< PATCH
            # Registrar resultado SOLO si es definido, con features enriquecidas
            try:
                global racha_actual_bot
                # 1) Actualizar racha del bot
                racha_anterior = racha_actual_bot
                if resultado == "GANANCIA":
                    racha_actual_bot = racha_actual_bot + 1 if racha_actual_bot > 0 else 1
                else:  # "PÉRDIDA"
                    racha_actual_bot = racha_actual_bot - 1 if racha_actual_bot < 0 else -1
                # 2) Detectar rebote (PRE-TRADE, sin fuga):
                #    Si veníamos de racha negativa larga ANTES del trade, marcamos rebote potencial.
                es_rebote_flag = 1 if (racha_anterior <= -4) else 0

                # 3) Escribir fila en CSV
                # ==========================================================
                # payout robusto (CIERRE NORMAL):
                # - si payout <= 3.5 => es payout_multiplier (ratio_total)
                # - si payout > 3.5  => es payout_total (USD)
                # Resultado SIEMPRE coherente:
                #   payout_total_f y ratio_total
                # ==========================================================
                payout_total_f = 0.0
                ratio_total = 0.0
                # monto
                try:
                    monto_f = float(monto) if monto not in (None, "", "nan", "NaN") else 0.0
                except Exception:
                    monto_f = 0.0

                # payout (puede venir como multiplier o como total)
                try:
                    p = float(payout) if payout not in (None, "", "nan", "NaN") else 0.0
                except Exception:
                    p = 0.0
                # si p es NaN/inf, lo anulamos
                try:
                    if not math.isfinite(p):
                        p = 0.0
                    if not math.isfinite(monto_f):
                        monto_f = 0.0
                except Exception:
                    pass                   
                try:
                    if p > 0 and p <= 3.5:
                        # payout viene como multiplier (1.95 etc.)
                        ratio_total = p
                        payout_total_f = (monto_f * ratio_total) if monto_f > 0 else 0.0
                    elif p > 3.5:
                        # payout viene como total (USD)
                        payout_total_f = p
                        ratio_total = (payout_total_f / monto_f) if monto_f > 0 else 0.0
                    else:
                        payout_total_f = 0.0
                        ratio_total = 0.0
                except Exception:
                    payout_total_f = 0.0
                    ratio_total = 0.0

                now = datetime.now(timezone.utc)
                epoch_val = int(epoch_pretrade) if epoch_pretrade is not None else int(now.timestamp())
                ts_val = now.isoformat()
                
                async with csv_lock:
                    # ==========================
                    # CIERRE CERRADO (DICT MODERNO)
                    # ==========================
                    puntaje01 = _norm_puntaje_01(condiciones)  # helper REAL del bot
                    ack_ctx = estado_bot.get("ack_ctx", {}) if isinstance(estado_bot.get("ack_ctx", {}), dict) else {}
                    ia_prob_en_juego = ack_ctx.get("ia_prob_en_juego", "")
                    ia_prob_source = str(ack_ctx.get("ia_prob_source", "") or "").strip()
                    ia_ready_ack = bool(ack_ctx.get("ia_ready_ack", False))
                    if isinstance(ia_prob_en_juego, (int, float)):
                        ia_prob_source = ia_prob_source or "HUD"
                        ia_ready_ack = True
                    else:
                        ia_prob_source = ia_prob_source or "NO_READY"

                    trade_uid_final = str(trade_uid or "").strip()
                    if not trade_uid_final:
                        trade_uid_final = _build_trade_uid(epoch_val, symbol, direccion, ciclo, token_antes, ts_iso=ts_val)
                    row_dict = {
                        "fecha": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                        "activo": symbol,
                        "direction": direccion,
                        "monto": float(monto_f),
                        "resultado": resultado,
                        "ganancia_perdida": float(f"{profit:.2f}"),
                        "rsi_9": rsi9,
                        "rsi_14": rsi14,
                        "sma_5": sma5,
                        "sma_20": sma20,
                        "cruce_sma": int(cruce),
                        "breakout": int(breakout),
                        "rsi_reversion": int(rsi_reversion),
                        "racha_actual": int(racha_anterior),
                        "es_rebote": int(es_rebote_flag),
                        "ciclo_martingala": int(ciclo),
                        "payout_total": float(round(payout_total_f, 2)),
                        "payout_multiplier": float(round(float(ratio_total), 6)),
                        "puntaje_estrategia": float(round(float(puntaje01), 6)),
                        "result_bin": 1 if resultado == "GANANCIA" else 0 if resultado == "PÉRDIDA" else "",
                        "trade_status": "CERRADO",
                        "epoch": int(epoch_val),
                        "ts": ts_val,
                        "ia_prob_en_juego": ia_prob_en_juego,
                        "ia_prob_source": ia_prob_source,
                        "ia_decision_id": trade_uid_final,
                        "ia_gate_real": ack_ctx.get("ia_gate_real", ""),
                        "ia_modo_ack": ack_ctx.get("ia_modo_ack", ""),
                        "ia_ready_ack": ia_ready_ack,
                    }
                    closes = _extract_close_snapshot(close_snapshot, n=20)
                    _warn_close_snapshot_insuficiente(closes)
                    for i, c in enumerate(closes):
                        row_dict[f"close_{i}"] = "" if c is None else float(c)
                    _write_row_dict_atomic(ARCHIVO_CSV, row_dict)

            except Exception as csv_e:
                print(Fore.RED + f"[ERROR] al escribir CSV: {csv_e}")
            # Calcular y mostrar % de éxito acumulado (solo cierres auditables)
            try:
                total_cerrados, ganancias, pendientes = _audit_csv_trade_metrics(ARCHIVO_CSV)

                if total_cerrados:
                    porcentaje_exito = (ganancias / total_cerrados) * 100
                    print(f"Éxito acumulado en {ARCHIVO_CSV}: {ganancias}/{total_cerrados} = {porcentaje_exito:.2f}%")
                else:
                    print(
                        f"Éxito acumulado en {ARCHIVO_CSV}: sin cierres auditables aún "
                        f"(pendientes={pendientes})"
                    )
            except Exception as e:
                print(f"No se pudo calcular % de éxito: {type(e).__name__}: {e!r}")

            # Acumular profit separado
            if token_antes == TOKEN_REAL:
                resultado_global["real"] += profit
            else:
                resultado_global["demo"] += profit
            # Si fue GANANCIA en REAL -> reproducir sonido (sin tocar token)
            if resultado == "GANANCIA" and token_antes == TOKEN_REAL:
                try:
                    pygame.mixer.music.load("ganabot.wav")
                    pygame.mixer.music.play()
                except Exception:
                    pass
                print(Fore.GREEN + Style.BRIGHT + "GANANCIA en cuenta REAL! (token lo maneja 5R6M; sigo en sesión)")
            # BLOQUE 2: Clear commit guard after REAL result
            if token_antes == TOKEN_REAL:
                commit_guard_clear()
            # >>> PATCH BLOQUE 5
            print(Fore.CYAN + f"Ciclo #{ciclo} | {symbol} {direccion} | payout={float(payout or 0):.2f} | {resultado} {profit:+.2f} USD")
            # <<< PATCH
            return resultado, profit
        except websockets.exceptions.ConnectionClosed:
            if _print_once("no-close-frame", ttl=15):
                print(Fore.YELLOW + "WS cerrado sin close frame (resolverá en background). Mismo ciclo.")
            try:
                play_sfx("REINTENTA", vol=0.8)
            except Exception:
                pass
            return "INDEFINIDO", 0.0
        except Exception as e:
            print(Fore.RED + Style.BRIGHT + f"[ERROR] Resultado INDEFINIDO: {e}. Reintentando mismo ciclo...")
            try:
                play_sfx("REINTENTA", vol=0.8)
            except Exception:
                pass
            return "INDEFINIDO", 0.0
    finally:
        estado_bot["barra_activa"] = False
        _flush_log_buffer()

async def finalizar_contrato_bg(contract_id, remaining, symbol, direccion, monto,
                                rsi9, rsi14, sma5, sma20, cruce, breakout, rsi_reversion,
                                ciclo, payout, condiciones, token_usado, epoch_pretrade=None, trade_uid=None, close_snapshot=None):
    """
    Finaliza un contrato en background cuando hubo cambio de token / reinicio.
    Importante IA:
    - es_rebote debe ser PRE-TRADE (racha previa <= -4), NO depender del resultado (sin fuga).
    """
    try:
        if remaining and remaining > 0:
            await asyncio.sleep(remaining)

        # === Consultar contrato ===
        async with websockets.connect(DERIV_WS_URL, **WS_KW) as ws_bg:
            await api_call(ws_bg, {"authorize": token_usado}, expect_msg_type=None)
            data = await api_call(
                ws_bg,
                {"proposal_open_contract": 1, "contract_id": contract_id},
                expect_msg_type="proposal_open_contract"
            )

        poc = data.get("proposal_open_contract", {}) if isinstance(data, dict) else {}
        profit = float(poc.get("profit", 0.0) or 0.0)
        resultado = "GANANCIA" if profit > 0 else "PÉRDIDA"

        # === SFX BG (solo REAL) ===
        try:
            if token_usado == TOKEN_REAL:
                if resultado == "GANANCIA":
                    play_sfx("FELICITACIONES", vol=1.0)
                else:
                    play_sfx("LO_SIENTO", vol=0.9)
        except Exception:
            pass

        # === Evitar doble commit por mismo contrato ===
        if contract_id in _contratos_procesados:
            return
        _contratos_procesados.add(contract_id)

        # === IA / racha / es_rebote (SIN FUGA) ===
        try:
            global racha_actual_bot

            racha_anterior = int(racha_actual_bot)

            # actualizar racha con el resultado (esto es post-trade, OK)
            if resultado == "GANANCIA":
                racha_actual_bot = racha_actual_bot + 1 if racha_actual_bot > 0 else 1
            else:
                racha_actual_bot = racha_actual_bot - 1 if racha_actual_bot < 0 else -1

            # es_rebote PRE-TRADE: venías de 4+ pérdidas antes de este trade
            es_rebote_flag = 1 if (racha_anterior <= -4) else 0

        except Exception:
            racha_anterior = int(racha_actual_bot) if "racha_actual_bot" in globals() else 0
            es_rebote_flag = 1 if (racha_anterior <= -4) else 0

        # === Escribir fila resultado en CSV enriquecido ===
        now = datetime.now(timezone.utc)
        epoch_val = int(epoch_pretrade) if epoch_pretrade is not None else int(now.timestamp())
        ts_val = now.isoformat()

        # ==========================================================
        # payout robusto:
        # - si payout <= 3.5 => es payout_multiplier (ratio_total)
        # - si payout > 3.5  => es payout_total (USD)
        # Guardamos SIEMPRE:
        #   payout_total = monto * payout_multiplier
        #   payout_multiplier = payout_total / monto
        # ==========================================================
        payout_total = 0.0
        payout_ratio_total = 0.0

        # monto
        try:
            monto_f = float(monto) if monto not in (None, "", "nan", "NaN") else 0.0
        except Exception:
            monto_f = 0.0

        # payout (puede venir como multiplier o como total)
        try:
            p = float(payout) if payout not in (None, "", "nan", "NaN") else 0.0
        except Exception:
            p = 0.0

        # si p es NaN/inf, lo anulamos
        try:
            if not math.isfinite(p):
                p = 0.0
            if not math.isfinite(monto_f):
                monto_f = 0.0
        except Exception:
            pass

        try:
            if p > 0 and p <= 3.5:
                # payout viene como multiplier (1.95 etc.)
                payout_ratio_total = p
                payout_total = (monto_f * payout_ratio_total) if monto_f > 0 else 0.0
            elif p > 3.5:
                # payout viene como total (15.62 etc.)
                payout_total = p
                payout_ratio_total = (payout_total / monto_f) if monto_f > 0 else 0.0
            else:
                payout_total = 0.0
                payout_ratio_total = 0.0
        except Exception:
            payout_total = 0.0
            payout_ratio_total = 0.0

        async with csv_lock:
            # ==========================
            # CIERRE BG CERRADO (DICT MODERNO)
            # ==========================
            try:
                monto_f = float(monto or 0.0)
            except Exception:
                monto_f = 0.0
            try:
                payout_total_f = float(payout_total or 0.0)
            except Exception:
                payout_total_f = 0.0
            try:
                payout_mult_f = float(payout_ratio_total or 0.0)
            except Exception:
                payout_mult_f = 0.0
            puntaje01 = _norm_puntaje_01(condiciones)  # helper REAL del bot
            trade_uid_final = str(trade_uid or "").strip()
            if not trade_uid_final:
                trade_uid_final = _build_trade_uid(epoch_val, symbol, direccion, ciclo, token_usado, ts_iso=ts_val)
            row_dict = {
                "fecha": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                "activo": symbol,
                "direction": direccion,
                "monto": float(monto_f),
                "resultado": resultado,
                "ganancia_perdida": float(f"{profit:.2f}"),
                "rsi_9": rsi9,
                "rsi_14": rsi14,
                "sma_5": sma5,
                "sma_20": sma20,
                "cruce_sma": int(cruce),
                "breakout": int(breakout),
                "rsi_reversion": int(rsi_reversion),
                "racha_actual": int(racha_anterior),
                "es_rebote": int(es_rebote_flag),
                "ciclo_martingala": int(ciclo),
                "payout_total": float(round(payout_total_f, 2)),
                "payout_multiplier": float(round(payout_mult_f, 6)),
                "puntaje_estrategia": float(round(float(puntaje01), 6)),
                "result_bin": 1 if resultado == "GANANCIA" else 0 if resultado == "PÉRDIDA" else "",
                "trade_status": "CERRADO",
                "epoch": int(epoch_val),
                "ts": ts_val,
                "ia_decision_id": trade_uid_final,
            }
            closes = _extract_close_snapshot(close_snapshot, n=20)
            _warn_close_snapshot_insuficiente(closes)
            for i, c in enumerate(closes):
                row_dict[f"close_{i}"] = "" if c is None else float(c)
            _write_row_dict_atomic(ARCHIVO_CSV, row_dict)
        # === Logs ===
        msg = Fore.CYAN + f"Contrato #{contract_id} finalizado en background: {resultado} {profit:.2f} USD"
        if estado_bot.get("barra_activa", False):
            _buffer_log(msg)
        else:
            print(msg)

        # Clear commit guard cuando REAL finaliza en BG
        if token_usado == TOKEN_REAL:
            commit_guard_clear()

        msg2 = Fore.CYAN + (
            f"Ciclo #{ciclo} | {symbol} {direccion} | payout={float(payout or 0):.2f} | "
            f"{resultado} {profit:+.2f} USD"
        )
        if estado_bot.get("barra_activa", False):
            _buffer_log(msg2)
        else:
            print(msg2)

    except Exception as e:
        msg = Fore.YELLOW + f"finalizar_contrato_bg: {type(e).__name__}: {e!r}"
        if estado_bot.get("barra_activa", False):
            _buffer_log(msg)
        else:
            print(msg)
        return

async def leer_csv():
    """Lee el archivo CSV y devuelve los registros."""
    registros = []
    try:
        with open(ARCHIVO_CSV, "r", encoding="utf-8", errors="replace") as f:
            reader = csv.reader(f)
            header = next(reader, None)
            if header is None:
                print(Fore.YELLOW + "CSV vacío o sin encabezado.")
                return registros
            for row in reader:
                registros.append(row)
        print(Fore.GREEN + f"Leídos {len(registros)} registros del CSV.")
        return registros
    except Exception as e:
        print(Fore.RED + Style.BRIGHT + f"[ERROR] al leer CSV: {e}")
        return []

async def mostrar_saldos():
    global saldo_demo_last, saldo_real_last, _last_saldo_ts
    print(Fore.GREEN + Style.BRIGHT + "\nConsultando Saldos")

    # BLOQUE 8: Rate-limit with cache
    if time.time() - _last_saldo_ts < REFRESCO_SALDO:
        print(Fore.LIGHTBLUE_EX + Style.BRIGHT + f"Saldo cuenta DEMO (cached): {saldo_demo_last:.2f} USD")
        print(Fore.YELLOW + Style.BRIGHT + f"Saldo cuenta REAL (cached): {saldo_real_last:.2f} USD")
        print(Fore.GREEN + "─" * 80)
        return

    saldo_demo = saldo_demo_last
    saldo_real = saldo_real_last

    # DEMO
    try:
        async with websockets.connect(DERIV_WS_URL, **WS_KW) as ws:  # BLOQUE 1.2
            await authorize_ws(ws, TOKEN_DEMO, tries=2, timeout=6.0)
            data = await api_call(ws, {"balance": 1}, expect_msg_type="balance")
            b = data.get("balance", {}).get("balance")
            if b is not None:
                saldo_demo = float(b)
                saldo_demo_last = saldo_demo
            else:
                if _print_once("saldo-demo-empty", ttl=REFRESCO_SALDO):
                    print(Fore.YELLOW + "Balance DEMO no disponible, usando último valor válido.")
    except Exception as e:
        if _print_once("saldo-demo-error", ttl=REFRESCO_SALDO):
            print(Fore.YELLOW + Style.BRIGHT + f"[WARN] saldo DEMO: {type(e).__name__}: {e!r}")
            print(Fore.YELLOW + "Balance DEMO no disponible, usando último valor válido.")

    # REAL
    try:
        async with websockets.connect(DERIV_WS_URL, **WS_KW) as ws:  # BLOQUE 1.2
            await authorize_ws(ws, TOKEN_REAL, tries=2, timeout=6.0)
            data = await api_call(ws, {"balance": 1}, expect_msg_type="balance")
            b = data.get("balance", {}).get("balance")
            if b is not None:
                saldo_real = float(b)
                saldo_real_last = saldo_real
            else:
                if _print_once("saldo-real-empty", ttl=REFRESCO_SALDO):
                    print(Fore.YELLOW + "Balance REAL no disponible, usando último valor válido.")
    except Exception as e:
        if _print_once("saldo-real-error", ttl=REFRESCO_SALDO):
            print(Fore.YELLOW + Style.BRIGHT + f"[WARN] saldo REAL: {type(e).__name__}: {e!r}")
            print(Fore.YELLOW + "Balance REAL no disponible, usando último valor válido.")

    print(Fore.LIGHTBLUE_EX + Style.BRIGHT + f"Saldo cuenta DEMO: {saldo_demo:.2f} USD")
    print(Fore.YELLOW + Style.BRIGHT + f"Saldo cuenta REAL: {saldo_real:.2f} USD")
    print(Fore.GREEN + "─" * 80)
    print(Fore.GREEN + "─" * 80)
    _last_saldo_ts = time.time()


# ==================== LOOP PRINCIPAL ====================
async def ejecutar_panel():
    global ultimo_token
    global _ws_fail_streak

    # Eliminado: reset_csv_and_total() para acumular histórico completo
    await mostrar_saldos()
    # =================== PATCH CSV (SOLO) ===================
    global _CSV_REPARADO_1VEZ
    if not _CSV_REPARADO_1VEZ:
        reparar_csv_esrebote_ciclo(ARCHIVO_CSV)
        _CSV_REPARADO_1VEZ = True
    # ================= FIN PATCH CSV (SOLO) =================
   
    
    async def _cerrar_ws(_ws):
        try:
            if _ws is not None:
                await _ws.close()
        except Exception:
            pass

    async def _abrir_ws(token: str, tries: int = 4):
        last = None
        for intento in range(1, tries + 1):
            try:
                _ws = await websockets.connect(DERIV_WS_URL, **WS_KW)
                await authorize_ws(_ws, token)
                return _ws
            except Exception as e:
                last = e
                if _es_error_transitorio_ws(e):
                    espera = min(6.0, 0.8 * intento + random.uniform(0.0, 0.6))
                    if _print_once(f"ws-open-retry-{intento}", ttl=2):
                        print(Fore.YELLOW + f"WS/NET inestable al abrir sesión ({type(e).__name__}). Reintento {intento}/{tries} en {espera:.1f}s...")
                    await asyncio.sleep(espera)
                    continue
                raise
        raise last

    ws = None
    try:
        current_token = leer_token_desde_archivo()
        ultimo_token = current_token  # ✅ evita reinicio fantasma del watcher al inicio
        ws = await _abrir_ws(current_token)

        indefinidos_consecutivos = 0  # Contador para indefinidos por ciclo

        while not stop_event.is_set():

            # ========= REINICIO FORZADO (token / watcher) =========
            if reinicio_forzado.is_set():
                estado_bot["reinicios_consecutivos"] += 1
                if estado_bot["reinicios_consecutivos"] > 5:
                    print(Fore.RED + "Demasiados reinicios consecutivos. Fallback a ciclo #1 + backoff 5s.")
                    estado_bot["ciclo_forzado"] = 1
                    estado_bot["reinicios_consecutivos"] = 0
                    await asyncio.sleep(5)

                print(Fore.YELLOW + Style.BRIGHT + "Reinicio forzado detectado. (reconectando sin salir)")
                reinicio_forzado.clear()
                indefinidos_consecutivos = 0

                await _cerrar_ws(ws)
                ws = None
                new_token = leer_token_desde_archivo()
                ws = await _abrir_ws(new_token)

                current_token = new_token
                ultimo_token = new_token
                await asyncio.sleep(0.6 + random.uniform(0.0, 0.5))
                continue

            # ========= ARRANQUE DE MARTINGALA =========
            modo_real = (current_token == TOKEN_REAL)
            if modo_real:
                if not estado_bot.get("barra_activa", False) and _print_once("real-start-msg", ttl=120):
                    hora = ""
                    try:
                        hora = datetime.now().strftime("%H:%M:%S")
                    except Exception:
                        hora = ""
                    print(
                        Fore.LIGHTRED_EX + Back.WHITE + Style.BRIGHT
                        + f"\n🚨 {NOMBRE_BOT.upper()} MODO REAL ACTIVADO {hora} 🚨"
                        + Style.RESET_ALL
                    )

            martingala = MARTINGALA_REAL if modo_real else MARTINGALA_DEMO

            sep_ciclo()
            ciclo_orden, _ts, _quiet, _src = leer_orden_real(NOMBRE_BOT)
            ciclo_forzado = estado_bot.get("ciclo_forzado")
            ciclo = ciclo_orden or ciclo_forzado or 1

            estado_bot["ciclo_forzado"] = None
            estado_bot["reinicios_consecutivos"] = 0
            N = len(martingala)
            indefinidos_consecutivos = 0

            while ciclo <= N and (not stop_event.is_set()):

                monto = martingala[ciclo - 1]
                estado_bot["ciclo_actual"] = int(ciclo)

                # Sync token/WS con el maestro (sin perder ciclo)
                ws, current_token = await check_token_and_reconnect(ws, current_token)

                if reinicio_forzado.is_set():
                    estado_bot["ciclo_forzado"] = ciclo
                    proximo = estado_bot.get("ciclo_forzado") or ciclo
                    print(Fore.YELLOW + Style.BRIGHT + f"Reinicio forzado durante ciclo. Ciclo actual #{ciclo} → siguiente #{proximo}.")
                    reinicio_forzado.clear()
                    await asyncio.sleep(2)
                    indefinidos_consecutivos = 0
                    break

                modo_real = (current_token == TOKEN_REAL)
                martingala = MARTINGALA_REAL if modo_real else MARTINGALA_DEMO

                print(Fore.CYAN + Style.BRIGHT + "=" * 80)
                titulo = f"{NOMBRE_BOT.upper()} | MODO {'REAL' if modo_real else 'DEMO'} | CICLO #{ciclo}/{len(martingala)}"
                print(Fore.CYAN + Style.BRIGHT + titulo.center(80))
                print(Fore.CYAN + Style.BRIGHT + "=" * 80)

                # Salud WS (si buscar_estrategia detectó 1006 masivos)
                if ws_reset_needed.is_set():
                    await _cerrar_ws(ws)
                    ws = await _abrir_ws(current_token)
                    _ws_fail_streak = 0
                    ws_reset_needed.clear()
                    if _print_once("ws-reopened", ttl=20):
                        print(Fore.CYAN + Style.BRIGHT + "WS reabierto por salud. Retomando MISMO ciclo.")
                    await asyncio.sleep(0.6 + random.uniform(0.0, 0.5))

                # ========= BUSCAR SEÑAL =========
                symbol, direccion, rsi9, rsi14, sma5, sma20, breakout, cruce, condiciones, rsi_reversion, close_snapshot = await buscar_estrategia(ws, ciclo, current_token)

                if symbol == "REINTENTAR" or symbol is None:
                    continue

                if not all([direccion, rsi9 is not None, rsi14 is not None]):
                    print(Fore.YELLOW + "Datos de estrategia incompletos. Reintentando ciclo.")
                    continue

                # Rechequeo token justo antes de avanzar
                ws, current_token = await check_token_and_reconnect(ws, current_token)

                if reinicio_forzado.is_set():
                    estado_bot["ciclo_forzado"] = ciclo
                    print(Fore.YELLOW + Style.BRIGHT + f"Reinicio forzado tras buscar estrategia. Mantengo ciclo #{ciclo}.")
                    reinicio_forzado.clear()
                    await asyncio.sleep(2)
                    indefinidos_consecutivos = 0
                    break

                modo_real_now = (current_token == TOKEN_REAL)
                if modo_real_now != modo_real:
                    estado_bot["ciclo_forzado"] = ciclo
                    print(Fore.YELLOW + Style.BRIGHT + "Token cambió justo antes de validar saldo/compra. Reinicio limpio para mantener sincronía con el maestro.")
                    reinicio_forzado.set()
                    break

                # ========= SALDO REAL (si aplica) =========
                if modo_real:
                    saldo = await consultar_saldo_real(ws)
                    if saldo < monto:
                        estado_bot["intentos_saldo"] += 1
                        if estado_bot["intentos_saldo"] > 3:
                            print(Fore.RED + Style.BRIGHT + "Saldo no recuperado tras 3 intentos. Paso a DEMO.")
                            try:
                                play_sfx("NO_PASAR_REAL", vol=0.9)
                            except Exception:
                                pass
                            # ✅ Liberación segura (CAS): solo si aún soy el dueño del REAL
                            release_real_token_if_owned()
                            estado_bot["intentos_saldo"] = 0
                            reinicio_forzado.set()
                        else:
                            print(Fore.RED + Style.BRIGHT + f"Saldo REAL insuficiente: {saldo:.2f} < {monto:.2f}. Espero y reintento MISMO ciclo ({estado_bot['intentos_saldo']}/3).")
                            await asyncio.sleep(15 + random.uniform(0.0, 0.5))
                        continue

                # ========= REVALIDACIÓN PRE-BUY =========
                try:
                    score_sel = estado_bot.get("score_senal")
                    velas_rv = await obtener_velas(ws, symbol, current_token, reintentos=2)
                    if velas_rv and len(velas_rv) >= int(REVALIDAR_VELAS_N):
                        cond2, dir2, rsi9_2, rsi14_2, sma5_2, sma20_2, br2, cr2, rev2 = evaluar_estrategia(velas_rv)
                        score2 = puntuar_setups(cond2, dir2, rsi9_2, rsi14_2, sma5_2, sma20_2, br2, cr2, rev2)
                        piso = float(SCORE_MIN)
                        if isinstance(score_sel, (int, float)):
                            piso = max(piso, float(score_sel) - float(SCORE_DROP_MAX))

                        if (dir2 != direccion) or (int(cond2) < 2) or (float(score2) < piso):
                            print(Fore.YELLOW + Style.BRIGHT + f"Revalidación falló en {symbol}: dir {direccion}->{dir2}, cond={cond2}, score={score2:.3f}<piso {piso:.3f}. Reintentando ciclo...")
                            await asyncio.sleep(2.0 + random.uniform(0.0, 0.5))
                            continue

                        # refresca snapshot para compra/log consistentes
                        direccion, rsi9, rsi14, sma5, sma20, breakout, cruce, rsi_reversion, condiciones = dir2, rsi9_2, rsi14_2, sma5_2, sma20_2, br2, cr2, rev2, cond2
                        estado_bot["score_senal"] = float(score2)
                except Exception:
                    pass

                # ========= PROPOSAL =========
                try:
                    data_proposal = await api_call(ws, {
                        "proposal": 1,
                        "amount": float(monto),
                        "basis": "stake",
                        "contract_type": direccion,
                        "currency": "USD",
                        "duration": 1,
                        "duration_unit": "m",
                        "symbol": symbol
                    }, expect_msg_type="proposal", timeout=8.0)
                except RuntimeError as api_e:
                    _symbol_cooldown[symbol] = time.time() + 60
                    print(Fore.RED + Style.BRIGHT + f"[ERROR] Propuesta: {api_e}. {symbol} en cooldown 60s.")
                    estado_bot["token_msg_mostrado"] = False
                    await asyncio.sleep(8 + random.uniform(0.0, 0.5))
                    continue
                except Exception as e:
                    if _es_error_transitorio_ws(e):
                        if _print_once("proposal-transient", ttl=8):
                            print(Fore.YELLOW + Style.BRIGHT + f"[WARN] Propuesta inestable ({type(e).__name__}). Reabro WS y mantengo ciclo #{ciclo}.")
                        await _cerrar_ws(ws)
                        ws = await _abrir_ws(current_token)
                        await asyncio.sleep(0.6 + random.uniform(0.0, 0.4))
                        continue
                    raise

                # Si token cambió DURANTE proposal → NO compramos, reinicio limpio
                if reinicio_forzado.is_set():
                    estado_bot["ciclo_forzado"] = ciclo
                    print(Fore.YELLOW + Style.BRIGHT + f"Token cambió durante proposal. Cancelo compra y reinicio en ciclo #{ciclo}.")
                    reinicio_forzado.clear()
                    await asyncio.sleep(1.2)
                    break

                proposal = data_proposal.get("proposal", {})
                payout = float(proposal.get("payout", 0.0))
                ask_price = float(proposal.get("ask_price", monto))
                payout_ratio = (payout / float(monto)) if float(monto) > 0 else 0.0

                if payout_ratio < 0.70:
                    print(Fore.YELLOW + Style.BRIGHT + f"Payout de {payout_ratio*100:.1f}% demasiado bajo. Reintentando mismo ciclo...")
                    try:
                        play_sfx("NO_PASAR_REAL", vol=0.9)
                    except Exception:
                        pass
                    estado_bot["token_msg_mostrado"] = False
                    await asyncio.sleep(15 + random.uniform(0.0, 0.5))
                    continue

                print(Fore.CYAN + Style.BRIGHT + f"[{symbol}] Martingala #{ciclo} - {direccion} - {monto} USD")
                # === PRE-TRADE SNAPSHOT (para inferencia real del Maestro) ===
                epoch_pre = None
                now_pre = datetime.now(timezone.utc)
                ts_pre = now_pre.isoformat()
                trade_uid = _build_trade_uid(int(now_pre.timestamp()), symbol, direccion, ciclo, current_token, ts_iso=ts_pre)
                try:
                    # es_rebote PRE-TRADE: venías de 4+ pérdidas ANTES de este trade
                    es_rebote_pre = 1.0 if int(racha_actual_bot) <= -4 else 0.0

                    epoch_pre = write_pretrade_snapshot(
                        ARCHIVO_CSV,
                        fecha=datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                        activo=symbol,
                        direccion=direccion,              # CALL/PUT
                        monto=float(monto),
                        rsi_9=float(rsi9),
                        rsi_14=float(rsi14),
                        sma_5=float(sma5),
                        sma_20=float(sma20),
                        cruce_sma=float(int(cruce)),
                        breakout=float(int(breakout)),
                        rsi_reversion=float(int(rsi_reversion)),
                        racha_actual=int(racha_actual_bot),     # racha vigente ANTES del trade
                        es_rebote=float(es_rebote_pre),         # ✅ SIN FUGA (pre-trade real)
                        ciclo_martingala=int(ciclo),
                        payout=float(payout),
                        puntaje_estrategia=float(condiciones),  # tu score
                        token=current_token,
                        trade_uid=trade_uid,
                        close_snapshot=close_snapshot,
                    )
                except Exception:
                    epoch_pre = None

                # === /PRE-TRADE SNAPSHOT ===
                # ==================== VENTANA DE DECISIÓN IA (GATEWIN) ====================
                # Ya escribimos el PRE-TRADE snapshot. Ahora damos tiempo para que:
                # 1) el MAESTRO calcule/muestre la prob IA
                # 2) tú elijas bot/ciclo
                # 3) si el MAESTRO asigna REAL (token), el watcher lo detecte y dispare reinicio_forzado
                # Resultado: evitamos comprar en DEMO cuando justo tocaba REAL.
                if VENTANA_DECISION_IA_S > 0:
                    t0 = time.time()
                    ack_visto = False

                    while (time.time() - t0) < VENTANA_DECISION_IA_S:
                        if reinicio_forzado.is_set():
                            break
                        # Doble seguro: si el token cambió durante GateWin, corta ya
                        try:
                            tok_now = leer_token_desde_archivo()
                            if tok_now != current_token:
                                reinicio_forzado.set()
                                break
                        except Exception:
                            pass
                        # ✅ Leer ACK del maestro (si llega, lo mostramos una sola vez)
                        if (not ack_visto) and epoch_pre:
                            ack = leer_ia_ack(NOMBRE_BOT)
                            try:
                                ep_ack = int(float(ack.get("epoch", 0) or 0)) if ack else 0
                                ep_pre = int(float(epoch_pre or 0))
                                # tolera pequeños desfases de epoch para no dejar telemetría en NO_READY
                                epoch_ok = bool(ep_ack >= max(0, ep_pre - 2))
                                if ack and epoch_ok:
                                    p = ack.get("prob", None)
                                    p_hud = ack.get("prob_hud", None)
                                    p_play = ack.get("prob_en_juego", None)
                                    has_prob_hud = ack.get("has_prob_hud", None)
                                    has_prob_play = ack.get("has_prob_en_juego", None)
                                    if isinstance(has_prob_play, bool):
                                        p_show = p_play if has_prob_play else None
                                    elif isinstance(has_prob_hud, bool):
                                        p_show = p_hud if has_prob_hud else p
                                    else:
                                        p_show = p_hud if isinstance(p_hud, (int, float)) else p

                                    auc = float(ack.get("auc", 0.0) or 0.0)
                                    modo = ack.get("modo", "OFF")
                                    thr_real = ack.get("real_thr", None)
                                    reliable_ack = bool(ack.get("reliable", False))
                                    ready_ack = bool(ack.get("ia_ready", False))
                                    modo_norm = str(modo or "OFF").strip().upper()
                                    # Si hay prob visible, no forzar vacío solo por modo OFF transitorio.
                                    if modo_norm == "OFF" and (not isinstance(p_show, (int, float))):
                                        p_show = None
                                    auc_txt = f"{auc:.3f}" if (reliable_ack and 0.0 < auc < 1.0 and modo_norm != "OFF") else "N/A"

                                    estado_bot["ack_ctx"] = {
                                        "ia_prob_en_juego": p_show if isinstance(p_show, (int, float)) else "",
                                        "ia_prob_source": str(ack.get("prob_source", "")) or ("HUD" if isinstance(p_show, (int, float)) else "NO_READY"),
                                        "ia_decision_id": str(ack.get("decision_id", "")),
                                        "ia_gate_real": float(thr_real) if isinstance(thr_real, (int, float)) else "",
                                        "ia_modo_ack": str(modo),
                                        "ia_ready_ack": bool(ready_ack or isinstance(p_show, (int, float))),
                                    }

                                    if isinstance(p_show, (int, float)):
                                        if isinstance(thr_real, (int, float)):
                                            print(f"🤖 IA ACK ({NOMBRE_BOT}) → {p_show*100:.1f}% | Gate REAL={float(thr_real)*100:.1f}% | AUC={auc_txt} | modo={modo}")
                                        else:
                                            print(f"🤖 IA ACK ({NOMBRE_BOT}) → {p_show*100:.1f}% | AUC={auc_txt} | modo={modo}")
                                    else:
                                        print(f"🤖 IA ACK ({NOMBRE_BOT}) → (sin prob) | AUC={auc_txt} | modo={modo}")

                                    ack_visto = True
                            except Exception:
                                pass

                        await asyncio.sleep(VENTANA_DECISION_IA_POLL_S)

                    # Si el token cambió durante la ventana, NO compramos con estado viejo.
                    if reinicio_forzado.is_set():
                        estado_bot["ciclo_forzado"] = ciclo
                        print(
                            Fore.YELLOW + Style.BRIGHT +
                            f"[VENTANA IA] Token cambió durante la decisión. Reintentando ciclo #{ciclo} (sin comprar)."
                        )
                        reinicio_forzado.clear()
                        await asyncio.sleep(0.8)
                        continue

# ==================== /VENTANA DE DECISIÓN IA ====================

                try:
                    data_buy = await api_call(ws, {
                        "buy": 1,
                        "price": float(ask_price),
                        "parameters": {
                            "amount": float(monto),
                            "basis": "stake",
                            "contract_type": direccion,
                            "currency": "USD",
                            "duration": 1,
                            "duration_unit": "m",
                            "symbol": symbol
                        }
                    }, expect_msg_type="buy", timeout=8.0)
                except RuntimeError as api_e:
                    print(Fore.RED + Style.BRIGHT + f"[ERROR] Compra: {api_e}. Reintentando mismo ciclo...")
                    estado_bot["token_msg_mostrado"] = False
                    await asyncio.sleep(10 + random.uniform(0.0, 0.5))
                    continue
                except Exception as e:
                    if _es_error_transitorio_ws(e):
                        if _print_once("buy-transient", ttl=8):
                            print(Fore.YELLOW + Style.BRIGHT + f"[WARN] Compra inestable ({type(e).__name__}). Reabro WS y mantengo ciclo #{ciclo}.")
                        await _cerrar_ws(ws)
                        ws = await _abrir_ws(current_token)
                        await asyncio.sleep(0.6 + random.uniform(0.0, 0.4))
                        continue
                    raise

                contract_id = data_buy["buy"]["contract_id"]

                # ✅ Ciclo en progreso significa: YA hay contrato abierto
                estado_bot["ciclo_en_progreso"] = True

                # Commit guard REAL
                if modo_real:
                    commit_guard_set(contract_id)

                # Si justo hubo cambio de token y pidieron reinicio, forzamos detach inmediato
                if reinicio_forzado.is_set():
                    estado_bot["interrumpir_ciclo"] = True

                # ========= RESULTADO =========
                resultado, profit = await esperar_resultado(
                    ws, contract_id, symbol, direccion, monto,
                    rsi9, rsi14, sma5, sma20, cruce, breakout, rsi_reversion,
                    ciclo, payout, condiciones, current_token, epoch_pre, trade_uid=trade_uid, close_snapshot=close_snapshot
                )

                if resultado == "INDEFINIDO":
                    print(Fore.YELLOW + "INDEFINIDO: WS/Token restart. Se mantiene MISMO ciclo (BG resolverá).")
                    indefinidos_consecutivos += 1

                    if indefinidos_consecutivos > 5:
                        print(Fore.RED + Style.BRIGHT + "Demasiados indefinidos consecutivos. Reiniciando martingala para evitar loop.")
                        try:
                            play_sfx("NO_CONCLUYO", vol=0.9)
                        except Exception:
                            pass
                        indefinidos_consecutivos = 0
                        estado_bot["ciclo_en_progreso"] = False
                        estado_bot["token_msg_mostrado"] = False
                        break

                    await asyncio.sleep(random.uniform(0.5, 1.2))
                    await _cerrar_ws(ws)
                    ws = await _abrir_ws(current_token)
                    estado_bot["ciclo_en_progreso"] = False
                    estado_bot["token_msg_mostrado"] = False
                    continue

                # Resultado definido
                indefinidos_consecutivos = 0
                estado_bot["intentos_saldo"] = 0
                estado_bot["ciclo_en_progreso"] = False
                estado_bot["token_msg_mostrado"] = False

                print(Back.BLUE + Style.BRIGHT + f"\nTotal DEMO: {resultado_global['demo']:.2f} USD | Total REAL: {resultado_global['real']:.2f} USD")
                await mostrar_saldos()
                sep_ciclo()

                # ========= MODO REAL =========
                if modo_real:
                    # ✅ En REAL: SIEMPRE 1 operación (gane o pierda) y volvemos a DEMO de inmediato.
                    if resultado == "GANANCIA":
                        print(Fore.GREEN + Style.BRIGHT + "✅ GANANCIA en REAL. Turno terminado. Volviendo a DEMO...\n")
                    else:
                        print(Fore.RED + Style.BRIGHT + "❌ PÉRDIDA en REAL. Turno terminado. Volviendo a DEMO...\n")

                    # ✅ Liberación segura (CAS): solo si aún soy el dueño del REAL
                    try:
                        release_real_token_if_owned()
                    except Exception:
                        pass

                    # ✅ Importantísimo: resetear ventana para que PASO_A_REAL suene la próxima vez
                    try:
                        globals()["primer_ingreso_real"] = False
                    except Exception:
                        pass
                    try:
                        globals()["real_activado_en_bot"] = 0.0
                    except Exception:
                        pass

                    # ✅ Limpia commit-guard por si quedó armado (no afecta otras lógicas)
                    try:
                        commit_guard_clear()
                    except Exception:
                        pass

                    reinicio_forzado.set()
                    break


                # ========= DEMO =========
                print(Fore.YELLOW + f"Pausa de {PAUSA_POST_OPERACION_S}s antes de continuar...")
                await asyncio.sleep(PAUSA_POST_OPERACION_S + random.uniform(0.0, 0.5))

                if resultado == "GANANCIA":
                    print(Fore.CYAN + Style.BRIGHT + "Ganancia en DEMO. Fin de Martingala.\n")
                    break
                else:
                    ciclo += 1

            # si salimos del inner por reinicio_forzado, el outer lo procesará arriba
            if stop_event.is_set():
                break

    except Exception as e:
        if _es_error_transitorio_ws(e):
            ciclo_ref = int(estado_bot.get("ciclo_actual", 1) or 1)
            estado_bot["ciclo_forzado"] = max(1, ciclo_ref)
            reinicio_forzado.set()
            print(Fore.YELLOW + Style.BRIGHT + f"[WARN] WS/NET transitorio ({type(e).__name__}). Blindaje activo: reintento en ciclo #{estado_bot['ciclo_forzado']}.")
            await asyncio.sleep(1.2 + random.uniform(0.0, 0.5))
        else:
            print(Fore.RED + Style.BRIGHT + f"[ERROR] Fallo general: {type(e).__name__}: {e!r}")
            await asyncio.sleep(10 + random.uniform(0.0, 0.5))
    finally:
        try:
            await _cerrar_ws(ws)
        except Exception:
            pass

async def monitor():
    while not stop_event.is_set():
        await ejecutar_panel()
        if stop_event.is_set():
            break
        await asyncio.sleep(2)

async def main():
    if not WEBSOCKETS_OK:
        print(Fore.YELLOW + "[WARN] websockets no disponible; bot en espera sin operar.")
        while not stop_event.is_set():
            await asyncio.sleep(2)
        return

    # watcher del token (CRÍTICO para GateWin)
    try:
        asyncio.create_task(vigilar_token())
    except Exception as e:
        try:
            print(Fore.YELLOW + f"[WARN] no pude iniciar vigilar_token(): {e!r}")
        except Exception:
            print(f"[WARN] no pude iniciar vigilar_token(): {e!r}")

    # loop principal
    await monitor()

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        try:
            if not stop_event.is_set():
                stop_event.set()
        except Exception:
            pass
        print(Fore.YELLOW + "\n⛔ Interrumpido por usuario.")