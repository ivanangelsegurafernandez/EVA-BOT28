# -*- coding: utf-8 -*-

# === BLOQUE 0 — OBJETIVOS DEL PROGRAMA 5R6M-1-2-4-8-16 ===
#
# Este script coordina:
# - Lectura de CSV enriquecidos de los bots fulll45–fulll50
# - Control de Martingala 1-2-4-8
# - Gestión de tokens DEMO/REAL
# - IA (XGBoost) para probabilidades de éxito
# - HUD visual con Prob IA, % éxito, saldo, meta y eventos
#
# ÍNDICE DE BLOQUES:
#   BLOQUE 1 — IMPORTS Y ENTORNO BÁSICO
#   BLOQUE 2 — CONFIGURACIÓN GLOBAL (MARTINGALA, HUD, AUDIO, IA)
#   BLOQUE 3 — CONFIGURACIÓN DE REENTRENAMIENTO Y MODOS IA
#   BLOQUE 4 — AUDIO (INIT Y REPRODUCCIÓN)
#   BLOQUE 5 — TOKENS, BOT_NAMES Y ESTADO GLOBAL
#   BLOQUE 6 — LOCKS, FIRMAS Y UTILIDADES CSV
#   BLOQUE 7 — ORDEN DE REAL Y CONTROL DE TOKEN
#   BLOQUE 8 — NORMALIZACIÓN Y PUNTAJE DE ESTRATEGIA
#   BLOQUE 9 — DETECCIÓN DE MARTINGALA Y REINICIOS
#   BLOQUE 10 — IA: DATASET, MODELO Y PREDICCIÓN
#   BLOQUE 11 — HUD Y PANEL VISUAL
#   BLOQUE 12 — CONTROL MANUAL REAL Y CONDICIONES SEGURAS
#   BLOQUE 13 — LOOP PRINCIPAL, WEBSOCKET Y TECLADO
#   BLOQUE 99 — RESUMEN FINAL DE LO QUE SE LOGRA
#
# Nota:
#   Esta organización NO cambia la lógica del programa.
#   Solo añade estructura para facilitar futuras modificaciones.
#
# === FIN BLOQUE 0 ===

# === BLOQUE 1 — IMPORTS Y ENTORNO BÁSICO ===
import os, csv, time, random, asyncio, json, re
from collections import deque
from unicodedata import normalize
import threading
from datetime import datetime, timedelta, timezone
from contextlib import contextmanager
import sys
import shutil
import joblib
import numpy as np
import pandas as pd
import importlib
import traceback

import math
import hashlib
from sklearn.model_selection import train_test_split, TimeSeriesSplit
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import roc_auc_score, f1_score, fbeta_score, brier_score_loss
from sklearn.calibration import CalibratedClassifierCV
from sklearn.linear_model import LogisticRegression
from sklearn.isotonic import IsotonicRegression

import warnings
warnings.filterwarnings(
    "ignore",
    message="X does not have valid feature names, but StandardScaler was fitted with feature names"
)


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


def _safe_mean_np(values, default=None):
    """Media robusta: evita RuntimeWarning en slices vacíos y NaN-only."""
    try:
        arr = np.asarray(values)
        if arr.size <= 0:
            return default
        with np.errstate(invalid="ignore", divide="ignore"):
            m = np.nanmean(arr.astype(float))
        if not np.isfinite(m):
            return default
        return float(m)
    except Exception:
        return default


websockets = _load_optional_module("websockets")
WEBSOCKETS_OK = websockets is not None


colorama = _load_optional_module("colorama")
if colorama is not None:
    Fore = colorama.Fore
    Style = colorama.Style
    init = colorama.init
else:
    class _NoColor:
        def __getattr__(self, _name):
            return ""
    Fore = _NoColor()
    Style = _NoColor()
    def init(*args, **kwargs):
        return None

pygame = _load_optional_module("pygame")
PYGAME_OK = pygame is not None
if not PYGAME_OK:
    class _DummyMixer:
        def get_init(self):
            return False
        def pre_init(self, *args, **kwargs):
            return None
        def init(self, *args, **kwargs):
            return None
        def quit(self):
            return None
        def Sound(self, *args, **kwargs):
            return None

    class _DummyPygame:
        mixer = _DummyMixer()

    pygame = _DummyPygame()

winsound = _load_optional_module("winsound")

# ============================================================
# XGBoost (robusto): permite correr aunque xgboost no esté
# ============================================================
try:
    import xgboost as xgb  # opcional (por compatibilidad)
    from xgboost import XGBClassifier
    _XGBOOST_OK = True
except Exception:
    xgb = None
    XGBClassifier = None
    _XGBOOST_OK = False

# --- Teclado Windows (seguro y único) ---
try:
    import msvcrt as _msvcrt
    class _MSWrap:
        def __bool__(self): return True
        def kbhit(self):
            try: return _msvcrt.kbhit()
            except Exception: return False
        def getch(self):
            try: return _msvcrt.getch()
            except Exception: return b''
    msvcrt = _MSWrap()
    HAVE_MSVCRT = True
except Exception:
    class _DummyMS:
        def __bool__(self): return False
        def kbhit(self): return False
        def getch(self): return b''
    msvcrt = _DummyMS()
    HAVE_MSVCRT = False

# Forzar la ruta fija al directorio del script
try:
    script_dir = os.path.dirname(os.path.abspath(__file__))
    os.chdir(script_dir)
    print(f"📁 Directorio de trabajo fijado a: {script_dir}")
except Exception as e:
    print(f"⚠️ No se pudo cambiar al directorio del script: {e}. Usando cwd actual.")

init(autoreset=True)
# === FIN BLOQUE 1 ===

# === BLOQUE 2 — CONFIGURACIÓN GLOBAL (MARTINGALA, HUD, AUDIO, IA) ===
# === CONFIGURACIÓN DE MARTINGALA ===
MARTI_ESCALADO = [1, 2, 4, 8]  # Escalado oficial de 4 pasos
MONTO_TOL = 0.01  # Tolerancia para redondeos
SONAR_TAMBIEN_EN_DEMO = False  # Activar sonidos para victorias en DEMO
SONAR_SOLO_EN_GATEWIN = True   # Solo sonar dentro de la ventana GateWIN
SONAR_FUERA_DE_GATEWIN = False # Permitir sonidos fuera de GateWIN si se se habilita
AUDIO_TIMEOUT_S = 0  # 0 significa sin timeout

# === CTT FASE (Consenso Temporal de Trades cerrados) ===
# 3 relojes: ola (WAVE), rezago (LAG) y expiración de permiso (TTL)
CTT_WAVE_WINDOW_S = 180            # W_wave: ventana de ola (120-180s recomendado)
CTT_WAVE_TTL_S = 150               # TTL_wave: permiso útil de la ola (<= W_wave)
CTT_THR_GREEN = 0.85               # Verde fuerte de régimen
CTT_THR_GREEN_OPERABLE = 0.85      # Verde operable: habilita solo con rezago válido + ola viva
CTT_THR_GREEN_WEAK = 0.75          # Verde diagnóstica mínima
CTT_THR_RED = 0.15                 # Rojo fuerte de régimen
CTT_THR_RED_WEAK = 0.25            # Rojo débil (endurece, no siempre veto total)
CTT_LAG_MIN_S = 45                 # rezago mínimo válido
CTT_LAG_MAX_S = 120                # rezago máximo válido (evita "arqueología")
CTT_DENSITY_MIN_CPM = 1.6          # densidad mínima de cierres/min para verde operable
CTT_RED_WEAK_SCORE_PENALTY = 0.02  # castigo suave en rojo débil
CTT_GREEN_OPERABLE_SCORE_BONUS = 0.01  # premio leve en verde operable
CTT_REQUIRE_SAME_ASSET = True      # no mezclar activos en consenso
CTT_ACTIVO_UNICO = "1HZ50V"         # opción 1: todos los bots operan el mismo sintético
CTT_NEUTRAL_POLICY = "normal"      # normal | block
CTT_CIERRE_LOOKBACK_MAX = 600       # higiene memoria eventos
CTT_ENABLE_GREEN_IN_MARTI_ADVANCED = False  # C2..C{MAX_CICLOS}: CTT actúa como freno más que como habilitador

def _ctt_min_confirmadores() -> int:
    n = int(len(BOT_NAMES))
    if n >= 10:
        return 7
    if n >= 6:
        return 4
    return max(1, int(math.ceil(0.7 * n)))


# === REMATE (modo cierre solo con WIN) ===
MODO_REMATE = True           # Continuar hasta WIN o fin de Martingala
REMATE_SIN_TOPE = False      # Limitado por MAX_CICLOS

# === HUD / Layout ===
HUD_LAYOUT = "bottom_center"  # Fijado en centro inferior
HUD_VISIBLE = True       # Para ocultarlo con tecla
# Visual/UI (no afecta lógica funcional): reducir ruido en consola
HUD_COMPACT_MODE = True
HUD_SHOW_TOP3_GATES = False
HUD_SHOW_RACHA_BLOQUES = False
HUD_EVENTS_MAX = 4
HUD_EVENT_MAX_CHARS = 150

# --- Objetivos / umbrales globales de IA ---
IA_OBJETIVO_REAL_THR = 0.75   # objetivo de calidad REAL (meta: 75% aprox)
IA_ACTIVACION_REAL_THR = 0.60 # perfil moderado: habilitar REAL desde 60% con candados activos
IA_ACTIVACION_REAL_THR_POST_N15 = 0.58  # post-n15: bajar piso operativo para destrabar REAL moderado
# En modo unreliable (reliable=false), permitir piso post-n15 más realista para no congelar entradas.
IA_ACTIVACION_REAL_THR_POST_N15_UNREL = 0.56
IA_ACTIVACION_REAL_THR_POST_N15_UNREL_MIN_SAMPLES = 300
IA_ACTIVACION_REAL_MIN_N_POR_BOT = 5   # condición: todos los bots deben tener al menos n=5

# --- Oráculo visual ---
ORACULO_THR_MIN   = IA_ACTIVACION_REAL_THR
ORACULO_N_MIN     = 40
ORACULO_DELTA_PRE = 0.05

# Umbral visual/alerta: alineado al mínimo operativo REAL
IA_VERDE_THR = IA_ACTIVACION_REAL_THR
IA_SUCESO_LOOKBACK = 16
IA_SUCESO_DELTA_MIN = 0.035
IA_SUCESO_EVENTO_MIN = 0.20
IA_SUCESO_EVENTO_Q = 0.85
IA_SUCESO_EVENTO_HIST = 120
IA_SENSOR_DOM_HOT = 0.95
IA_SENSOR_MIN_HOT_FEATS = 3
IA_SENSOR_MIN_SAMPLE = 30
IA_REDUNDANCY_SCORE_PENALTY = 0.03
IA_SENSOR_PLANO_SCORE_PENALTY = 0.04
IA_SUCESO_SCORE_WEIGHT = 0.08
IA_OBSERVE_THR = 0.70
AUTO_REAL_THR = IA_OBJETIVO_REAL_THR      # techo dinámico objetivo (70%)
AUTO_REAL_BASE_FLOOR = 0.60                 # piso base dinámico para evitar bloqueo permanente en MODELO experimental
AUTO_REAL_THR_MIN = max(float(IA_ACTIVACION_REAL_THR), float(AUTO_REAL_BASE_FLOOR))
AUTO_REAL_TOP_Q = 0.80    # cuantíl de probs históricas para calibrar el gate REAL
AUTO_REAL_MARGIN = 0.01   # pequeño margen para evitar quedar fuera por décimas
AUTO_REAL_LOG_MAX_ROWS = 300  # máximo de señales históricas usadas en la calibración
AUTO_REAL_LIVE_MIN_BOTS = 3   # mínimos bots con prob viva para calibración por tick

# Umbral "operativo/UI" (señales actuales, semáforo, etc.)
IA_METRIC_THRESHOLD = AUTO_REAL_THR_MIN
# Modo clásico: activación REAL con umbral operativo vigente (hoy 65%, con techo dinámico base 70%).
# Mantiene lock de un solo bot en REAL y ciclo martingala global en HUD.
REAL_CLASSIC_GATE = True
MODO_PURIFICACION_REAL = True  # Llave maestra: bypassea toda promoción/activación REAL sin apagar IA/HUD.
LXV_SYNC_REAL_ROUTE_ENABLE = True
LXV_SYNC_REAL_SOURCE = "LXV_SYNC"

# ✅ Umbral SOLO para auditoría/calibración (señales CERRADAS en ia_signals_log)
# Esto es lo que querías: contar cierres desde 60% sin afectar la operativa.
IA_CALIB_THRESHOLD = 0.60
IA_CALIB_GOAL_THRESHOLD = IA_OBJETIVO_REAL_THR  # objetivo real: medir cierres fuertes cerca de 70%
IA_CALIB_MIN_CLOSED = 200  # mínimo recomendado para considerar estable la auditoría
REAL_GO_N_MIN = 180
REAL_GO_CLOSED_MIN = 50

# Recomendaciones operativas conservadoras (anti-sobreconfianza)
IA_TEMP_THR_HIGH = 0.80              # umbral temporal sugerido cuando la muestra fuerte es baja
IA_MIN_CLOSED_70_FOR_STRUCT = 200    # mínimo de cierres IA>=70% para cambios estructurales
IA_SHRINK_ALPHA = 0.60               # p_ajustada = alpha*p + (1-alpha)*tasa_base
IA_SHRINK_ALPHA_MIN = 0.45           # piso de mezcla (más conservador en descalibración fuerte)
IA_SHRINK_ALPHA_MAX = 0.85           # techo de mezcla (más sensible cuando la calibración mejora)
IA_BASE_RATE_WINDOW = 300            # cierres recientes para tasa base rolling
# Guardrail explícito de sobreconfianza en bucket alto (fase 1, bajo riesgo).
IA_OVERCONF_BUCKET_MIN_PROB = 0.90
IA_OVERCONF_MIN_N = 20
IA_OVERCONF_GAP_MAX_PP = 0.15
IA_OVERCONF_DYNAMIC_CAP = 0.90
IA_CHECKPOINT_CLOSED_STEP = 20
# Guardrail duro de salud IA (global+por bot): evita sobreconfianza con muestra inmadura.
IA_HARD_GUARD_ENABLE = True
IA_HARD_GUARD_RED_MIN_CLOSED = 0
IA_HARD_GUARD_AMBER_MIN_CLOSED = 80
IA_HARD_GUARD_RED_MIN_AUC = 0.48
IA_HARD_GUARD_GREEN_MIN_AUC = 0.55
IA_HARD_GUARD_MIN_FEATURES_RED = 3
IA_HARD_GUARD_MIN_FEATURES_GREEN = 6
IA_HARD_GUARD_RED_CAP = 0.66
IA_HARD_GUARD_AMBER_CAP = 0.66
IA_HARD_GUARD_RED_REQUIRE_MODEL_READY = True  # evita RED duro por AUC=0 cuando aún no existe modelo válido
IA_HARD_GUARD_SEVERE_GAP_MIN_N = 10
IA_HARD_GUARD_SEVERE_OVERCONF_GAP_PP = 0.25
IA_HARD_GUARD_AMBER_OVERCONF_GAP_PP = 0.15
IA_HARD_GUARD_GREEN_MAX_GAP_PP = 0.10
IA_HARD_GUARD_HYSTERESIS_S = 180.0
IA_HARD_GUARD_LOG_COOLDOWN_S = 45.0
IA_HARD_GUARD_BOT_MIN_N = 10
IA_HARD_GUARD_BOT_GAP_PP = 0.18
# Impulso por racha reciente (micro-ajuste dinámico para evitar Prob IA plana).
IA_RACHA_BOOST_ENABLE = True
IA_RACHA_BOOST_WINDOW = 8
IA_RACHA_BOOST_MAX_UP = 0.10
IA_RACHA_BOOST_MAX_DN = 0.05
IA_RACHA_BOOST_MIN_WINS = 5
IA_RACHA_BOOST_LOG_COOLDOWN_S = 25.0
# Cap conservador de probabilidad durante warmup para evitar inflado (ej. 99-100%).
IA_WARMUP_PROB_CAP_MIN = 0.70
IA_WARMUP_PROB_CAP_MAX = 0.85
IA_WARMUP_CAP_RAMP_ROWS = 120         # rampa de cap en warmup: permite tocar 75% antes sin abrir 90%
IA_WARMUP_LOW_EVIDENCE_CAP_BASE = 0.80
IA_WARMUP_LOW_EVIDENCE_CAP_POST_N15 = 0.85

AUTO_REAL_ALLOW_UNRELIABLE_POST_N15 = True
AUTO_REAL_UNRELIABLE_MIN_N = 0
AUTO_REAL_UNRELIABLE_MIN_PROB = 0.54  # modo unreliable conservador: exige mejor discriminación antes de REAL
AUTO_REAL_UNRELIABLE_MIN_AUC = 0.52   # unreliable conservador: evita activaciones con AUC marginal débil
AUTO_REAL_BLOCK_WHEN_WARMUP = False   # no bloquear REAL por warmup (perfil prueba protegida)
# Ajuste mínimo anti-congelamiento lateral: permite bajar el umbral UNREL
# solo cuando hay evidencia operativa consistente por bot.
AUTO_REAL_UNREL_LATERAL_ADAPT_ENABLE = True
AUTO_REAL_UNREL_LATERAL_MIN_N = 50
AUTO_REAL_UNREL_LATERAL_MIN_WR = 0.50
AUTO_REAL_UNREL_LATERAL_MIN_PROB = 0.50
AUTO_REAL_UNRELIABLE_FLOOR = 0.51      # piso REAL temporal cuando reliable=false y ya hay n mínimo por bot
# Micro-relajación gradual del umbral UNREL basada en cierres auditados reales.
# Solo aplica cuando ya hay muestra suficiente y rendimiento sostenido.
AUTO_REAL_UNREL_MICRO_RELAX_ENABLE = True
AUTO_REAL_UNREL_MICRO_RELAX_MIN_CLOSED = 20
AUTO_REAL_UNREL_MICRO_RELAX_MIN_WINRATE = 0.70
AUTO_REAL_UNREL_MICRO_RELAX_MAX_DELTA = 0.02
AUTO_REAL_UNREL_MICRO_RELAX_LOG_COOLDOWN_S = 45.0
# Bypass controlado: si la compuerta REAL ya está sólida en vivo, permitir AUTO
# aunque el modelo siga en warmup/reliable=false.
AUTO_REAL_UNRELIABLE_ALLOW_STRONG_GATE = True
AUTO_REAL_UNRELIABLE_GATE_MIN_PROB = IA_ACTIVACION_REAL_THR_POST_N15
AUTO_REAL_MICRO_EARLY_CONFIRM_ENABLE = True
AUTO_REAL_MICRO_EARLY_CONFIRM_MARGIN = 0.02
AUTO_REAL_MICRO_EARLY_CONFIRM_DEFICIT_MAX = 1

# Guardas por bot para reducir desalineación Prob IA vs % Éxito observado en HUD.
IA_PROMO_MIN_WR_POR_BOT = 0.45         # no promover bots con WR rolling claramente negativo
IA_PROMO_MAX_OVERCONF_GAP = 0.18       # si p_real supera WR por >18pp con evidencia, bloquear promoción

# Gate de calidad operativo (objetivo: mejorar precisión real, no volumen)
GATE_RACHA_NEG_BLOQUEO = -2.0        # bloquear señales con racha <= -2
GATE_PERMITE_REBOTE_EN_NEG = True    # permitir excepción si hay rebote confirmado
GATE_ACTIVO_MIN_MUESTRA = 40         # mínimo de cierres por activo para evaluar régimen
GATE_ACTIVO_MIN_WR = 0.48            # si WR reciente por activo cae debajo, bloquear temporalmente
GATE_ACTIVO_LOOKBACK = 180           # cierres recientes por bot para estimar régimen
ASSET_PROTECT_ENABLE = True          # protección dinámica por activo basada en degradación real
ASSET_PROTECT_LOOKBACK = 80
ASSET_COOLDOWN_S = 900
ASSET_MAX_CONSEC_LOSS = 4
ASSET_MAX_DRAWDOWN = -4.0
ASSET_MIN_WR = 0.42
ASSET_MAX_DEEP_CYCLE_RATIO = 0.55
ASSET_ALERT_COOLDOWN_S = 60.0
# Gate por segmentos (payout/vol/hora): prioriza zonas con señal estable de racha_actual
GATE_SEGMENTO_ENABLED = True  # gate segmento operativo para filtrar contexto débil
GATE_SEGMENTO_MIN_MUESTRA = 35
GATE_SEGMENTO_MIN_WR = 0.50
GATE_SEGMENTO_LOOKBACK = 240

# Candados inteligentes: evita bloqueos rígidos en empates/planicies cuando ya
# hay evidencia real robusta de un bot claramente apto.
SMART_LOCKS_ENABLE = True
SMART_CLONE_OVERRIDE_MIN_N = 20
SMART_CLONE_OVERRIDE_MIN_LB = 0.53
SMART_CLONE_OVERRIDE_MIN_PROB = 0.62
SMART_CLONE_OVERRIDE_MIN_GAP = 0.002

# Embudo IA en 2 capas: A=régimen (tradeable), B=prob fina (modelo)
REGIME_GATE_MIN_SCORE = 0.52          # mínimo score de régimen para considerar señal
REGIME_GATE_WEIGHT_PROB = 0.70        # peso de la prob del modelo en ranking final
REGIME_GATE_WEIGHT_REGIME = 0.20      # peso de la calidad de régimen
REGIME_GATE_WEIGHT_EVIDENCE = 0.10    # peso de evidencia histórica real (N + WR)
EVIDENCE_MIN_N_HARD = 60              # si hay >=N evidencia fuerte, exigir WR mínimo
EVIDENCE_MIN_WR_HARD = 0.70           # objetivo de calidad real por bot para habilitar auto-REAL
EVIDENCE_MIN_LB_HARD = 0.65           # candado conservador: límite inferior mínimo con evidencia fuerte
EVIDENCE_MIN_N_SOFT = 20              # evidencia mínima blanda para validar LB intermedio
EVIDENCE_MIN_LB_SOFT = 0.55           # LB mínimo cuando N aún es intermedio
EVIDENCE_LOW_N_EXTRA_MARGIN = 0.05    # margen extra de p_real si aún no hay N mínimo blando
POSTERIOR_EVIDENCE_K = 80             # inercia: más alto = más peso al histórico para p_real
POSTERIOR_REGIME_BLEND = 0.35         # mezcla del score de régimen dentro de p_real
EVIDENCE_CACHE_TTL_S = 20.0

# Guardas de honestidad operacional (alineadas al diagnóstico)
DIAG_PATH = "diagnostico_pipeline_ia.json"
ORIENTATION_RECHECK_S = 90.0
ORIENTATION_FLIP_MIN_DELTA = 0.03
ORIENTATION_MIN_CLOSED = 80
ORIENTATION_REQUIRE_RELIABLE_MODEL = True  # evita invertir p->1-p durante warmup/experimental
HARD_GATE_MAX_GAP_HIGH_BINS = 0.10
HARD_GATE_MIN_N_FOR_HIGH_THR = 200
INCREMENTAL_DUP_SCAN_LINES = 6000

# Umbral del aviso de audio (archivo ia_scifi_02_ia53_dry.wav)
AUDIO_IA53_THR = IA_ACTIVACION_REAL_THR

# Anti-spam + rearme
AUDIO_IA53_COOLDOWN_S = 20     # no repetir más de 1 vez cada X segundos por bot
AUDIO_IA53_RESET_HYST = 0.03   # se rearma cuando cae por debajo de (thr - hyst)

# === Caché de sonidos ===
SOUND_CACHE = {}
SOUND_LOAD_ERRORS = set()
SOUND_PATHS = {
    "ganancia_real": "ganabot.wav",
    "ganancia_demo": "ganabot.wav",
    "perdida_real": "perdida.wav",
    "perdida_demo": "perdida.wav",
    "meta_15": "meta15%.wav",
    "racha_detectada": "detectaracha.wav",
    "test": "test.wav",
    "ia_53": "ia_scifi_08_53porciento_dry.wav",

}
AUDIO_AVAILABLE = False
META_ACEPTADA = False
MODAL_ACTIVO = False
sonido_disparado = False
# === FIN BLOQUE 2 ===

# === BLOQUE 2.5 — PLAN OPERATIVO PATRÓN V1 (RESUMEN EJECUTIVO) ===
# IMPORTANTE:
# - Este bloque NO reemplaza todavía la lógica de entrada actual.
# - Sirve para dejar la integración preparada y revisable.
# - Los candados existentes (hard_guard/confirm/trigger/roof) se mantienen.
PATTERN_V1_ENABLE = True
PATTERN_V1_SCORE_THR = 6.0
PATTERN_V1_BONUS_DUAL = 1.0
PATTERN_V1_PENAL_TARDIA = 2.0
PATTERN_V1_REQUIRE_CONFIRM_FULL = True   # confirm=2/2
PATTERN_V1_REQUIRE_TRIGGER_OK = True     # trigger_ok=sí
PATTERN_V1_USE_HYBRID_RANKING = True    # ranking híbrido operativo (prob + pattern + evidencia)
PATTERN_V1_LOG_COOLDOWN_S = 25.0
PATTERN_V1_HYBRID_PTS_TO_PROB = 0.03  # 1 punto pattern = 3pp sobre score probabilístico
PATTERN_COL_WINDOW = 40
PATTERN_COL80_THRESHOLD = 0.80
PATTERN_COL90_THRESHOLD = 0.90
PATTERN_REBOTE_LOOKBACK = 12
PATTERN_REBOTE_MIN = 0.65
PATTERN_REBOTE_MIN_SAMPLES = 3
PATTERN_STRONG_STREAK_BLOCK = 2
PATTERN_ENABLE = True
PATTERN_COL_BONUS_CONTINUIDAD = 0.60
PATTERN_COL_BONUS_REBOTE = 0.80
PATTERN_COL_PENAL_SATURACION = 1.20
PATTERN_COL_PENAL_LATE_CHASE = 1.00
PATTERN_COL_LAST_STATE = {
    "green_ratio_col_actual": None,
    "total_verdes_col_actual": 0,
    "total_rojos_col_actual": 0,
    "rebote_rate_hist": None,
    "rebote_samples_hist": 0,
    "total_x_hist": 0,
    "total_x_rebote_hist": 0,
    "pattern_state": "BLOQUEADO",
    "strong_streak_80": 0,
    "strong_streak_90": 0,
    "late_chase": False,
    "pattern_delta": 0.0,
    "pattern_bonus_penalty": 0.0,
}
PATTERN_V1_Q3_PROXY = {
    "rsi_9": 64.0,
    "rsi_reversion": 0.060,
    "es_rebote": 0.090,
    "puntaje_estrategia": 0.28,
    "cruce_sma": 0.62,
    "breakout": 0.20,
    "payout": 0.9525,
    "racha_actual": 2.0,
}
PATTERN_V1_Q2_PROXY = {
    "volatilidad": 0.049,
}
PATTERN_V1_LAST_LOG_TS = {}
# Fase operativa REAL por madurez: SHADOW -> MICRO -> NORMAL
REAL_PILOT_MODE_ENABLE = True
REAL_MICRO_REQUIRE_PATTERN = False
REAL_MICRO_PATTERN_MIN_TOTAL = 4.0
REAL_MICRO_REQUIRE_DUAL = False
REAL_MICRO_REQUIRE_STRUCTURE = False
REAL_MICRO_MIN_WR = 0.50
REAL_MICRO_MIN_TRADES = 40
REAL_MICRO_TOP_K = 1
REAL_MICRO_ALLOW_SOFT_HIGH_PROB = True
REAL_MICRO_SOFT_MIN_PROB = 0.58
REAL_MICRO_SOFT_MIN_SUCESO = 18.0
REAL_MICRO_SOFT_MIN_WR = 0.47
REAL_SHADOW_MICRO_ENABLE = True
REAL_SHADOW_MICRO_MIN_PROB = 0.56
REAL_SHADOW_MICRO_MAX_ENTRIES = 6
REAL_SHADOW_MICRO_WINDOW_S = 300
REAL_SHADOW_MICRO_TOP_K = 1
REAL_SHADOW_MICRO_LOG_COOLDOWN_S = 20.0
_REAL_SHADOW_MICRO_OPEN_TS = deque(maxlen=64)
_REAL_SHADOW_MICRO_LAST_LOG_TS = 0.0
REAL_MICRO_STRONG_GATE_FALLBACK_ENABLE = True
REAL_MICRO_STRONG_GATE_MIN_PROB = 0.60
EMBUDO_FINAL_BLOCK_HARD = "BLOCK_HARD"
EMBUDO_FINAL_WAIT_SOFT = "WAIT_SOFT"
EMBUDO_FINAL_REAL_MICRO = "REAL_MICRO"
EMBUDO_FINAL_REAL_NORMAL = "REAL_NORMAL"
EMBUDO_FINAL_SHADOW_OK = "SHADOW_OK"
IA_PROB_POLARIZE_ENABLE = True
IA_PROB_POLARIZE_FACTOR_RELIABLE = 1.25
IA_PROB_POLARIZE_FACTOR_UNRELIABLE = 2.05
IA_PROB_POLARIZE_CENTER = 0.50


def _validar_pattern_v1_config() -> None:
    """Sanitiza parámetros para evitar valores inválidos en runtime."""
    global PATTERN_V1_SCORE_THR, PATTERN_V1_BONUS_DUAL, PATTERN_V1_PENAL_TARDIA, PATTERN_V1_LOG_COOLDOWN_S, PATTERN_V1_HYBRID_PTS_TO_PROB
    global PATTERN_COL_WINDOW, PATTERN_COL80_THRESHOLD, PATTERN_COL90_THRESHOLD, PATTERN_REBOTE_LOOKBACK
    global PATTERN_REBOTE_MIN, PATTERN_REBOTE_MIN_SAMPLES, PATTERN_STRONG_STREAK_BLOCK
    PATTERN_V1_SCORE_THR = max(0.0, float(PATTERN_V1_SCORE_THR))
    PATTERN_V1_BONUS_DUAL = max(0.0, float(PATTERN_V1_BONUS_DUAL))
    PATTERN_V1_PENAL_TARDIA = max(0.0, float(PATTERN_V1_PENAL_TARDIA))
    PATTERN_V1_LOG_COOLDOWN_S = max(5.0, float(PATTERN_V1_LOG_COOLDOWN_S))
    PATTERN_V1_HYBRID_PTS_TO_PROB = min(0.10, max(0.0, float(PATTERN_V1_HYBRID_PTS_TO_PROB)))
    PATTERN_COL_WINDOW = max(5, int(PATTERN_COL_WINDOW))
    PATTERN_COL80_THRESHOLD = min(0.99, max(0.50, float(PATTERN_COL80_THRESHOLD)))
    PATTERN_COL90_THRESHOLD = min(1.0, max(float(PATTERN_COL80_THRESHOLD), float(PATTERN_COL90_THRESHOLD)))
    PATTERN_REBOTE_LOOKBACK = max(2, int(PATTERN_REBOTE_LOOKBACK))
    PATTERN_REBOTE_MIN = min(1.0, max(0.0, float(PATTERN_REBOTE_MIN)))
    PATTERN_REBOTE_MIN_SAMPLES = max(1, int(PATTERN_REBOTE_MIN_SAMPLES))
    PATTERN_STRONG_STREAK_BLOCK = max(1, int(PATTERN_STRONG_STREAK_BLOCK))


def resumen_plan_cambios_5r6m() -> list[str]:
    """Resumen corto de cambios planificados en 5R6M-1-2-4-8-16.py."""
    return [
        "1) Añadir Pattern Score compuesto (señales duales + estructura técnica).",
        "2) Añadir veto tardío para evitar perseguir rachas verdes iniciadas.",
        "3) Separar detección de oportunidad vs permiso final de entrada.",
        "4) Mantener candados existentes (hard_guard, confirm, trigger, roof).",
        "5) Usar ranking híbrido: prob_ia_oper + bonus_patron - penal_tardia - crowding.",
        "6) Medir drift por ventanas y degradar score cuando no hay persistencia.",
    ]


def pattern_score_operativo_v1(features: dict, q3: dict, q2: dict) -> tuple[float, float, float, float]:
    """Score proxy para integración gradual (sin reemplazar la decisión vigente).

    Retorna: (score, bonus_dual, penal_tardia, score_final)
    """
    score = 0.0
    if features.get("rsi_9", 0.0) >= q3.get("rsi_9", 1e9):
        score += 2.0
    if features.get("rsi_reversion", 0.0) >= q3.get("rsi_reversion", 1e9):
        score += 2.0
    if features.get("es_rebote", 0.0) >= q3.get("es_rebote", 1e9):
        score += 2.0
    if features.get("puntaje_estrategia", 0.0) >= q3.get("puntaje_estrategia", 1e9):
        score += 1.0
    if features.get("cruce_sma", 0.0) >= q3.get("cruce_sma", 1e9):
        score += 1.0
    if features.get("breakout", 0.0) >= q3.get("breakout", 1e9):
        score += 1.0
    if features.get("payout", 0.0) >= q3.get("payout", 1e9):
        score += 1.0
    if features.get("volatilidad", 1e9) <= q2.get("volatilidad", -1e9):
        score += 1.0

    dual = (
        features.get("rsi_reversion", 0.0) >= q3.get("rsi_reversion", 1e9)
        or features.get("es_rebote", 0.0) >= q3.get("es_rebote", 1e9)
    )
    bonus_dual = (
        PATTERN_V1_BONUS_DUAL
        if dual and features.get("rsi_9", 0.0) >= q3.get("rsi_9", 1e9)
        else 0.0
    )
    penal_tardia = 0.0
    if features.get("racha_actual", 0.0) >= q3.get("racha_actual", 1e9) and not dual:
        penal_tardia = PATTERN_V1_PENAL_TARDIA

    score_final = score + bonus_dual - penal_tardia
    return score, bonus_dual, penal_tardia, score_final


def _pattern_v1_thresholds_proxy() -> tuple[dict, dict]:
    """Umbrales proxy (Q3/Q2) para operar Pattern V1 sin dependencia externa."""
    return dict(PATTERN_V1_Q3_PROXY), dict(PATTERN_V1_Q2_PROXY)


def _pattern_v1_log_bot(bot: str, pattern_score: float, bonus_dual: float, penal_tardia: float, score_hibrido: float) -> None:
    """Log por bot con cooldown para auditar impacto del Pattern V1."""
    try:
        ahora = time.time()
        last = float(PATTERN_V1_LAST_LOG_TS.get(bot, 0.0) or 0.0)
        if (ahora - last) < float(PATTERN_V1_LOG_COOLDOWN_S):
            return
        PATTERN_V1_LAST_LOG_TS[bot] = float(ahora)
        agregar_evento(
            f"🧠 PatternV1 {bot}: score={pattern_score:.1f} bonus={bonus_dual:.1f} "
            f"penal={penal_tardia:.1f} score_hibrido={score_hibrido*100:.1f}%"
        )
    except Exception:
        pass


def _purificacion_real_activa() -> bool:
    """Llave maestra centralizada para apagar capa REAL sin romper flujo IA/HUD."""
    try:
        route_src = str(globals().get("_REAL_ROUTE_SOURCE", "") or "").strip().upper()
        if bool(globals().get("LXV_SYNC_REAL_ROUTE_ENABLE", False)) and route_src == str(globals().get("LXV_SYNC_REAL_SOURCE", "LXV_SYNC")).upper():
            return False
        return bool(globals().get("MODO_PURIFICACION_REAL", False))
    except Exception:
        return False


def _emitir_marca_purificacion_real() -> None:
    """Marca visual/evento con cooldown para confirmar bypass REAL activo."""
    global _LAST_PURIFICACION_REAL_EVENT_TS
    try:
        if not _purificacion_real_activa():
            return
        now = float(time.time())
        if (now - float(_LAST_PURIFICACION_REAL_EVENT_TS or 0.0)) < float(PURIFICACION_REAL_EVENT_COOLDOWN_S):
            return
        _LAST_PURIFICACION_REAL_EVENT_TS = now
        agregar_evento("🧪 MODO PURIFICACION REAL ACTIVO: promoción/orden REAL desactivada (bypass).")
    except Exception:
        pass


def _guardar_real_owner_state(bot: str, ciclo: int, source: str, round_id: int | None = None, token_state: str | None = None) -> None:
    """Telemetría mínima del owner REAL asignado por el maestro."""
    try:
        payload = {
            "owner_bot": str(bot),
            "assigned_ts": float(time.time()),
            "ciclo": int(ciclo),
            "source": str(source or "UNKNOWN"),
            "round_id": int(round_id) if isinstance(round_id, (int, float)) else None,
            "token_state": str(token_state) if token_state is not None else None,
        }
        _atomic_write(REAL_OWNER_STATE_FILE, json.dumps(payload, ensure_ascii=False, indent=2))
        globals()["LAST_REAL_OWNER_STATE"] = payload
    except Exception:
        pass


def _registrar_real_close_trace(data: dict) -> None:
    """Append conservador de cierre REAL confirmado (sin tocar cálculo de saldo)."""
    try:
        payload = dict(data or {})
        payload.setdefault("ts", float(time.time()))
        _append_line_safe(REAL_CLOSE_TRACE_FILE, json.dumps(payload, ensure_ascii=False) + "\n")
        globals()["LAST_REAL_CLOSE_TRACE"] = payload
    except Exception:
        pass


def _resolver_estado_real(meta_live: dict | None = None) -> str:
    """Estado operativo REAL: SHADOW, MICRO, NORMAL."""
    try:
        if _purificacion_real_activa():
            return "SHADOW"
        if not bool(REAL_PILOT_MODE_ENABLE):
            return "NORMAL"
        meta = meta_live if isinstance(meta_live, dict) else (_ORACLE_CACHE.get("meta") or leer_model_meta() or {})
        n = int(meta.get("n_samples", meta.get("n", 0)) or 0)
        auc = float(meta.get("auc", 0.0) or 0.0)
        warmup = bool(meta.get("warmup_mode", n < int(TRAIN_WARMUP_MIN_ROWS)))
        reliable = bool(meta.get("reliable", False)) and (not warmup)
        hg = _estado_guardrail_ia_fuerte(force=False)
        if reliable and (auc >= 0.53) and (not bool(hg.get("hard_block", False))):
            return "NORMAL"
        if n >= int(MIN_FIT_ROWS_PROD):
            return "MICRO"
        return "SHADOW"
    except Exception:
        return "SHADOW"


def _micro_pattern_gate_ok(bot: str, ctx: dict | None = None) -> tuple[bool, str]:
    """Filtro principal en MICRO: patrón dual + estructura + recencia mínima."""
    try:
        if not bool(REAL_MICRO_REQUIRE_PATTERN):
            return True, "off"
        st = estado_bots.get(bot, {}) if isinstance(estado_bots, dict) else {}
        c = ctx if isinstance(ctx, dict) else _ultimo_contexto_operativo_bot(bot)
        q3, q2 = _pattern_v1_thresholds_proxy()
        p_score, p_bonus, p_penal, p_total = pattern_score_operativo_v1(c or {}, q3, q2)
        strict_ok = True
        why = f"pat={p_total:.1f}"
        if float(p_total) < float(REAL_MICRO_PATTERN_MIN_TOTAL):
            strict_ok = False
            why = f"pat<{REAL_MICRO_PATTERN_MIN_TOTAL:.1f}"
        if strict_ok and bool(REAL_MICRO_REQUIRE_DUAL) and float(p_bonus) <= 0.0:
            strict_ok = False
            why = "dual=no"
        if strict_ok and bool(REAL_MICRO_REQUIRE_STRUCTURE):
            breakout_ok = bool(float((c or {}).get("breakout", 0.0) or 0.0) >= float(q3.get("breakout", 1e9)))
            cruce_ok = bool(float((c or {}).get("cruce_sma", 0.0) or 0.0) >= float(q3.get("cruce_sma", 1e9)))
            if not (breakout_ok or cruce_ok):
                strict_ok = False
                why = "struct=no"

        g = int(st.get("ganancias", 0) or 0)
        d = int(st.get("perdidas", 0) or 0)
        n = int(max(0, g + d))
        wr = float((g + 1.0) / (n + 2.0))
        if strict_ok and n >= int(REAL_MICRO_MIN_TRADES) and wr < float(REAL_MICRO_MIN_WR):
            strict_ok = False
            why = f"wr<{REAL_MICRO_MIN_WR*100:.0f}%"
        if strict_ok and float(p_penal) > 0.0:
            strict_ok = False
            why = "late=veto"
        if strict_ok:
            return True, why

        # Fallback suave: permite fluir entradas cuando la calidad viva es alta
        # aunque el patrón dual/estructura no complete en ese tick.
        if bool(REAL_MICRO_ALLOW_SOFT_HIGH_PROB):
            p_oper = float(st.get("prob_ia_oper", st.get("prob_ia", 0.0)) or 0.0)
            suceso = float(st.get("ia_suceso_idx", 0.0) or 0.0)
            if (
                p_oper >= float(REAL_MICRO_SOFT_MIN_PROB)
                and suceso >= float(REAL_MICRO_SOFT_MIN_SUCESO)
                and wr >= float(REAL_MICRO_SOFT_MIN_WR)
                and float(p_penal) <= float(PATTERN_V1_PENAL_TARDIA)
            ):
                return True, f"soft:p={p_oper*100:.1f}%/s={suceso:.1f}"

        return False, why
    except Exception:
        return False, "pattern_err"


def _shadow_micro_quota_status(now_ts: float | None = None) -> tuple[int, int, float]:
    """Estado de cuota para micro-REAL temporal en SHADOW."""
    try:
        now = float(time.time() if now_ts is None else now_ts)
        window_s = max(60.0, float(REAL_SHADOW_MICRO_WINDOW_S))
        while _REAL_SHADOW_MICRO_OPEN_TS and (now - float(_REAL_SHADOW_MICRO_OPEN_TS[0])) > window_s:
            _REAL_SHADOW_MICRO_OPEN_TS.popleft()
        used = int(len(_REAL_SHADOW_MICRO_OPEN_TS))
        max_entries = max(1, int(REAL_SHADOW_MICRO_MAX_ENTRIES))
        left = max(0, max_entries - used)
        return left, used, window_s
    except Exception:
        return 0, 0, max(60.0, float(REAL_SHADOW_MICRO_WINDOW_S))


def _shadow_micro_gate_ok(candidatos: list, dyn_gate: dict | None = None) -> tuple[bool, str]:
    """Bypass seguro para permitir micro-REAL temporal aun en SHADOW."""
    global _REAL_SHADOW_MICRO_LAST_LOG_TS
    try:
        if not bool(REAL_SHADOW_MICRO_ENABLE):
            return False, "off"
        if not candidatos:
            return False, "sin_candidatos"
        if not bool(_todos_bots_con_n_minimo_real()):
            return False, "n_min_real"

        dgate = dyn_gate if isinstance(dyn_gate, dict) else {}
        confirm_need = int(dgate.get("confirm_need", DYN_ROOF_CONFIRM_TICKS) or DYN_ROOF_CONFIRM_TICKS)
        confirm_ok = int(dgate.get("confirm_streak", 0) or 0) >= confirm_need
        trigger_ok = bool(dgate.get("trigger_ok", False))
        allow_gate = bool(dgate.get("allow_real", False))

        best = candidatos[0]
        best_bot = str(best[1])
        p_best = float(best[2] or 0.0)
        if best_bot != str(dgate.get("best_bot", best_bot)):
            return False, "best_mismatch"
        if p_best < float(REAL_SHADOW_MICRO_MIN_PROB):
            return False, f"p<{REAL_SHADOW_MICRO_MIN_PROB*100:.0f}%"
        if not (confirm_ok and trigger_ok and allow_gate):
            return False, "gate_debil"

        hg = _estado_guardrail_ia_fuerte(force=False)
        if bool(hg.get("hard_block", False)):
            return False, "hard_guard"

        left, used, window_s = _shadow_micro_quota_status()
        if left <= 0:
            return False, f"quota:{used}/{max(1, int(REAL_SHADOW_MICRO_MAX_ENTRIES))}/{int(window_s//60)}m"

        now = time.time()
        if (now - float(_REAL_SHADOW_MICRO_LAST_LOG_TS or 0.0)) >= float(REAL_SHADOW_MICRO_LOG_COOLDOWN_S):
            _REAL_SHADOW_MICRO_LAST_LOG_TS = float(now)
            agregar_evento(
                f"🟢 REAL=SHADOW→MICRO temporal: {best_bot} p={p_best*100:.1f}% "
                f"confirm={int(dgate.get('confirm_streak', 0))}/{confirm_need} trigger_ok=sí "
                f"quota={used}/{max(1, int(REAL_SHADOW_MICRO_MAX_ENTRIES))}"
            )
        return True, "ok"
    except Exception:
        return False, "shadow_micro_err"


def _micro_strong_gate_fallback_ok(candidatos: list, dyn_gate: dict | None = None) -> tuple[bool, str]:
    """Fallback moderado para MICRO cuando el patrón no completa pero la compuerta está sólida."""
    try:
        if not bool(REAL_MICRO_STRONG_GATE_FALLBACK_ENABLE):
            return False, "off"
        if not candidatos:
            return False, "sin_candidatos"
        dgate = dyn_gate if isinstance(dyn_gate, dict) else {}
        top = candidatos[0]
        best_bot = str(top[1])
        p_best = float(top[2] or 0.0)
        confirm_need = int(dgate.get("confirm_need", DYN_ROOF_CONFIRM_TICKS) or DYN_ROOF_CONFIRM_TICKS)
        confirm_ok = int(dgate.get("confirm_streak", 0) or 0) >= confirm_need
        trigger_ok = bool(dgate.get("trigger_ok", False))
        allow_gate = bool(dgate.get("allow_real", False))
        if best_bot != str(dgate.get("best_bot", best_bot)):
            return False, "best_mismatch"
        if p_best < float(REAL_MICRO_STRONG_GATE_MIN_PROB):
            return False, f"p<{REAL_MICRO_STRONG_GATE_MIN_PROB*100:.0f}%"
        if not (confirm_ok and trigger_ok and allow_gate):
            return False, "gate_debil"
        hg = _estado_guardrail_ia_fuerte(force=False)
        if bool(hg.get("hard_block", False)):
            return False, "hard_guard"
        return True, f"p={p_best*100:.1f}%"
    except Exception:
        return False, "micro_fallback_err"


_validar_pattern_v1_config()


# === BLOQUE 3 — CONFIGURACIÓN DE REENTRENAMIENTO Y MODOS IA ===
# === CONFIGURACIÓN DE REENTRENAMIENTO ===
RETRAIN_INTERVAL_ROWS = 100     # por volumen
RETRAIN_INTERVAL_MIN  = 15      # por tiempo
MIN_NEW_ROWS_FOR_TIME = 20      # al menos 20 filas nuevas para reentrenar por tiempo
MAX_DATASET_ROWS = 10000
last_retrain_count = 0
last_retrain_ts    = time.time()  # Inicializado al boot para arranque en frío
AUTO_RETRAIN_TICK_S = 20.0  # reintento periódico para no quedarse sin modelo tras warmup
IA_NO_MODEL_LOG_COOLDOWN_S = 30.0  # evita spam cuando aún no hay modelo
_entrenando_lock = threading.Lock()  # Lock para antireentradas en maybe_retrain

# === MODO ENTRENAMIENTO CON POCA DATA (no toca la lógica de IA) ===
LOW_DATA_MODE = True           # True = permite entrenar con muy pocas filas
MIN_FIT_ROWS_PROD = 100        # umbral “confiable” para producción (lo que ya usabas)
MIN_FIT_ROWS_LOW  = 4          # umbral mínimo para permitir fit “experimental”
RELIABLE_POS_MIN  = 20         # mínimos para considerar fiable (calibración/umbral estable)
RELIABLE_NEG_MIN  = 20

# Modo manual desactivado: priorizamos automatización completa por Prob IA.
# Si luego quieres volver al modo manual, ponlo en True.
MODO_REAL_MANUAL = False

# Martingala global
marti_paso = 0
marti_activa = False

# Contador global de ciclos de martingala (HUD + orquestación automática)
# 0 = sin pérdidas consecutivas en REAL; 1..MAX_CICLOS = racha de pérdidas vigente.
marti_ciclos_perdidos = 0

# Anti-repetición de bot en REAL:
# - Si el HUD está en C1, se puede repetir bot.
# - Si el HUD está en C2..C{MAX_CICLOS}, se prioriza no repetir; puede haber fallback controlado.
ultimo_bot_real = None

# Rotación por corrida de martingala REAL (C1..C{MAX_CICLOS})
# Guarda el orden de bots usados en la corrida activa para evitar repeticiones.
bots_usados_en_esta_marti = []
# Continuidad inteligente C2..C{MAX_CICLOS}: si no hay bot nuevo elegible, permitir repetir
# el mejor candidato SOLO bajo umbral mínimo de probabilidad operativa.
MARTI_CYCLE_ALLOW_REPEAT_FALLBACK = True
MARTI_CYCLE_REPEAT_MIN_PROB = 0.68
MARTI_CYCLE_REPEAT_MIN_PROB_UNRELIABLE_CAP = 0.66


def _marti_repeat_min_prob_live(meta_live=None):
    """Umbral vivo para fallback C2..C{MAX_CICLOS}, con ajuste conservador en modo no confiable."""
    base = float(MARTI_CYCLE_REPEAT_MIN_PROB)
    try:
        if not isinstance(meta_live, dict):
            meta_live = resolver_canary_estado(leer_model_meta() or {})
        n_samples = int(meta_live.get("n_samples", meta_live.get("n", 0)) or 0)
        warmup = bool(meta_live.get("warmup_mode", n_samples < int(TRAIN_WARMUP_MIN_ROWS)))
        reliable = bool(meta_live.get("reliable", False)) and (not warmup)
        if not reliable:
            base = min(base, float(MARTI_CYCLE_REPEAT_MIN_PROB_UNRELIABLE_CAP))
    except Exception:
        pass
    return float(max(0.0, min(1.0, base)))

# Auditoría de secuencia martingala (C1..C{MAX_CICLOS}) para traza explícita.
marti_audit_run_id = 1
marti_audit_historial = deque(maxlen=80)
marti_audit_desviaciones = 0
marti_audit_ultimo_ciclo_ordenado = None

# Nueva: Umbrales mínimos para historial IA
MIN_IA_SENIALES_CONF = 10  # Mínimo señales cerradas para confiar en prob_hist
MIN_AUC_CONF = 0.65        # AUC mínimo para audios/colores verdes
MAX_CLASS_IMBALANCE = 0.8  # Máx proporción pos/neg para entrenar (evita 99% wins)
AUC_DROP_TOL = 0.05        # Tolerancia para no machacar modelo si AUC baja
TRAIN_REFRESH_STALE_MIN = 45 * 60   # forzar revisión de refresh si el campeón lleva mucho sin actualizar (s)
TRAIN_REFRESH_MIN_GROWTH = 0.20     # crecimiento mínimo relativo de dataset para considerar stale override
TRAIN_REFRESH_MIN_ABS_ROWS = 60      # crecimiento mínimo absoluto de filas para stale override
TRAIN_REFRESH_MIN_ABS_ROWS_LOWN = 20 # override para modelos pequeños: refresco más temprano
TRAIN_REFRESH_LOWN_CUTOFF = 180      # n por debajo de esto usa umbral absoluto reducido
TRAIN_CANARY_FORCE_UNRELIABLE = True # canary: refresca probs pero bloquea REAL hasta validar en operación cerrada
CANARY_MIN_CLOSED_SIGNALS = 20      # cierres mínimos para decidir salida de canary
CANARY_MIN_HITRATE = 0.50           # hit-rate mínimo de cierres durante canary para promover
CANARY_RETRY_BATCH = 10             # si canary falla, ampliar ventana en este tamaño
CANARY_EVAL_COOLDOWN_S = 10.0       # evaluar progreso canary como máximo cada N segundos
# Escape controlado: evita deadlock cuando CANARY no acumula cierres pero la compuerta REAL ya está sólida.
CANARY_ALLOW_STRONG_GATE_REAL = True
CANARY_STRONG_GATE_MIN_PROB = IA_ACTIVACION_REAL_THR_POST_N15
CANARY_STRONG_GATE_MIN_CONFIRM = 2
TRAIN_ROWS_DROP_GUARD_RATIO = 0.35  # no reemplazar modelo si la muestra cae demasiado vs meta anterior
TRAIN_ROWS_DROP_GUARD_MIN_PREV = 120  # activar guard solo si el modelo previo ya tenía muestra razonable
FEATURE_MAX_DOMINANCE = 0.90  # Si una feature repite >90%, se considera casi constante
FEATURE_DQ_MIN_OK = 5         # mínimo de features sanas para no bloquear warmup por 1 columna ruidosa
TRAIN_WARMUP_MIN_ROWS = 250          # evita declarar modo confiable sin muestra mínima
INPUT_DUP_DIAG_COOLDOWN_S = 25.0     # anti-spam de diagnóstico por inputs duplicados
CLONED_PROB_TICKS_ALERT = 3          # ticks consecutivos de probs clonadas para alertar
INPUT_DUP_FINGERPRINT_DECIMALS = 6   # precisión estable para huella de inputs IA


# Semáforo de calibración (lectura rápida PredMedia/Real/Inflación/n)
SEM_CAL_N_ROJO = 30
SEM_CAL_N_AMARILLO = 100
SEM_CAL_INFL_OK_PP = 5.0
SEM_CAL_INFL_WARN_PP = 15.0

# ============================================================
# Defaults IA (centralizados, sin duplicados)
# ============================================================
MIN_TRAIN_ROWS  = 250
TEST_SIZE_FRAC  = 0.20
MIN_TEST_ROWS   = 40
THR_DEFAULT = 0.50
MIN_TRAIN_ROWS_ADAPTIVE = 40  # evita entrenar con train ridículo cuando el dataset aún es chico
MIN_TRAIN_SHARE_ADAPTIVE = 0.60

# Split honesto: TRAIN_BASE (pasado) / CALIB (más reciente) / TEST (último)
CALIB_SIZE_FRAC = 0.15
MIN_CALIB_ROWS = 80

# Feature list canónica (si tu reentreno define otra, ahí la cambias UNA vez)
# ============================================================
# Feature set CORE (13) — estable y sin mutaciones
# ============================================================
FEATURE_NAMES_CORE_13 = [
    # CORE13_v2 (scalping 1-min): mantener aportantes + reemplazo de no-aportantes.
    "racha_actual", "puntaje_estrategia", "payout",
    "ret_1m", "ret_3m", "ret_5m", "slope_5m", "rv_20",
    "range_norm", "bb_z", "body_ratio", "wick_imbalance", "micro_trend_persist",
]

# Por defecto entrenamos SOLO con las 13 core (modo estable)
FEATURE_NAMES_INTERACCIONES = [
    "racha_x_rebote",
    "rev_x_breakout",
]

# Gobernanza calidad>cantidad: entrenar solo con features que realmente aporten.
FEATURE_ALWAYS_KEEP = ["racha_actual"]
FEATURE_MAX_PROD = 6
FEATURE_SET_PROD_WARMUP = ["racha_actual", "puntaje_estrategia", "ret_1m", "slope_5m", "rv_20", "bb_z"]
FEATURE_SET_CORE_EXT = ["racha_actual", "puntaje_estrategia", "ret_1m", "slope_5m", "rv_20", "bb_z"]
FEATURE_SET_CORE_EXT_MIN_ROWS = 500
FEATURE_MIN_AUC_DELTA = 0.015      # aporte mínimo (|AUC_uni - 0.5|)
FEATURE_MAX_DOMINANCE_GATE = 0.965 # evita casi-constantes
FEATURE_DYNAMIC_SELECTION = False
# Durante warmup evitamos selección agresiva para no colapsar a 2-4 features.
FEATURE_FREEZE_CORE_DURING_WARMUP = True
FEATURE_FREEZE_CORE_MIN_ROWS = TRAIN_WARMUP_MIN_ROWS
# Si el modelo anterior colapsó a muy pocas features, permitimos reemplazarlo
# aunque la AUC temporal baje levemente en un reentreno puntual.
FEATURE_MIN_ACCEPTED_COUNT = 6

# Meta objetivo (calidad real en señales fuertes)
IA_TARGET_PRECISION = 0.70
IA_TARGET_PRECISION_FLOOR = 0.65   # piso mínimo para declarar confiable
IA_TARGET_MIN_SIGNALS = 30         # mínimo de señales en zona alta para validar

# Guardas de promoción de campeón: evitar reemplazar por modelos débiles/colapsados.
TRAIN_PROMOTE_MIN_AUC = 0.50
TRAIN_PROMOTE_MIN_FEATURES = 5

FEATURE_NAMES_PROD = list(FEATURE_SET_PROD_WARMUP)
FEATURE_NAMES_SHADOW = [f for f in FEATURE_NAMES_CORE_13 if f not in FEATURE_NAMES_PROD]
FEATURE_NAMES_DEFAULT = list(FEATURE_NAMES_CORE_13)
PROXY_FEATURES_BLOCK_TRAIN = [
    "ret_1m", "ret_3m", "ret_5m", "slope_5m", "rv_20",
    "range_norm", "bb_z", "body_ratio", "wick_imbalance", "micro_trend_persist",
]

class ModeloXGBCalibrado:
    """
    Wrapper picklable para calibrar probabilidades con un holdout temporal (CALIB),
    sin re-entrenar el modelo base. El modelo espera X ya escalado.
    calib_kind: "sigmoid" (Platt con LogisticRegression sobre logit(p)) o "isotonic".
    """
    def __init__(self, modelo_base, calib_kind: str, calib_obj):
        self.modelo_base = modelo_base
        self.calib_kind = str(calib_kind)
        self.calib_obj = calib_obj

    def _calibrar_p(self, p: np.ndarray) -> np.ndarray:
        p = np.asarray(p, dtype=float)
        p = np.clip(p, 1e-6, 1.0 - 1e-6)

        if self.calib_kind == "sigmoid":
            z = np.log(p / (1.0 - p)).reshape(-1, 1)
            p_cal = self.calib_obj.predict_proba(z)[:, 1]
            return np.clip(p_cal, 1e-6, 1.0 - 1e-6)

        # isotonic
        p_cal = self.calib_obj.transform(p)
        return np.clip(np.asarray(p_cal, dtype=float), 1e-6, 1.0 - 1e-6)

    def predict_proba(self, X):
        p_base = self.modelo_base.predict_proba(X)[:, 1]
        p_cal = self._calibrar_p(p_base)
        return np.vstack([1.0 - p_cal, p_cal]).T

    def predict(self, X):
        proba = self.predict_proba(X)[:, 1]
        return (proba >= 0.5).astype(int)

# === FIN BLOQUE 3 ===

# === BLOQUE 4 — AUDIO (INIT Y REPRODUCCIÓN) ===
# Inicialización de audio
def init_audio():
    global AUDIO_AVAILABLE, SOUND_CACHE

    # No asumimos nada: recalculamos disponibilidad cada vez
    AUDIO_AVAILABLE = False

    # 1) Asegurar mixer (si no está listo)
    if pygame.mixer.get_init():
        AUDIO_AVAILABLE = True
    else:
        drivers = ['directsound', 'winmm', 'wasapi', None]
        configs = [
            (44100, -16, 2, 1024),
            (22050, -16, 2, 512),
            (44100, -16, 1, 1024),
        ]
        for driver in drivers:
            for freq, size, channels, buffer in configs:
                try:
                    if driver:
                        os.environ["SDL_AUDIODRIVER"] = driver
                    pygame.mixer.pre_init(frequency=freq, size=size, channels=channels, buffer=buffer)
                    pygame.mixer.init()
                    AUDIO_AVAILABLE = True
                    break
                except Exception:
                    pass
            if AUDIO_AVAILABLE:
                break

    # 2) Fallback winsound (aunque no tengamos pygame)
    if not AUDIO_AVAILABLE and winsound:
        AUDIO_AVAILABLE = True

    # 3) Cargar sonidos SOLO si mixer está operativo
    if pygame.mixer.get_init():
        base_dir = os.path.dirname(__file__)
        for event, filename in SOUND_PATHS.items():
            if event in SOUND_LOAD_ERRORS:
                continue
            path = os.path.join(base_dir, filename)
            if os.path.exists(path):
                try:
                    SOUND_CACHE[event] = pygame.mixer.Sound(path)
                except Exception:
                    SOUND_LOAD_ERRORS.add(event)

def reproducir_evento(evento, es_demo=False, dentro_gatewin=True):
    global sonido_disparado

    if not AUDIO_AVAILABLE:
        return

    # Reglas de GateWIN/DEMO (mismas que tenías)
    if evento != "ia_53":
        if SONAR_SOLO_EN_GATEWIN and (not dentro_gatewin) and (not SONAR_FUERA_DE_GATEWIN):
            return
        if es_demo and not SONAR_TAMBIEN_EN_DEMO:
            return

    # 1) Preferir pygame si está cargado
    try:
        if evento in SOUND_CACHE:
            SOUND_CACHE[evento].play()
            sonido_disparado = True
            return
    except Exception:
        pass

    # 2) Fallback winsound (si pygame no está usable o no cargó el sonido)
    if winsound:
        try:
            filename = SOUND_PATHS.get(evento)
            if not filename:
                return
            base_dir = os.path.dirname(__file__)
            path = os.path.join(base_dir, filename)
            if os.path.exists(path):
                winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC)
                sonido_disparado = True
        except Exception:
            pass
# === FIN BLOQUE 4 ===

# === BLOQUE 5 — TOKENS, BOT_NAMES Y ESTADO GLOBAL ===
# Leer tokens del usuario
def leer_tokens_usuario():
    if not os.path.exists("tokens_usuario.txt"):
        return None, None
    try:
        with open("tokens_usuario.txt", "r", encoding="utf-8") as file:
            lines = [line.strip() for line in file.readlines()]
            if len(lines) < 2:
                return None, None
            token_demo, token_real = lines[0], lines[1]
            if not token_demo or not token_real:
                return None, None
            return token_demo, token_real
    except Exception:
        return None, None

# Escritura atómica de token
def write_token_atomic(path, content):
    temp_path = path + ".tmp"
    try:
        with open(temp_path, "w", encoding="utf-8") as f:
            f.write(content)
            f.flush()
            os.fsync(f.fileno())
        os.replace(temp_path, path)
        return True
    except Exception:
        try:
            if os.path.exists(temp_path):
                os.remove(temp_path)
        except Exception:
            pass
        return False


# Orden operativo recomendado (calidad real primero):
# 1) fulll47: mejor hit-rate y menor inflación del set comparado.
# 2) fulll50/fulll45: rendimiento similar pero con muestra algo mayor.
# 3) fulll48: intermedio, baja muestra.
# 4) fulll49/fulll46: sobreconfianza alta y peor hit-rate reciente.
BOT_NAMES = ["fulll47", "fulll50", "fulll45", "fulll48", "fulll49", "fulll46"]
IA53_TRIGGERED = {bot: False for bot in BOT_NAMES}
IA53_LAST_TS = {bot: 0.0 for bot in BOT_NAMES}
TOKEN_FILE = "token_actual.txt"
DERIV_WS_URL = "wss://ws.derivws.com/websockets/v3?app_id=1089"
saldo_real = "--"
SALDO_INICIAL = None
META = None
meta_mostrada = False
eventos_recentes = deque(maxlen=8)
reinicio_forzado = asyncio.Event()

salir = False
pausado = False
reinicio_manual = False
MAESTRO_PAUSE_FILE = os.path.abspath(os.path.expanduser(os.getenv("MAESTRO_PAUSE_STATE_PATH", os.path.join(os.path.dirname(os.path.abspath(__file__)), "maestro_pause_state.json"))))
maestro_pause_active = False
maestro_pause_reason = ""
maestro_pause_resume_ts = 0.0
maestro_pause_started_ts = 0.0
maestro_pause_last_read_ts = 0.0
maestro_pause_last_log_ts = 0.0
maestro_pause_ref_balance = None
maestro_pause_trigger_balance = None
maestro_pause_source = ""
maestro_pause_last_state = False

LIMPIEZA_PANEL_HASTA = 0
ULTIMA_ACT_SALDO = 0
REFRESCO_SALDO = 12
MAX_CICLOS = len(MARTI_ESCALADO)
huellas_usadas = {bot: set() for bot in BOT_NAMES}
SNAPSHOT_FILAS = {bot: 0 for bot in BOT_NAMES}
REAL_ENTRY_BASELINE = {bot: 0 for bot in BOT_NAMES}  # filas al entrar/reafirmar REAL
OCULTAR_HASTA_NUEVO = {bot: False for bot in BOT_NAMES}
t_inicio_indef = {bot: None for bot in BOT_NAMES}
last_update_time = {bot: time.time() for bot in BOT_NAMES}
LAST_REAL_CLOSE_SIG = {bot: None for bot in BOT_NAMES}  # evita procesar el mismo cierre REAL varias veces
CTT_CLOSE_EVENTS = deque(maxlen=6000)
CTT_CLOSE_SEEN = set()
CTT_STATE = {
    "status": "NEUTRAL",
    "regime": "NEUTRAL",
    "gate": "NEUTRAL",
    "asset": None,
    "t_front": 0.0,
    "wave_start": 0.0,
    "wave_age_s": None,
    "wave_ttl_ok": False,
    "wave_ratio": 0.0,
    "wave_total": 0,
    "confirmadores": 0,
    "density_cpm": 0.0,
    "diversity_ratio": 0.0,
    "redundancy_high": False,
    "green_mode": "none",
    "rezagados_validos": [],
    "no_participantes": [],
    "sample": 0,
    "roof_policy": "normal",
    "roof_delta": 0.0,
    "reason": "init",
}
REAL_OWNER_LOCK = None  # owner REAL en memoria (evita carreras de lectura de archivo)
REAL_LOCK_MISMATCH_SINCE = 0.0
REAL_LOCK_RECONCILE_S = 6.0
REAL_OWNER_STATE_FILE = "real_owner_state.json"
REAL_CLOSE_TRACE_FILE = "real_close_trace.jsonl"
LAST_REAL_CLOSE_TRACE = {}

EMBUDO_DECISION_STATE = {
    "decision_final": EMBUDO_FINAL_WAIT_SOFT,
    "decision_reason": "init",
    "gate_quality": "weak",
    "risk_mode": "WAIT_SOFT",
    "hard_block_reason": "",
    "soft_wait_reason": "init",
    "top1_bot": None,
    "top2_bot": None,
    "gap_value": 0.0,
    "top1_prob": 0.0,
    "top2_prob": 0.0,
    "degrade_from": "none",
}

try:
    last_sig_por_bot
except NameError:
    last_sig_por_bot = {b: None for b in BOT_NAMES}

estado_bots = {
    bot: {
        "resultados": [], 
        "token": "DEMO", 
        "trigger_real": False,
        "ganancias": 0, 
        "perdidas": 0, 
        "porcentaje_exito": None,
        "tamano_muestra": 0,
        "prob_ia": None,              # guardará prob REAL (0..1). OJO: ya NO la forzamos a 0 por “no señal”
        "ia_ready": False,           # True solo si logramos armar features + predecir sin error
        "ia_last_err": None,         # texto corto del motivo si no se pudo predecir
        "ia_last_prob_ts": 0.0,      # timestamp de la última prob calculada
        "ciclo_actual": 1,
        "modo_real_anunciado": False, 
        "ultimo_resultado": None,
        "reintentar_ciclo": False,
        "remate_active": False,
        "remate_start": None,
        "remate_reason": "",
        "fuente": None,  
        "real_activado_en": 0.0,  
        "ignore_cierres_hasta": 0.0,
        "real_timeout_first_warn": 0.0,
        "modo_ia": "low_data",  # Arranca visible en warmup para evitar confusión de OFF al inicio
        "ia_seniales": 0,  # contadores para medir IA
        "ia_aciertos": 0,
        "ia_fallos": 0,
        "ia_senal_pendiente": False,  # Flag para operación recomendada por IA
        "ia_prob_senal": None,        # prob IA en el momento de la señal
        "ia_regime_score": 0.0,       # capa A (régimen)
        "ia_evidence_n": 0,           # soporte histórico en umbral objetivo
        "ia_evidence_wr": 0.0,        # win-rate real en umbral objetivo
        # Telemetría Pattern V1 (existente)
        "ia_pattern_bonus": 0.0,
        "ia_pattern_penal": 0.0,
        # Telemetría patrón por columnas (separada, evita colisión con Pattern V1)
        "ia_pattern_col_state": "BLOQUEADO",
        "ia_pattern_col_bonus": 0.0,
        "ia_pattern_col_penal": 0.0,
        "ia_pattern_col_delta": 0.0,
        "sync_wait": False,
        "last_sync_round": 1,
        "last_seen_ts": 0.0,
        "estado_visual": "ACTIVO",
    }
    for bot in BOT_NAMES
}
IA90_stats = {bot: {"n": 0, "ok": 0, "pct": 0.0, "pct_raw": 0.0, "pct_smooth": 50.0} for bot in BOT_NAMES}
# Ventana corta para diagnosticar el bloqueo dominante del embudo en HUD.
HUD_BLOQUEO_WINDOW = 120
HUD_BLOQUEOS_RECIENTES = deque(maxlen=HUD_BLOQUEO_WINDOW)
HUD_BOT_GATE_DIAG_EVERY_S = 6.0
_LAST_HUD_BOT_GATE_DIAG_TS = 0.0
PURIFICACION_REAL_EVENT_COOLDOWN_S = 90.0
_LAST_PURIFICACION_REAL_EVENT_TS = 0.0

EVENTO_MAX_CHARS = 220

def _normalizar_evento_texto(msg: str, max_chars: int = EVENTO_MAX_CHARS) -> str:
    try:
        txt = str(msg if msg is not None else "")
    except Exception:
        txt = ""
    for ch in ("\r", "\n", "\t"):
        txt = txt.replace(ch, " ")
    txt = " ".join(txt.split())
    if len(txt) > int(max_chars):
        txt = txt[: max(0, int(max_chars) - 1)] + "…"
    return txt

# === FIN BLOQUE 5 ===

# === BLOQUE 6 — LOCKS, FIRMAS Y UTILIDADES CSV ===
def _firma_registro(feature_names, row_vals, label):
    """
    Firma estable anti-duplicados:
    - Formato fijo para floats (evita variaciones 0.1 vs 0.10000000002)
    """
    parts = []
    for v in row_vals:
        try:
            parts.append(f"{float(v):.6f}")
        except Exception:
            parts.append(str(v))
    try:
        parts.append(str(int(label)))
    except Exception:
        parts.append(str(label))
    return "|".join(parts)

# Contar filas en CSV (sin header)
def contar_filas_csv(bot_name: str) -> int:
    ruta = f"registro_enriquecido_{bot_name}.csv"
    if not os.path.exists(ruta):
        return 0
    for encoding in ["utf-8", "latin-1", "windows-1252"]:
        try:
            with open(ruta, "r", newline="", encoding=encoding, errors="replace") as f:
                n = sum(1 for _ in f) - 1
                return max(0, n)
        except Exception:
            continue
    return 0

INCREMENTAL_LOCK_FILE = "incremental.lock"

# Contar filas en dataset_incremental.csv (sin contar header)
def contar_filas_incremental() -> int:
    """
    Devuelve número de filas (sin header) de dataset_incremental.csv.

    Optimizado:
    - Cachea (pos, size, rows) para evitar re-escaneo completo en cada llamada.
    - Si el archivo crece, cuenta solo las líneas nuevas.
    """
    try:
        path = "dataset_incremental.csv"

        if not os.path.exists(path):
            contar_filas_incremental._cache = {"pos": 0, "rows": 0, "size": 0}
            return 0

        cache = getattr(contar_filas_incremental, "_cache", None)
        size = os.path.getsize(path)

        # Recuento completo en binario (robusto a encoding)
        def _count_full_rows() -> int:
            total = 0
            last_byte = b""
            with open(path, "rb") as f:
                while True:
                    chunk = f.read(1024 * 1024)
                    if not chunk:
                        break
                    total += chunk.count(b"\n")
                    last_byte = chunk[-1:]
            # Si el archivo NO termina en \n, hay una línea final sin salto
            if size > 0 and last_byte != b"\n":
                total += 1
            # Quita header si existe
            return max(0, total - 1)

        # Sin cache o el archivo se redujo/truncó: recuenta todo
        if (not cache) or (size < int(cache.get("size", 0) or 0)) or (int(cache.get("pos", 0) or 0) > size):
            rows = _count_full_rows()
            contar_filas_incremental._cache = {"pos": size, "rows": rows, "size": size}
            return rows

        # Si no cambió, devuelve cache
        if size == int(cache.get("size", 0) or 0):
            return int(cache.get("rows", 0) or 0)

        # Creció: cuenta solo líneas nuevas desde la última posición
        pos = int(cache.get("pos", 0) or 0)
        new_lines = 0
        with open(path, "rb") as f:
            f.seek(pos)
            while True:
                chunk = f.read(1024 * 1024)
                if not chunk:
                    break
                new_lines += chunk.count(b"\n")

        rows = int(cache.get("rows", 0) or 0) + new_lines
        contar_filas_incremental._cache = {"pos": size, "rows": rows, "size": size}
        return rows

    except Exception:
        return 0

# Lock de archivo
@contextmanager
def file_lock(path="real.lock", timeout=5.0, stale_after=30.0):
    """
    Lock por archivo (cross-platform) con protección anti-colisión:

    - NO borra el lock de otro proceso activo.
    - Solo intenta limpiar locks *stale* (viejos) si supera stale_after segundos.
    - Si no logra adquirir lock, continúa SIN exclusión (como ya venías haciendo),
      pero sin destruir el lock ajeno.
    """
    start_time = time.time()
    fd = None
    acquired = False

    try:
        # 1) Intento normal por timeout
        while (time.time() - start_time) < float(timeout):
            try:
                fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR)
                acquired = True
                break
            except FileExistsError:
                time.sleep(0.10)
            except Exception:
                time.sleep(0.10)

        # 2) Si no se pudo, evaluar si el lock parece "stale"
        if not acquired:
            age = None
            try:
                age = time.time() - os.path.getmtime(path)
            except Exception:
                age = None

            if age is not None and age > float(stale_after):
                # Solo si es viejo de verdad, intentamos limpiar
                try:
                    os.remove(path)
                    fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR)
                    acquired = True
                except Exception as e:
                    try:
                        print(f"⚠️ Lock stale no se pudo limpiar ({path}): {e}. Continúo sin exclusión.")
                    except Exception:
                        pass
            else:
                # Lock reciente: NO tocarlo
                try:
                    print(f"⚠️ No se adquirió lock ({path}) en {timeout}s (lock reciente). Continúo sin exclusión.")
                except Exception:
                    pass

        # 3) Ejecutar la sección crítica (con o sin lock adquirido)
        yield

    finally:
        if acquired and fd is not None:
            try:
                os.close(fd)
            except Exception:
                pass
            try:
                os.remove(path)
            except Exception:
                pass
# ============================================================
# DATASET INCREMENTAL — Reparación de esquema "mutante"
# (header viejo / columnas extra / filas con campos de más)
# Objetivo: mantener SIEMPRE un CSV estable para pandas/IA.
# ============================================================

# Reusar el set core (13) para que incremental y entrenamiento nunca diverjan
try:
    INCREMENTAL_FEATURES_V2 = list(FEATURE_NAMES_CORE_13)
except Exception:
    INCREMENTAL_FEATURES_V2 = [
        "racha_actual", "puntaje_estrategia", "payout",
        "ret_1m", "ret_3m", "ret_5m", "slope_5m", "rv_20",
        "range_norm", "bb_z", "body_ratio", "wick_imbalance", "micro_trend_persist",
    ]
INCREMENTAL_CLOSE_COLS = [f"close_{i}" for i in range(20)]
INCREMENTAL_META_FLAGS = ["row_has_proxy_features", "row_train_eligible"]
for _c in INCREMENTAL_CLOSE_COLS:
    if _c not in INCREMENTAL_FEATURES_V2:
        INCREMENTAL_FEATURES_V2.append(_c)
# === LOCK ESTRICTO (solo para escrituras sensibles como incremental.csv) ===
@contextmanager
def file_lock_required(path: str, timeout: float = 6.0, stale_after: float = 30.0):
    """
    Igual que file_lock, pero:
    - Si NO adquiere lock, NO ejecuta la sección crítica (yield False).
    - Para escrituras que NO toleran concurrencia (append CSV).
    """
    start_time = time.time()
    fd = None
    acquired = False

    try:
        while (time.time() - start_time) < float(timeout):
            try:
                fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR)
                acquired = True
                break
            except FileExistsError:
                time.sleep(0.10)
            except Exception:
                time.sleep(0.10)

        if not acquired:
            age = None
            try:
                age = time.time() - os.path.getmtime(path)
            except Exception:
                age = None

            if age is not None and age > float(stale_after):
                try:
                    os.remove(path)
                    fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR)
                    acquired = True
                except Exception:
                    acquired = False

        yield acquired

    finally:
        if acquired and fd is not None:
            try:
                os.close(fd)
            except Exception:
                pass
            try:
                os.remove(path)
            except Exception:
                pass
# === /LOCK ESTRICTO ===

def _canonical_incremental_cols(feature_names: list | None = None) -> list:
    fn = feature_names if feature_names else INCREMENTAL_FEATURES_V2
    out = list(fn)
    for mc in INCREMENTAL_META_FLAGS:
        if mc not in out:
            out.append(mc)
    return out + ["result_bin"]

_INCREMENTAL_INGEST_STATS = {
    "filas_incremental_aceptadas": 0,
    "filas_incremental_saneadas_close": 0,
    "filas_incremental_proxy_no_train": 0,
    "filas_incremental_descartadas_total": 0,
    "filas_incremental_close_reales_validas": 0,
    "last_log_ts": 0.0,
}

def _safe_float(x):
    try:
        if x is None:
            return None
        if isinstance(x, str):
            x = x.strip()
            if x == "":
                return None
        v = float(x)
        if not np.isfinite(v):
            return None
        return v
    except Exception:
        return None

def _safe_int01(x):
    try:
        if x is None:
            return None
        if isinstance(x, str):
            x = x.strip()
            if x == "":
                return None
        v = int(float(x))
        if v not in (0, 1):
            return None
        return v
    except Exception:
        return None

def reparar_dataset_incremental_mutante(ruta: str = "dataset_incremental.csv", cols: list | None = None) -> bool:
    """
    Repara dataset_incremental.csv cuando quedó 'mutante' por:
    - header corrupto (ej: racha...ia) o incompleto
    - filas con más/menos columnas (ej: bot_id, activo_id metidos)
    - mezcla de esquemas (Expected X fields, saw Y)

    Estrategia:
    - Reescribe un CSV limpio con columnas canónicas (cols).
    - Si el archivo actual tiene columnas canónicas presentes, mapea por header.
    - Si el header no es usable, intenta rescate por POSICIÓN:
        * len>=16: [0..12] + [15] (drop bot_id/activo_id)
        * len==15: [0..12] + [14]
        * len==14: [0..12] + [13]  (13 feats + label)
        * len>len(cols): toma primeras (len(cols)-1) + última como label
    - Crea backup del archivo original con sufijo .bak_<epoch>.
    """
    cols = cols or _canonical_incremental_cols()
    if not os.path.exists(ruta):
        return False

    # Leer header y detectar mutación
    header_list = None
    enc_usado = None
    for enc in ("utf-8", "latin-1", "windows-1252"):
        try:
            with open(ruta, "r", newline="", encoding=enc, errors="replace") as f:
                first = f.readline()
            header_list = [h.strip() for h in first.strip().split(",")] if first else []
            enc_usado = enc
            break
        except Exception:
            continue

    if header_list is None:
        return False

    # Si el header ya es canónico, igual escanear rápido por longitudes
    header_ok = (header_list == cols)
    header_has_canonical = set(cols).issubset(set(header_list))

    needs_repair = not header_ok

    # Escaneo rápido de longitudes (si hay mezcla de campos, se marca mutante)
    try:
        with open(ruta, "r", newline="", encoding=enc_usado or "utf-8", errors="replace") as f:
            reader = csv.reader(f)
            _ = next(reader, None)  # header
            for j, row in enumerate(reader, start=1):
                if not row:
                    continue
                if len(row) != len(header_list):
                    needs_repair = True
                    break
                if j >= 3000:
                    break
    except Exception:
        needs_repair = True

    if not needs_repair:
        return False

    # Armar filas limpias
    cleaned_rows = []
    seen_rows = set()
    header_index = {name: i for i, name in enumerate(header_list)} if header_has_canonical else {}

    for enc in ("utf-8", "latin-1", "windows-1252"):
        try:
            with open(ruta, "r", newline="", encoding=enc, errors="replace") as f:
                reader = csv.reader(f)
                _ = next(reader, None)  # header
                for row in reader:
                    if not row:
                        continue

                    new_row = None

                    # 1) Si el header contiene columnas canónicas, mapear por nombre
                    if header_has_canonical:
                        try:
                            new_row = [row[header_index[c]] if header_index[c] < len(row) else "" for c in cols]
                        except Exception:
                            new_row = None

                    # 2) Si el header no es canónico, intentar conversión por nombre (legacy->v2)
                    if new_row is None and header_list and len(header_list) == len(row):
                        try:
                            row_map = {str(header_list[i]).strip(): row[i] for i in range(len(row))}
                            row_map = _enriquecer_scalping_features_row(row_map)
                            lb = row_map.get("result_bin", row_map.get("label", row_map.get("y", None)))
                            new_row = [row_map.get(c, "") for c in cols[:-1]] + [lb]
                        except Exception:
                            new_row = None

                    # 3) Rescate por posición (último recurso legacy; evitar para v2 salvo emergencia)
                    if new_row is None:
                        ncols = len(cols)
                        rlen = len(row)
                        if rlen >= ncols:
                            new_row = list(row[:ncols - 1]) + [row[-1]]
                        else:
                            continue


                    # Validación y saneo defensivo (clip + contrato activo)
                    try:
                        row_map_clean = {cols[i]: new_row[i] for i in range(len(cols))}
                        feat_validate = [c for c in cols[:-1] if c not in INCREMENTAL_META_FLAGS and c != "ts_ingest"]
                        row_map_clean = clip_feature_values(row_map_clean, feat_validate)
                        for mc in INCREMENTAL_META_FLAGS:
                            if mc not in row_map_clean or row_map_clean.get(mc, "") in ("", None):
                                row_map_clean[mc] = 0 if mc == "row_has_proxy_features" else 1
                        if "ts_ingest" in cols and (row_map_clean.get("ts_ingest", "") in ("", None)):
                            row_map_clean["ts_ingest"] = float(time.time())
                        ok_row, _reason = validar_fila_incremental(row_map_clean, feat_validate)
                        if not ok_row:
                            continue
                        lab = _safe_int01(row_map_clean.get("result_bin", new_row[-1]))
                        if lab is None:
                            continue
                        row_clean = []
                        for c in cols[:-1]:
                            if c in INCREMENTAL_META_FLAGS:
                                row_clean.append(int(float(row_map_clean.get(c, 0 if c == "row_has_proxy_features" else 1) or 0)))
                            else:
                                row_clean.append(float(row_map_clean.get(c, 0.0) or 0.0))
                        row_clean = row_clean + [lab]
                        # Deduplicar durante repair para no inflar entrenamiento por filas repetidas.
                        sig = tuple(round(float(v), 10) for v in row_clean[:-1]) + (int(row_clean[-1]),)
                        if sig in seen_rows:
                            continue
                        seen_rows.add(sig)
                        cleaned_rows.append(row_clean)
                    except Exception:
                        continue
            break
        except Exception:
            continue

    # Reescritura atómica con backup
    tmp = ruta + ".tmp_repair"
    try:
        with open(tmp, "w", newline="", encoding="utf-8") as f:
            w = csv.writer(f)
            w.writerow(cols)
            for r in cleaned_rows:
                w.writerow(r)
            f.flush()
            os.fsync(f.fileno())

        backup = f"{ruta}.bak_{int(time.time())}"
        backed_up = False

        # 1) Intento preferido: renombrar (rápido y atómico)
        try:
            os.replace(ruta, backup)
            backed_up = True
        except Exception:
            backed_up = False

        # 2) Fallback: copiar (cuando rename falla por permisos/locks)
        if not backed_up:
            try:
                shutil.copy2(ruta, backup)
                backed_up = True
            except Exception:
                backed_up = False

        # 3) Si NO hay backup, NO pisamos el original
        if not backed_up:
            raise RuntimeError("No se pudo crear backup del incremental; se aborta reparación para no perder datos.")

        os.replace(tmp, ruta)
        return True

    except Exception as e:
        try:
            if os.path.exists(tmp):
                os.remove(tmp)
        except Exception:
            pass
        fn_evt = globals().get("agregar_evento", None)
        try:
            if callable(fn_evt):
                fn_evt(f"⚠️ Incremental: reparación falló: {e}")
            else:
                print(f"⚠️ Incremental: reparación falló: {e}")
        except Exception:
            print(f"⚠️ Incremental: reparación falló: {e}")
        return False

# Firma persistente anti-duplicados
_SIG_DIR = ".sigcache"
os.makedirs(_SIG_DIR, exist_ok=True)

def _sig_path(bot): 
    safe = str(bot).replace("/", "_").replace("\\", "_")
    return os.path.join(_SIG_DIR, f"{safe}.sig")

def _load_recent_sigs(bot: str, max_keep: int = 50) -> list:
    """
    Devuelve lista de firmas recientes (últimas N) desde disco.
    Compatible con formato viejo (1 sola firma).
    """
    try:
        p = _sig_path(bot)
        if not os.path.exists(p):
            return []
        with open(p, "r", encoding="utf-8", errors="replace") as f:
            lines = [ln.strip() for ln in f.read().splitlines() if ln.strip()]
        if not lines:
            return []
        return lines[-int(max_keep):]
    except Exception:
        return []

def _sig_in_cache(bot: str, sig: str, max_keep: int = 50) -> bool:
    try:
        return sig in set(_load_recent_sigs(bot, max_keep=max_keep))
    except Exception:
        return False

def _append_sig_cache(bot: str, sig: str, max_keep: int = 50):
    """
    Guarda firma al final, manteniendo solo últimas N (y sin duplicados internos).
    """
    try:
        max_keep = int(max_keep)
        if max_keep < 5:
            max_keep = 5

        lst = _load_recent_sigs(bot, max_keep=max_keep)
        # mover al final si existe
        lst = [x for x in lst if x != sig] + [sig]
        lst = lst[-max_keep:]

        with open(_sig_path(bot), "w", encoding="utf-8") as f:
            f.write("\n".join(lst))
    except Exception:
        pass
# === COMPAT: helpers legacy (evita NameError y mantiene tu lógica actual) ===
def _load_last_sig(bot: str) -> str | None:
    """
    Compatibilidad: versiones antiguas esperaban una sola firma.
    Hoy guardamos varias en _sigcache; devolvemos la última.
    """
    try:
        lst = _load_recent_sigs(bot, max_keep=50)
        if not lst:
            return None
        return lst[-1]
    except Exception:
        return None

def _save_last_sig(bot: str, sig: str):
    """
    Compatibilidad: guarda como “última firma”, manteniendo historial.
    """
    try:
        _append_sig_cache(bot, sig, max_keep=50)
    except Exception:
        pass
# === /COMPAT ===

def _make_sig(row_dict):
    """Firma estable para comparar filas entre reinicios (sin timestamp si no existe)."""
    try:
        # Orden determinista
        data = {k: row_dict.get(k) for k in sorted(row_dict.keys())}
        s = json.dumps(data, ensure_ascii=False, sort_keys=True)
        return hashlib.sha256(s.encode("utf-8")).hexdigest()
    except:
        return None

_INCREMENTAL_SIG_CACHE = {"mtime": 0.0, "sigs": set()}

def _load_incremental_signatures(ruta: str, feats: list, max_rows: int = INCREMENTAL_DUP_SCAN_LINES) -> set:
    """Carga firmas recientes del incremental para bloquear duplicados exactos aunque reinicie el bot."""
    try:
        if not os.path.exists(ruta):
            return set()
        mtime = float(os.path.getmtime(ruta) or 0.0)
        cache = _INCREMENTAL_SIG_CACHE
        if cache.get("mtime") == mtime and cache.get("sigs"):
            return set(cache.get("sigs") or set())

        sigs = set()
        with open(ruta, "r", encoding="utf-8", errors="replace", newline="") as f:
            rows = list(csv.DictReader(f))
        if max_rows > 0:
            rows = rows[-int(max_rows):]
        for r in rows:
            try:
                vals = [float(r.get(k, 0.0) or 0.0) for k in feats]
                lab = int(float(r.get("result_bin", 0) or 0))
                sigs.add(_firma_registro(feats, vals, lab))
            except Exception:
                continue
        _INCREMENTAL_SIG_CACHE["mtime"] = mtime
        _INCREMENTAL_SIG_CACHE["sigs"] = set(sigs)
        return sigs
    except Exception:
        return set()

def _incremental_signature_exists(ruta: str, sig: str, feats: list) -> bool:
    try:
        return sig in _load_incremental_signatures(ruta, feats, max_rows=INCREMENTAL_DUP_SCAN_LINES)
    except Exception:
        return False

# Core scalping mínimo válido para no cuarentenar filas útiles por close_* incompleto
def _core_scalping_ready_from_row(row: dict) -> bool:
    try:
        keys = ("ret_1m", "slope_5m", "rv_20", "bb_z")
        for k in keys:
            v = row.get(k, None)
            if v is None or (isinstance(v, str) and v.strip() == ""):
                return False
            vf = float(v)
            if not np.isfinite(vf):
                return False
        return True
    except Exception:
        return False

def _close_snapshot_issue_from_row(row: dict, required_closes: int = 20) -> bool:
    try:
        need = int(required_closes)
        valid = 0
        for i in range(need):
            v = row.get(f"close_{i}", None)
            if v is None or (isinstance(v, str) and v.strip() == ""):
                continue
            vf = float(v)
            if np.isfinite(vf) and vf > 0.0:
                valid += 1
        return bool(valid < need)
    except Exception:
        return True

# Nueva: Validar fila para incremental (blindaje contra basura)
def validar_fila_incremental(fila_dict, feature_names):
    close_sanitized = False
    close_valid_count = 0
    # Asegura numericidad real
    for k in feature_names:
        v = fila_dict.get(k, None)
        if str(k).startswith("close_"):
            try:
                if v is None or (isinstance(v, str) and v.strip() == ""):
                    raise ValueError("close_missing")
                vf = float(v)
                if (not np.isfinite(vf)) or vf <= 0.0:
                    raise ValueError("close_invalid")
                fila_dict[k] = float(vf)
                close_valid_count += 1
                continue
            except Exception:
                fila_dict[k] = 0.0
                close_sanitized = True
                continue
        try:
            v = float(v)
            if not np.isfinite(v):
                return False, f"{k}=NaN/inf"
        except Exception:
            return False, f"{k}=no numérico"
        fila_dict[k] = v  # normaliza en sitio

    # Rangos lógicos por contrato activo (v2 + compat legacy opcional)
    ranges = {
        "rsi_9": (0, 100), "rsi_14": (0, 100),
        "payout": (0, 1.5), "volatilidad": (0, 1), "es_rebote": (0, 1), "hora_bucket": (0, 1),
        "ret_1m": (-1, 1), "ret_3m": (-1, 1), "ret_5m": (-1, 1),
        "slope_5m": (-1, 1), "rv_20": (0, 1), "range_norm": (0, 1),
        "bb_z": (-3, 3), "body_ratio": (0, 1), "wick_imbalance": (-1, 1), "micro_trend_persist": (-1, 1),
    }
    for k in feature_names:
        if k in ranges:
            lo, hi = ranges[k]
            v = float(fila_dict.get(k, 0.0) or 0.0)
            if not (lo <= v <= hi):
                return False, f"{k} fuera de rango [{lo},{hi}]"

    # Cuarentena conservadora: filas sospechosas que contaminan entrenamiento
    try:
        vals = [float(fila_dict.get(k, 0.0) or 0.0) for k in feature_names]
        nz = sum(1 for v in vals if abs(v) > 1e-12)
        if len(vals) >= 8 and nz <= 2:
            return False, "fila_sospechosa: casi_todo_cero"
        if sum(1 for v in vals if not np.isfinite(v)) > 0:
            return False, "fila_sospechosa: no_finito"
    except Exception:
        return False, "fila_sospechosa: parse"

    close_snapshot_issue = bool(close_sanitized or close_valid_count < 20)
    core_scalping_ready = _core_scalping_ready_from_row(fila_dict)
    if close_snapshot_issue and (not core_scalping_ready):
        fila_dict["row_has_proxy_features"] = 1
        fila_dict["row_train_eligible"] = 0

    return True, ""
        
def _anexar_incremental_desde_bot_CANON(bot: str, fila_dict_or_full: dict, label: int | None = None, feature_names: list | None = None) -> bool:
    """
    Anexa 1 fila al dataset_incremental.csv de forma estable:
    - Header canónico (anti "mutante")
    - Lock dedicado (incremental.lock) para evitar choques
    - Repair del CSV SOLO bajo lock (evita corrupción por concurrencia)
    - Retry ante PermissionError (Excel/OneDrive/AV)
    - Anti-duplicado por firma persistente (_sigcache por bot)
    """
    try:
        def _ingest_bump(key: str, delta: int = 1):
            try:
                stats = globals().get("_INCREMENTAL_INGEST_STATS", {})
                stats[key] = int(stats.get(key, 0) or 0) + int(delta)
                now_ts = time.time()
                if (now_ts - float(stats.get("last_log_ts", 0.0) or 0.0)) >= 15.0:
                    txt = (
                        "🧾 incremental-ingest: filas_incremental_aceptadas={a} "
                        "filas_incremental_saneadas_close={s} filas_incremental_proxy_no_train={p} "
                        "filas_incremental_descartadas_total={d} filas_incremental_close_reales_validas={r}"
                    ).format(
                        a=int(stats.get("filas_incremental_aceptadas", 0) or 0),
                        s=int(stats.get("filas_incremental_saneadas_close", 0) or 0),
                        p=int(stats.get("filas_incremental_proxy_no_train", 0) or 0),
                        d=int(stats.get("filas_incremental_descartadas_total", 0) or 0),
                        r=int(stats.get("filas_incremental_close_reales_validas", 0) or 0),
                    )
                    try:
                        agregar_evento(txt)
                    except Exception:
                        print(txt)
                    stats["last_log_ts"] = now_ts
            except Exception:
                pass

        ruta = "dataset_incremental.csv"
        feats = feature_names or INCREMENTAL_FEATURES_V2
        cols = _canonical_incremental_cols(feats)
        if "ts_ingest" not in cols:
            cols = list(cols[:-1]) + ["ts_ingest", cols[-1]]

        if not isinstance(fila_dict_or_full, dict) or not fila_dict_or_full:
            _ingest_bump("filas_incremental_descartadas_total", 1)
            return False

        # Normalizar/enriquecer fila para contrato CORE13_v2 (con fallback legacy).
        fila_dict_or_full = _enriquecer_scalping_features_row(fila_dict_or_full)

        # Label: aceptar parámetro o leer del dict
        if label is None:
            lb = fila_dict_or_full.get("result_bin", None)
            try:
                label = int(float(lb))
            except Exception:
                _ingest_bump("filas_incremental_descartadas_total", 1)
                return False

        try:
            label = int(label)
        except Exception:
            _ingest_bump("filas_incremental_descartadas_total", 1)
            return False
        if label not in (0, 1):
            _ingest_bump("filas_incremental_descartadas_total", 1)
            return False

        # Dict solo con features canónicas + metadatos de elegibilidad
        fila_dict = {k: fila_dict_or_full.get(k, None) for k in feats}
        try:
            row_has_proxy = int(float(fila_dict_or_full.get("row_has_proxy_features", 0) or 0))
        except Exception:
            row_has_proxy = 0
        try:
            row_train_eligible = int(float(fila_dict_or_full.get("row_train_eligible", 1) or 1))
        except Exception:
            row_train_eligible = 1
        if row_has_proxy == 1 and (not _core_scalping_ready_from_row(fila_dict_or_full)) and _close_snapshot_issue_from_row(fila_dict_or_full):
            row_train_eligible = 0
        ts_ing = fila_dict_or_full.get("ts_ingest", None)
        if ts_ing is None:
            try:
                ts_ing = float(time.time())
            except Exception:
                ts_ing = ""

        # Validación fuerte
        ok, why = validar_fila_incremental(fila_dict, feats)
        if not ok:
            fn_evt = globals().get("agregar_evento", None)
            try:
                if callable(fn_evt):
                    fn_evt(f"⚠️ Incremental: fila descartada {bot}: {why}")
            except Exception:
                pass
            _ingest_bump("filas_incremental_descartadas_total", 1)
            return False
        try:
            row_has_proxy = int(max(row_has_proxy, int(float(fila_dict.get("row_has_proxy_features", 0) or 0))))
        except Exception:
            pass
        try:
            row_train_eligible = int(min(row_train_eligible, int(float(fila_dict.get("row_train_eligible", 1) or 1))))
        except Exception:
            pass
        if row_has_proxy == 1 and (not _core_scalping_ready_from_row(fila_dict)) and _close_snapshot_issue_from_row(fila_dict):
            row_train_eligible = 0

        row_vals = [float(fila_dict[k]) for k in feats]
        row_all = list(row_vals) + [int(row_has_proxy), int(row_train_eligible)]
        sig = _firma_registro(feats, row_vals, label)

        # Anti-duplicado persistente (cache local + escaneo incremental reciente)
        if _sig_in_cache(bot, sig, max_keep=50):
            return False
        if _incremental_signature_exists(ruta, sig, feats):
            return False

        attempts = 8
        base_sleep = 0.08

        with file_lock_required("incremental.lock", timeout=6.0, stale_after=30.0) as got:
            if not got:
                fn_evt = globals().get("agregar_evento", None)
                try:
                    if callable(fn_evt):
                        fn_evt("⚠️ Incremental: no se pudo adquirir lock (incremental.lock). Fila omitida para evitar corrupción.")
                except Exception:
                    pass
                return False

            # ✅ Bajo lock: asegurar existencia + header estable + repair si hace falta
            if os.path.exists(ruta):
                try:
                    with open(ruta, "r", encoding="utf-8", errors="replace", newline="") as f:
                        first = f.readline().strip()
                    header_now = [h.strip() for h in first.split(",")] if first else []
                    if header_now != cols:
                        reparar_dataset_incremental_mutante(ruta=ruta, cols=cols)
                except Exception:
                    try:
                        reparar_dataset_incremental_mutante(ruta=ruta, cols=cols)
                    except Exception:
                        pass
            else:
                try:
                    with open(ruta, "w", newline="", encoding="utf-8") as f:
                        w = csv.writer(f)
                        w.writerow(cols)
                        f.flush()
                        os.fsync(f.fileno())
                except Exception:
                    _ingest_bump("filas_incremental_descartadas_total", 1)
                    return False

            # Append con retry
            for n in range(attempts):
                try:
                    with open(ruta, "a", newline="", encoding="utf-8") as f:
                        w = csv.writer(f)
                        w.writerow(row_all + [ts_ing, label])
                        f.flush()
                        os.fsync(f.fileno())

                    _save_last_sig(bot, sig)
                    try:
                        _INCREMENTAL_SIG_CACHE.setdefault("sigs", set()).add(sig)
                        _INCREMENTAL_SIG_CACHE["mtime"] = float(os.path.getmtime(ruta) or 0.0)
                    except Exception:
                        pass
                    _ingest_bump("filas_incremental_aceptadas", 1)
                    if int(row_has_proxy) == 1 or int(row_train_eligible) == 0:
                        _ingest_bump("filas_incremental_proxy_no_train", 1)
                    try:
                        close_real_valid = all(float(fila_dict.get(f"close_{i}", 0.0) or 0.0) > 0.0 for i in range(20))
                    except Exception:
                        close_real_valid = False
                    if close_real_valid:
                        _ingest_bump("filas_incremental_close_reales_validas", 1)
                    else:
                        _ingest_bump("filas_incremental_saneadas_close", 1)
                    return True

                except PermissionError:
                    time.sleep(base_sleep * (n + 1) + random.uniform(0, 0.07))
                    continue
                except Exception:
                    break

        _ingest_bump("filas_incremental_descartadas_total", 1)
        return False

    except Exception:
        try:
            globals().get("_INCREMENTAL_INGEST_STATS", {})["filas_incremental_descartadas_total"] = int(
                globals().get("_INCREMENTAL_INGEST_STATS", {}).get("filas_incremental_descartadas_total", 0) or 0
            ) + 1
        except Exception:
            pass
        return False
        
# === Canonización: aunque existan duplicados en el archivo, esta es la versión oficial ===
anexar_incremental_desde_bot = _anexar_incremental_desde_bot_CANON
       
# === FIN BLOQUE 6 ===

# === BLOQUE 7 — ORDEN DE REAL Y CONTROL DE TOKEN ===
# === ORDEN DE REAL (handshake maestro→bot) ===
ORDEN_DIR = "orden_real"

def _ensure_dir(p):
    try:
        os.makedirs(p, exist_ok=True)
    except Exception as e:
        print(f"⚠️ Falló creación de dir {p}: {e}")

def _atomic_write(path: str, text: str):
    _ensure_dir(os.path.dirname(path) or ".")
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
        f.flush(); os.fsync(f.fileno())
    os.replace(tmp, path)

def path_orden(bot: str) -> str:
    _ensure_dir(ORDEN_DIR)
    return os.path.join(ORDEN_DIR, f"{bot}.json")


def leer_pause_state_maestro() -> dict:
    base = {
        "paused": False,
        "reason": "",
        "started_ts": 0.0,
        "resume_ts": 0.0,
        "duration_sec": 0,
        "source": "",
        "reference_balance": None,
        "trigger_balance": None,
    }
    path = MAESTRO_PAUSE_FILE
    if (not path) or (not os.path.exists(path)):
        return base
    try:
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            raw = f.read().strip()
        if not raw:
            return base
        data = json.loads(raw)
        if not isinstance(data, dict):
            return base
        out = dict(base)
        out.update(data)
        return out
    except Exception:
        return base


def tiempo_restante_pausa_maestro() -> int:
    try:
        if not maestro_pause_active:
            return 0
        return max(0, int(round(float(maestro_pause_resume_ts or 0.0) - time.time())))
    except Exception:
        return 0


def motivo_pausa_maestro() -> str:
    try:
        reason = str(maestro_pause_reason or "drawdown_20_monitor").strip()
        if reason == "drawdown_20_monitor":
            return "Protección por drawdown 20% activada desde monitor"
        if reason == "manual_resume":
            return "Pausa liberada manualmente desde monitor"
        return reason
    except Exception:
        return "Pausa externa"


def maestro_en_pausa() -> bool:
    try:
        return bool(maestro_pause_active)
    except Exception:
        return False


def _maybe_log_pause_state(force: bool = False):
    global maestro_pause_last_log_ts
    now = time.time()
    if (not force) and ((now - float(maestro_pause_last_log_ts or 0.0)) < 7.0):
        return
    maestro_pause_last_log_ts = now
    if maestro_pause_active:
        remain = tiempo_restante_pausa_maestro()
        mm, ss = divmod(max(0, int(remain)), 60)
        ref_txt = f"{float(maestro_pause_ref_balance):,.2f}" if isinstance(maestro_pause_ref_balance, (int, float)) else "--"
        trg_txt = f"{float(maestro_pause_trigger_balance):,.2f}" if isinstance(maestro_pause_trigger_balance, (int, float)) else "--"
        print(
            f"⛔ MAESTRO EN PAUSA | {mm:02d}:{ss:02d} | reason={maestro_pause_reason or 'drawdown_20_monitor'} "
            f"| ref={ref_txt} | trigger={trg_txt}"
        )


def actualizar_pause_state_maestro():
    global maestro_pause_active, maestro_pause_reason, maestro_pause_resume_ts, maestro_pause_started_ts
    global maestro_pause_last_read_ts, maestro_pause_ref_balance, maestro_pause_trigger_balance, maestro_pause_source
    global maestro_pause_last_state
    now = time.time()
    if (now - float(maestro_pause_last_read_ts or 0.0)) < 0.35:
        return
    maestro_pause_last_read_ts = now

    def _as_float(v):
        try:
            if v is None:
                return None
            return float(v)
        except Exception:
            return None

    data = leer_pause_state_maestro()
    paused_flag = bool(data.get("paused", False))
    resume_ts = float(data.get("resume_ts") or 0.0)
    started_ts = float(data.get("started_ts") or 0.0)
    reason = str(data.get("reason") or "")
    source = str(data.get("source") or "")
    ref_bal = _as_float(data.get("reference_balance"))
    trg_bal = _as_float(data.get("trigger_balance"))

    active_now = bool(paused_flag and resume_ts > now)
    just_changed = (active_now != bool(maestro_pause_last_state))

    if active_now:
        maestro_pause_active = True
        maestro_pause_resume_ts = resume_ts
        maestro_pause_started_ts = started_ts
        maestro_pause_reason = reason or "drawdown_20_monitor"
        maestro_pause_source = source
        maestro_pause_ref_balance = ref_bal
        maestro_pause_trigger_balance = trg_bal
        if just_changed:
            agregar_evento("⛔ MAESTRO EN PAUSA · Protección por drawdown 20% activada desde monitor.")
            _maybe_log_pause_state(force=True)
    else:
        maestro_pause_active = False
        maestro_pause_resume_ts = resume_ts
        maestro_pause_started_ts = started_ts
        if just_changed:
            if reason == "manual_resume":
                agregar_evento("✅ Pausa liberada manualmente desde monitor.")
                print("✅ Pausa liberada manualmente desde monitor")
            else:
                agregar_evento("✅ Pausa finalizada por tiempo.")
                print("✅ Pausa finalizada por tiempo")
        maestro_pause_reason = reason or ""
        maestro_pause_source = source
        maestro_pause_ref_balance = ref_bal
        maestro_pause_trigger_balance = trg_bal

    maestro_pause_last_state = bool(maestro_pause_active)

# === SALDO LIVE FEED (maestro -> monitor_saldo_pro) ===
SALDO_LIVE_FILE = "saldo_real_live.json"
SALDO_LIVE_HISTORY_FILE = "saldo_real_live_history.jsonl"
SALDO_SERIES_CSV_FILE = "saldo_real_series.csv"
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
_DEFAULT_SALDO_LIVE_PATH = os.path.join(os.path.expanduser("~"), SALDO_LIVE_FILE)
SALDO_LIVE_SHARED_PATH = os.path.abspath(
    os.path.expanduser(os.getenv("SALDO_LIVE_SHARED_PATH", _DEFAULT_SALDO_LIVE_PATH))
)
_DEFAULT_SALDO_HISTORY_PATH = os.path.join(os.path.dirname(SALDO_LIVE_SHARED_PATH), SALDO_LIVE_HISTORY_FILE)
SALDO_LIVE_HISTORY_SHARED_PATH = os.path.abspath(
    os.path.expanduser(os.getenv("SALDO_LIVE_HISTORY_SHARED_PATH", _DEFAULT_SALDO_HISTORY_PATH))
)
SALDO_SERIES_CSV_PATH = os.path.abspath(
    os.path.expanduser(os.getenv("SALDO_SERIES_CSV_PATH", os.path.join(SCRIPT_DIR, SALDO_SERIES_CSV_FILE)))
)

def _saldo_feed_targets() -> dict:
    return {
        "live": [SALDO_LIVE_SHARED_PATH],
        "history": [SALDO_LIVE_HISTORY_SHARED_PATH],
        "series": [SALDO_SERIES_CSV_PATH],
    }

def _append_line_safe(path: str, line: str):
    try:
        _ensure_dir(os.path.dirname(path) or ".")
    except Exception:
        pass
    tmp_lock = f"{os.path.basename(path)}.lock"
    with file_lock_required(tmp_lock, timeout=2.0, stale_after=20.0) as got:
        if not got:
            return
        with open(path, "a", encoding="utf-8") as f:
            f.write(line)
            f.flush()
            os.fsync(f.fileno())

def _read_last_nonempty_line(path: str) -> str:
    try:
        if (not os.path.exists(path)) or os.path.getsize(path) <= 0:
            return ""
        with open(path, "rb") as fh:
            fh.seek(0, os.SEEK_END)
            size = fh.tell()
            start = max(0, size - 8192)
            fh.seek(start, os.SEEK_SET)
            chunk = fh.read().decode("utf-8", errors="ignore")
        lines = [ln.strip() for ln in chunk.splitlines() if ln.strip()]
        return lines[-1] if lines else ""
    except Exception:
        return ""

def _ensure_series_header_if_needed(path: str):
    try:
        _ensure_dir(os.path.dirname(path) or ".")
        if (not os.path.exists(path)) or os.path.getsize(path) <= 0:
            _append_line_safe(path, "timestamp,equity,source\n")
            return
        with open(path, "r", encoding="utf-8", errors="ignore") as fh:
            first = (fh.readline() or "").strip().lower()
        if ("timestamp" not in first) or ("equity" not in first):
            bak = f"{path}.bak"
            try:
                os.replace(path, bak)
            except Exception:
                pass
            _append_line_safe(path, "timestamp,equity,source\n")
            if os.path.exists(bak):
                try:
                    with open(bak, "r", encoding="utf-8", errors="ignore") as bf:
                        for raw in bf:
                            row = raw.strip()
                            if not row:
                                continue
                            cols = [c.strip() for c in row.split(",")]
                            if len(cols) < 2 or cols[0].lower() in ("timestamp", "ts_utc"):
                                continue
                            _append_line_safe(path, f"{cols[0]},{cols[1]},{(cols[2] if len(cols) >= 3 else 'MAESTRO_5R6M')}\n")
                except Exception:
                    pass
    except Exception:
        pass

def _append_series_csv_if_new(path: str, ts_iso: str, val: float, source: str):
    try:
        _ensure_series_header_if_needed(path)
        line = f"{ts_iso},{float(val):.2f},{source}\n"
        last = _read_last_nonempty_line(path)
        if last and (last == line.strip()):
            return
        _append_line_safe(path, line)
    except Exception:
        pass

def _update_saldo_monitor_feed(valor_saldo: float):
    try:
        val = float(valor_saldo)
        now = float(time.time())
        ts_iso = datetime.now(timezone.utc).isoformat()
        payload_live = {
            "saldo_real": val,
            "equity": val,
            "balance": val,
            "timestamp": ts_iso,
            "ts": now,
            "source": "MAESTRO_5R6M",
        }
        payload_hist = {
            "timestamp": ts_iso,
            "equity": val,
            "saldo_real": val,
            "balance": val,
            "source": "MAESTRO_5R6M",
        }
        for p in dict.fromkeys(_saldo_feed_targets()["live"]):
            _atomic_write(p, json.dumps(payload_live, ensure_ascii=False))
        for p in dict.fromkeys(_saldo_feed_targets()["history"]):
            _append_line_safe(p, json.dumps(payload_hist, ensure_ascii=False) + "\n")
        for p in dict.fromkeys(_saldo_feed_targets()["series"]):
            _append_series_csv_if_new(p, ts_iso, val, "MAESTRO_5R6M")
        print(f"[SALDO LIVE] destino: {SALDO_LIVE_SHARED_PATH}")
        print(f"[SALDO HIST] destino: {SALDO_LIVE_HISTORY_SHARED_PATH}")
        print(f"[SALDO CSV] destino: {SALDO_SERIES_CSV_PATH}")
        print(f"[SALDO FEED][OK] saldo={val:.2f} ts={ts_iso}")
        return True
    except Exception as e:
        print(f"[SALDO FEED][ERROR] {e}")
        return False
# === /SALDO LIVE FEED ===

# === LXV_SYNC_COLUMN: sincronización de ronda/columna maestro↔bots ===
SYNC_ROUND_DIR = "sync_round"
SYNC_ROUND_STATE_PATH = os.path.join(SYNC_ROUND_DIR, "state.json")
TTL_ACK_SYNC_ROUND_S = 300.0
ACK_SYNC_ROUND_FUTURE_DRIFT_S = 20.0
LXV_SYNC_ROUND_FAILSAFE_ENABLE = True
LXV_SYNC_ROUND_MAX_WAIT_S = 240.0
LXV_SYNC_BOT_STALE_S = 120.0
LXV_SYNC_PENDING_MAX_WAIT_S = 240.0
LXV_SYNC_MIN_CLOSED_FOR_EVAL = 4
_SYNC_ROUND_LAST_ANNOUNCED = None
_SYNC_ROUND_LAST_CLOSED_COUNT = {}
_LXV_LAST_EMITTED_ROUND = 0
_SYNC_PENDING_WARN_TS = {}
_SYNC_STALE_WARN_TS = {}

def _sync_round_ack_path(bot: str) -> str:
    _ensure_dir(SYNC_ROUND_DIR)
    return os.path.join(SYNC_ROUND_DIR, f"{bot}.json")

def _sync_round_safe_read_json(path: str):
    try:
        if not os.path.exists(path):
            return None
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else None
    except Exception:
        return None

def _sync_round_write_json_atomic(path: str, payload: dict) -> bool:
    try:
        _atomic_write(path, json.dumps(payload, ensure_ascii=False, indent=2))
        return True
    except Exception:
        return False

def _sync_round_bootstrap_state(force: bool = False):
    _ensure_dir(SYNC_ROUND_DIR)
    if (not force) and os.path.exists(SYNC_ROUND_STATE_PATH):
        return
    payload = {
        "round_id": 1,
        "released_round": 1,
        "expected_bots": list(BOT_NAMES),
        "closed_bots": {},
        "completed": False,
        "status": "running",
        "reason": "boot",
        "started_at": time.time(),
        "ts": time.time(),
    }
    _sync_round_write_json_atomic(SYNC_ROUND_STATE_PATH, payload)

def _sync_round_apply_visual_heartbeat(bot: str) -> None:
    """
    Mantiene señal visual de vida/standby sin releer CSV completo.
    """
    try:
        if bot not in BOT_NAMES:
            return
        st = estado_bots.get(bot, {})
        if not isinstance(st, dict):
            return
        ack = _sync_round_safe_read_json(_sync_round_ack_path(bot)) or {}
        gstate = _sync_round_safe_read_json(SYNC_ROUND_STATE_PATH) or {}
        round_id = int(gstate.get("round_id", 1) or 1)
        released = int(gstate.get("released_round", 1) or 1)
        wait_flag = bool(ack.get("sync_wait", False))
        wait_round = int(ack.get("round_id", 0) or 0)
        waiting_release = int(ack.get("waiting_release_round", wait_round + 1) or (wait_round + 1))
        active_wait = bool(wait_flag and wait_round == round_id and released < waiting_release)
        st["sync_wait"] = active_wait
        st["last_sync_round"] = wait_round if wait_round > 0 else round_id
        st["last_seen_ts"] = float(ack.get("last_seen_ts", time.time()) or time.time())
        st["estado_visual"] = "STANDBY_RONDA" if active_wait else st.get("estado_visual", "ACTIVO")
        # Alias visuales para evitar incompatibilidades de nombres en HUD/diagnóstico
        st["sync_round_id"] = int(wait_round if wait_round > 0 else round_id)
        st["sync_released_round"] = int(released)
        st["sync_last_seen_ts"] = float(st.get("last_seen_ts", time.time()) or time.time())
        st["sync_estado_visual"] = str(st.get("estado_visual", "ACTIVO"))
        if active_wait:
            last_update_time[bot] = time.time()
    except Exception:
        pass

def _lxv_round_snapshot(round_id: int, closed: dict) -> list[dict]:
    out = []
    for bot in BOT_NAMES:
        c = closed.get(bot)
        if not isinstance(c, dict):
            continue
        st = estado_bots.get(bot, {})
        out.append({
            "bot": bot,
            "round_id": int(round_id),
            "resultado": str(c.get("resultado", "")).upper().strip(),
            "ciclo": int(c.get("ciclo", st.get("ciclo_actual", 1)) or 1),
            "asset": c.get("asset"),
            "ts": float(c.get("ts", 0.0) or 0.0),
            "prob_ia_oper": st.get("prob_ia_oper"),
            "prob_ia": st.get("prob_ia"),
            "score_senal": st.get("ia_score_hibrido", st.get("ia_regime_score")),
            "payout": c.get("payout"),
            "winrate": st.get("porcentaje_exito"),
        })
    return out

def _lxv_rank_key(item: dict) -> tuple:
    def _num(v, default=-1e9):
        try:
            return float(v)
        except Exception:
            return float(default)
    bot = str(item.get("bot", ""))
    order_idx = BOT_NAMES.index(bot) if bot in BOT_NAMES else 999
    return (
        _num(item.get("prob_ia_oper"), -1e9),
        _num(item.get("prob_ia"), -1e9),
        _num(item.get("score_senal"), -1e9),
        _num(item.get("payout"), -1e9),
        _num(item.get("winrate"), -1e9),
        _num(item.get("ts"), -1e9),
        -float(order_idx),
    )

def _lxv_evaluar_columna(round_id: int, snapshot: list[dict]) -> tuple[dict | None, str, str]:
    verdes = [x for x in snapshot if x.get("resultado") == "GANANCIA"]
    rojos = [x for x in snapshot if x.get("resultado") == "PÉRDIDA"]
    patron = f"{len(verdes)}V/{len(rojos)}X"
    if len(verdes) == 5 and len(rojos) == 1:
        pick = dict(rojos[0])
        motivo = "5 verdes / 1 X (X única)"
        return pick, patron, motivo
    if len(verdes) == 4 and len(rojos) == 2:
        ranked = sorted(rojos, key=_lxv_rank_key, reverse=True)
        pick = dict(ranked[0]) if ranked else None
        motivo = "4 verdes / 2 X (mayor peso: prob_ia_oper > prob_ia > score > payout > winrate > ts > BOT_NAMES)"
        return pick, patron, motivo
    return None, patron, "patrón no válido para LXV_REAL"

def _sync_round_tick_maestro():
    global _SYNC_ROUND_LAST_ANNOUNCED, _LXV_LAST_EMITTED_ROUND
    _sync_round_bootstrap_state(force=False)
    st = _sync_round_safe_read_json(SYNC_ROUND_STATE_PATH) or {}

    try:
        round_id = max(1, int(st.get("round_id", 1) or 1))
    except Exception:
        round_id = 1
    try:
        released_round = max(1, int(st.get("released_round", round_id) or round_id))
    except Exception:
        released_round = round_id
    try:
        started_at = float(st.get("started_at", 0.0) or 0.0)
    except Exception:
        started_at = 0.0
    if started_at <= 0.0:
        started_at = float(time.time())

    expected = st.get("expected_bots")
    if not isinstance(expected, list) or not expected:
        expected = list(BOT_NAMES)
    expected = [b for b in expected if b in BOT_NAMES]
    if not expected:
        expected = list(BOT_NAMES)

    if _SYNC_ROUND_LAST_ANNOUNCED != round_id:
        agregar_evento(f"🧭 LXV_SYNC_COLUMN ronda #{round_id} iniciada ({len(expected)} bots esperados).")
        _SYNC_ROUND_LAST_ANNOUNCED = round_id

    closed = {}
    now_ts = float(time.time())
    for bot in expected:
        ack = _sync_round_safe_read_json(_sync_round_ack_path(bot))
        if not isinstance(ack, dict):
            continue
        st_bot = estado_bots.get(bot, {}) if isinstance(estado_bots.get(bot, {}), dict) else {}
        pending_flag = bool(st_bot.get("pending_contract_resolution", False) or ack.get("pending_contract_resolution", False))
        if pending_flag:
            now_p = float(time.time())
            last_p = float(_SYNC_PENDING_WARN_TS.get(bot, 0.0) or 0.0)
            if (now_p - last_p) >= 20.0:
                _SYNC_PENDING_WARN_TS[bot] = now_p
                agregar_evento(f"⏳ LXV_SYNC_COLUMN: {bot} pendiente por contrato incierto; no cuenta como cierre.")
            continue
        try:
            ack_round = int(ack.get("round_id", 0) or 0)
        except Exception:
            continue
        if ack_round != round_id:
            continue
        if str(ack.get("status", "")).lower().strip() != "closed":
            continue
        try:
            ack_ts = float(ack.get("ts", 0.0) or 0.0)
        except Exception:
            continue
        if ack_ts <= 0:
            continue
        if (now_ts - ack_ts) > float(TTL_ACK_SYNC_ROUND_S):
            last_s = float(_SYNC_STALE_WARN_TS.get(bot, 0.0) or 0.0)
            if (now_ts - last_s) >= 20.0:
                _SYNC_STALE_WARN_TS[bot] = now_ts
                agregar_evento(f"🧹 LXV_SYNC_COLUMN: ACK stale ignorado para {bot}.")
            continue
        if ack_ts > (now_ts + float(ACK_SYNC_ROUND_FUTURE_DRIFT_S)):
            last_s = float(_SYNC_STALE_WARN_TS.get(bot, 0.0) or 0.0)
            if (now_ts - last_s) >= 20.0:
                _SYNC_STALE_WARN_TS[bot] = now_ts
                agregar_evento(f"🧹 LXV_SYNC_COLUMN: ACK con timestamp futuro ignorado para {bot}.")
            continue
        res = str(ack.get("resultado", "")).upper().strip()
        if res not in ("GANANCIA", "PÉRDIDA"):
            continue
        closed[bot] = {
            "resultado": res,
            "ts": float(ack.get("ts", 0.0) or 0.0),
            "contract_id": ack.get("contract_id"),
            "asset": ack.get("asset"),
            "ciclo": ack.get("ciclo"),
        }

    n_closed = len(closed)
    missing = [b for b in expected if b not in closed]
    now_ts = float(time.time())
    wait_s = max(0.0, now_ts - float(started_at))
    stale_ignored = []
    if bool(LXV_SYNC_ROUND_FAILSAFE_ENABLE) and missing:
        for bot in missing:
            ack_bot = _sync_round_safe_read_json(_sync_round_ack_path(bot)) or {}
            st_bot = estado_bots.get(bot, {}) if isinstance(estado_bots.get(bot, {}), dict) else {}
            last_seen = float(ack_bot.get("last_seen_ts", st_bot.get("sync_last_seen_ts", st_bot.get("last_seen_ts", 0.0))) or 0.0)
            ack_ts_any = float(ack_bot.get("ts", 0.0) or 0.0)
            pending = bool(st_bot.get("pending_contract_resolution", False) or ack_bot.get("pending_contract_resolution", False))
            pending_since = float(st_bot.get("pending_since_ts", 0.0) or 0.0)
            pending_old = bool(pending and pending_since > 0 and (now_ts - pending_since) >= float(LXV_SYNC_PENDING_MAX_WAIT_S))
            stale_seen = bool(last_seen > 0 and (now_ts - last_seen) >= float(LXV_SYNC_BOT_STALE_S))
            stale_ack = bool(ack_ts_any > 0 and (now_ts - ack_ts_any) >= float(TTL_ACK_SYNC_ROUND_S))
            timed_out = bool(wait_s >= float(LXV_SYNC_ROUND_MAX_WAIT_S))
            if stale_seen or stale_ack or pending_old or timed_out:
                stale_ignored.append(bot)

    effective_expected = [b for b in expected if b not in stale_ignored] if stale_ignored else list(expected)
    effective_need = max(1, len(effective_expected))
    prev_n = int(_SYNC_ROUND_LAST_CLOSED_COUNT.get(round_id, -1))
    if n_closed != prev_n:
        _SYNC_ROUND_LAST_CLOSED_COUNT[round_id] = n_closed
        agregar_evento(f"🧩 LXV_SYNC_COLUMN cierres ronda #{round_id}: {n_closed}/{len(expected)}.")

    completed_normal = bool(n_closed >= len(expected))
    completed_failsafe = bool(stale_ignored and n_closed >= effective_need)
    completed = bool(completed_normal or completed_failsafe)
    next_round = round_id + 1 if completed else round_id
    next_released = max(released_round, next_round if completed else released_round)

    payload = {
        "round_id": next_round if completed else round_id,
        "released_round": next_released,
        "expected_bots": expected,
        "expected_bots_effective": effective_expected,
        "closed_bots": closed,
        "completed": completed,
        "status": "released_failsafe" if completed_failsafe else ("released" if completed else "waiting_closures"),
        "reason": "failsafe_stale_or_timeout" if completed_failsafe else ("all_bots_closed" if completed else "waiting_bots"),
        "bots_missing": missing,
        "bots_stale_ignored": stale_ignored,
        "round_wait_s": float(wait_s),
        "started_at": float(time.time()) if completed else float(started_at),
        "ts": time.time(),
    }
    _sync_round_write_json_atomic(SYNC_ROUND_STATE_PATH, payload)

    if completed:
        if completed_failsafe and stale_ignored:
            agregar_evento(f"🟠 LXV_SYNC_COLUMN failsafe: liberando ronda #{round_id} sin {stale_ignored} por stale/timeout.")
        agregar_evento(f"✅ LXV_SYNC_COLUMN columna/ronda #{round_id} COMPLETA.")
        agregar_evento(f"🚀 LXV_SYNC_COLUMN ronda #{next_round} LIBERADA.")
        snapshot = _lxv_round_snapshot(round_id, closed)
        if len(snapshot) < int(LXV_SYNC_MIN_CLOSED_FOR_EVAL):
            pick, patron, motivo = None, f"{len([x for x in snapshot if x.get('resultado') == 'GANANCIA'])}V/{len([x for x in snapshot if x.get('resultado') == 'PÉRDIDA'])}X", "masa mínima insuficiente para evaluar LXV_REAL"
        else:
            pick, patron, motivo = _lxv_evaluar_columna(round_id, snapshot)
        if pick:
            bot_pick = str(pick.get("bot"))

            # Solo diagnóstico: ciclo que venía en el snapshot de la columna
            ciclo_snapshot = int(
                pick.get("ciclo", estado_bots.get(bot_pick, {}).get("ciclo_actual", 1)) or 1
            )

            # Fuente canónica real del ciclo de martingala
            ciclo_pick = ciclo_martingala_siguiente()

            # Blindaje por saldo, igual que en otras rutas REAL
            saldo_val = obtener_valor_saldo()
            if reset_martingala_por_saldo(ciclo_pick, saldo_val):
                ciclo_pick = 1

            agregar_evento(
                f"🧠 LXV columna #{round_id}: {patron} → candidato REAL {bot_pick} ({motivo}) "
                f"| snapshot=C{ciclo_snapshot} | global=C{ciclo_pick}"
            )

            if int(_LXV_LAST_EMITTED_ROUND or 0) != int(round_id):
                ok_emit = emitir_real_autorizado(bot_pick, ciclo_pick, source=LXV_SYNC_REAL_SOURCE)
                _LXV_LAST_EMITTED_ROUND = int(round_id) if ok_emit else int(_LXV_LAST_EMITTED_ROUND or 0)
                if ok_emit:
                    try:
                        estado_bots[bot_pick]["ciclo_actual"] = int(ciclo_pick)
                    except Exception:
                        pass
                    agregar_evento(
                        f"🚨 LXV_SYNC REAL emitido: ronda #{round_id} -> {bot_pick} ciclo_global C{ciclo_pick}."
                    )
                else:
                    agregar_evento(
                        f"⚠️ LXV_SYNC REAL no emitido en ronda #{round_id} (lock/purificación/estado)."
                    )
        else:
            agregar_evento(f"ℹ️ LXV columna #{round_id}: {patron} → {motivo}.")
        # Higiene mínima: baja "sync_wait" en bots ya contabilizados
        for bot in closed.keys():
            try:
                ack_path = _sync_round_ack_path(bot)
                ack_cur = _sync_round_safe_read_json(ack_path) or {}
                if isinstance(ack_cur, dict):
                    ack_cur["sync_wait"] = False
                    ack_cur["last_seen_ts"] = time.time()
                    _sync_round_write_json_atomic(ack_path, ack_cur)
            except Exception:
                pass
# === /LXV_SYNC_COLUMN ===

# === PATCH: REAL INMEDIATO EN HUD AL EMITIR ORDEN (sin esperar compra) ===
# Objetivo:
# - Al emitir una ORDEN manual (bot+ciclo), reservar REAL y mostrarlo YA en HUD.
# - Evitar recursión/doble llamada.
# - Si activar_real_inmediato se llama desde otro flujo (no orden_real),
#   asegurar que el bot tenga también su orden_real.json escrita (sin recursión).

_last_real_push_ts = {bot: 0.0 for bot in BOT_NAMES}

def limpiar_orden_real(bot: str):
    """
    Evita re-entradas fantasma:
    si se liberó REAL, la orden ya no debe quedar viva.
    """
    try:
        p = path_orden(bot)
        if os.path.exists(p):
            os.remove(p)
    except Exception:
        pass

def _set_ui_token_holder(holder: str | None):
    """
    Sincroniza UI + estado interno:
    - token (texto REAL/DEMO)
    - trigger_real (lógica)
    Además: si un bot DEJA de ser holder REAL, limpia su estado REAL residual
    para evitar "REAL fantasma" y escudos pegados.
    """
    try:
        if _purificacion_real_activa() and holder in BOT_NAMES:
            _emitir_marca_purificacion_real()
            return
        now = time.time()
        for b in BOT_NAMES:
            # ultra defensivo: si por algo falta el dict del bot, lo crea
            if b not in estado_bots or not isinstance(estado_bots.get(b), dict):
                estado_bots[b] = {}

            is_holder = bool(holder) and (b == holder)
            prev_token = estado_bots[b].get("token", "DEMO")

            # UI base
            estado_bots[b]["token"] = "REAL" if is_holder else "DEMO"
            estado_bots[b]["trigger_real"] = True if is_holder else False

            # Si dejó de ser REAL, limpiar residuos (solo si antes era REAL)
            if (not is_holder) and (prev_token == "REAL"):
                estado_bots[b]["modo_real_anunciado"] = False
                estado_bots[b]["real_activado_en"] = 0.0

                # micro-colchón anti-carreras: evitamos leer cierres viejos justo al soltar token
                estado_bots[b]["ignore_cierres_hasta"] = now + 1.5

                estado_bots[b]["fuente"] = None

                # IA / pending
                estado_bots[b]["ia_senal_pendiente"] = False
                estado_bots[b]["ia_prob_senal"] = None

                # Remate
                estado_bots[b]["remate_active"] = False
                estado_bots[b]["remate_start"] = None
                estado_bots[b]["remate_reason"] = ""

                # Ciclo vuelve a default (solo al perder REAL)
                estado_bots[b]["ciclo_actual"] = 1

    except Exception:
        pass

def _enforce_single_real_standby(owner: str | None):
    """
    Si hay owner REAL activo, deja a los demás bots en standby estricto:
    - token DEMO visual
    - sin señal IA pendiente
    """
    try:
        if owner not in BOT_NAMES:
            return
        for b in BOT_NAMES:
            if b == owner:
                continue
            estado_bots[b]["token"] = "DEMO"
            estado_bots[b]["ia_senal_pendiente"] = False
            estado_bots[b]["ia_prob_senal"] = None
    except Exception:
        pass

def _escribir_orden_real_raw(bot: str, ciclo: int):
    """
    Escritura RAW de orden_real (sin activar_real_inmediato, sin recursión).
    """
    ciclo = max(1, min(int(ciclo), MAX_CICLOS))
    payload = {"bot": bot, "ciclo": ciclo, "ts": time.time()}
    try:
        _atomic_write(path_orden(bot), json.dumps(payload, ensure_ascii=False))
        agregar_evento(f"📝 Orden REAL escrita para {bot}: ciclo #{ciclo}")
    except Exception as e:
        try:
            agregar_evento(f"⚠️ Falló escritura de orden para {bot}: {e}")
        except Exception:
            pass

def activar_real_inmediato(bot: str, ciclo: int, origen: str = "orden_real") -> bool:

    """
    Reserva REAL y actualiza HUD de forma INMEDIATA.

    Regla anti “órdenes fantasma”:
    - SOLO si origen == "manual" se auto-escribe orden_real.json aquí.
    - Si la orden viene por escribir_orden_real(...), ese wrapper YA escribe el JSON.
    - Flujos de sync/UI/token jamás deben escribir orden_real.json.
    """
    global LIMPIEZA_PANEL_HASTA, sonido_disparado, marti_paso, REAL_OWNER_LOCK, REAL_ENTRY_BASELINE

    try:
        if _purificacion_real_activa():
            _emitir_marca_purificacion_real()
            return False
        if bot not in BOT_NAMES:
            return False

        now = time.time()

        # 🔒 No permitir reemplazar owner REAL activo por otro bot.
        # Solo se puede activar si no hay owner o si es el mismo bot.
        try:
            owner_lock = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else leer_token_actual()
        except Exception:
            owner_lock = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else None
        if owner_lock in BOT_NAMES and owner_lock != bot:
            try:
                agregar_evento(f"🔒 REAL bloqueado: {owner_lock.upper()} sigue activo. Ignorando intento de {bot.upper()}.")
            except Exception:
                pass
            try:
                if origen == "orden_real":
                    limpiar_orden_real(bot)
            except Exception:
                pass
            return False

        # Anti doble-disparo (tecla rebotona)
        if (now - _last_real_push_ts.get(bot, 0.0)) < 0.25:
            return False
        _last_real_push_ts[bot] = now

        ciclo_obj = max(1, min(int(ciclo), MAX_CICLOS))

        # Baseline REAL: a partir de aquí recién aceptamos cierres para este turno.
        try:
            REAL_ENTRY_BASELINE[bot] = int(contar_filas_csv(bot) or 0)
        except Exception:
            REAL_ENTRY_BASELINE[bot] = 0

        # Idempotencia token_sync: evita re-enganche/spam si ya está el mismo holder/ciclo.
        if origen == "token_sync":
            try:
                owner_now = leer_token_actual()
                cyc_now = int(estado_bots.get(bot, {}).get("ciclo_actual", 1) or 1)
                if owner_now == bot and cyc_now == ciclo_obj:
                    return True
            except Exception:
                pass

        # ✅ Solo “manual” auto-escribe orden_real (la orden explícita)
        if origen == "manual":
            try:
                _escribir_orden_real_raw(bot, ciclo_obj)
            except Exception:
                pass

        prev_holder = None
        try:
            prev_holder = leer_token_actual()  # sincroniza UI
        except Exception:
            prev_holder = None

        # Persistir primero token REAL y confirmar después memoria/UI
        if origen in ("orden_real", "manual", "token_sync"):
            with file_lock_required("real.lock", timeout=6.0, stale_after=30.0) as got:
                if not got:
                    agregar_evento("⚠️ Token REAL no escrito: lock real.lock ocupado. Se evita activar sin exclusión.")
                    try:
                        if origen == "orden_real":
                            limpiar_orden_real(bot)
                    except Exception:
                        pass
                    return False
                ok_write = bool(write_token_atomic(TOKEN_FILE, f"REAL:{bot}"))
                if not ok_write:
                    agregar_evento("⚠️ Token REAL no escrito: fallo de persistencia en token_actual.txt.")
                    try:
                        if origen == "orden_real":
                            limpiar_orden_real(bot)
                    except Exception:
                        pass
                    return False

        # Confirmación en memoria SOLO tras persistencia correcta
        REAL_OWNER_LOCK = bot

        # 2) Estado interno inmediato (HUD)
        _set_ui_token_holder(bot)
        estado_bots[bot]["trigger_real"] = True
        estado_bots[bot]["ciclo_actual"] = ciclo_obj

        # Congelar probabilidad de señal al entrar REAL (si no estaba ya fijada)
        # para evitar divergencia visual/ACK durante toda la operación.
        try:
            if not isinstance(estado_bots[bot].get("ia_prob_senal"), (int, float)):
                p_live = estado_bots[bot].get("prob_ia", None)
                if isinstance(p_live, (int, float)) and 0.0 <= float(p_live) <= 1.0:
                    estado_bots[bot]["ia_prob_senal"] = float(p_live)
        except Exception:
            pass

        # Marcas de “entrada a real”
        first_entry = not bool(estado_bots[bot].get("modo_real_anunciado", False))
        if first_entry or (prev_holder != bot):
            estado_bots[bot]["modo_real_anunciado"] = True
            estado_bots[bot]["real_activado_en"] = now
            estado_bots[bot]["ignore_cierres_hasta"] = now + 15.0
            estado_bots[bot]["real_timeout_first_warn"] = 0.0

            # Snapshot visual/diagnóstico (independiente del baseline REAL)
            try:
                SNAPSHOT_FILAS[bot] = contar_filas_csv(bot)
            except Exception:
                SNAPSHOT_FILAS[bot] = 0

            # Mantener marti_paso global coherente con el ciclo elegido
            try:
                marti_paso = ciclo_obj - 1
            except Exception:
                pass

            try:
                agregar_evento(f"🚨 REAL INMEDIATO ({origen}) → {bot.upper()} | ciclo #{ciclo_obj}")
            except Exception:
                pass

            # Sonido de activación (solo si tu config lo permite)
            try:
                reproducir_evento("racha_detectada", es_demo=False, dentro_gatewin=True)
            except Exception:
                pass

            LIMPIEZA_PANEL_HASTA = 0
            sonido_disparado = False

        # 3) Redibujar panel YA
        try:
            fn_panel = globals().get("mostrar_panel", None)
            if callable(fn_panel):
                fn_panel()
        except Exception:
            pass

        # 4) Standby estricto del resto (evita doble-REAL visual)
        try:
            _enforce_single_real_standby(bot)
        except Exception:
            pass

        return True

    except Exception:
        return False

def escribir_orden_real(bot: str, ciclo: int) -> bool:
    global REAL_OWNER_LOCK
    """
    Wrapper oficial:
    - Escribe orden_real.json (RAW)
    - Activa REAL inmediato en HUD + token file
    """
    ciclo = max(1, min(int(ciclo), MAX_CICLOS))

    actualizar_pause_state_maestro()
    if maestro_en_pausa():
        try:
            remain = tiempo_restante_pausa_maestro()
            mm, ss = divmod(max(0, int(remain)), 60)
            agregar_evento(f"⛔ Entrada bloqueada por pausa monitor ({mm:02d}:{ss:02d}).")
        except Exception:
            pass
        _maybe_log_pause_state(force=False)
        return False

    if _purificacion_real_activa():
        _emitir_marca_purificacion_real()
        return False

    # 🔒 No crear orden si ya hay otro owner REAL activo.
    try:
        owner_lock = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else leer_token_actual()
    except Exception:
        owner_lock = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else None

    if owner_lock in BOT_NAMES and owner_lock != bot:
        try:
            agregar_evento(f"🔒 Orden REAL bloqueada para {bot.upper()}: {owner_lock.upper()} está activo.")
        except Exception:
            pass
        return False

    # ✅ Auditoría Real vs Ficticia: abrir señal SOLO si esta orden está respaldada por IA (prob >= umbral)
    try:
        st = estado_bots.get(str(bot), {}) if isinstance(estado_bots, dict) else {}
        prob_sig = st.get("prob_ia_oper", st.get("prob_ia"))
        modo_sig = str(st.get("modo_ia") or "").upper()
        thr_sig = float(get_umbral_operativo())
        if isinstance(prob_sig, (int, float)) and modo_sig not in ("", "OFF", "0") and float(prob_sig) >= thr_sig:
            ep_sig = ia_audit_get_last_pre_epoch(str(bot))
            if isinstance(ep_sig, (int, float)) and int(ep_sig) > 0:
                log_ia_open(str(bot), int(ep_sig), float(prob_sig), float(thr_sig), str(st.get("fuente") or "ORDEN_REAL"))
    except Exception:
        pass

    _escribir_orden_real_raw(bot, ciclo)
    ok_activate = bool(activar_real_inmediato(bot, ciclo, origen="orden_real"))

    owner_after_mem = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else None
    owner_after_file = leer_token_archivo_raw()
    ok = bool(ok_activate and owner_after_mem == bot and owner_after_file == bot)
    if ok:
        _marti_audit_log_orden(ciclo, bot=bot, origen="escribir_orden_real")
        if int(ciclo) == 1:
            agregar_evento("🟢 MARTI-AUDIT: apertura explícita en C1 (nuevo ciclo confirmado).")
        _marcar_compuerta_real_consumida()
        DYN_ROOF_STATE["last_real_open_ts"] = float(time.time())
        try:
            _guardar_real_owner_state(
                bot=bot,
                ciclo=int(ciclo),
                source=str(globals().get("_REAL_ROUTE_SOURCE", "LEGACY") or "LEGACY"),
                round_id=globals().get("SYNC_ROUND_ID", None),
                token_state=f"REAL:{bot}",
            )
        except Exception:
            pass
        try:
            _REAL_SHADOW_MICRO_OPEN_TS.append(float(time.time()))
        except Exception:
            pass
    return ok
# === FIN PATCH REAL INMEDIATO ===

def emitir_real_autorizado(bot: str, ciclo: int, source: str = "LEGACY") -> bool:
    """
    Ruta única de emisión REAL cuando LXV_SYNC_REAL_ROUTE_ENABLE está activo.
    Conserva la infraestructura existente (orden_real/token/HUD), pero restringe la decisión.
    """
    src = str(source or "LEGACY").strip().upper()
    allow_src = str(globals().get("LXV_SYNC_REAL_SOURCE", "LXV_SYNC")).upper()
    if bool(globals().get("LXV_SYNC_REAL_ROUTE_ENABLE", False)) and src != allow_src:
        agregar_evento(f"🧊 REAL legacy congelado: source={src} bloqueado (solo {allow_src}).")
        return False
    prev_src = globals().get("_REAL_ROUTE_SOURCE", None)
    globals()["_REAL_ROUTE_SOURCE"] = src
    try:
        return bool(escribir_orden_real(bot, int(ciclo)))
    finally:
        globals()["_REAL_ROUTE_SOURCE"] = prev_src

# === IA ACK (handshake maestro→bot: confirma que el PRE-TRADE ya fue evaluado) ===
IA_ACK_DIR = "ia_ack"
_LAST_IA_ACK_HEARTBEAT_TS = 0.0

def path_ia_ack(bot: str) -> str:
    _ensure_dir(IA_ACK_DIR)
    return os.path.join(IA_ACK_DIR, f"{bot}.json")

def _prob_ia_para_ack(bot: str, st: dict | None = None):
    """
    Prob IA efectiva para ACK:
    - Si el bot tiene una señal ya seleccionada (ia_prob_senal), la conservamos para
      evitar que el ACK oscile durante reintentos/token-sync.
    - Si no hay señal bloqueada, SOLO usamos prob_ia viva cuando el bot reporta
      ia_ready=True y modo_ia != off.

    Esto evita mostrar 0.0% fantasma cuando prob_ia quedó en default durante resets.
    """
    try:
        st = st if isinstance(st, dict) else estado_bots.get(str(bot), {})
        p_lock = st.get("ia_prob_senal", None)
        if isinstance(p_lock, (int, float)) and 0.0 <= float(p_lock) <= 1.0:
            return float(p_lock)

        ia_ready = bool(st.get("ia_ready", False))
        modo = str(st.get("modo_ia", "off") or "off").strip().lower()
        p_live = st.get("prob_ia", None)
        if ia_ready and (modo != "off") and isinstance(p_live, (int, float)) and 0.0 <= float(p_live) <= 1.0:
            return float(p_live)
    except Exception:
        pass
    return None

def _resolver_prob_en_juego_ack(bot: str, st: dict | None = None):
    """Devuelve (prob_en_juego, source) para unificar la fuente de verdad del ACK."""
    try:
        st = st if isinstance(st, dict) else estado_bots.get(str(bot), {})
        p_lock = st.get("ia_prob_senal", None)
        if isinstance(p_lock, (int, float)) and 0.0 <= float(p_lock) <= 1.0:
            return float(p_lock), "SENAL"

        ia_ready = bool(st.get("ia_ready", False))
        modo = str(st.get("modo_ia", "off") or "off").strip().lower()
        p_live = st.get("prob_ia", None)
        if isinstance(p_live, (int, float)) and 0.0 <= float(p_live) <= 1.0 and (modo != "off"):
            # MODELO: predicción lista y usable para decisión real.
            if ia_ready:
                return float(p_live), "MODELO"
            # LOW_DATA/NO_READY: mostramos prob viva del maestro como referencia visual
            # (evita ocultar 54.2% en bot cuando el HUD sí la está mostrando).
            if float(p_live) > 0.0:
                return float(p_live), "HUD"

        if modo == "off":
            return None, "OFF"
        return None, "NO_READY"
    except Exception:
        return None, "NO_READY"

def escribir_ia_ack(bot: str, epoch: int | None, prob: float | None, modo_ia: str, meta: dict | None):
    """
    Escribe un ACK por-bot para que el bot muestre la prob IA asociada a su PRE.
    Incluye:
      - prob: prob calibrada (0..1) o None
      - prob_raw: prob sin calibrar (0..1), si está disponible
      - calib_factor: factor aplicado (si aplica)
      - auc / thr / reliable desde model_meta
    """
    try:
        ack_path = path_ia_ack(bot)
        os.makedirs(os.path.dirname(ack_path), exist_ok=True)

        st = estado_bots.get(str(bot), {}) if isinstance(estado_bots, dict) else {}

        p_hud = _prob_ia_para_ack(bot, st)
        p_play, p_source = _resolver_prob_en_juego_ack(bot, st)
        decision_id = st.get("ia_decision_id")
        if not decision_id:
            ep = int(epoch) if epoch is not None else 0
            decision_id = f"{bot}|{ep}"
        payload = {
            "bot": str(bot),
            "epoch": int(epoch) if epoch is not None else 0,
            "prob": float(prob) if isinstance(prob, (int, float)) else None,
            # prob_hud/modo_hud = valor vigente que pinta el HUD del maestro (fuente visual principal)
            "prob_hud": p_hud,
            "has_prob_hud": isinstance(p_hud, (int, float)),
            "ia_ready": bool(st.get("ia_ready", False)),
            "modo_hud": str(st.get("modo_ia", "off") or "off").upper(),
            "prob_en_juego": p_play,
            "has_prob_en_juego": isinstance(p_play, (int, float)),
            "prob_source": str(p_source),
            "decision_id": str(decision_id),
            "ack_ts": time.time(),
            "prob_raw": float(st.get("prob_ia_raw")) if isinstance(st.get("prob_ia_raw"), (int, float)) else None,
            "calib_factor": float(st.get("cal_factor")) if isinstance(st.get("cal_factor"), (int, float)) else None,
            "auc": float((meta or {}).get("auc", 0.0) or 0.0),
            "thr": float((meta or {}).get("threshold", 0.0) or 0.0),
            "real_thr": float(get_umbral_real_calibrado()),
            "real_thr_cap": float(AUTO_REAL_THR),
            "reliable": bool((meta or {}).get("reliable", True)),
            "modo": str(modo_ia).upper() if modo_ia else "OFF",
            "model_version": str((meta or {}).get("trained_at", "")),
            "ts": time.time()
        }

        with open(ack_path, "w", encoding="utf-8") as f:
            json.dump(payload, f, ensure_ascii=False, indent=2)
    except Exception:
        pass

def refrescar_ia_ack_desde_hud(intervalo_s: float = 1.0):
    """
    Heartbeat de ACK: mantiene `ia_ack/<bot>.json` sincronizado con el HUD.
    Objetivo: que los bots vean la prob IA vigente del maestro durante GateWin,
    incluso si no entraron filas nuevas de CSV en ese instante.
    """
    global _LAST_IA_ACK_HEARTBEAT_TS
    now = time.time()
    if (now - float(_LAST_IA_ACK_HEARTBEAT_TS or 0.0)) < float(intervalo_s):
        return

    meta = leer_model_meta() or {}
    for bot in BOT_NAMES:
        try:
            st = estado_bots.get(bot, {}) if isinstance(estado_bots, dict) else {}
            ep = st.get("ultimo_epoch_pretrade", 0)
            if ep is None:
                ep = 0
            ep = int(float(ep)) if str(ep).strip() != "" else 0
            if ep <= 0:
                continue

            p_eff = _prob_ia_para_ack(bot, st)
            modo = str(st.get("modo_ia", "off") or "off").upper()
            escribir_ia_ack(bot, ep, p_eff if isinstance(p_eff, (int, float)) else None, modo, meta)
        except Exception:
            continue

    _LAST_IA_ACK_HEARTBEAT_TS = now
# Leer token actual
def leer_token_actual():
    """
    Lee token_actual.txt y además sincroniza el HUD (estado_bots[*]["token"])
    para que REAL/DEMO se refleje sin esperar compra del bot.
    Prioriza lock en memoria para evitar parpadeos DEMO durante REAL en curso.
    """
    holder = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else None

    # Si ya hay owner REAL en memoria, mantenemos sincronía visual inmediata.
    if holder in BOT_NAMES:
        _set_ui_token_holder(holder)
        _enforce_single_real_standby(holder)
        return holder

    if not os.path.exists(TOKEN_FILE):
        _set_ui_token_holder(None)
        return None
    try:
        with open(TOKEN_FILE, encoding="utf-8", errors="replace") as f:
            linea = (f.read() or "").strip()
        if linea.startswith("REAL:"):
            bot_name = linea.split(":", 1)[1].strip()
            if bot_name in BOT_NAMES:
                holder = bot_name
            elif bot_name == "none":
                holder = None
        _set_ui_token_holder(holder)
        if holder in BOT_NAMES:
            _enforce_single_real_standby(holder)
        return holder
    except Exception as e:
        try:
            print(f"⚠️ Error leyendo token: {e}")
        except Exception:
            pass
        fallback = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else None
        _set_ui_token_holder(fallback)
        if fallback in BOT_NAMES:
            _enforce_single_real_standby(fallback)
        return fallback


def leer_token_archivo_raw():
    """
    Lee token_actual.txt SIN priorizar REAL_OWNER_LOCK (para reconciliar desincronías).
    Retorna bot owner REAL o None.
    """
    if not os.path.exists(TOKEN_FILE):
        return None
    try:
        with open(TOKEN_FILE, encoding="utf-8", errors="replace") as f:
            linea = (f.read() or "").strip()
        if not linea.startswith("REAL:"):
            return None
        bot_name = linea.split(":", 1)[1].strip()
        if bot_name in BOT_NAMES:
            return bot_name
        return None
    except Exception:
        return None

# Escribir token actual
async def escribir_token_actual(bot):
    """
    Sync UI/token: refleja REAL en HUD y token file.
    ⚠️ Regla: este flujo NO debe generar orden_real.json.
    """
    try:
        try:
            _ = leer_token_actual()  # sincroniza UI
        except Exception:
            pass

        ciclo_objetivo = estado_bots.get(bot, {}).get("ciclo_actual", 1)
        try:
            ciclo_objetivo = int(ciclo_objetivo)
        except Exception:
            ciclo_objetivo = 1

        # ✅ origen "sync_ui": NO debe escribir orden_real.json
        activar_real_inmediato(bot, ciclo_objetivo, origen="token_sync")

        # No bloqueamos: saldo en background
        try:
            asyncio.create_task(obtener_saldo_real())
        except Exception:
            try:
                asyncio.create_task(refresh_saldo_real(forzado=True))
            except Exception:
                pass

    except Exception:
        pass

# Activar remate
def activar_remate(bot: str, reason: str):
    if not estado_bots[bot]["remate_active"]:
        estado_bots[bot]["remate_active"] = True
        estado_bots[bot]["remate_start"] = datetime.now()
        estado_bots[bot]["remate_reason"] = reason

# Cerrar por WIN
def cerrar_por_win(bot: str, reason: str):
    global REAL_OWNER_LOCK, REAL_COOLDOWN_UNTIL_TS

    # Liberar token REAL en archivo primero (commit de salida)
    liberado = False
    try:
        with file_lock_required("real.lock", timeout=6.0, stale_after=30.0) as got:
            if got:
                liberado = bool(write_token_atomic(TOKEN_FILE, "REAL:none"))
                if not liberado:
                    agregar_evento("⚠️ Token REAL no liberado: fallo de persistencia en token_actual.txt.")
            else:
                agregar_evento("⚠️ Token REAL no liberado por lock ocupado (real.lock).")
    except Exception:
        liberado = False

    if not liberado:
        return

    # Liberación consolidada: recién aquí memoria/UI pasan a DEMO
    REAL_OWNER_LOCK = None
    REAL_COOLDOWN_UNTIL_TS = time.time() + float(_cooldown_post_trade_s())

    # Limpieza total de “estado REAL” para evitar REAL fantasma
    try:
        estado_bots[bot]["token"] = "DEMO"
        estado_bots[bot]["trigger_real"] = False
        estado_bots[bot]["ciclo_actual"] = 1
        estado_bots[bot]["modo_real_anunciado"] = False
        estado_bots[bot]["fuente"] = None
        estado_bots[bot]["real_activado_en"] = 0.0
        estado_bots[bot]["ignore_cierres_hasta"] = 0.0


        # Flags IA/pending (si quedó algo colgado)
        estado_bots[bot]["ia_senal_pendiente"] = False
        estado_bots[bot]["ia_prob_senal"] = None

        # Remate limpio
        estado_bots[bot]["remate_active"] = False
        estado_bots[bot]["remate_start"] = None
        estado_bots[bot]["remate_reason"] = ""

    except Exception:
        pass

    # Limpiar orden REAL para evitar re-entradas fantasma
    try:
        limpiar_orden_real(bot)
    except Exception:
        pass

    # Sync inmediato del HUD/token para evitar “REAL fantasma”
    try:
        _set_ui_token_holder(None)
    except Exception:
        pass

    # Resync de snapshots y panel
    try:
        REAL_ENTRY_BASELINE[bot] = 0
        SNAPSHOT_FILAS[bot] = contar_filas_csv(bot)
    except Exception:
        pass

    try:
        OCULTAR_HASTA_NUEVO[bot] = False
    except Exception:
        pass

    try:
        agregar_evento(f"✅ WIN: REAL liberado para {bot.upper()} ({reason})")
    except Exception:
        pass

    try:
        reinicio_forzado.set()
    except Exception:
        pass

# === FIN BLOQUE 7 ===

# === BLOQUE 8 — NORMALIZACIÓN Y PUNTAJE DE ESTRATEGIA ===
# Normalizar resultado
def normalizar_resultado(texto):
    if texto is None:
        return "INDEFINIDO"

    raw = str(texto)

    # 1) Detectar símbolos ANTES de normalización ASCII (ASCII los borra)
    if any(sym in raw for sym in ("✓", "✔", "✅", "🟢")):
        return "GANANCIA"
    if any(sym in raw for sym in ("✗", "❌", "🔴", "🟥")):
        return "PÉRDIDA"

    # 2) Normalización de texto (acentos/encoding raros)
    raw = raw.replace("Ã‰", "É").replace("PÃ‰RDIDA", "PÉRDIDA")
    t = normalize("NFKD", raw).encode("ASCII", "ignore").decode("ASCII").strip().upper()

    # Nota: después de ASCII, "PÉRDIDA" se vuelve "PERDIDA"
    if "PERD" in t or "LOSS" in t:
        return "PÉRDIDA"
    if "GAN" in t or "WIN" in t:
        return "GANANCIA"
    return "INDEFINIDO"
def normalizar_trade_status(ts):
    """
    Normaliza trade_status a canónico del Maestro:
      - "CERRADO"   (CERRADO/CLOSED/SETTLED/etc.)
      - "PRE_TRADE" (PRE_TRADE/PENDIENTE/PENDING/OPEN/ABIERTO/etc.)
      - otros: upper limpio (compat)
    """
    try:
        if ts is None:
            return ""
        s = str(ts).strip().upper()
        if s in ("", "NAN", "NONE"):
            return ""

        # --- CIERRES ---
        if s in (
            "CERRADO", "CERRADA",
            "CLOSED", "CLOSE",
            "SETTLED",
            "SOLD",
            "EXPIRED", "EXPIRE",
            "CANCELLED", "CANCELED",
            "VOID"
        ):
            return "CERRADO"

        # --- PRE / PENDIENTE / ABIERTO ---
        if s in (
            "PRE_TRADE", "PRETRADE",
            "PENDIENTE", "PENDING",
            "OPEN", "ABIERTO", "ABIERTA",
            "IN_PROGRESS", "INPROGRESS", "RUNNING"
        ):
            return "PRE_TRADE"

        return s
    except Exception:
        return ""

def canonicalizar_campos_bot_maestro(row_dict: dict | None):
    """
    Mapeo central BOT -> Maestro para mantener un único esquema canónico.

    Este normalizador NO inventa datos: solo renombra/duplica aliases conocidos
    hacia los nombres oficiales que consume la IA del maestro.
    """
    out = dict(row_dict or {})

    alias_map = {
        "direction": ("direccion",),
        "ciclo_martingala": ("ciclo",),
        "cruce_sma": ("cruce",),
        "payout_multiplier": ("payout_decimal_rounded",),
    }

    for canon, aliases in alias_map.items():
        if out.get(canon) in (None, ""):
            for a in aliases:
                if out.get(a) not in (None, ""):
                    out[canon] = out.get(a)
                    break

    return out

# ==========================================================
# Payout/ROI — Normalización consistente (SIN confundir %)
# Convención:
# - payout_total: total recibido (ej 1.95, 15.62)
# - payout (feature IA): ROI = (payout_total / monto) - 1  en [0.0, 1.5]
# ==========================================================
# Reutilizamos _safe_float (BLOQUE 6) para evitar duplicados
_safe_float_local = _safe_float
                                    
def _norm_01(x, lo=0.0, hi=3.5):
    """
    Normaliza x a [0..1] usando rango [lo..hi].
    Si no se puede convertir, devuelve 0.0
    """
    try:
        v = _safe_float_local(x)
        if v is None:
            return 0.0
        v = float(v)
        if not math.isfinite(v):
            return 0.0
        if hi <= lo:
            return 0.0
        t = (v - lo) / (hi - lo)
        return max(0.0, min(1.0, t))
    except Exception:
        return 0.0
      
def extraer_payout_multiplier(row_dict_full: dict):
    """
    payout_multiplier = payout_total / monto (ratio_total).

    Fuentes (en orden):
      1) payout_multiplier (nuevo BOT)
      2) payout_decimal_rounded (legacy ratio)
      3) payout legacy SOLO si parece RATIO (>=1.05 y <=3.50) o si con monto cuadra como total
      4) payout_total / monto

    Blindaje:
      - Si 'payout' parece ROI feature (0..1.5), se IGNORA como ratio/total.
      - Si 'payout' < 1.05, NO se acepta como ratio (en Deriv el ratio típico >1).
    """
    mult = _safe_float_local(row_dict_full.get("payout_multiplier"))
    if mult is not None and mult > 0:
        return mult

    mult = _safe_float_local(row_dict_full.get("payout_decimal_rounded"))
    if mult is not None and mult > 0:
        return mult

    monto = _safe_float_local(row_dict_full.get("monto"))
    p = _safe_float_local(row_dict_full.get("payout"))  # legacy (a veces ratio, a veces total, a veces ROI feature)

    # 🔒 Si payout parece ROI-feature (0..1.5), NO usarlo para ratio/total
    if p is not None and 0.0 <= p <= 1.5:
        p = None

    if p is not None and p > 0:
        if monto is not None and monto > 0:
            # Caso 1: p parece ratio típico (1.05..3.50)
            if 1.05 <= p <= 3.50:
                return p

            # Caso 2: p parece total (grande)
            if p > 3.50:
                return p / monto

            # Caso 3: p es "total pequeño" (monto<1) donde p/monto cae como ratio
            # Ej: monto=0.5, payout_total=0.975 -> ratio=1.95
            cand = p / monto
            if 1.05 <= cand <= 3.50:
                return cand

            return None
        else:
            # Sin monto: solo aceptar si parece ratio típico
            if 1.05 <= p <= 3.50:
                return p
            return None

    # Fallback por payout_total explícito
    pay_total = _safe_float_local(row_dict_full.get("payout_total"))
    if pay_total is None:
        pay_total = _safe_float_local(row_dict_full.get("payout"))  # legacy total a veces

    if pay_total is not None and monto is not None and monto > 0:
        return pay_total / monto

    return None


def extraer_payout_total(row_dict_full: dict):
    """
    payout_total = retorno total (stake + profit).

    Fuentes (en orden):
      1) payout_total (nuevo BOT)
      2) payout legacy si parece total (>3.5)
      3) monto * payout_multiplier (incluye payout_decimal_rounded o ratio legacy)
      4) si payout legacy parece total (monto<1), usarlo como total
    """
    pay_total = _safe_float_local(row_dict_full.get("payout_total"))
    if pay_total is not None and pay_total > 0:
        return pay_total

    monto = _safe_float_local(row_dict_full.get("monto"))
    p = _safe_float_local(row_dict_full.get("payout"))  # legacy

    if p is not None and p > 0:
        # Claramente total
        if p > 3.50:
            return p

        # Caso monto<1: payout_total puede ser 0.975, que cae <=3.5
        if monto is not None and monto > 0:
            # Si p/monto cae como ratio típico, p es total
            cand = p / monto
            if 0.90 <= cand <= 3.50:
                return p  # total

    mult = extraer_payout_multiplier(row_dict_full)
    if monto is not None and mult is not None and monto > 0 and mult > 0:
        return monto * mult

    return None


def calcular_roi_desde_total_y_monto(payout_total: float, monto: float):
    if payout_total is None or monto is None or monto <= 0:
        return None
    return (payout_total / monto) - 1.0


def calcular_payout_feature(row_dict_full: dict):
    """
    Feature IA 'payout' = ROI = (payout_multiplier - 1).
    Fallback: (payout_total / monto) - 1 si no hay multiplier.
    """
    mult = extraer_payout_multiplier(row_dict_full)

    # ✅ Rescate: algunos logs legacy guardan ratio en "payout" (ej 1.20, 1.35)
    # Esto NO confunde ROI real (ROI típico sería 0.20, no 1.20).
    if mult is None:
        try:
            p_leg = row_dict_full.get("payout", None)
            p_leg = float(p_leg) if p_leg is not None else None
            if p_leg is not None and math.isfinite(p_leg) and (1.05 <= p_leg <= 3.50):
                mult = float(p_leg)
        except Exception:
            pass

    if mult is not None:
        roi = float(mult) - 1.0
    else:
        payout_total = extraer_payout_total(row_dict_full)
        monto = _safe_float_local(row_dict_full.get("monto"))
        roi = calcular_roi_desde_total_y_monto(payout_total, monto)


    if roi is None:
        return None

    # clamps defensivos
    if roi < 0:
        roi = 0.0
    if roi > 1.5:
        roi = 1.5

    return roi

def normalizar_roi_0a1(roi):
    """Convierte ROI [0..1.5] a [0..1] cuando necesitas un 'factor'."""
    try:
        if roi is None:
            return 0.0
        roi = float(roi)
        if not math.isfinite(roi):
            return 0.0
        roi = max(0.0, min(roi, 1.5))
        return roi / 1.5
    except Exception:
        return 0.0
  
# Nueva: Clipping de features a rangos lógicos (para blindaje contra outliers)
def clip_feature_values(fila_dict, feature_names):
    ranges = {
        "rsi_9": (0, 100),
        "rsi_14": (0, 100),
        "cruce_sma": (-1, 1),
        "breakout": (0, 1),
        "rsi_reversion": (0, 1),
        "racha_actual": (-50, 50),
        "payout": (0, 1.5),
        "puntaje_estrategia": (0, 1),
        "volatilidad": (0, 1),
        "es_rebote": (0, 1),
        "hora_bucket": (0, 1),
        # CORE13_v2 scalping
        "ret_1m": (-1, 1),
        "ret_3m": (-1, 1),
        "ret_5m": (-1, 1),
        "slope_5m": (-1, 1),
        "rv_20": (0, 1),
        "range_norm": (0, 1),
        "bb_z": (-3, 3),
        "body_ratio": (0, 1),
        "wick_imbalance": (-1, 1),
        "micro_trend_persist": (-1, 1),
        # sma_5 / sma_20: no clip, pero sí normalizar a float cuando se pueda
    }
    clipped = dict(fila_dict)
    close_sanitized = False

    for feat in feature_names:
        val = clipped.get(feat, None)

        if str(feat).startswith("close_"):
            try:
                v = float(val)
                if (not np.isfinite(v)) or v <= 0.0:
                    raise ValueError("close_invalid")
                clipped[feat] = float(v)
            except Exception:
                clipped[feat] = 0.0
                close_sanitized = True
            continue

        # Normaliza a float si se puede
        try:
            if val is None or (isinstance(val, str) and val.strip() == ""):
                clipped[feat] = np.nan
                continue
            v = float(val)
            if not np.isfinite(v):
                clipped[feat] = np.nan
                continue
        except Exception:
            clipped[feat] = np.nan
            continue

        # Aplica clip solo donde hay rango definido
        if feat in ranges:
            lo, hi = ranges[feat]
            clipped[feat] = float(np.clip(v, lo, hi))
        else:
            clipped[feat] = float(v)

    close_valid_count = sum(1 for feat in feature_names if str(feat).startswith("close_") and float(clipped.get(feat, 0.0) or 0.0) > 0.0)
    close_snapshot_issue = bool(close_sanitized or close_valid_count < 20)
    core_scalping_ready = _core_scalping_ready_from_row(clipped)
    if close_snapshot_issue and (not core_scalping_ready):
        clipped["row_has_proxy_features"] = 1
        clipped["row_train_eligible"] = 0

    return clipped

def _close_series_from_row_dict(row_dict: dict, min_points: int = 2) -> list[float]:
    vals = []
    for i in range(20):
        k = f"close_{i}"
        v = row_dict.get(k, None)
        try:
            vf = float(v)
            if math.isfinite(vf) and vf > 0:
                vals.append(vf)
            else:
                break
        except Exception:
            break
    return vals if len(vals) >= int(min_points) else []

def _calc_scalping_from_close_series(close_vals: list[float]) -> dict:
    out = {}
    c = [float(v) for v in list(close_vals or []) if isinstance(v, (int, float)) or (isinstance(v, np.floating))]
    c = [v for v in c if math.isfinite(v) and abs(v) > 1e-12]
    if len(c) >= 2 and abs(c[1]) > 1e-12:
        out["ret_1m"] = float(np.clip((c[0] - c[1]) / c[1], -1.0, 1.0))
    if len(c) >= 4 and abs(c[3]) > 1e-12:
        out["ret_3m"] = float(np.clip((c[0] - c[3]) / c[3], -1.0, 1.0))
    if len(c) >= 6 and abs(c[5]) > 1e-12:
        out["ret_5m"] = float(np.clip((c[0] - c[5]) / c[5], -1.0, 1.0))
    if len(c) >= 5:
        arr5 = np.asarray([c[4], c[3], c[2], c[1], c[0]], dtype=float)
        base = float(abs(arr5[0])) if abs(arr5[0]) > 1e-9 else float(max(abs(arr5.mean()), 1e-9))
        y = arr5 / base
        x = np.arange(5, dtype=float)
        slope = float(np.polyfit(x, y, 1)[0])
        out["slope_5m"] = float(np.clip(slope, -1.0, 1.0))
    if len(c) >= 3:
        rets = []
        for i in range(len(c) - 1):
            den = c[i + 1]
            if abs(den) <= 1e-12:
                continue
            rets.append((c[i] - den) / den)
        if rets:
            rv = float(np.std(np.asarray(rets, dtype=float), ddof=0))
            out["rv_20"] = float(np.clip(rv, 0.0, 1.0))
    if len(c) >= 20:
        arr20 = np.asarray(c[:20], dtype=float)
        sma20 = float(np.mean(arr20))
        std20 = float(np.std(arr20, ddof=0))
        if std20 > 1e-12:
            bbz = (float(c[0]) - sma20) / (2.0 * std20)
        else:
            bbz = 0.0
        out["bb_z"] = float(np.clip(bbz, -3.0, 3.0))
        rng = float(np.max(arr20) - np.min(arr20))
        out["range_norm"] = float(np.clip(rng / max(abs(float(c[0])), 1e-9), 0.0, 1.0))
    if len(c) >= 2:
        # Derivable con closes: tamaño de vela relativo entre cierres consecutivos (sin OHLC real).
        out["body_ratio"] = float(np.clip(abs(float(out.get("ret_1m", 0.0))), 0.0, 1.0))
    if len(c) >= 6:
        # Persistencia direccional micro: balance de signos en últimos 5 pasos.
        steps = []
        for i in range(5):
            den = c[i + 1]
            if abs(den) <= 1e-12:
                continue
            r = (c[i] - den) / den
            if r > 0:
                steps.append(1.0)
            elif r < 0:
                steps.append(-1.0)
            else:
                steps.append(0.0)
        if steps:
            out["micro_trend_persist"] = float(np.clip(float(np.mean(np.asarray(steps, dtype=float))), -1.0, 1.0))
    return out
    
def _enriquecer_scalping_features_row(fila_dict: dict) -> dict:
    """Completa CORE13_v2 scalping desde campos legacy cuando falten."""
    out = dict(fila_dict or {})
    proxy_used = set()

    def _missing(name: str) -> bool:
        v = out.get(name, None)
        if v is None:
            return True
        if isinstance(v, str) and v.strip() == "":
            return True
        try:
            vf = float(v)
            return not math.isfinite(vf)
        except Exception:
            return True

    def _f(name, default=0.0):
        try:
            v = float(out.get(name, default) if out.get(name, default) not in (None, "") else default)
            return v if math.isfinite(v) else float(default)
        except Exception:
            return float(default)

    # Legacy proxies (si no vienen directos de bot):
    rsi9 = _f("rsi_9", 50.0)
    rsi14 = _f("rsi_14", 50.0)
    sma_spread = _f("sma_spread", 0.0)
    cruce_sma = _f("cruce_sma", 0.0)
    breakout = _f("breakout", 0.0)
    rsi_rev = _f("rsi_reversion", 0.0)
    vol = _f("volatilidad", 0.0)
    reb = _f("es_rebote", 0.0)
    racha = _f("racha_actual", 0.0)
    close_vals = _close_series_from_row_dict(out, min_points=2)
    close_calc = _calc_scalping_from_close_series(close_vals) if close_vals else {}

    for k_real in ("ret_1m", "ret_3m", "ret_5m", "slope_5m", "rv_20", "bb_z", "range_norm", "body_ratio", "micro_trend_persist"):
        if k_real in close_calc:
            out[k_real] = float(close_calc[k_real])

    if _missing("ret_1m"):
        if "ret_1m" in close_calc:
            out["ret_1m"] = float(close_calc["ret_1m"])
        else:
            out["ret_1m"] = float(np.clip((rsi9 - 50.0) / 50.0, -1.0, 1.0))
            proxy_used.add("ret_1m")
    if _missing("ret_3m"):
        if "ret_3m" in close_calc:
            out["ret_3m"] = float(close_calc["ret_3m"])
        else:
            out["ret_3m"] = float(np.clip((rsi14 - 50.0) / 50.0, -1.0, 1.0))
            proxy_used.add("ret_3m")
    if _missing("ret_5m"):
        if "ret_5m" in close_calc:
            out["ret_5m"] = float(close_calc["ret_5m"])
        else:
            out["ret_5m"] = float(np.clip(0.6 * float(out.get("ret_3m", 0.0)) + 0.4 * float(out.get("ret_1m", 0.0)), -1.0, 1.0))
            proxy_used.add("ret_5m")
    if _missing("slope_5m"):
        if "slope_5m" in close_calc:
            out["slope_5m"] = float(close_calc["slope_5m"])
        else:
            out["slope_5m"] = float(np.clip(sma_spread + 0.05 * cruce_sma, -1.0, 1.0))
            proxy_used.add("slope_5m")
    if _missing("rv_20"):
        if "rv_20" in close_calc:
            out["rv_20"] = float(close_calc["rv_20"])
        else:
            out["rv_20"] = float(np.clip(vol, 0.0, 1.0))
            proxy_used.add("rv_20")
    if _missing("range_norm"):
        if "range_norm" in close_calc:
            out["range_norm"] = float(close_calc["range_norm"])
        else:
            out["range_norm"] = float(np.clip(breakout, 0.0, 1.0))
            proxy_used.add("range_norm")
    if _missing("bb_z"):
        if "bb_z" in close_calc:
            out["bb_z"] = float(close_calc["bb_z"])
        else:
            out["bb_z"] = float(np.clip((2.0 * rsi_rev) - 1.0, -3.0, 3.0))
            proxy_used.add("bb_z")
    if _missing("body_ratio"):
        if "body_ratio" in close_calc:
            out["body_ratio"] = float(close_calc["body_ratio"])
        else:
            out["body_ratio"] = float(np.clip(abs(float(out.get("ret_1m", 0.0))), 0.0, 1.0))
            proxy_used.add("body_ratio")
    if _missing("wick_imbalance"):
        out["wick_imbalance"] = float(np.clip((2.0 * reb) - 1.0, -1.0, 1.0))
        proxy_used.add("wick_imbalance")
    if _missing("micro_trend_persist"):
        if "micro_trend_persist" in close_calc:
            out["micro_trend_persist"] = float(close_calc["micro_trend_persist"])
        else:
            out["micro_trend_persist"] = float(np.clip(racha / 10.0, -1.0, 1.0))
            proxy_used.add("micro_trend_persist")

    core_scalping_ready = _core_scalping_ready_from_row(out)
    if len(close_vals) < 20 and (not core_scalping_ready):
        proxy_used.add("close_snapshot_insuficiente")

    out["row_proxy_features"] = ",".join(sorted(proxy_used))
    out["row_has_proxy_features"] = 1 if proxy_used else 0
    core_keys = {"ret_1m", "slope_5m", "rv_20", "bb_z"}
    critical_proxy = any(k in proxy_used for k in core_keys)
    out["row_train_eligible"] = 0 if (critical_proxy or ((len(close_vals) < 20) and (not core_scalping_ready))) else 1

    return out


def calcular_volatilidad_simple(row_dict: dict) -> float:
    """
    Proxy de volatilidad 0–1 menos saturante que el clip lineal.

    Prioridad:
    1) spread relativo SMA5/SMA20
    2) fallback OHLC (high-low sobre close/open)
    """
    try:
        sma5 = float(row_dict.get("sma_5", 0.0) or 0.0)
        sma20 = float(row_dict.get("sma_20", 0.0) or 0.0)
    except Exception:
        sma5 = 0.0
        sma20 = 0.0

    base = abs(sma20) if abs(sma20) > 1e-9 else 0.0
    spread_pct = (abs(sma5 - sma20) / base) if base > 0 else 0.0

    # Fallback OHLC cuando SMA viene vacío/plano
    if (not math.isfinite(spread_pct)) or spread_pct <= 0.0:
        try:
            hi = float(row_dict.get("high", row_dict.get("max", 0.0)) or 0.0)
            lo = float(row_dict.get("low", row_dict.get("min", 0.0)) or 0.0)
            c0 = float(row_dict.get("close", row_dict.get("precio_cierre", 0.0)) or 0.0)
            o0 = float(row_dict.get("open", row_dict.get("precio_apertura", 0.0)) or 0.0)
            base2 = max(abs(c0), abs(o0), 1e-9)
            spread_pct = abs(hi - lo) / base2
        except Exception:
            spread_pct = 0.0

    if not math.isfinite(spread_pct) or spread_pct <= 0.0:
        return 0.0

    # Compresión suave: 0 -> 0, crece rápido al inicio y evita techo constante.
    vol = 1.0 - math.exp(-40.0 * min(spread_pct, 0.25))
    return float(max(0.0, min(vol, 1.0)))
    

def calcular_volatilidad_por_bot(bot: str, lookback: int = 40) -> float | None:
    """
    Estima volatilidad 0..1 desde historial real del bot (retornos absolutos en close).
    Sirve como fallback cuando la fila puntual viene plana (vol=0 por falta de SMA/OHLC).
    """
    try:
        ruta = f"registro_enriquecido_{bot}.csv"
        if not os.path.exists(ruta):
            return None

        df = None
        for enc in ("utf-8", "utf-8-sig", "latin-1", "windows-1252"):
            try:
                df = pd.read_csv(ruta, encoding=enc, engine="python", on_bad_lines="skip")
                break
            except Exception:
                continue
        if df is None or df.empty:
            return None

        close_col = None
        for c in ("close", "precio_cierre", "price", "spot", "last_price"):
            if c in df.columns:
                close_col = c
                break
        if close_col is None:
            return None

        sclose = pd.to_numeric(df[close_col], errors="coerce").dropna()
        if len(sclose) < 6:
            return None

        sclose = sclose.tail(int(max(8, lookback)))
        rets = sclose.pct_change().replace([np.inf, -np.inf], np.nan).dropna().abs()
        if len(rets) < 4:
            return None

        # Mediana robusta de retorno absoluto + compresión suave a [0,1]
        med = float(rets.median())
        if (not math.isfinite(med)) or med <= 0.0:
            return None

        vol = 1.0 - math.exp(-120.0 * min(med, 0.20))
        return float(max(0.0, min(vol, 1.0)))
    except Exception:
        return None


# --- Helper: detectar rebote tras racha larga negativa --- 
def calcular_es_rebote(row_dict):
    """
    es_rebote = 1 si:
      - |racha_actual| >= 4  (racha larga, positiva o negativa)
      - y hay señal de giro (RSI reversión alta, breakout fuerte o cruce+fuerza a favor)
    En caso contrario, 0.
    """
    try:
        racha = float(row_dict.get("racha_actual", 0) or 0.0)
    except Exception:
        racha = 0.0

    # Solo consideramos rebote cuando la racha (ganadora o perdedora) es larga
    if abs(racha) < 4:
        return 0.0

    def _safe_num(key, default=0.0):
        try:
            return float(row_dict.get(key, default) or default)
        except Exception:
            return default

    rsi_rev  = _safe_num("rsi_reversion", 0.0)
    breakout = _safe_num("breakout", 0.0)
    cruce    = _safe_num("cruce_sma", 0.0)
    fuerza   = _safe_num("fuerza_vela", 0.0)

    # "Señal de giro": cualquiera de estos empuja a rebote
    giro_flag = (
        rsi_rev >= 0.60 or
        breakout >= 0.50 or
        (cruce > 0 and fuerza > 0)
    )

    if not giro_flag:
        return 0.0

    # Intensidad de rebote (evita booleano congelado):
    # combina longitud de racha + fuerza de señales de giro en [0,1].
    intensidad_racha = min(1.0, max(0.0, (abs(racha) - 3.0) / 6.0))
    intensidad_giro = min(
        1.0,
        max(
            0.0,
            0.45 * min(1.0, rsi_rev) +
            0.35 * min(1.0, breakout) +
            0.20 * (1.0 if (cruce > 0 and fuerza > 0) else 0.0)
        )
    )
    return max(0.0, min(1.0, 0.60 * intensidad_racha + 0.40 * intensidad_giro))

def _parse_hora_bucket(row_dict) -> tuple[float, bool]:
    """Parsea hora y devuelve (bucket_0_1, parseado_ok)."""
    def _missing(v):
        if v is None:
            return True
        try:
            if pd.isna(v):
                return True
        except Exception:
            pass
        return isinstance(v, str) and v.strip() == ""

    def _bucket(hour: int, minute: int = 0):
        h = int(max(0, min(23, hour)))
        m = int(max(0, min(59, minute)))
        idx_48 = (h * 2) + (1 if m >= 30 else 0)
        return float(idx_48) / 47.0

    v = (row_dict or {}).get("ts", None)
    if not _missing(v) and isinstance(v, str):
        try:
            dt = pd.to_datetime(v, utc=True, errors="coerce")
            if dt is not None and pd.notna(dt):
                try:
                    dt = dt.tz_convert("America/Lima")
                except Exception:
                    pass
                return _bucket(int(dt.hour), int(dt.minute)), True
        except Exception:
            pass

    for k in ("epoch", "timestamp", "open_epoch", "close_epoch", "entry_epoch", "ts_epoch", "server_time"):
        v = (row_dict or {}).get(k, None)
        if _missing(v):
            continue
        try:
            val = float(v)
            if val > 1e12:
                val = val / 1000.0
            if val > 1e9:
                dt = pd.to_datetime(val, unit="s", utc=True, errors="coerce")
                if dt is not None and pd.notna(dt):
                    try:
                        dt = dt.tz_convert("America/Lima")
                    except Exception:
                        pass
                    return _bucket(int(dt.hour), int(dt.minute)), True
        except Exception:
            pass

    v = (row_dict or {}).get("fecha", None)
    if not _missing(v) and isinstance(v, str):
        try:
            dt = pd.to_datetime(v, errors="coerce")
            if dt is not None and pd.notna(dt):
                return _bucket(int(dt.hour), int(dt.minute)), True
        except Exception:
            pass

    v = (row_dict or {}).get("hora", None)
    if not _missing(v) and isinstance(v, str):
        try:
            s = v.strip()
            if ":" in s:
                h = int(s.split(":")[0])
                if 0 <= h <= 23:
                    mm = 0
                    if len(s.split(":")) >= 2:
                        try:
                            mm = int(s.split(":")[1])
                        except Exception:
                            mm = 0
                    return _bucket(h, mm), True
        except Exception:
            pass

    return 0.0, False


def calcular_hora_bucket(row_dict):
    """Devuelve bucket horario normalizado 0..1 (fallback 0.0)."""
    hb, _ok = _parse_hora_bucket(row_dict)
    return float(hb)


def calcular_hora_features(row_dict: dict) -> tuple[float, float]:
    """
    Contrato horario explícito:
      - hora_bucket: 0..1
      - hora_missing: 1.0 cuando falta hora parseable, 0.0 en caso contrario.

    Si no hay timestamp parseable, usa fallback neutro estable (0.0)
    para mantener reproducibilidad histórica sin depender del reloj actual.
    """
    hb, parsed_ok = _parse_hora_bucket(row_dict)
    if not bool(parsed_ok):
        hb = 0.0
    try:
        hb = float(hb)
    except Exception:
        hb = 0.0
    hb = float(max(0.0, min(1.0, hb)))
    hm = 0.0 if bool(parsed_ok) else 1.0
    return hb, hm


def _calcular_sma_spread_robusto(row_dict: dict | None) -> float | None:
    """Calcula sma_spread continuo con fallback de denominador para evitar constantes artificiales."""
    try:
        d = dict(row_dict or {})
        sma5 = _safe_float_local(d.get("sma_5"))
        sma20 = _safe_float_local(d.get("sma_20"))
        px = None
        for k in ("close", "cierre", "price", "precio"):
            v = _safe_float_local(d.get(k))
            if v is not None and math.isfinite(float(v)) and abs(float(v)) > 1e-12:
                px = float(v)
                break

        if sma5 is None and sma20 is None:
            return None

        if sma5 is None:
            sma5 = sma20
        if sma20 is None:
            sma20 = sma5

        denom = abs(float(sma20))
        if (not math.isfinite(denom)) or denom <= 1e-12:
            denom = abs(float(px)) if px is not None else 1e-9

        spread = abs(float(sma5) - float(sma20)) / max(denom, 1e-9)
        if not math.isfinite(spread):
            return None
        return float(max(0.0, min(float(spread), 5.0)))
    except Exception:
        return None


def _calcular_eventos_pretrade_desde_historial(df: pd.DataFrame, idx_ref: int, row_base: dict | None = None) -> dict:
    """
    Calcula señales de evento (no estado) para PRE_TRADE usando solo pasado <= idx_ref.
    - cruce_sma: 1 solo si cambia el signo de (sma_5 - sma_20) entre vela previa y actual.
    - breakout: 1 solo si el close rompe max/min de ventana previa (sin incluir vela actual).
    - sma_spread: intensidad continua del spread SMA (0..5) para conservar información.
    """
    out = dict(row_base or {})
    try:
        if df is None or df.empty:
            return out

        if idx_ref not in df.index:
            return out

        pos = int(df.index.get_indexer([idx_ref])[0])
        if pos < 0:
            return out

        d = df.copy()
        for c in ("sma_5", "sma_20", "close", "cierre", "price", "precio", "high", "maximo", "low", "minimo"):
            if c in d.columns:
                d[c] = pd.to_numeric(d[c], errors="coerce")

        row_now = d.iloc[pos]
        sma5 = _safe_float_local(row_now.get("sma_5"))
        sma20 = _safe_float_local(row_now.get("sma_20"))

        # Intensidad de spread SMA (continua)
        if sma5 is not None and sma20 is not None:
            sp = _calcular_sma_spread_robusto({"sma_5": sma5, "sma_20": sma20, "close": row_now.get("close", None)})
            if sp is not None:
                out["sma_spread"] = float(sp)

        # cruce_sma como evento (cambio de signo)
        cruce_evt = 0.0
        if pos >= 1 and sma5 is not None and sma20 is not None:
            row_prev = d.iloc[pos - 1]
            sma5_prev = _safe_float_local(row_prev.get("sma_5"))
            sma20_prev = _safe_float_local(row_prev.get("sma_20"))
            if sma5_prev is not None and sma20_prev is not None:
                prev_diff = float(sma5_prev) - float(sma20_prev)
                now_diff = float(sma5) - float(sma20)
                if (prev_diff < 0.0 <= now_diff) or (prev_diff > 0.0 >= now_diff):
                    cruce_evt = 1.0
        out["cruce_sma"] = cruce_evt

        # breakout como evento (rompe máximo/mínimo de ventana previa)
        breakout_evt = 0.0
        lookback = 20
        if pos >= 2:
            i0 = max(0, pos - lookback)
            hist = d.iloc[i0:pos]
            if not hist.empty:
                close_now = None
                for cc in ("close", "cierre", "price", "precio"):
                    v = _safe_float_local(row_now.get(cc))
                    if v is not None:
                        close_now = float(v)
                        break

                hi_prev = None
                lo_prev = None
                for hc in ("high", "maximo", "close", "cierre"):
                    if hc in hist.columns:
                        s = pd.to_numeric(hist[hc], errors="coerce").dropna()
                        if len(s) > 0:
                            hi_prev = float(s.max())
                            break
                for lc in ("low", "minimo", "close", "cierre"):
                    if lc in hist.columns:
                        s = pd.to_numeric(hist[lc], errors="coerce").dropna()
                        if len(s) > 0:
                            lo_prev = float(s.min())
                            break

                if close_now is not None and hi_prev is not None and lo_prev is not None:
                    if (close_now > hi_prev) or (close_now < lo_prev):
                        breakout_evt = 1.0
        out["breakout"] = breakout_evt

    except Exception:
        return out
    return out


def enriquecer_features_evento(row_dict: dict):
    """Convierte señales binarias en intensidades continuas para reducir dominancia."""
    d = dict(row_dict or {})

    def _f(key, default=0.0):
        try:
            v = d.get(key, default)
            if v in (None, ""):
                return float(default)
            return float(v)
        except Exception:
            return float(default)

    sma5 = _f("sma_5", 0.0)
    sma20 = _f("sma_20", 0.0)
    base = max(abs(sma20), 1e-9)
    spread = abs(sma5 - sma20) / base

    vol_raw = d.get("volatilidad", None)
    if vol_raw in (None, ""):
        vol = calcular_volatilidad_simple(d)
    else:
        try:
            vol = float(vol_raw)
        except Exception:
            vol = calcular_volatilidad_simple(d)
    vol = max(0.0, min(1.0, float(vol)))
    d["volatilidad"] = float(vol)

    rsi9 = _f("rsi_9", 50.0)
    rsi14 = _f("rsi_14", 50.0)
    rsi_center_dist = min(1.0, (abs(rsi9 - 50.0) + abs(rsi14 - 50.0)) / 70.0)

    cruce_raw = _f("cruce_sma", 0.0)
    cruce_int = spread / (spread + 0.0015) if spread > 0 else 0.0
    d["cruce_sma"] = float(max(0.0, min(1.0, 0.75 * cruce_int + 0.25 * (1.0 if cruce_raw >= 0.5 else 0.0))))

    breakout_raw = _f("breakout", 0.0)
    breakout_int = max(0.0, min(1.0, 0.45 * (spread / (spread + 0.0020) if spread > 0 else 0.0) + 0.35 * vol + 0.20 * rsi_center_dist))
    d["breakout"] = float(max(0.0, min(1.0, 0.55 * breakout_int + 0.45 * (1.0 if breakout_raw >= 0.5 else 0.0))))

    low_ext = max(0.0, (35.0 - min(rsi9, rsi14)) / 35.0)
    high_ext = max(0.0, (max(rsi9, rsi14) - 65.0) / 35.0)
    rsi_rev_int = max(low_ext, high_ext, 0.35 * rsi_center_dist)
    d["rsi_reversion"] = float(max(0.0, min(1.0, rsi_rev_int)))

    reb_base = float(max(0.0, min(1.0, calcular_es_rebote(d))))
    racha = abs(_f("racha_actual", 0.0))
    racha_term = max(0.0, min(1.0, racha / 10.0))
    d["es_rebote"] = float(max(0.0, min(1.0, 0.60 * reb_base + 0.25 * d["rsi_reversion"] + 0.15 * racha_term)))

    try:
        pe = calcular_puntaje_estrategia_normalizado(d)
        if pe is not None:
            d["puntaje_estrategia"] = float(max(0.0, min(1.0, float(pe))))
    except Exception:
        pass

    return d

# === Nuevo: cálculo enriquecido de puntaje_estrategia normalizado (0–1) ===
def calcular_puntaje_estrategia_normalizado(fila: dict) -> float:
    """
    Puntaje 0..1 usando señales + RSI + ROI (payout como ROI [0..1.5]).
    Robusto a valores 1.0/0.0 y strings.
    """
    def as_cont01(x):
        try:
            if isinstance(x, str):
                x = x.strip().lower()
                if x in ("1", "true", "yes", "y"):
                    return 1.0
                if x in ("0", "false", "no", "n", ""):
                    return 0.0
            v = float(x)
            if not math.isfinite(v):
                return 0.0
            return max(0.0, min(1.0, v))
        except Exception:
            return 0.0

    score = 0.0

    # IMPORTANTE: score continuo (NO binarizar señales continuas por umbral >=0.5)
    breakout      = as_cont01(fila.get("breakout", 0))
    cruce_sma     = as_cont01(fila.get("cruce_sma", 0))
    rsi_reversion = as_cont01(fila.get("rsi_reversion", 0))
    es_rebote     = as_cont01(fila.get("es_rebote", 0))

    score += breakout * 0.24
    score += cruce_sma * 0.20
    score += rsi_reversion * 0.18
    score += es_rebote * 0.14

    # RSI zona caliente (bonus pequeño)
    try:
        rsi_9 = float(fila.get("rsi_9", 50.0) or 50.0)
        rsi_14 = float(fila.get("rsi_14", 50.0) or 50.0)
        if rsi_9 >= 70 or rsi_14 >= 70:
            score += 0.05
        if rsi_9 <= 30 or rsi_14 <= 30:
            score += 0.05
    except Exception:
        pass

    # ROI (feature payout) en 0..1
    # Si ya viene como ROI (0..1.5) úsalo directo; si no, recién calcula.
    roi = fila.get("payout", None)
    try:
        roi = float(roi)
        # Si parece ROI válido
        if (not math.isfinite(roi)) or roi < 0 or roi > 1.5:
            roi = None
    except Exception:
        roi = None

    if roi is None:
        roi = calcular_payout_feature(fila)  # fallback

    roi01 = 0.0
    try:
        roi01 = max(0.0, min(float(roi or 0.0), 1.5)) / 1.5
    except Exception:
        roi01 = 0.0

    score += roi01 * 0.05

    try:
        vol = float(fila.get("volatilidad", 0.0) or 0.0)
    except Exception:
        vol = 0.0
    vol = max(0.0, min(1.0, vol))
    score += 0.08 * vol

    try:
        hb = float(fila.get("hora_bucket", 0.5) or 0.5)
    except Exception:
        hb = 0.5
    hb = max(0.0, min(1.0, hb))
    score += 0.03 * (1.0 - abs((hb * 2.0) - 1.0))

    if not math.isfinite(score):
        score = 0.0
    return max(0.0, min(score, 1.0))

# Leer última fila válida
def leer_ultima_fila_con_resultado(bot: str) -> tuple[dict | None, int | None]:
    """
    Devuelve (fila_dict_features_pretrade, label) emparejando:
      - LABEL: desde el último trade CERRADO (GANANCIA/PÉRDIDA)
      - FEATURES: desde el PRE_TRADE/PENDIENTE del mismo epoch (o el más cercano ANTES)

    FIX CLAVE:
      - racha_actual se RECALCULA desde el historial de CIERRES ANTERIORES,
        excluyendo SIEMPRE el cierre actual (anti-contaminación).
      - payout(feature) prioriza ratio cotizado (mult/decimal_rounded).
        Si existe payout_total en PRE_TRADE, se usa como fallback seguro (más rango real).
    """
    try:
        ruta = f"registro_enriquecido_{bot}.csv"
        if not os.path.exists(ruta):
            return None, None

        df = None
        for enc in ("utf-8", "latin-1", "windows-1252"):
            try:
                df = pd.read_csv(ruta, sep=",", encoding=enc, engine="python", on_bad_lines="skip")
                break
            except Exception:
                continue

        if df is None or df.empty:
            return None, None
        if "resultado" not in df.columns:
            return None, None

        # Normalizar resultado robusto
        df["resultado_norm"] = df["resultado"].apply(normalizar_resultado)

        # Normalizar trade_status de forma canónica (evita CLOSED/SETTLED vs CERRADO)
        # IMPORTANTÍSIMO:
        # - No basta con que exista la columna: debe haber valores reales.
        # - normalizar_trade_status() canoniza a: "CERRADO" o "PRE_TRADE" (o "")
        ts_source_col = None
        if "trade_status_norm" in df.columns:
            ts_source_col = "trade_status_norm"
        elif "trade_status" in df.columns:
            ts_source_col = "trade_status"

        if ts_source_col:
            try:
                df["trade_status_norm"] = df[ts_source_col].apply(normalizar_trade_status)
            except Exception:
                df["trade_status_norm"] = ""
        else:
            df["trade_status_norm"] = ""

        # has_trade_status = hay valores reales (no solo columna vacía)
        try:
            has_trade_status = df["trade_status_norm"].astype(str).str.strip().ne("").any()
        except Exception:
            has_trade_status = False

        def _calc_racha_pretrade(_df: pd.DataFrame, _idx_close: int) -> float:
            """
            racha_actual PRE-TRADE:
              - Usa SOLO cierres (GANANCIA/PÉRDIDA)
              - Usa SOLO filas con índice < idx_close (excluye el cierre actual)
              - Si hay trade_status usable, acepta:
                    * CERRADO
                    * "" (legacy sin status) PERO solo si es cierre real por resultado_norm
              - Devuelve racha firmada: +N (wins), -N (losses), 0 si no hay historial
            """
            try:
                try:
                    d = _df.loc[_df.index < _idx_close].copy()
                except Exception:
                    d = _df.copy()

                d = d[d["resultado_norm"].isin(["GANANCIA", "PÉRDIDA"])].copy()
                if d.empty:
                    return 0.0

                if has_trade_status and "trade_status_norm" in d.columns:
                    try:
                        ts = d["trade_status_norm"].astype(str).str.strip()
                        d = d[(ts.eq("CERRADO")) | (ts.eq(""))].copy()
                    except Exception:
                        d = d[d["trade_status_norm"].eq("CERRADO")].copy()

                if d.empty:
                    return 0.0

                seq = d["resultado_norm"].tolist()
                last = seq[-1]
                streak = 0
                for r in reversed(seq):
                    if r == last:
                        streak += 1
                    else:
                        break

                val = float(streak if last == "GANANCIA" else -streak)
                if val > 50:
                    val = 50.0
                if val < -50:
                    val = -50.0
                return val
            except Exception:
                return 0.0

        # 1) Último cierre válido (label)
        df_cerr = df[df["resultado_norm"].isin(["GANANCIA", "PÉRDIDA"])].copy()

        # Si hay trade_status usable, filtramos CERRADO o "" (legacy)
        if has_trade_status:
            try:
                ts = df_cerr["trade_status_norm"].astype(str).str.strip()
                df_cerr = df_cerr[(ts.eq("CERRADO")) | (ts.eq(""))].copy()
            except Exception:
                df_cerr = df_cerr[df_cerr["trade_status_norm"].eq("CERRADO")].copy()

        if df_cerr.empty:
            return None, None

        idx_close = int(df_cerr.index[-1])
        r_close = df.loc[idx_close].to_dict()
        epoch_close = r_close.get("epoch", None)

        res_norm = r_close.get("resultado_norm", None)
        if res_norm not in ("GANANCIA", "PÉRDIDA"):
            res_norm = normalizar_resultado(r_close.get("resultado"))
        label = 1 if res_norm == "GANANCIA" else 0

        # 2) Buscar PRE_TRADE correspondiente (SIN futuro)
        pre_row = None
        pre_idx = None

        if has_trade_status:
            # ✅ OJO: después del normalizador solo existe PRE_TRADE (no PENDIENTE/OPEN/ABIERTO)
            df_pending = df[df["trade_status_norm"].eq("PRE_TRADE")].copy()

            # evitar futuro: solo filas con índice <= cierre
            try:
                df_pending = df_pending.loc[df_pending.index <= idx_close]
            except Exception:
                pass

            # prioridad: mismo epoch
            if epoch_close is not None and "epoch" in df_pending.columns:
                try:
                    ep = pd.to_numeric(df_pending["epoch"], errors="coerce")
                    ec = float(epoch_close)
                    same_ep = df_pending[ep.notna() & (ep == ec)].copy()
                except Exception:
                    same_ep = df_pending[df_pending["epoch"] == epoch_close].copy()

                if not same_ep.empty:
                    pre_idx = int(same_ep.index[-1])
                    pre_row = df.loc[pre_idx].to_dict()

            # fallback: último PRE_TRADE antes del cierre
            if pre_row is None and not df_pending.empty:
                pre_idx = int(df_pending.index[-1])
                pre_row = df.loc[pre_idx].to_dict()

        # ✅ Fallback UNIVERSAL:
        # Si no hubo PRE_TRADE (o trade_status era “usable” pero no encontró), usamos la última fila NO cierre antes del cierre.
        if pre_row is None:
            try:
                df_before = df.loc[df.index <= idx_close].copy()
            except Exception:
                df_before = df.copy()

            cand = df_before[~df_before["resultado_norm"].isin(["GANANCIA", "PÉRDIDA"])].copy()
            if not cand.empty:
                pre_idx = int(cand.index[-1])
                pre_row = df.loc[pre_idx].to_dict()
            else:
                pre_idx = int(df_before.index[-1])
                pre_row = df.loc[pre_idx].to_dict()

        if pre_row is None:
            return None, None

        row_dict_full = canonicalizar_campos_bot_maestro(pre_row)

        # Señales de evento reales (anti-saturación): usar solo historial pasado hasta PRE_TRADE.
        try:
            if pre_idx is not None:
                row_dict_full = _calcular_eventos_pretrade_desde_historial(df, int(pre_idx), row_base=row_dict_full)
        except Exception:
            pass

        # 3) Asegurar monto (stake) desde PRE; si falta, tomar del cierre (monto NO filtra label)
        if ("monto" not in row_dict_full) or (row_dict_full.get("monto") in (None, "", 0, 0.0)):
            if "monto" in r_close:
                row_dict_full["monto"] = r_close.get("monto")

        # 4) Copiar ratio cotizado desde cierre SOLO si viene como multiplier/decimal_rounded (ratio seguro)
        for k in ("payout_multiplier", "payout_decimal_rounded"):
            if (k not in row_dict_full) or (row_dict_full.get(k) in (None, "", 0, 0.0)):
                if k in r_close:
                    row_dict_full[k] = r_close.get(k)

        # 4.9) Anti-leakage duro:
        # - Nunca permitir campos que puedan oler al cierre (resultado/profit).
        for k in ("ganancia_perdida", "profit", "resultado", "resultado_norm"):
            try:
                row_dict_full.pop(k, None)
            except Exception:
                pass

        # payout_total: SOLO lo permitimos si viene del PRE_TRADE/PENDIENTE (no cierre).
        # Importante: detectar CERRADO también si viene como CLOSED/SETTLED.
        try:
            ts_pre_norm = normalizar_trade_status(
                pre_row.get("trade_status_norm", None) or pre_row.get("trade_status", None)
            )
        except Exception:
            ts_pre_norm = ""

        if ts_pre_norm == "CERRADO":
            try:
                row_dict_full.pop("payout_total", None)
            except Exception:
                pass
        else:
            try:
                pt = _safe_float_local(row_dict_full.get("payout_total"))
                if pt is not None and pt <= 0:
                    row_dict_full.pop("payout_total", None)
            except Exception:
                try:
                    row_dict_full.pop("payout_total", None)
                except Exception:
                    pass


        # 5) FIX CONTAMINACIÓN: recalcular racha_actual PRE-TRADE desde historia real
        racha_safe = _calc_racha_pretrade(df, idx_close)
        try:
            old_racha = _safe_float_local(row_dict_full.get("racha_actual"))
        except Exception:
            old_racha = None

        row_dict_full["racha_actual"] = float(racha_safe)

        # opcional: avisar SOLO si había valor y cambia fuerte (útil para ver contaminación)
        try:
            if old_racha is not None and math.isfinite(float(old_racha)):
                if abs(float(old_racha) - float(racha_safe)) >= 1.0:
                    fn_evt = globals().get("agregar_evento", None)
                    if callable(fn_evt):
                        fn_evt(f"🧼 racha_actual corregida {bot}: {old_racha:.0f} → {racha_safe:.0f} (anti-contaminación)")
        except Exception:
            pass

        # Blindaje: si 'payout' existe, puede ser ROI-feature (0..1.5) o total legacy.
        # - ROI-feature: ignorar SIEMPRE (no sirve para ratio)
        # - total grande o ratio inválido: ignorar
        try:
            _p = _safe_float_local(row_dict_full.get("payout"))
            if _p is not None:
                if 0.0 <= _p <= 1.5:
                    row_dict_full["payout"] = None
                elif _p > 3.50:
                    row_dict_full["payout"] = None
                elif _p < 1.05:
                    row_dict_full["payout"] = None
        except Exception:
            pass

        # 6) payout feature (ROI) usando ratio cotizado / payout_total PRETRADE como fallback seguro
        mult = extraer_payout_multiplier(row_dict_full)

        # Si no hay ratio, inferimos por moda histórica del ratio (SOLO hasta el cierre)
        if mult is None:
            mult_moda = None
            try:
                df_hist = df.loc[df.index <= idx_close].copy()

                cand_cols = []
                if "payout_multiplier" in df_hist.columns:
                    cand_cols.append("payout_multiplier")
                if "payout_decimal_rounded" in df_hist.columns:
                    cand_cols.append("payout_decimal_rounded")

                for col in cand_cols:
                    s = pd.to_numeric(df_hist[col], errors="coerce").dropna()
                    if len(s) > 0:
                        moda = float(s.value_counts().idxmax())
                        if 1.05 < moda < 3.50:
                            mult_moda = moda
                            break
            except Exception:
                mult_moda = None

            if mult_moda is None:
                return None, None
            mult = float(mult_moda)

        try:
            pay_ok = float(mult) - 1.0
        except Exception:
            return None, None

        if not math.isfinite(pay_ok):
            return None, None

        pay_ok = max(0.0, min(pay_ok, 1.5))
        row_dict_full["payout"] = float(pay_ok)

        # 7) Completar derivados si faltan
        vol = _safe_float_local(row_dict_full.get("volatilidad"))
        if vol is None:
            vol = calcular_volatilidad_simple(row_dict_full)
        if vol is None or not math.isfinite(float(vol)):
            return None, None
        row_dict_full["volatilidad"] = float(vol)

        hb = _safe_float_local(row_dict_full.get("hora_bucket"))
        if hb is None:
            hb, hm = calcular_hora_features(row_dict_full)
            row_dict_full["hora_missing"] = float(hm)
        if hb is None or not math.isfinite(float(hb)):
            return None, None
        row_dict_full["hora_bucket"] = float(hb)

        # Enriquecer señales evento para evitar columnas booleanas congeladas
        row_dict_full = enriquecer_features_evento(row_dict_full)

        er = _safe_float_local(row_dict_full.get("es_rebote"))
        if er is None:
            er = calcular_es_rebote(row_dict_full)
        if er is None or not math.isfinite(float(er)):
            return None, None
        row_dict_full["es_rebote"] = float(er)

        pe = None
        try:
            pe = calcular_puntaje_estrategia_normalizado(row_dict_full)
        except Exception:
            pe = None

        if pe is None:
            pe_raw = _safe_float_local(row_dict_full.get("puntaje_estrategia"))
            if pe_raw is None:
                return None, None
            pe = _norm_01(pe_raw)

        pe = float(pe)
        if not math.isfinite(pe):
            return None, None
        pe = max(0.0, min(pe, 1.0))
        row_dict_full["puntaje_estrategia"] = pe

        try:
            sma5 = _safe_float_local(row_dict_full.get("sma_5"))
            sma20 = _safe_float_local(row_dict_full.get("sma_20"))
            if sma5 is not None and sma20 is not None:
                sp = _calcular_sma_spread_robusto({"sma_5": sma5, "sma_20": sma20, "close": row_dict_full.get("close", None)})
                if sp is not None:
                    row_dict_full["sma_spread"] = float(sp)
        except Exception:
            pass

        # 8) Features requeridas (13 core, estricto)
        required = [
            "rsi_9","rsi_14","sma_5","sma_spread","cruce_sma","breakout",
            "rsi_reversion","racha_actual","payout","puntaje_estrategia",
            "volatilidad","es_rebote","hora_bucket",
        ]

        fila_dict = {}
        for k in required:
            fv = _safe_float_local(row_dict_full.get(k))
            if fv is None or not math.isfinite(float(fv)):
                return None, None
            fila_dict[k] = float(fv)

        return fila_dict, int(label)

    except Exception as e:
        print(f"[WARN] leer_ultima_fila_con_resultado({bot}) fallo: {e}")
        return None, None

# ==========================================================
# === BLOQUE 10A — AUDITORÍA DE SEÑALES IA (solo logging; NO toca trading) ===
# Objetivo:
# - Registrar señales IA (bot, epoch, prob, thr, modo) en ia_signals_log.csv
# - Cerrar señales cuando aparezca el CIERRE real (GANANCIA/PÉRDIDA) para ese epoch
# - Calcular métricas simples (Brier/AUC/Acc) con señales cerradas
# ==========================================================

IA_SIGNALS_LOG = "ia_signals_log.csv"
CANARY_STATE_CACHE = {"ts": 0.0, "meta": None}
IA_SIGNALS_TELEMETRY_LAST = {"opens": 0, "closes": 0, "orphans": 0, "ts": 0.0}
IA_SIGNALS_HISTORICAL_UNRECOVERABLE_EMITTED = False

# Blindaje: evita crash si threading aún no estaba importado (aunque tú sí lo tienes)
try:
    import threading as _audit_threading
    IA_SIGNALS_LOCK = _audit_threading.Lock()
except Exception:
    class _DummyLock:
        def __enter__(self): return self
        def __exit__(self, exc_type, exc, tb): return False
    IA_SIGNALS_LOCK = _DummyLock()

def _col_as_str_series(df: pd.DataFrame, col: str) -> pd.Series:
    """Devuelve df[col] como Series(str) y trata NaN como vacío (""). Si no existe, Series vacía del tamaño del df."""
    try:
        if col in df.columns:
            s = df[col]
            try:
                s = s.fillna("")
            except Exception:
                pass
            return s.astype(str)
        return pd.Series([""] * len(df), index=df.index, dtype="object")
    except Exception:
        return pd.Series([""] * len(df), index=df.index, dtype="object")

def _ag_evt(msg: str):
    try:
        fn = globals().get("agregar_evento", None)
        if callable(fn):
            fn(msg)
        else:
            print(msg)
    except Exception:
        pass

def _safe_read_csv_any_encoding(path: str) -> pd.DataFrame | None:
    if not os.path.exists(path):
        return None
    for enc in ("utf-8", "latin-1", "windows-1252"):
        try:
            return pd.read_csv(path, sep=",", encoding=enc, engine="python", on_bad_lines="skip")
        except Exception:
            continue
    return None

_IA_RUNTIME_CAL_CACHE = {"ts": 0.0, "base_rate": 0.5, "n70": 0}
_IA_OVERCONF_CACHE = {"ts": 0.0, "active": False, "cap": 1.0, "n": 0, "gap_pp": 0.0}
_IA_HARD_GUARD_CACHE = {"ts": 0.0, "active": False, "cap": 1.0, "level": "GREEN", "closed": 0, "auc": 0.0, "reliable": False, "features": 0, "reasons": [], "until": 0.0}
_IA_HARD_GUARD_BOT_CACHE = {"ts": 0.0, "data": {}}
_IA_HARD_GUARD_LOG_TS = 0.0
_IA_CHECKPOINT_CACHE = {"last_closed": 0, "last_ts": 0.0}
_IA_BOT45_TRACE_CACHE = {"ts": 0.0, "msg": ""}
_GATE_ACTIVO_CACHE = {}
_ASSET_COOLDOWN_STATE = {}
_ASSET_RUNTIME_LOG_CACHE = {"ts": 0.0, "sig": ""}
_GATE_SEGMENTO_CACHE = {}


def _bucket_tercil(v: float, q1: float, q2: float) -> str:
    try:
        x = float(v)
    except Exception:
        x = 0.0
    if x <= q1:
        return "bajo"
    if x <= q2:
        return "medio"
    return "alto"


def _inferir_segmento_hora(hb01: float) -> str:
    try:
        hb = int(round(max(0.0, min(1.0, float(hb01))) * 23.0))
    except Exception:
        hb = 12
    h0 = (hb // 6) * 6
    h1 = min(h0 + 5, 23)
    return f"h{h0:02d}-{h1:02d}"


def _segmento_key_from_df(df: pd.DataFrame) -> pd.DataFrame:
    d = df.copy()
    d["payout"] = pd.to_numeric(d.get("payout", 0.0), errors="coerce").fillna(0.0)
    d["volatilidad"] = pd.to_numeric(d.get("volatilidad", 0.0), errors="coerce").fillna(0.0)
    d["hora_bucket"] = pd.to_numeric(d.get("hora_bucket", 0.0), errors="coerce").fillna(0.0)

    p_q1 = float(d["payout"].quantile(1/3)) if len(d) else 0.0
    p_q2 = float(d["payout"].quantile(2/3)) if len(d) else 0.0
    v_q1 = float(d["volatilidad"].quantile(1/3)) if len(d) else 0.0
    v_q2 = float(d["volatilidad"].quantile(2/3)) if len(d) else 0.0

    d["seg_payout"] = d["payout"].map(lambda x: _bucket_tercil(x, p_q1, p_q2))
    d["seg_vol"] = d["volatilidad"].map(lambda x: _bucket_tercil(x, v_q1, v_q2))
    d["seg_hora"] = d["hora_bucket"].map(_inferir_segmento_hora)
    d["seg_key"] = d["seg_payout"].astype(str) + "|" + d["seg_vol"].astype(str) + "|" + d["seg_hora"].astype(str)
    return d


def _gate_segmento_ok(bot: str, ctx: dict, ttl_s: float = 45.0):
    """Gate por segmento operativo (payout/vol/hora) para explotar zonas con señal y filtrar planas."""
    try:
        if not bool(globals().get("GATE_SEGMENTO_ENABLED", True)):
            return True, 0.5, 0, "off"

        seg_key = "NA|NA|NA"
        try:
            pb = str(ctx.get("seg_payout", "") or "").strip()
            vb = str(ctx.get("seg_vol", "") or "").strip()
            hs = str(ctx.get("seg_hora", "") or "").strip()
            if pb and vb and hs:
                seg_key = f"{pb}|{vb}|{hs}"
        except Exception:
            seg_key = "NA|NA|NA"

        now = time.time()
        key = f"{bot}|{seg_key}"
        c = _GATE_SEGMENTO_CACHE.get(key)
        if c and (now - float(c.get("ts", 0.0))) <= float(ttl_s):
            return bool(c.get("ok", True)), float(c.get("wr", 0.5)), int(c.get("n", 0)), str(c.get("seg", seg_key))

        ruta = f"registro_enriquecido_{bot}.csv"
        if not os.path.exists(ruta):
            return True, 0.5, 0, seg_key

        df = None
        for enc in ("utf-8", "latin-1", "windows-1252"):
            try:
                df = pd.read_csv(ruta, encoding=enc, on_bad_lines="skip")
                break
            except Exception:
                continue

        if df is None or df.empty:
            return True, 0.5, 0, seg_key

        if "trade_status" in df.columns:
            d = df[df["trade_status"].astype(str).str.upper().eq("CERRADO")].copy()
        else:
            d = df.copy()

        if "result_bin" not in d.columns:
            return True, 0.5, 0, seg_key

        d["result_bin"] = pd.to_numeric(d["result_bin"], errors="coerce")
        d = d[d["result_bin"].isin([0, 1])].copy()
        if d.empty:
            return True, 0.5, 0, seg_key

        d = _segmento_key_from_df(d)

        if int(GATE_SEGMENTO_LOOKBACK) > 0 and len(d) > int(GATE_SEGMENTO_LOOKBACK):
            d = d.tail(int(GATE_SEGMENTO_LOOKBACK)).copy()

        seg = d[d["seg_key"].astype(str).eq(str(seg_key))]
        n = int(len(seg))
        wr = float(seg["result_bin"].mean()) if n > 0 else 0.5
        ok = True
        if n >= int(GATE_SEGMENTO_MIN_MUESTRA):
            ok = bool(wr >= float(GATE_SEGMENTO_MIN_WR))

        _GATE_SEGMENTO_CACHE[key] = {"ts": now, "ok": ok, "wr": wr, "n": n, "seg": seg_key}
        return ok, wr, n, seg_key
    except Exception:
        return True, 0.5, 0, "NA|NA|NA"


def _ultimo_contexto_operativo_bot(bot: str) -> dict:
    """Lee contexto reciente (racha/es_rebote/activo) para gate de calidad por señal."""
    out = {"racha_actual": 0.0, "es_rebote": 0.0, "activo": "", "seg_payout": "", "seg_vol": "", "seg_hora": ""}
    try:
        row = leer_ultima_fila_features_para_pred(bot)
        if isinstance(row, dict):
            out["racha_actual"] = float(row.get("racha_actual", 0.0) or 0.0)
            out["es_rebote"] = float(row.get("es_rebote", 0.0) or 0.0)
            out["activo"] = str(row.get("activo", "") or "").strip()
            try:
                out["seg_payout"] = _bucket_tercil(float(row.get("payout", 0.0) or 0.0), 0.70, 0.82)
                out["seg_vol"] = _bucket_tercil(float(row.get("volatilidad", 0.0) or 0.0), 0.0008, 0.0018)
                out["seg_hora"] = _inferir_segmento_hora(float(row.get("hora_bucket", 0.0) or 0.0))
            except Exception:
                pass
            return out
    except Exception:
        pass

    # Fallback robusto: leer la última fila del CSV enriquecido
    try:
        ruta = f"registro_enriquecido_{bot}.csv"
        if not os.path.exists(ruta):
            return out
        for enc in ("utf-8", "latin-1", "windows-1252"):
            try:
                df = pd.read_csv(ruta, encoding=enc, on_bad_lines="skip")
                if df is None or df.empty:
                    continue
                last = df.iloc[-1].to_dict()
                out["racha_actual"] = float(last.get("racha_actual", 0.0) or 0.0)
                out["es_rebote"] = float(last.get("es_rebote", 0.0) or 0.0)
                out["activo"] = str(last.get("activo", "") or "").strip()
                try:
                    out["seg_payout"] = _bucket_tercil(float(last.get("payout", 0.0) or 0.0), 0.70, 0.82)
                    out["seg_vol"] = _bucket_tercil(float(last.get("volatilidad", 0.0) or 0.0), 0.0008, 0.0018)
                    out["seg_hora"] = _inferir_segmento_hora(float(last.get("hora_bucket", 0.0) or 0.0))
                except Exception:
                    pass
                break
            except Exception:
                continue
    except Exception:
        pass
    return out



def _score_regimen_contexto(ctx: dict) -> float:
    """Capa A del embudo: score 0..1 de calidad de régimen actual."""
    try:
        racha = float(ctx.get("racha_actual", 0.0) or 0.0)
        reb = float(ctx.get("es_rebote", 0.0) or 0.0)
        seg_p = str(ctx.get("seg_payout", "") or "")
        seg_h = str(ctx.get("seg_hora", "") or "")

        score = 0.50
        # racha positiva suma; racha muy negativa resta
        score += max(-0.18, min(0.18, 0.03 * racha))
        # rebote puede rescatar contextos negativos
        score += 0.08 if reb >= 0.5 else 0.0
        # payout bajo suele rendir peor
        if seg_p == "bajo":
            score -= 0.12
        elif seg_p == "alto":
            score += 0.04
        # franjas horarias menos estables -> leve castigo
        if seg_h in ("h00-05", "h18-23"):
            score -= 0.04

        return float(max(0.0, min(1.0, score)))
    except Exception:
        return 0.5


def _wilson_lower_bound(successes: int, n: int, z: float = 1.96) -> float:
    """Límite inferior Wilson (conservador) para probabilidad real."""
    try:
        n = int(n or 0)
        successes = int(successes or 0)
        if n <= 0:
            return 0.0
        p = float(successes) / float(n)
        den = 1.0 + (z * z / n)
        cen = (p + (z * z / (2.0 * n))) / den
        mar = (z * math.sqrt((p * (1.0 - p) / n) + (z * z / (4.0 * n * n)))) / den
        return float(max(0.0, min(1.0, cen - mar)))
    except Exception:
        return 0.0


def _prob_real_posterior(prob_model: float, regime_score: float, ev_n: int, ev_wr: float, ev_lb: float) -> float:
    """Posterior operativa: modelo + evidencia + régimen + bound conservador."""
    try:
        p = float(max(0.0, min(1.0, prob_model)))
        reg = float(max(0.0, min(1.0, regime_score)))
        n = int(max(0, ev_n or 0))
        wr = float(max(0.0, min(1.0, ev_wr or 0.0)))
        lb = float(max(0.0, min(1.0, ev_lb or 0.0)))

        # Peso de evidencia por tamaño muestral (N/(N+K))
        w = float(n) / float(n + int(POSTERIOR_EVIDENCE_K)) if n >= 0 else 0.0

        # 1) Mezcla modelo-histórico real
        p_mix = ((1.0 - w) * p) + (w * wr)

        # 2) Ajuste por régimen (score centrado en 0.5)
        reg_adj = 0.5 + ((reg - 0.5) * 0.8)
        p_reg = ((1.0 - float(POSTERIOR_REGIME_BLEND)) * p_mix) + (float(POSTERIOR_REGIME_BLEND) * reg_adj)

        # 3) Candado conservador: acercar a límite inferior cuando ya hay evidencia
        w_lb = min(0.45, w)
        p_post = ((1.0 - w_lb) * p_reg) + (w_lb * lb)

        return float(max(0.0, min(1.0, p_post)))
    except Exception:
        return float(max(0.0, min(1.0, prob_model or 0.0)))


def _evidencia_bot_umbral_objetivo(bot: str, force: bool = False) -> dict:
    """Resumen por bot en umbral objetivo (N, WR, Brier/ECE) para no inflar señales."""
    try:
        now = time.time()
        cache = globals().setdefault("_EVIDENCE_BOT_CACHE", {})
        key = f"{bot}|{float(IA_CALIB_GOAL_THRESHOLD):.4f}"
        c = cache.get(key)
        if c and (not force) and ((now - float(c.get("ts", 0.0))) <= float(EVIDENCE_CACHE_TTL_S)):
            return c

        rep = auditar_calibracion_seniales_reales(min_prob=float(IA_CALIB_GOAL_THRESHOLD)) or {}
        por_bot = rep.get("por_bot", {}) if isinstance(rep, dict) else {}
        b = por_bot.get(str(bot), {}) if isinstance(por_bot, dict) else {}

        n = int(b.get("n", 0) or 0)
        wr = float(b.get("win_rate", 0.0) or 0.0) if n > 0 else 0.0
        hits = int(round(wr * n)) if n > 0 else 0
        lb = _wilson_lower_bound(hits, n) if n > 0 else 0.0
        brier = b.get("brier", None)
        ece = b.get("ece", None)
        ok_hard = (n < int(EVIDENCE_MIN_N_HARD)) or ((wr >= float(EVIDENCE_MIN_WR_HARD)) and (lb >= float(EVIDENCE_MIN_LB_HARD)))

        out = {
            "ts": now,
            "n": n,
            "wr": wr,
            "hits": int(hits),
            "lb": float(lb),
            "brier": brier,
            "ece": ece,
            "ok_hard": bool(ok_hard),
            "goal": float(IA_CALIB_GOAL_THRESHOLD),
        }
        cache[key] = out
        return out
    except Exception:
        return {"ts": time.time(), "n": 0, "hits": 0, "wr": 0.0, "lb": 0.0, "brier": None, "ece": None, "ok_hard": True, "goal": float(IA_CALIB_GOAL_THRESHOLD)}


def _asset_runtime_snapshot(bot: str, activo: str, lookback: int = 80) -> dict:
    out = {"n": 0, "wr": 0.5, "wr_c1": 0.5, "avg_cycle": 1.0, "deep_ratio": 0.0, "pnl": 0.0, "consec_loss": 0, "drawdown": 0.0}
    try:
        ruta = f"registro_enriquecido_{bot}.csv"
        if not os.path.exists(ruta):
            return out
        df = _safe_read_csv_any_encoding(ruta)
        if df is None or df.empty or ("result_bin" not in df.columns):
            return out
        d = df.copy()
        if "trade_status" in d.columns:
            d = d[d["trade_status"].astype(str).str.upper().eq("CERRADO")]
        d["result_bin"] = pd.to_numeric(d["result_bin"], errors="coerce")
        d = d[d["result_bin"].isin([0, 1])]
        if activo and ("activo" in d.columns):
            d = d[d["activo"].astype(str).str.upper().eq(str(activo).upper())]
        if d.empty:
            return out
        if int(lookback) > 0 and len(d) > int(lookback):
            d = d.tail(int(lookback))

        ciclo_col = next((c for c in ("ciclo", "ciclo_actual", "marti_ciclo") if c in d.columns), None)
        if ciclo_col is not None:
            ciclos = pd.to_numeric(d[ciclo_col], errors="coerce").fillna(1.0)
        else:
            ciclos = pd.Series(1.0, index=d.index)

        pnl_col = next((c for c in ("ganancia_perdida", "pnl", "profit") if c in d.columns), None)
        if pnl_col is not None:
            pnl = pd.to_numeric(d[pnl_col], errors="coerce").fillna(0.0)
        else:
            pnl = pd.Series(np.where(pd.to_numeric(d["result_bin"], errors="coerce").fillna(0.0) > 0.5, 1.0, -1.0), index=d.index)

        y = pd.to_numeric(d["result_bin"], errors="coerce").fillna(0.0).astype(int)
        n = int(len(d))
        wr = float(y.mean()) if n > 0 else 0.5
        mask_c1 = ciclos <= 1.0
        wr_c1 = float(y[mask_c1].mean()) if int(mask_c1.sum()) > 0 else wr
        avg_cycle = float(ciclos.mean()) if n > 0 else 1.0
        deep_ratio = float((ciclos >= 4.0).mean()) if n > 0 else 0.0
        consec = 0
        for v in reversed(y.tolist()):
            if int(v) == 0:
                consec += 1
            else:
                break
        eq = pnl.cumsum()
        drawdown = float((eq - eq.cummax()).min()) if len(eq) > 0 else 0.0

        out.update({
            "n": n, "wr": wr, "wr_c1": wr_c1, "avg_cycle": avg_cycle, "deep_ratio": deep_ratio,
            "pnl": float(pnl.sum()), "consec_loss": int(consec), "drawdown": drawdown,
        })
        return out
    except Exception:
        return out


def _log_operational_degradation_runtime(ttl_s: float = 60.0):
    try:
        now = time.time()
        cache = globals().get("_ASSET_RUNTIME_LOG_CACHE", {}) or {}
        if (now - float(cache.get("ts", 0.0))) < float(ttl_s):
            return
        rows = []
        for b in BOT_NAMES:
            ruta = f"registro_enriquecido_{b}.csv"
            if not os.path.exists(ruta):
                continue
            df = _safe_read_csv_any_encoding(ruta)
            if df is None or df.empty or ("result_bin" not in df.columns):
                continue
            d = df.copy()
            if "trade_status" in d.columns:
                d = d[d["trade_status"].astype(str).str.upper().eq("CERRADO")]
            if d.empty:
                continue
            if "activo" in d.columns:
                activos = [str(x).strip().upper() for x in d["activo"].dropna().unique().tolist() if str(x).strip()]
            else:
                activos = [""]
            for a in activos[:12]:
                s = _asset_runtime_snapshot(b, a, lookback=int(ASSET_PROTECT_LOOKBACK))
                if int(s.get("n", 0)) >= 8:
                    rows.append((a or "NA", b, s))
        if not rows:
            globals()["_ASSET_RUNTIME_LOG_CACHE"] = {"ts": now, "sig": "empty"}
            return
        rows_sorted = sorted(rows, key=lambda t: float(t[2].get("pnl", 0.0)))
        worst = rows_sorted[0]
        best = rows_sorted[-1]
        wr_vals = [float(r[2].get("wr_c1", 0.5)) for r in rows]
        cyc_vals = [float(r[2].get("avg_cycle", 1.0)) for r in rows]
        deep_vals = [float(r[2].get("deep_ratio", 0.0)) for r in rows]
        pnl_vals = [float(r[2].get("pnl", 0.0)) for r in rows]
        sig = f"{worst[0]}:{worst[1]}:{worst[2].get('pnl',0):.2f}|{best[0]}:{best[1]}:{best[2].get('pnl',0):.2f}|{sum(pnl_vals):.2f}"
        if sig != str(cache.get("sig", "")) or (now - float(cache.get("ts", 0.0))) >= float(max(20.0, ttl_s)):
            agregar_evento(
                "📊 Degradación vivo: "
                f"WR_C1={np.mean(wr_vals)*100:.1f}% ciclo={np.mean(cyc_vals):.2f} C4+={np.mean(deep_vals)*100:.1f}% "
                f"PnL_roll={sum(pnl_vals):+.2f} | peor={worst[0]}/{worst[1]} {worst[2]['pnl']:+.2f} "
                f"mejor={best[0]}/{best[1]} {best[2]['pnl']:+.2f}"
            )
            if (np.mean(wr_vals) < 0.46) or (np.mean(deep_vals) > 0.50) or (sum(pnl_vals) < 0.0):
                agregar_evento("🚨 Alerta degradación: calidad operativa en caída (WR_C1/PnL/C4+).")
        globals()["_ASSET_RUNTIME_LOG_CACHE"] = {"ts": now, "sig": sig}
    except Exception:
        pass


def _gate_regimen_activo_ok(bot: str, activo: str = "", ttl_s: float = 45.0):
    """Valida régimen por activo reciente (HZ10/HZ25/HZ50/HZ75) para no mezclar contextos."""
    try:
        now = time.time()
        asset_key = str(activo or "*").strip().upper()
        key = f"{bot}|{asset_key}"
        c = _GATE_ACTIVO_CACHE.get(key)
        if c and (now - float(c.get("ts", 0.0))) <= float(ttl_s):
            return bool(c.get("ok", True)), float(c.get("wr", 0.5)), int(c.get("n", 0))

        ruta = f"registro_enriquecido_{bot}.csv"
        if not os.path.exists(ruta):
            return True, 0.5, 0

        df = None
        for enc in ("utf-8", "latin-1", "windows-1252"):
            try:
                df = pd.read_csv(ruta, encoding=enc, on_bad_lines="skip")
                break
            except Exception:
                continue
        if df is None or df.empty:
            return True, 0.5, 0

        if "trade_status" in df.columns:
            d = df[df["trade_status"].astype(str).str.upper().eq("CERRADO")].copy()
        else:
            d = df.copy()

        if "result_bin" not in d.columns:
            return True, 0.5, 0

        d["result_bin"] = pd.to_numeric(d["result_bin"], errors="coerce")
        d = d[d["result_bin"].isin([0, 1])]

        if activo and "activo" in d.columns:
            d = d[d["activo"].astype(str).str.upper().eq(str(activo).upper())]

        if int(GATE_ACTIVO_LOOKBACK) > 0 and len(d) > int(GATE_ACTIVO_LOOKBACK):
            d = d.tail(int(GATE_ACTIVO_LOOKBACK))

        n = int(len(d))
        wr = float(d["result_bin"].mean()) if n > 0 else 0.5
        ok = True
        if n >= int(GATE_ACTIVO_MIN_MUESTRA):
            ok = bool(wr >= float(GATE_ACTIVO_MIN_WR))

        if bool(ASSET_PROTECT_ENABLE):
            cd = _ASSET_COOLDOWN_STATE.get(key, {}) if isinstance(_ASSET_COOLDOWN_STATE.get(key, {}), dict) else {}
            until = float(cd.get("until", 0.0) or 0.0)
            if until > now:
                ok = False
            snap = _asset_runtime_snapshot(bot, asset_key if asset_key != "*" else "", lookback=int(ASSET_PROTECT_LOOKBACK))
            if int(snap.get("n", 0)) >= max(12, int(ASSET_PROTECT_LOOKBACK * 0.4)):
                reasons = []
                if int(snap.get("consec_loss", 0)) >= int(ASSET_MAX_CONSEC_LOSS):
                    reasons.append(f"loss_streak>={int(ASSET_MAX_CONSEC_LOSS)}")
                if float(snap.get("drawdown", 0.0)) <= float(ASSET_MAX_DRAWDOWN):
                    reasons.append(f"drawdown<={float(ASSET_MAX_DRAWDOWN):.2f}")
                if float(snap.get("wr", 0.5)) < float(ASSET_MIN_WR):
                    reasons.append(f"wr<{float(ASSET_MIN_WR):.2f}")
                if float(snap.get("deep_ratio", 0.0)) > float(ASSET_MAX_DEEP_CYCLE_RATIO):
                    reasons.append(f"c4+>{float(ASSET_MAX_DEEP_CYCLE_RATIO):.2f}")
                if reasons:
                    until_new = now + float(ASSET_COOLDOWN_S)
                    prev_until = float(cd.get("until", 0.0) or 0.0)
                    _ASSET_COOLDOWN_STATE[key] = {"until": until_new, "reasons": reasons, "last_log": now}
                    ok = False
                    if (prev_until <= now) or ((now - float(cd.get("last_log", 0.0) or 0.0)) >= float(ASSET_ALERT_COOLDOWN_S)):
                        agregar_evento(
                            f"🧯 Asset cooldown ON {bot}/{asset_key}: {','.join(reasons)} "
                            f"| wr={snap['wr']*100:.1f}% c1={snap['wr_c1']*100:.1f}% deep={snap['deep_ratio']*100:.1f}% dd={snap['drawdown']:.2f}."
                        )
                elif until > 0.0 and until <= now:
                    _ASSET_COOLDOWN_STATE[key] = {"until": 0.0, "reasons": [], "last_log": now}
                    agregar_evento(f"✅ Asset cooldown OFF {bot}/{asset_key}: métrica recuperada.")

        _GATE_ACTIVO_CACHE[key] = {"ts": now, "ok": ok, "wr": wr, "n": n}
        return ok, wr, n
    except Exception:
        return True, 0.5, 0


def _leer_base_rate_y_n70(ttl_s: float = 30.0):
    """
    Lee métricas rápidas desde ia_signals_log para estabilizar operación:
    - base_rate rolling en cierres recientes (y en {0,1})
    - n70: cantidad de cierres con prob >= IA_CALIB_GOAL_THRESHOLD
    Cacheado para no cargar CSV en cada tick.
    """
    global _IA_RUNTIME_CAL_CACHE
    now = time.time()
    try:
        if (now - float(_IA_RUNTIME_CAL_CACHE.get("ts", 0.0))) <= float(ttl_s):
            return float(_IA_RUNTIME_CAL_CACHE.get("base_rate", 0.5)), int(_IA_RUNTIME_CAL_CACHE.get("n70", 0))

        _ensure_ia_signals_log()
        df = _safe_read_csv_any_encoding(IA_SIGNALS_LOG)
        base_rate = 0.5
        n70 = 0

        if df is not None and not df.empty and ("y" in df.columns):
            y = pd.to_numeric(df["y"], errors="coerce")
            mask_closed = y.isin([0, 1])
            d = df.loc[mask_closed].copy()
            if not d.empty:
                yv = pd.to_numeric(d["y"], errors="coerce")
                tail = yv.tail(int(max(20, IA_BASE_RATE_WINDOW)))
                if len(tail) > 0:
                    base_rate = float(tail.mean())

                if "prob" in d.columns:
                    pv = pd.to_numeric(d["prob"], errors="coerce")
                    n70 = int(((pv >= float(IA_CALIB_GOAL_THRESHOLD)) & yv.isin([0, 1])).sum())

        _IA_RUNTIME_CAL_CACHE = {"ts": now, "base_rate": float(base_rate), "n70": int(n70)}
        return float(base_rate), int(n70)
    except Exception:
        return 0.5, 0


_IA_ORIENTATION_CACHE = {"ts": 0.0, "invert": False, "auc": None, "auc_flip": None, "source": "none"}
_DIAG_RUNTIME_GATE_CACHE = {"ts": 0.0, "max_gap": 0.0, "n75": 0, "force_evidence": False}

def _leer_gate_desde_diagnostico(ttl_s: float = 60.0) -> dict:
    """Lee guardas operativas desde diagnostico_pipeline_ia.json."""
    global _DIAG_RUNTIME_GATE_CACHE
    now = time.time()
    try:
        if (now - float(_DIAG_RUNTIME_GATE_CACHE.get("ts", 0.0))) <= float(ttl_s):
            return dict(_DIAG_RUNTIME_GATE_CACHE)

        out = {"ts": now, "max_gap": 0.0, "n75": 0, "force_evidence": False}
        if os.path.exists(DIAG_PATH):
            with open(DIAG_PATH, "r", encoding="utf-8", errors="replace") as f:
                diag = json.load(f)
            sig = (diag or {}).get("signals", {}) if isinstance(diag, dict) else {}
            out["max_gap"] = float(sig.get("max_gap_abs_high_bins", 0.0) or 0.0)
            out["n75"] = int((sig.get("by_threshold", {}).get("0.75", {}) or {}).get("n", 0) or 0)
            out["force_evidence"] = (out["max_gap"] > float(HARD_GATE_MAX_GAP_HIGH_BINS)) or (out["n75"] < int(HARD_GATE_MIN_N_FOR_HIGH_THR))

        _DIAG_RUNTIME_GATE_CACHE = out
        return dict(out)
    except Exception:
        return {"ts": now, "max_gap": 0.0, "n75": 0, "force_evidence": False}


def _resolver_orientacion_runtime(ttl_s: float = ORIENTATION_RECHECK_S) -> dict:
    """
    Determina si conviene invertir p->1-p con evidencia cerrada (mismo set p vs 1-p).
    Regla conservadora: jamás invertir por heurística de model_meta con n bajo.
    """
    global _IA_ORIENTATION_CACHE
    now = time.time()
    try:
        if (now - float(_IA_ORIENTATION_CACHE.get("ts", 0.0))) <= float(ttl_s):
            return dict(_IA_ORIENTATION_CACHE)

        inv = False
        auc = None
        auc_flip = None
        source = "none"

        # En warmup/experimental, no forzar inversión de orientación:
        # evita voltear señales verdes recientes por histórico viejo/no estable.
        if bool(ORIENTATION_REQUIRE_RELIABLE_MODEL):
            meta = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
            n_samples = int(meta.get("n_samples", meta.get("n", 0)) or 0)
            warmup = bool(meta.get("warmup_mode", n_samples < int(TRAIN_WARMUP_MIN_ROWS)))
            reliable = bool(meta.get("reliable", False)) and (not warmup)
            if not reliable:
                _IA_ORIENTATION_CACHE = {"ts": now, "invert": False, "auc": None, "auc_flip": None, "source": "model_unreliable"}
                return dict(_IA_ORIENTATION_CACHE)

        _ensure_ia_signals_log()
        df = _safe_read_csv_any_encoding(IA_SIGNALS_LOG)
        if df is not None and not df.empty and {"prob", "y"}.issubset(df.columns):
            y = pd.to_numeric(df["y"], errors="coerce")
            p = pd.to_numeric(df["prob"], errors="coerce")
            m = y.isin([0, 1]) & p.notna()
            yy = y[m].astype(int)
            pp = p[m].astype(float)
            n = int(len(yy))
            if n >= int(ORIENTATION_MIN_CLOSED) and len(set(yy.tolist())) >= 2:
                auc = float(roc_auc_score(yy, pp))
                auc_flip = float(roc_auc_score(yy, 1.0 - pp))
                if (auc_flip - auc) >= float(ORIENTATION_FLIP_MIN_DELTA):
                    inv = True
                source = "signals"

        _IA_ORIENTATION_CACHE = {"ts": now, "invert": bool(inv), "auc": auc, "auc_flip": auc_flip, "source": source}
        return dict(_IA_ORIENTATION_CACHE)
    except Exception:
        return {"ts": now, "invert": False, "auc": None, "auc_flip": None, "source": "error"}


def _aplicar_orientacion_prob(prob: float | None) -> float | None:
    try:
        if not isinstance(prob, (int, float)):
            return prob
        p = max(0.0, min(1.0, float(prob)))
        ori = _resolver_orientacion_runtime()
        if bool(ori.get("invert", False)):
            return float(max(0.0, min(1.0, 1.0 - p)))
        return p
    except Exception:
        return prob


def _ajustar_prob_operativa(prob: float | None) -> float | None:
    """
    Shrinkage anti-sobreconfianza: p_ajustada = a*p + (1-a)*tasa_base_rolling.
    Regla anti-aplastamiento:
      - En warmup o con pocas señales cerradas, NO se aplica shrink para evitar
        colapsar todo alrededor de la tasa base (síntoma típico: 32.x% repetido).
    """
    try:
        if not isinstance(prob, (int, float)):
            return prob
        p = max(0.0, min(1.0, float(prob)))

        base_rate, n70 = _leer_base_rate_y_n70(ttl_s=30.0)

        # Si aún no hay suficiente evidencia cerrada o el modelo sigue en warmup,
        # devolvemos p cruda calibrada (sin shrink).
        try:
            meta = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
            n_samples = int(meta.get("n_samples", meta.get("n", 0)) or 0)
            warmup = bool(meta.get("warmup_mode", n_samples < int(TRAIN_WARMUP_MIN_ROWS)))
        except Exception:
            n_samples = 0
            warmup = True

        if warmup or int(n70) < int(max(MIN_IA_SENIALES_CONF, 12)):
            return p

        # Alpha adaptativo por calibración reciente:
        # - sube un poco cuando el modelo está estable y bien calibrado
        # - baja cuando hay inflación fuerte (PredMedia >> Real)
        a = float(IA_SHRINK_ALPHA)
        try:
            rep = auditar_calibracion_seniales_reales(min_prob=float(IA_CALIB_THRESHOLD)) or {}
            n = int(rep.get("n", 0) or 0)
            infl_pp = float(rep.get("inflacion_pp", 0.0) or 0.0)
            pred_mean = float(rep.get("avg_pred", 0.0) or 0.0)
            win_rate = float(rep.get("win_rate", 0.0) or 0.0)

            if n < int(MIN_IA_SENIALES_CONF):
                a -= 0.10
            else:
                if infl_pp > float(SEM_CAL_INFL_WARN_PP) and pred_mean > win_rate:
                    a -= 0.12
                elif (abs(infl_pp) <= float(SEM_CAL_INFL_OK_PP)) and (n >= int(max(50, IA_CALIB_MIN_CLOSED // 2))):
                    a += 0.08
        except Exception:
            pass

        a = max(float(IA_SHRINK_ALPHA_MIN), min(float(IA_SHRINK_ALPHA_MAX), float(a)))
        p_adj = (a * p) + ((1.0 - a) * float(base_rate))
        return max(0.0, min(1.0, float(p_adj)))
    except Exception:
        return prob


def _ajustar_prob_por_evidencia_bot(bot: str, prob: float | None) -> float | None:
    """
    Ajuste leve por evidencia específica del bot para mejorar discriminación
    cuando el modelo queda plano entre varios bots.

    - Usa WR suavizado (Beta(1,1)) del bot (ganancias/pérdidas en memoria).
    - Si el input del bot fue marcado como redundante en el tick, reduce el efecto.
    - Ajuste acotado: máximo ±2pp para no romper calibración global.
    """
    try:
        if not isinstance(prob, (int, float)):
            return prob
        p = max(0.0, min(1.0, float(prob)))

        st = estado_bots.get(bot, {}) if isinstance(estado_bots, dict) else {}
        g = int(st.get("ganancias", 0) or 0)
        d = int(st.get("perdidas", 0) or 0)
        n = max(0, g + d)

        # WR suavizado para no sobre-reaccionar con n bajo.
        wr = float((g + 1.0) / (n + 2.0))
        edge = float(max(-0.20, min(0.20, wr - 0.50)))

        # Peso crece con muestra, saturando en n=120.
        w = min(1.0, float(n) / 120.0)
        delta = float(edge * w * 0.10)  # máx teórico ±2pp

        # Si la entrada fue redundante este tick, hacemos el ajuste más conservador.
        if bool(st.get("ia_input_redundante", False)):
            delta *= 0.35

        p2 = float(max(0.0, min(1.0, p + delta)))
        return p2
    except Exception:
        return prob




def _to_win01(v) -> int | None:
    """Normaliza resultado a {1=win,0=loss,None}."""
    try:
        if v is None:
            return None
        if isinstance(v, (int, float)):
            fv = float(v)
            if fv == 1.0:
                return 1
            if fv == 0.0:
                return 0
        s = str(v).strip()
        if not s:
            return None
        if s in ("✓", "1", "WIN", "G", "GANANCIA"):
            return 1
        if s in ("✗", "0", "LOSS", "L", "PÉRDIDA", "PERDIDA"):
            return 0
        nr = normalizar_resultado(s)
        if nr == "GANANCIA":
            return 1
        if nr == "PÉRDIDA":
            return 0
    except Exception:
        pass
    return None


def _ajustar_prob_por_racha_reciente(bot: str, prob: float | None) -> float | None:
    """Micro-ajuste por racha reciente para reducir planicie de probabilidad en runtime."""
    try:
        if not bool(IA_RACHA_BOOST_ENABLE):
            return prob
        if not isinstance(prob, (int, float)):
            return prob
        p = max(0.0, min(1.0, float(prob)))

        st = estado_bots.get(bot, {}) if isinstance(estado_bots, dict) else {}
        res = st.get("resultados", [])
        if not isinstance(res, list) or len(res) == 0:
            return p

        w = max(4, int(IA_RACHA_BOOST_WINDOW))
        tail_raw = res[-w:]
        tail = []
        for x in tail_raw:
            y = _to_win01(x)
            if y in (0, 1):
                tail.append(y)

        if len(tail) < 4:
            return p

        wins = int(sum(tail))
        losses = int(len(tail) - wins)
        wr = float(wins / max(1, len(tail)))

        streak = 0
        for y in reversed(tail):
            if y == 1:
                streak += 1
            else:
                break

        # Núcleo: edge vs 50% + bono por racha terminal de wins
        edge = max(-0.5, min(0.5, wr - 0.5))
        delta = edge * 0.12
        if wins >= int(IA_RACHA_BOOST_MIN_WINS):
            delta += min(0.03, 0.01 * float(streak))

        # Protección: con n corto, hacer ajuste más suave
        n_eff = float(len(tail)) / float(max(1, w))
        delta *= max(0.60, min(1.0, n_eff))

        up = float(max(0.0, IA_RACHA_BOOST_MAX_UP))
        dn = float(max(0.0, IA_RACHA_BOOST_MAX_DN))
        delta = max(-dn, min(up, float(delta)))

        p2 = float(max(0.0, min(1.0, p + delta)))

        # Seguimiento específico de fulll45
        if str(bot) == "fulll45":
            global _IA_BOT45_TRACE_CACHE
            now = time.time()
            last_ts = float(_IA_BOT45_TRACE_CACHE.get("ts", 0.0) or 0.0)
            if (now - last_ts) >= float(IA_RACHA_BOOST_LOG_COOLDOWN_S):
                msg = (
                    f"🔎 BOT45 racha: wins={wins}/{len(tail)} streak={streak} "
                    f"p_base={p*100:.1f}% -> p_racha={p2*100:.1f}% (Δ={delta*100:+.1f}pp)"
                )
                _ag_evt(msg)
                _IA_BOT45_TRACE_CACHE = {"ts": now, "msg": msg}

        return p2
    except Exception:
        return prob


def _get_overconf_guardrail_state(force: bool = False, ttl_s: float = 15.0) -> dict:
    """Estado de sobreconfianza en bucket alto para aplicar cap temporal."""
    global _IA_OVERCONF_CACHE
    now = time.time()
    try:
        if (not force) and ((now - float(_IA_OVERCONF_CACHE.get("ts", 0.0) or 0.0)) <= float(ttl_s)):
            return dict(_IA_OVERCONF_CACHE)

        rep = auditar_calibracion_seniales_reales(min_prob=float(IA_OVERCONF_BUCKET_MIN_PROB)) or {}
        n = int(rep.get("n", 0) or 0)
        avg_pred = rep.get("avg_pred", None)
        win_rate = rep.get("win_rate", None)
        if isinstance(avg_pred, (int, float)) and isinstance(win_rate, (int, float)):
            gap_pp = float((float(avg_pred) - float(win_rate)) * 100.0)
            gap_abs = float(abs(float(avg_pred) - float(win_rate)))
        else:
            gap_pp = 0.0
            gap_abs = 0.0

        active = bool((n >= int(IA_OVERCONF_MIN_N)) and (gap_abs >= float(IA_OVERCONF_GAP_MAX_PP)) and (gap_pp > 0.0))
        out = {
            "ts": now,
            "active": bool(active),
            "cap": float(IA_OVERCONF_DYNAMIC_CAP if active else 1.0),
            "n": int(n),
            "gap_pp": float(gap_pp),
        }
        _IA_OVERCONF_CACHE = out
        return dict(out)
    except Exception:
        return dict(_IA_OVERCONF_CACHE)


def _estado_guardrail_ia_fuerte(force: bool = False, ttl_s: float = 20.0) -> dict:
    """Guardrail global por niveles (RED/AMBER/GREEN) con histéresis para evitar parpadeos."""
    global _IA_HARD_GUARD_CACHE, _IA_HARD_GUARD_LOG_TS
    now = time.time()
    out = {
        "ts": now,
        "active": False,
        "cap": 1.0,
        "level": "GREEN",
        "closed": 0,
        "auc": 0.0,
        "reliable": False,
        "features": 0,
        "reasons": [],
        "until": 0.0,
    }
    try:
        if not bool(IA_HARD_GUARD_ENABLE):
            _IA_HARD_GUARD_CACHE = dict(out)
            return out

        cache = _IA_HARD_GUARD_CACHE if isinstance(_IA_HARD_GUARD_CACHE, dict) else {}
        if (not force) and ((now - float(cache.get("ts", 0.0) or 0.0)) <= float(ttl_s)):
            return dict(cache)

        meta = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
        auc = float(meta.get("auc", 0.0) or 0.0)
        reliable = bool(meta.get("reliable", False))
        n_samples_meta = int(meta.get("n_samples", meta.get("n", 0)) or 0)
        feats = meta.get("feature_names", [])
        feat_count = len(feats) if isinstance(feats, list) else 0
        model_ready_for_auc = bool((n_samples_meta >= int(max(1, MIN_FIT_ROWS_LOW))) and (auc > 0.0))

        rep_all = auditar_calibracion_seniales_reales(min_prob=float(IA_CALIB_THRESHOLD)) or {}
        closed = int(rep_all.get("n_total_closed", rep_all.get("n", 0)) or 0)

        rep90 = auditar_calibracion_seniales_reales(min_prob=float(IA_OVERCONF_BUCKET_MIN_PROB)) or {}
        n90 = int(rep90.get("n", 0) or 0)
        avg90 = rep90.get("avg_pred", None)
        wr90 = rep90.get("win_rate", None)
        gap90 = 0.0
        if isinstance(avg90, (int, float)) and isinstance(wr90, (int, float)):
            gap90 = float(avg90) - float(wr90)

        severe_gap = bool((n90 >= int(IA_HARD_GUARD_SEVERE_GAP_MIN_N)) and (gap90 >= float(IA_HARD_GUARD_SEVERE_OVERCONF_GAP_PP)))
        amber_gap = bool((n90 >= int(IA_HARD_GUARD_SEVERE_GAP_MIN_N)) and (gap90 >= float(IA_HARD_GUARD_AMBER_OVERCONF_GAP_PP)))

        reasons = []
        if closed < int(IA_HARD_GUARD_RED_MIN_CLOSED):
            reasons.append(f"HG:CLOSED<{int(IA_HARD_GUARD_RED_MIN_CLOSED)}")
        if (not bool(IA_HARD_GUARD_RED_REQUIRE_MODEL_READY) or model_ready_for_auc) and (auc < float(IA_HARD_GUARD_RED_MIN_AUC)):
            reasons.append(f"HG:AUC<{float(IA_HARD_GUARD_RED_MIN_AUC):.2f}")
        if not reliable:
            reasons.append("HG:REL=false")
        if feat_count > 0 and feat_count < int(IA_HARD_GUARD_MIN_FEATURES_RED):
            reasons.append(f"HG:FEATS<{int(IA_HARD_GUARD_MIN_FEATURES_RED)}")
        if severe_gap:
            reasons.append(f"HG:GAP90>={float(IA_HARD_GUARD_SEVERE_OVERCONF_GAP_PP)*100:.0f}pp")

        level = "GREEN"
        cap = 1.0
        hard_block = False

        red_cond = bool(
            (closed < int(IA_HARD_GUARD_RED_MIN_CLOSED))
            or (((not bool(IA_HARD_GUARD_RED_REQUIRE_MODEL_READY)) or model_ready_for_auc) and (auc < float(IA_HARD_GUARD_RED_MIN_AUC)))
            or (feat_count > 0 and feat_count < int(IA_HARD_GUARD_MIN_FEATURES_RED))
            or severe_gap
        )
        amber_cond = bool(
            (closed < int(IA_HARD_GUARD_AMBER_MIN_CLOSED))
            or (not reliable)
            or amber_gap
        )
        green_cond = bool(
            (closed >= int(IA_HARD_GUARD_AMBER_MIN_CLOSED))
            and reliable
            and (auc >= float(IA_HARD_GUARD_GREEN_MIN_AUC))
            and (feat_count >= int(IA_HARD_GUARD_MIN_FEATURES_GREEN))
            and ((n90 < int(IA_HARD_GUARD_SEVERE_GAP_MIN_N)) or (gap90 < float(IA_HARD_GUARD_GREEN_MAX_GAP_PP)))
        )

        if red_cond:
            level = "RED"
            cap = float(IA_HARD_GUARD_RED_CAP)
            hard_block = True
        elif amber_cond and (not green_cond):
            level = "AMBER"
            cap = float(IA_HARD_GUARD_AMBER_CAP)
            if amber_gap:
                reasons.append(f"HG:GAP90>={float(IA_HARD_GUARD_AMBER_OVERCONF_GAP_PP)*100:.0f}pp")
        else:
            level = "GREEN"
            cap = 1.0

        # Histéresis: una vez activo, mantener hasta que venza la ventana o se fuerce.
        prev_level = str(cache.get("level", "GREEN") or "GREEN").upper()
        prev_until = float(cache.get("until", 0.0) or 0.0)
        if (not force) and (prev_level in {"RED", "AMBER"}) and (now < prev_until) and (level == "GREEN"):
            level = prev_level
            cap = float(cache.get("cap", IA_HARD_GUARD_AMBER_CAP) or IA_HARD_GUARD_AMBER_CAP)
            hard_block = bool(level == "RED")
            reasons = list(cache.get("reasons", []) or ["HG:HOLD"])

        until_ts = now + float(IA_HARD_GUARD_HYSTERESIS_S) if level in {"RED", "AMBER"} else 0.0

        out.update({
            "active": bool(level in {"RED", "AMBER"}),
            "cap": float(max(0.0, min(1.0, cap))),
            "level": str(level),
            "closed": int(closed),
            "auc": float(auc),
            "reliable": bool(reliable),
            "features": int(feat_count),
            "reasons": list(dict.fromkeys(reasons)),
            "until": float(until_ts),
            "hard_block": bool(hard_block),
            "n90": int(n90),
            "gap90_pp": float(gap90 * 100.0),
        })
        _IA_HARD_GUARD_CACHE = dict(out)

        if out["active"] and ((now - float(_IA_HARD_GUARD_LOG_TS or 0.0)) >= float(IA_HARD_GUARD_LOG_COOLDOWN_S)):
            _IA_HARD_GUARD_LOG_TS = now
            try:
                _ag_evt(
                    f"🧱 IA hard-guard {out['level']}: cap_oper<={out['cap']*100:.1f}% "
                    f"(closed={out['closed']}, auc={out['auc']:.3f}, feats={out['features']}, why={','.join(out['reasons'])})."
                )
            except Exception:
                pass

        return dict(out)
    except Exception:
        return dict(_IA_HARD_GUARD_CACHE if isinstance(_IA_HARD_GUARD_CACHE, dict) else out)


def _estado_guardrail_ia_bot(bot: str, force: bool = False, ttl_s: float = 25.0) -> dict:
    """Penalización por bot cuando su historial de falsas altas sugiere sobreconfianza local."""
    global _IA_HARD_GUARD_BOT_CACHE
    now = time.time()
    out = {"active": False, "cap": 1.0, "reasons": [], "n": 0, "gap_pp": 0.0}
    try:
        cache = _IA_HARD_GUARD_BOT_CACHE if isinstance(_IA_HARD_GUARD_BOT_CACHE, dict) else {}
        if (not force) and ((now - float(cache.get("ts", 0.0) or 0.0)) <= float(ttl_s)):
            data = cache.get("data", {}) if isinstance(cache.get("data", {}), dict) else {}
            if isinstance(data.get(str(bot)), dict):
                return dict(data.get(str(bot)))
            return out

        rows = _safe_read_csv_any_encoding(IA_SIGNALS_LOG)
        data = {}
        if rows is not None and (not rows.empty) and {"bot", "prob", "y"}.issubset(rows.columns):
            d = rows.copy()
            d["prob"] = pd.to_numeric(d["prob"], errors="coerce")
            y_num = pd.to_numeric(d["y"], errors="coerce")
            y_txt = d["y"].astype(str).str.strip().str.upper()
            y_num = y_num.where(
                ~y_num.isna(),
                np.where(y_txt.str.contains(r"GAN|WIN|✓"), 1.0, np.where(y_txt.str.contains(r"PERD|PÉRD|LOSS|✗"), 0.0, np.nan))
            )
            d["y"] = np.where(pd.isna(y_num), np.nan, np.where(y_num >= 0.5, 1, 0))
            d = d[d["y"].isin([0, 1])].copy()
            d["bot"] = d["bot"].astype(str).str.strip()

            for b, gb in d.groupby("bot"):
                gb2 = gb[gb["prob"] >= float(IA_OVERCONF_BUCKET_MIN_PROB)].copy()
                n = int(len(gb2))
                if n <= 0:
                    data[str(b)] = dict(out)
                    continue
                pred = float(gb2["prob"].mean())
                wr = float(gb2["y"].mean())
                gap = float(pred - wr)
                active = bool((n >= int(IA_HARD_GUARD_BOT_MIN_N)) and (gap >= float(IA_HARD_GUARD_BOT_GAP_PP)))
                cap = 1.0
                reasons = []
                if active:
                    cap = float(min(0.72, 1.0 - min(0.20, gap * 0.35)))
                    reasons = [f"HG:{str(b).upper()}:GAP90={gap*100.0:.1f}pp"]
                data[str(b)] = {
                    "active": bool(active),
                    "cap": float(max(0.0, min(1.0, cap))),
                    "reasons": reasons,
                    "n": int(n),
                    "gap_pp": float(gap * 100.0),
                }

        _IA_HARD_GUARD_BOT_CACHE = {"ts": now, "data": data}
        if isinstance(data.get(str(bot)), dict):
            return dict(data.get(str(bot)))
        return out
    except Exception:
        return out


def _cap_prob_por_guardrail_ia_fuerte(prob: float | None, bot: str | None = None) -> float | None:
    """Cap solo operativa: no altera p_raw/p_pre diagnósticas, solo p_oper para auto/real."""
    try:
        if not isinstance(prob, (int, float)):
            return prob
        p = max(0.0, min(1.0, float(prob)))
        st = _estado_guardrail_ia_fuerte(force=False)
        cap = 1.0
        if bool(st.get("active", False)):
            cap = float(min(cap, float(st.get("cap", 1.0) or 1.0)))
        if isinstance(bot, str) and bot:
            sb = _estado_guardrail_ia_bot(bot, force=False)
            if bool(sb.get("active", False)):
                cap = float(min(cap, float(sb.get("cap", 1.0) or 1.0)))
        return float(min(p, max(0.0, min(1.0, cap))))
    except Exception:
        return prob


def _prob_ia_operativa_bot(bot: str, default: float | None = None) -> float | None:
    try:
        st = estado_bots.get(bot, {}) if isinstance(estado_bots, dict) else {}
        p_oper = st.get("prob_ia_oper", None)
        if isinstance(p_oper, (int, float)) and np.isfinite(float(p_oper)):
            return float(p_oper)
        p = st.get("prob_ia", default)
        if isinstance(p, (int, float)) and np.isfinite(float(p)):
            return float(p)
        return default
    except Exception:
        return default


def _maybe_emit_calibration_checkpoint(force: bool = False) -> None:
    """Emitir checkpoint compacto cada +IA_CHECKPOINT_CLOSED_STEP cierres reales."""
    global _IA_CHECKPOINT_CACHE
    try:
        now = time.time()
        rep = auditar_calibracion_seniales_reales(min_prob=float(IA_CALIB_THRESHOLD)) or {}
        closed = int(rep.get("n_total_closed", rep.get("n", 0)) or 0)
        step = max(1, int(IA_CHECKPOINT_CLOSED_STEP))
        last_closed = int(_IA_CHECKPOINT_CACHE.get("last_closed", 0) or 0)
        last_ts = float(_IA_CHECKPOINT_CACHE.get("last_ts", 0.0) or 0.0)

        if (not force):
            if (closed - last_closed) < step:
                return
            if (now - last_ts) < 20.0:
                return

        wr = rep.get("win_rate", None)
        ap = rep.get("avg_pred", None)
        ece = rep.get("ece", None)
        brier = rep.get("brier", None)
        msg = (
            f"📊 IA checkpoint: cerradas={closed} | "
            f"Pred={((float(ap)*100.0) if isinstance(ap,(int,float)) else 0.0):.1f}% | "
            f"Real={((float(wr)*100.0) if isinstance(wr,(int,float)) else 0.0):.1f}% | "
            f"ECE={float(ece):.3f} | Brier={float(brier):.3f}"
        )
        _ag_evt(msg)

        high = _get_overconf_guardrail_state(force=True)
        if bool(high.get("active", False)):
            _ag_evt(
                "🛡️ IA guardrail: sobreconfianza alta detectada "
                f"(n90={int(high.get('n',0))}, gap={float(high.get('gap_pp',0.0)):+.1f}pp). "
                f"Cap temporal <= {float(high.get('cap',1.0))*100.0:.1f}%."
            )

        _IA_CHECKPOINT_CACHE = {"last_closed": int(closed), "last_ts": now}
    except Exception:
        pass


def _cap_prob_por_sobreconfianza(prob: float | None) -> float | None:
    """Cap dinámico cuando el bucket 90-100% se descalibra por sobreestimación."""
    try:
        if not isinstance(prob, (int, float)):
            return prob
        p = max(0.0, min(1.0, float(prob)))
        st = _get_overconf_guardrail_state(force=False)
        if not bool(st.get("active", False)):
            return p
        cap = float(st.get("cap", IA_OVERCONF_DYNAMIC_CAP) or IA_OVERCONF_DYNAMIC_CAP)
        return float(min(p, max(0.0, min(1.0, cap))))
    except Exception:
        return prob


def _cap_prob_por_madurez(prob: float | None, bot: str | None = None) -> float | None:
    """
    Evita inflado irreal de Prob IA durante warmup (n bajo).
    Mientras el modelo no alcanza madurez, limita la probabilidad máxima
    con un techo progresivo entre IA_WARMUP_PROB_CAP_MIN y IA_WARMUP_PROB_CAP_MAX.
    """
    try:
        if not isinstance(prob, (int, float)):
            return prob
        p = max(0.0, min(1.0, float(prob)))

        meta = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
        n_samples = int(meta.get("n_samples", meta.get("n", 0)) or 0)
        warmup = bool(meta.get("warmup_mode", n_samples < int(TRAIN_WARMUP_MIN_ROWS)))
        if not warmup:
            return p

        ramp_rows = max(1, int(IA_WARMUP_CAP_RAMP_ROWS))
        ratio = max(0.0, min(1.0, float(n_samples) / float(ramp_rows)))
        cap = float(IA_WARMUP_PROB_CAP_MIN + (IA_WARMUP_PROB_CAP_MAX - IA_WARMUP_PROB_CAP_MIN) * ratio)

        # Si el bot aún no tiene evidencia auditada mínima, mantener cap más conservador.
        if isinstance(bot, str) and bot:
            try:
                st = estado_bots.get(bot, {})
                cal_n = int(st.get("cal_n", 0) or 0)
                if cal_n < 20:
                    cap_low = float(IA_WARMUP_LOW_EVIDENCE_CAP_BASE)
                    if _todos_bots_con_n_minimo_real():
                        cap_low = max(cap_low, float(IA_WARMUP_LOW_EVIDENCE_CAP_POST_N15))
                    cap = min(cap, float(cap_low))
            except Exception:
                pass

        return float(min(p, cap))
    except Exception:
        return prob


def _ensure_ia_signals_log():
    """
    Asegura ia_signals_log.csv con header canónico.
    - Si no existe o está vacío: crea header.
    - Si existe con header roto/faltante: normaliza columnas sin inventar histórico.
    - Emite evento único cuando no hay forma de reconstruir auditoría histórica.
    """
    global IA_SIGNALS_HISTORICAL_UNRECOVERABLE_EMITTED
    expected = ["ts", "bot", "epoch", "prob", "thr", "modo", "y"]
    try:
        needs_boot_notice = False
        if not os.path.exists(IA_SIGNALS_LOG) or os.path.getsize(IA_SIGNALS_LOG) <= 0:
            with open(IA_SIGNALS_LOG, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f)
                w.writerow(expected)
                f.flush()
                os.fsync(f.fileno())
            needs_boot_notice = True
        else:
            df = _safe_read_csv_any_encoding(IA_SIGNALS_LOG)
            if df is None:
                with open(IA_SIGNALS_LOG, "w", newline="", encoding="utf-8") as f:
                    w = csv.writer(f)
                    w.writerow(expected)
                    f.flush()
                    os.fsync(f.fileno())
                needs_boot_notice = True
            else:
                changed = False
                for c in expected:
                    if c not in df.columns:
                        df[c] = ""
                        changed = True
                if list(df.columns) != expected:
                    df = df.reindex(columns=expected, fill_value="")
                    changed = True
                if changed:
                    _atomic_write_text(IA_SIGNALS_LOG, df.to_csv(index=False, lineterminator="\n"))
                if df.empty:
                    needs_boot_notice = True

        if needs_boot_notice and not IA_SIGNALS_HISTORICAL_UNRECOVERABLE_EMITTED:
            IA_SIGNALS_HISTORICAL_UNRECOVERABLE_EMITTED = True
            _ag_evt("ℹ️ IA audit: histórico de señales no reconstruible; auditoría real desde ahora.")
    except Exception:
        pass

def _collect_incremental_row_stats(path: str = "dataset_incremental.csv", sample_tail: int = 15000) -> dict:
    """Diagnóstico rápido del incremental: raw, usable, dedup y madurez."""
    stats = {
        "raw_rows": 0,
        "usable_rows": 0,
        "post_dedup_rows": 0,
        "invalid_label_rows": 0,
        "duplicates_removed": 0,
        "duplicate_ratio": 0.0,
    }
    try:
        if not os.path.exists(path):
            return stats
        df = _safe_read_csv_any_encoding(path)
        if df is None or df.empty:
            return stats
        stats["raw_rows"] = int(len(df))

        lab = _pick_label_col_incremental(df)
        if not lab:
            return stats
        y01 = _coerce_label_to_01(df[lab])
        mask = y01.isin([0.0, 1.0])
        stats["usable_rows"] = int(mask.sum())
        stats["invalid_label_rows"] = max(0, int(len(df)) - int(mask.sum()))

        if int(mask.sum()) <= 0:
            return stats

        d = df.loc[mask].copy()
        if sample_tail and len(d) > int(sample_tail):
            d = d.tail(int(sample_tail)).copy()

        feats = [f for f in INCREMENTAL_FEATURES_V2 if f in d.columns]
        if feats:
            xx = d.reindex(columns=feats, fill_value=0.0).replace([np.inf, -np.inf], np.nan).fillna(0.0)
            yy = _coerce_label_to_01(d[lab]).fillna(-1).astype(int)
            sig = xx.round(6).astype(str).agg("|".join, axis=1) + "|" + yy.astype(str)
            dedup_n = int((~sig.duplicated(keep="last")).sum())
            stats["post_dedup_rows"] = dedup_n
            stats["duplicates_removed"] = max(0, int(len(xx)) - dedup_n)
        else:
            stats["post_dedup_rows"] = int(mask.sum())
            stats["duplicates_removed"] = 0

        base = max(1, int(stats["usable_rows"]))
        stats["duplicate_ratio"] = float(stats["duplicates_removed"]) / float(base)
        return stats
    except Exception:
        return stats


def auditar_refresh_campeon_stale(meta: dict | None = None, dataset_stats: dict | None = None, force_log: bool = False) -> dict:
    """Audita desalineación campeón/dataset y decide revisión de refresh (no bloquea trading)."""
    out = {
        "needs_review": False,
        "reasons": [],
        "dataset": {},
        "meta": {},
    }
    try:
        ds = dataset_stats if isinstance(dataset_stats, dict) else _collect_incremental_row_stats("dataset_incremental.csv")
        m = _normalize_model_meta(meta if isinstance(meta, dict) else (leer_model_meta() or {}))

        raw_rows = int(ds.get("raw_rows", 0) or 0)
        usable_rows = int(ds.get("usable_rows", 0) or 0)
        post_dedup_rows = int(ds.get("post_dedup_rows", 0) or 0)
        trained_rows = int(m.get("rows_total", m.get("n_samples", m.get("n", 0))) or 0)
        n_samples = int(m.get("n_samples", trained_rows) or trained_rows)
        reliable = bool(m.get("reliable", False))
        reliable_candidate = bool(m.get("reliable_candidate", reliable))
        warmup_mode = bool(m.get("warmup_mode", n_samples < int(TRAIN_WARMUP_MIN_ROWS)))
        canary_mode = bool(m.get("canary_mode", False))
        refresh_policy = str(m.get("refresh_policy", "")).strip()

        dt_tr = None
        ts_train = str(m.get("trained_at", "") or "").strip()
        if ts_train:
            try:
                dt_tr = datetime.strptime(ts_train, "%Y-%m-%d %H:%M:%S")
            except Exception:
                dt_tr = None
        age_s = (datetime.now() - dt_tr).total_seconds() if dt_tr is not None else None

        min_abs_growth = int(TRAIN_REFRESH_MIN_ABS_ROWS)
        if trained_rows > 0 and trained_rows <= int(TRAIN_REFRESH_LOWN_CUTOFF):
            min_abs_growth = int(TRAIN_REFRESH_MIN_ABS_ROWS_LOWN)
        growth_abs = max(0, post_dedup_rows - trained_rows)
        growth_ratio = (float(post_dedup_rows) / float(max(1, trained_rows))) if trained_rows > 0 else (float(post_dedup_rows) if post_dedup_rows > 0 else 0.0)

        reasons = []
        if trained_rows <= 0 and post_dedup_rows >= int(MIN_FIT_ROWS_LOW):
            reasons.append("meta_sin_rows_con_dataset_util")
        if trained_rows > 0 and growth_abs >= int(min_abs_growth) and growth_ratio >= (1.0 + float(TRAIN_REFRESH_MIN_GROWTH)):
            reasons.append("campeon_quedo_muy_por_debajo_del_incremental")
        if warmup_mode and post_dedup_rows >= int(TRAIN_WARMUP_MIN_ROWS):
            reasons.append("warmup_persistente_con_dataset_maduro")
        if (not reliable) and post_dedup_rows >= int(max(TRAIN_WARMUP_MIN_ROWS, MIN_FIT_ROWS_PROD)):
            reasons.append("reliable_false_prolongado_con_data_madura")
        if age_s is not None and age_s >= float(TRAIN_REFRESH_STALE_MIN) and growth_abs >= int(min_abs_growth):
            reasons.append("modelo_stale_por_tiempo_y_crecimiento")

        artefacts = [globals().get("_MODEL_PATH", "modelo_xgb_v2.pkl"), globals().get("_SCALER_PATH", "scaler_v2.pkl"), globals().get("_FEATURES_PATH", "feature_names_v2.pkl"), globals().get("_META_PATH", "model_meta_v2.json")]
        mtimes = [_safe_mtime(p) for p in artefacts]
        if any(mt is None for mt in mtimes):
            reasons.append("artefactos_faltantes")

        out["needs_review"] = bool(reasons)
        out["reasons"] = reasons
        out["dataset"] = {
            "raw_rows": raw_rows,
            "usable_rows": usable_rows,
            "post_dedup_rows": post_dedup_rows,
            "duplicates_removed": int(ds.get("duplicates_removed", 0) or 0),
            "duplicate_ratio": float(ds.get("duplicate_ratio", 0.0) or 0.0),
        }
        out["meta"] = {
            "trained_rows": trained_rows,
            "n_samples": n_samples,
            "trained_at": ts_train,
            "age_s": float(age_s) if age_s is not None else None,
            "reliable": reliable,
            "reliable_candidate": reliable_candidate,
            "warmup_mode": warmup_mode,
            "canary_mode": canary_mode,
            "refresh_policy": refresh_policy,
        }

        sig = f"{out['dataset']['post_dedup_rows']}|{trained_rows}|{','.join(reasons)}"
        last = globals().get("_IA_REFRESH_AUDIT_LAST", {}) or {}
        now = time.time()
        should = force_log or sig != str(last.get("sig", "")) or (now - float(last.get("ts", 0.0) or 0.0)) >= 45.0
        if should:
            _ag_evt(
                "🧪 IA refresh-audit: raw={raw} usable={use} dedup={ded} trained={tr} n={n} rel={rel}/{rc} "
                "warmup={wu} canary={ca} policy={po} reasons={rs}".format(
                    raw=raw_rows,
                    use=usable_rows,
                    ded=post_dedup_rows,
                    tr=trained_rows,
                    n=n_samples,
                    rel=int(reliable),
                    rc=int(reliable_candidate),
                    wu=int(warmup_mode),
                    ca=int(canary_mode),
                    po=(refresh_policy or "--"),
                    rs=("|".join(reasons) if reasons else "ok"),
                )
            )
            globals()["_IA_REFRESH_AUDIT_LAST"] = {"sig": sig, "ts": now}
    except Exception:
        pass
    return out


def auditar_degradacion_temporal_modelo(
    path: str = "dataset_incremental.csv",
    output_path: str = "ia_temporal_degradation_report.json",
    windows: int = 4,
    min_rows_window: int = 40,
):
    """Auditoría temporal de degradación de calidad (no bloquea trading)."""
    try:
        if not os.path.exists(path):
            return None
        df = _safe_read_csv_any_encoding(path)
        if df is None or df.empty:
            return None

        d = df.copy().reset_index(drop=True)
        d["__row_idx"] = np.arange(len(d), dtype=int)
        has_ts = False
        for tcol in ("ts_ingest", "epoch", "timestamp", "ts", "fecha"):
            if tcol in d.columns:
                vals = pd.to_numeric(d[tcol], errors="coerce")
                if int(vals.notna().sum()) >= int(max(20, len(d) * 0.35)):
                    d["__t"] = vals
                    has_ts = True
                    break
        if not has_ts:
            d["__t"] = d["__row_idx"].astype(float)

        lab = _pick_label_col_incremental(d)
        if not lab:
            return None
        d["__y"] = _coerce_label_to_01(d[lab])
        d = d[d["__y"].isin([0.0, 1.0])].copy()
        if d.empty:
            return None

        n = int(len(d))
        nwin = max(2, int(windows))
        wsize = max(int(min_rows_window), int(n // nwin) if nwin > 0 else int(min_rows_window))
        chunks = []
        start = 0
        while start < n:
            end = min(n, start + wsize)
            chunks.append((start, end))
            start = end
        if len(chunks) < 2:
            chunks = [(0, n)]

        model, scaler, features, meta = get_oracle_assets()
        feat_names = _resolve_oracle_feature_names(model, scaler, features, meta or {}) or list(INCREMENTAL_FEATURES_V2)

        rows = []
        for wi, (a, b) in enumerate(chunks, start=1):
            seg = d.iloc[a:b].copy()
            raw_rows = int(len(seg))
            usable_rows = int(len(seg))
            xx = seg.reindex(columns=feat_names, fill_value=0.0).replace([np.inf, -np.inf], np.nan).fillna(0.0)
            yy = seg["__y"].astype(int).to_numpy()

            sig = xx.round(6).astype(str).agg("|".join, axis=1) + "|" + pd.Series(yy).astype(str)
            keep = ~sig.duplicated(keep="last")
            xx = xx.loc[keep].copy()
            yy = pd.Series(yy).loc[keep].astype(int).to_numpy()
            post_rows = int(len(xx))
            dup_rm = max(0, raw_rows - post_rows)

            if post_rows <= 0:
                continue

            pred = np.full(post_rows, 0.5, dtype=float)
            try:
                if model is not None:
                    Xuse = xx.copy()
                    if scaler is not None:
                        Xuse = pd.DataFrame(scaler.transform(Xuse), columns=Xuse.columns, index=Xuse.index)
                    if hasattr(model, "predict_proba"):
                        pred = np.asarray(model.predict_proba(Xuse)[:, 1], dtype=float)
                    else:
                        pred = np.asarray(model.predict(Xuse), dtype=float)
                    pred = np.clip(pred, 0.0, 1.0)
            except Exception:
                pred = np.full(post_rows, 0.5, dtype=float)

            try:
                auc = float(roc_auc_score(yy, pred)) if len(np.unique(yy)) > 1 else None
            except Exception:
                auc = None
            acc = _safe_mean_np((pred >= 0.5).astype(int) == yy, None) if post_rows > 0 else None
            try:
                brier = float(brier_score_loss(yy, pred)) if post_rows > 0 else None
            except Exception:
                brier = None
            base_rate = _safe_mean_np(yy, None) if post_rows > 0 else None
            mean_pred = _safe_mean_np(pred, 0.5) if post_rows > 0 else 0.5
            drift = float(abs(float(mean_pred) - (base_rate if base_rate is not None else 0.5)))

            rows.append({
                "window": int(wi),
                "start_idx": int(seg["__row_idx"].iloc[0]),
                "end_idx": int(seg["__row_idx"].iloc[-1]),
                "time_proxy": "timestamp" if has_ts else "row_order",
                "raw_rows": raw_rows,
                "usable_rows": usable_rows,
                "duplicates_removed": int(dup_rm),
                "post_dedup_rows": post_rows,
                "auc": auc,
                "accuracy": acc,
                "brier": brier,
                "base_rate": base_rate,
                "drift_score": drift,
            })

        if not rows:
            return None

        recent = rows[-1]
        hist = rows[:-1] if len(rows) > 1 else rows
        def _avg(key):
            vals = [r.get(key) for r in hist if isinstance(r.get(key), (int, float))]
            return float(sum(vals) / len(vals)) if vals else None

        avg_hist_auc = _avg("auc")
        avg_hist_acc = _avg("accuracy")
        avg_hist_brier = _avg("brier")
        degraded = False
        reasons = []
        if avg_hist_auc is not None and isinstance(recent.get("auc"), (int, float)) and recent["auc"] < (avg_hist_auc - 0.08):
            degraded = True
            reasons.append("auc_drop")
        if avg_hist_acc is not None and isinstance(recent.get("accuracy"), (int, float)) and recent["accuracy"] < (avg_hist_acc - 0.08):
            degraded = True
            reasons.append("accuracy_drop")
        if avg_hist_brier is not None and isinstance(recent.get("brier"), (int, float)) and recent["brier"] > (avg_hist_brier + 0.06):
            degraded = True
            reasons.append("brier_worse")

        report = {
            "generated_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "time_proxy": "timestamp" if has_ts else "row_order",
            "windows": rows,
            "summary": {
                "degradation_detected": bool(degraded),
                "reasons": reasons,
                "historical_auc": avg_hist_auc,
                "historical_accuracy": avg_hist_acc,
                "historical_brier": avg_hist_brier,
                "recent_window": recent,
            },
        }
        _json_dump_atomic(report, output_path)

        if degraded:
            _ag_evt(f"⚠️ IA degradación temporal detectada: {','.join(reasons)}")

        return report
    except Exception:
        return None


def _leer_stats_canary_desde_log(ts_inicio: str | None) -> tuple[int, int]:
    """
    Devuelve (cerradas, ganadas) desde ia_signals_log.csv,
    opcionalmente filtrando por ts >= ts_inicio.
    """
    _ensure_ia_signals_log()
    dt_inicio = None
    try:
        if isinstance(ts_inicio, str) and ts_inicio.strip():
            dt_inicio = datetime.strptime(ts_inicio.strip(), "%Y-%m-%d %H:%M:%S")
    except Exception:
        dt_inicio = None

    cerradas = 0
    ganadas = 0
    try:
        with open(IA_SIGNALS_LOG, "r", newline="", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for r in reader:
                yv = str(r.get("y", "")).strip()
                if yv not in ("0", "1"):
                    continue
                if dt_inicio is not None:
                    ts = str(r.get("ts", "")).strip()
                    try:
                        dt = datetime.strptime(ts, "%Y-%m-%d %H:%M:%S")
                    except Exception:
                        try:
                            tsf = float(ts)
                            dt = datetime.fromtimestamp(tsf)
                        except Exception:
                            continue
                    if dt < dt_inicio:
                        continue
                cerradas += 1
                if yv == "1":
                    ganadas += 1
    except Exception:
        pass
    return int(cerradas), int(ganadas)


def resolver_canary_estado(meta: dict | None) -> dict:
    """
    Evalúa y resuelve canary automáticamente cuando hay suficiente evidencia cerrada.
    - Si canary cumple target + hit-rate, promueve a champion_direct.
    - Si no cumple hit-rate, mantiene canary y amplía target (retry batch).
    """
    if not isinstance(meta, dict) or not bool(meta.get("canary_mode", False)):
        return meta if isinstance(meta, dict) else {}

    now = float(time.time())
    last_ts = float(CANARY_STATE_CACHE.get("ts", 0.0) or 0.0)
    cached_meta = CANARY_STATE_CACHE.get("meta")
    if (now - last_ts) < float(CANARY_EVAL_COOLDOWN_S) and isinstance(cached_meta, dict):
        return cached_meta

    out = dict(meta)
    ts_inicio = str(out.get("canary_started_at", "") or "").strip()
    target = int(out.get("canary_target_closed", CANARY_MIN_CLOSED_SIGNALS) or CANARY_MIN_CLOSED_SIGNALS)
    target = max(1, target)

    cerradas, ganadas = _leer_stats_canary_desde_log(ts_inicio)
    hit = (float(ganadas) / float(cerradas)) if cerradas > 0 else 0.0
    out["canary_closed_signals"] = int(cerradas)
    out["canary_hitrate"] = float(hit)

    changed = False
    if cerradas >= target:
        if hit >= float(CANARY_MIN_HITRATE):
            out["canary_mode"] = False
            out["refresh_policy"] = "champion_direct"
            out["reliable"] = bool(out.get("reliable_candidate", out.get("reliable", False)))
            out["canary_resolved_at"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            changed = True
            try:
                agregar_evento(f"✅ IA CANARY resuelto: {ganadas}/{cerradas} ({hit*100:.1f}%). Se habilita champion_direct.")
            except Exception:
                pass
        else:
            out["canary_target_closed"] = int(cerradas + max(1, int(CANARY_RETRY_BATCH)))
            changed = True
            try:
                agregar_evento(
                    f"🟡 IA CANARY extendido: hit-rate {hit*100:.1f}% ({ganadas}/{cerradas}) < {CANARY_MIN_HITRATE*100:.1f}%."
                )
            except Exception:
                pass

    if changed:
        try:
            if "guardar_model_meta" in globals() and callable(guardar_model_meta):
                guardar_model_meta(out)
        except Exception:
            pass

    CANARY_STATE_CACHE["ts"] = float(now)
    CANARY_STATE_CACHE["meta"] = dict(out)
    return out


def _atomic_write_text(path: str, text: str) -> bool:
    tmp = path + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(text)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
        return True
    except Exception:
        try:
            if os.path.exists(tmp):
                os.remove(tmp)
        except Exception:
            pass
        return False

def _to_int_epoch(v) -> int | None:
    try:
        if v is None:
            return None
        if isinstance(v, str):
            v = v.strip()
            if v == "":
                return None
        x = float(v)
        if not math.isfinite(x):
            return None
        # epoch ms -> s
        if x > 1e12:
            x = x / 1000.0
        if x < 1e9:
            return None
        return int(x)
    except Exception:
        return None

def _tail_rows_dict(path: str, max_lines: int = 1200) -> list[dict]:
    """
    Lee SOLO el header + últimas N líneas para no reventar rendimiento con CSV enormes.
    Devuelve lista de dicts (puede ser vacía).
    """
    if not os.path.exists(path):
        return []
    for enc in ("utf-8", "latin-1", "windows-1252"):
        try:
            from collections import deque as _dq
            with open(path, "r", encoding=enc, errors="replace", newline="") as f:
                header = f.readline()
                if not header:
                    return []
                dq = _dq(f, maxlen=int(max_lines))
            lines = [header] + list(dq)
            reader = csv.DictReader(lines)
            out = []
            for r in reader:
                if isinstance(r, dict) and r:
                    out.append(r)
            return out
        except Exception:
            continue
    return []

def ia_audit_get_last_pre_epoch(bot: str) -> int | None:
    """
    Intenta obtener epoch del último PRE_TRADE (incluye PENDING/OPEN/ABIERTO por normalizador).
    Si no existe trade_status, cae a la última fila NO cierre.
    """
    ruta = f"registro_enriquecido_{bot}.csv"
    rows = _tail_rows_dict(ruta, max_lines=1400)
    if not rows:
        return None

    norm_fn = globals().get("normalizar_resultado", None)

    def _norm(x):
        try:
            if callable(norm_fn):
                return norm_fn(x)
        except Exception:
            pass
        s = str(x or "").upper()
        if "GAN" in s or "WIN" in s or "✓" in s:
            return "GANANCIA"
        if "PERD" in s or "LOSS" in s or "✗" in s:
            return "PÉRDIDA"
        return "INDEFINIDO"

    # ¿Existe trade_status o trade_status_norm con contenido?
    def _has_key_nonempty(r, k):
        try:
            if k not in r:
                return False
            v = r.get(k, None)
            if v is None:
                return False
            return str(v).strip() != ""
        except Exception:
            return False

    has_ts = any((_has_key_nonempty(r, "trade_status") or _has_key_nonempty(r, "trade_status_norm")) for r in rows)

    # 1) Con trade_status: preferir PRE_TRADE real
    if has_ts:
        for r in reversed(rows):
            ts = normalizar_trade_status(r.get("trade_status_norm", None) or r.get("trade_status", None))
            if ts != "PRE_TRADE":
                continue

            # NO usar cierres como "pre"
            res = _norm(r.get("resultado", None))
            if res in ("GANANCIA", "PÉRDIDA"):
                continue

            ep = _to_int_epoch(r.get("epoch", None))
            if ep is not None:
                return ep

    # 2) Fallback: última fila que NO sea cierre
    for r in reversed(rows):
        res = _norm(r.get("resultado", None))
        if res not in ("GANANCIA", "PÉRDIDA"):
            ep = _to_int_epoch(r.get("epoch", None))
            if ep is not None:
                return ep

    return None
def ia_audit_get_last_close(bot: str) -> tuple[int | None, int | None]:
    """
    Devuelve (epoch_close, y) donde y=1 GANANCIA, y=0 PÉRDIDA.
    Acepta CERRADO y también CLOSED/SETTLED/etc. vía normalizar_trade_status().
    """
    ruta = f"registro_enriquecido_{bot}.csv"
    rows = _tail_rows_dict(ruta, max_lines=1800)
    if not rows:
        return None, None

    norm_fn = globals().get("normalizar_resultado", None)
    def _norm(x):
        try:
            if callable(norm_fn):
                return norm_fn(x)
        except Exception:
            pass
        s = str(x or "").upper()
        if "GAN" in s or "WIN" in s or "✓" in s:
            return "GANANCIA"
        if "PERD" in s or "LOSS" in s or "✗" in s:
            return "PÉRDIDA"
        return "INDEFINIDO"

    has_ts = any(("trade_status" in r) or ("trade_status_norm" in r) for r in rows)

    for r in reversed(rows):
        res = _norm(r.get("resultado", None))
        if res not in ("GANANCIA", "PÉRDIDA"):
            continue

        if has_ts:
            ts_raw = r.get("trade_status_norm", None) or r.get("trade_status", None)
            ts = normalizar_trade_status(ts_raw)
            if ts and ts != "CERRADO":
                continue

        ep = _to_int_epoch(r.get("epoch", None))
        if ep is None:
            continue

        y = 1 if res == "GANANCIA" else 0
        return ep, y

    return None, None


def log_ia_open(bot: str, epoch: int, prob: float, thr: float, modo: str):
    """
    Registra una señal IA ABIERTA (y="") asociada al epoch PRE_TRADE.
    Blindaje: normaliza columna y para que quede SIEMPRE como "", "0" o "1" (no 0.0/1.0).
    Además, normaliza epoch para evitar duplicados por "123" vs "123.0".
    """
    try:
        _ensure_ia_signals_log()
        with IA_SIGNALS_LOCK:
            df = _safe_read_csv_any_encoding(IA_SIGNALS_LOG)
            if df is None or df.empty:
                df = pd.DataFrame(columns=["ts", "bot", "epoch", "prob", "thr", "modo", "y"])

            # Asegurar columnas base
            for c in ["ts", "bot", "epoch", "prob", "thr", "modo", "y"]:
                if c not in df.columns:
                    df[c] = ""

            def _norm_y(v):
                if v is None:
                    return ""
                s = str(v).strip()
                if s == "" or s.lower() == "nan":
                    return ""
                try:
                    return "1" if float(s) >= 0.5 else "0"
                except Exception:
                    su = s.upper()
                    if ("GAN" in su) or ("WIN" in su) or ("✓" in su):
                        return "1"
                    if ("PERD" in su) or ("PÉRD" in su) or ("LOSS" in su) or ("✗" in su):
                        return "0"
                    return ""

            df["y"] = df["y"].map(_norm_y)

            bot_s = _col_as_str_series(df, "bot").str.strip()
            y_s = _col_as_str_series(df, "y").str.strip()
            epoch_num = pd.to_numeric(_col_as_str_series(df, "epoch"), errors="coerce")

            # Evitar duplicado exacto (misma señal abierta)
            try:
                ep = float(int(epoch))
            except Exception:
                ep = None

            if ep is not None:
                m_same_open = (bot_s == str(bot)) & (epoch_num == ep) & (y_s == "")
                if m_same_open.any():
                    return False

            row = {
                "ts": f"{time.time():.6f}",
                "bot": str(bot),
                "epoch": str(int(epoch)),
                "prob": float(prob),
                "thr": float(thr),
                "modo": str(modo or ""),
                "y": ""
            }

            df = pd.concat([df, pd.DataFrame([row])], ignore_index=True)
            _atomic_write_text(IA_SIGNALS_LOG, df.to_csv(index=False, lineterminator="\n"))
            try:
                IA_SIGNALS_TELEMETRY_LAST["opens"] = int(IA_SIGNALS_TELEMETRY_LAST.get("opens", 0) or 0) + 1
                IA_SIGNALS_TELEMETRY_LAST["ts"] = float(time.time())
            except Exception:
                pass
            return True
    except Exception:
        return False


def log_ia_close(
    bot: str,
    epoch: int,
    y: int,
    prob_override: float = None,
    thr_override: float = None,
    modo_override: str = None
):
    """
    Cierra la señal IA más cercana (ABIERTA) para ese bot.
    Blindaje: reconoce cierres aunque el CSV tenga y como 0.0/1.0 o texto, y re-normaliza a "0"/"1".
    """
    try:
        _ensure_ia_signals_log()
        with IA_SIGNALS_LOCK:
            df = _safe_read_csv_any_encoding(IA_SIGNALS_LOG)
            if df is None or df.empty:
                return False

            for c in ["ts", "bot", "epoch", "prob", "thr", "modo", "y"]:
                if c not in df.columns:
                    df[c] = ""

            def _norm_y(v):
                if v is None:
                    return ""
                s = str(v).strip()
                if s == "" or s.lower() == "nan":
                    return ""
                try:
                    return "1" if float(s) >= 0.5 else "0"
                except Exception:
                    su = s.upper()
                    if ("GAN" in su) or ("WIN" in su) or ("✓" in su):
                        return "1"
                    if ("PERD" in su) or ("PÉRD" in su) or ("LOSS" in su) or ("✗" in su):
                        return "0"
                    return ""

            df["y"] = df["y"].map(_norm_y)

            bot_s = _col_as_str_series(df, "bot").str.strip()
            y_s = _col_as_str_series(df, "y").str.strip()
            epoch_num = pd.to_numeric(_col_as_str_series(df, "epoch"), errors="coerce")

            is_open = (y_s == "")
            yv = 1 if int(y) == 1 else 0
            close_n = int(epoch)

            # 1) Match exacto a señal abierta por epoch
            m_exact_open = (bot_s == str(bot)) & is_open & (epoch_num == float(close_n))
            if m_exact_open.any():
                for idx in df.index[m_exact_open]:
                    df.at[idx, "y"] = str(yv)
                    if prob_override is not None:
                        df.at[idx, "prob"] = float(prob_override)
                    if thr_override is not None:
                        df.at[idx, "thr"] = float(thr_override)
                    if modo_override is not None:
                        df.at[idx, "modo"] = str(modo_override)

                _atomic_write_text(IA_SIGNALS_LOG, df.to_csv(index=False, lineterminator="\n"))
                try:
                    IA_SIGNALS_TELEMETRY_LAST["closes"] = int(IA_SIGNALS_TELEMETRY_LAST.get("closes", 0) or 0) + 1
                    IA_SIGNALS_TELEMETRY_LAST["ts"] = float(time.time())
                except Exception:
                    pass
                return True

            # 2) Si no hay exact match, cerrar la ABIERTA más reciente con epoch <= epoch_close
            cand = df[(bot_s == str(bot)) & is_open].copy()
            if cand.empty:
                return False

            cand_epoch = pd.to_numeric(cand["epoch"], errors="coerce")
            cand = cand[cand_epoch.notna()].copy()
            cand["epoch_num"] = cand_epoch[cand_epoch.notna()].astype(float)

            cand = cand[cand["epoch_num"] <= float(close_n)]
            if cand.empty:
                return False

            pick_idx = cand["epoch_num"].idxmax()
            df.at[pick_idx, "y"] = str(yv)
            if prob_override is not None:
                df.at[pick_idx, "prob"] = float(prob_override)
            if thr_override is not None:
                df.at[pick_idx, "thr"] = float(thr_override)
            if modo_override is not None:
                df.at[pick_idx, "modo"] = str(modo_override)

            _atomic_write_text(IA_SIGNALS_LOG, df.to_csv(index=False, lineterminator="\n"))
            try:
                IA_SIGNALS_TELEMETRY_LAST["closes"] = int(IA_SIGNALS_TELEMETRY_LAST.get("closes", 0) or 0) + 1
                IA_SIGNALS_TELEMETRY_LAST["ts"] = float(time.time())
            except Exception:
                pass
            return True
    except Exception:
        return False

IA_AUDIT_LAST_CLOSE_EPOCH = {b: None for b in BOT_NAMES}

def ia_audit_scan_close(bot: str, tail_lines: int = 2000, max_events: int = 6):
    """
    Detecta CIERRES reales nuevos en registro_enriquecido_{bot}.csv y cierra señales en ia_signals_log.csv.
    - Procesa hasta `max_events` cierres por tick para no sobrecargar.
    - Procesa en ORDEN ASCENDENTE para NO saltarse cierres antiguos (catch-up real).
    - Usa IA_AUDIT_LAST_CLOSE_EPOCH para avanzar incrementalmente.
    """
    try:
        last = IA_AUDIT_LAST_CLOSE_EPOCH.get(bot)
    except Exception:
        last = None

    ruta = f"registro_enriquecido_{bot}.csv"
    rows = _tail_rows_dict(ruta, max_lines=int(tail_lines))
    if not rows:
        return

    # ¿Existe trade_status (raw o norm) en alguna fila?
    try:
        has_ts = any(("trade_status" in (r or {})) or ("trade_status_norm" in (r or {})) for r in rows)
    except Exception:
        has_ts = False

    # Recolectar cierres > last
    cierres = []
    seen = set()

    for r in rows:
        try:
            rr = (r or {})
            ep = None
            for k in ("epoch", "fecha", "timestamp", "ts"):
                ep = _to_int_epoch(rr.get(k))
                if ep is not None:
                    break
        except Exception:
            ep = None

        if ep is None:
            continue


        if last is not None:
            try:
                if int(ep) <= int(last):
                    continue
            except Exception:
                continue

        if has_ts:
            try:
                ts_raw = (r or {}).get("trade_status_norm") or (r or {}).get("trade_status")
                tsn = normalizar_trade_status(ts_raw)
                if tsn and tsn != "CERRADO":
                    continue
            except Exception:
                pass

        try:
            resn = normalizar_resultado((r or {}).get("resultado"))
        except Exception:
            resn = ""
        if resn not in ("GANANCIA", "PÉRDIDA"):
            continue

        y = 1 if resn == "GANANCIA" else 0

        # Dedup por epoch en este tick (nos quedamos con el último y del epoch)
        if int(ep) in seen:
            for i in range(len(cierres) - 1, -1, -1):
                if cierres[i][0] == int(ep):
                    cierres[i] = (int(ep), int(y))
                    break
        else:
            cierres.append((int(ep), int(y)))
            seen.add(int(ep))

    if not cierres:
        return

    cierres.sort(key=lambda t: t[0])  # ASC

    # Limitar: tomamos LOS PRIMEROS para catch-up real (no saltar viejos)
    if max_events and len(cierres) > int(max_events):
        cierres = cierres[:int(max_events)]

    closes_ok = 0
    unmatched = 0
    for ep, y in cierres:
        closed = False
        try:
            closed = bool(log_ia_close(bot, ep, y))
        except Exception:
            closed = False
        if closed:
            closes_ok += 1
        else:
            unmatched += 1
            try:
                IA_SIGNALS_TELEMETRY_LAST["orphans"] = int(IA_SIGNALS_TELEMETRY_LAST.get("orphans", 0) or 0) + 1
            except Exception:
                pass
        # Avanzamos el puntero siempre: si no había señal abierta (trade sin señal IA), no queremos trabarnos.
        IA_AUDIT_LAST_CLOSE_EPOCH[bot] = int(ep)

    try:
        _ensure_ia_signals_log()
        dlog = _safe_read_csv_any_encoding(IA_SIGNALS_LOG)
        pending = 0
        if dlog is not None and not dlog.empty:
            for c in ["bot", "y"]:
                if c not in dlog.columns:
                    dlog[c] = ""
            pending = int(((dlog["bot"].astype(str).str.strip() == str(bot)) & (dlog["y"].astype(str).str.strip() == "")).sum())
        orphan_rate = (float(unmatched) / float(max(1, closes_ok + unmatched)))
        _ag_evt(
            f"🧾 IA audit tick {bot}: opens+{int(IA_SIGNALS_TELEMETRY_LAST.get('opens',0) or 0)} closes+{closes_ok} pending={pending} unmatched={unmatched} orphan_rate={orphan_rate:.2f} last_close={IA_AUDIT_LAST_CLOSE_EPOCH.get(bot)}"
        )
        IA_SIGNALS_TELEMETRY_LAST["opens"] = 0
        IA_SIGNALS_TELEMETRY_LAST["ts"] = float(time.time())
    except Exception:
        pass

def semaforo_calibracion(n: int, infl_pp: float | None):
    """Devuelve (emoji, etiqueta, detalle) para lectura rápida de calibración."""
    try:
        n = int(n or 0)
    except Exception:
        n = 0

    try:
        infl = abs(float(infl_pp)) if infl_pp is not None else None
    except Exception:
        infl = None

    if n < SEM_CAL_N_ROJO:
        return "🔴", "CRÍTICO", f"n={n}<{SEM_CAL_N_ROJO}"

    if infl is None:
        if n < SEM_CAL_N_AMARILLO:
            return "🟡", "PRECAUCIÓN", f"n={n}<{SEM_CAL_N_AMARILLO}"
        return "🟢", "CONFIABLE", f"n={n} (sin inflación calculable)"

    if infl > SEM_CAL_INFL_WARN_PP:
        return "🔴", "CRÍTICO", f"|infl|={infl:.1f}pp>{SEM_CAL_INFL_WARN_PP:.0f}pp"

    if (n < SEM_CAL_N_AMARILLO) or (infl > SEM_CAL_INFL_OK_PP):
        return "🟡", "PRECAUCIÓN", f"n={n}, |infl|={infl:.1f}pp"

    return "🟢", "CONFIABLE", f"n={n}, |infl|={infl:.1f}pp"

def diagnostico_calibracion(n: int, pred_mean: float, win_rate: float, infl_pp: float | None):
    """Mensaje corto para saber si la calibración va por buen camino."""
    try:
        n = int(n or 0)
    except Exception:
        n = 0

    try:
        infl_abs = abs(float(infl_pp)) if infl_pp is not None else None
    except Exception:
        infl_abs = None

    if n < SEM_CAL_N_ROJO:
        return "Todavía no se puede concluir (muestra muy chica): sigue juntando cierres reales."

    if infl_abs is None:
        return "Hay cierres, pero aún no alcanza para medir la brecha Pred vs Real con confianza."

    if infl_abs <= SEM_CAL_INFL_OK_PP:
        return "Vas por buen camino: la probabilidad predicha está cerca del resultado real."

    if infl_abs <= SEM_CAL_INFL_WARN_PP:
        sesgo = "sobreestima" if pred_mean >= win_rate else "subestima"
        return f"Hay avance, pero la IA aún {sesgo} el resultado real; conviene más muestra."

    sesgo = "sobreestimando" if pred_mean >= win_rate else "subestimando"
    return f"Se detecta descalibración fuerte ({sesgo}); no usar la probabilidad sola para decidir."

def auditar_calibracion_seniales_reales(min_prob: float = 0.70, max_rows: int = 20000, n_bins: int = 10):
    """
    Auditoría REAL vs PRED (señales cerradas en ia_signals_log.csv).

    Devuelve:
      - n
      - win_rate (real)
      - avg_pred (promedio de prob del modelo)
      - inflacion_pp = (avg_pred - win_rate)*100
      - factor = win_rate/avg_pred (clamp) si hay data suficiente
      - brier = mean((prob - y)^2)
      - ece = Expected Calibration Error (bins 0..1)
      - por_bot: métricas por bot
    """
    try:
        _ensure_ia_signals_log()
        df = _safe_read_csv_any_encoding(IA_SIGNALS_LOG)
        if df is None or df.empty:
            return None

        if ("prob" not in df.columns) or ("y" not in df.columns) or ("bot" not in df.columns):
            return None

        d = df.copy()

        # y debe ser 0/1 para considerar "cerrada"
        # (soporta 0/1, 0.0/1.0, "0"/"1", y texto tipo GANANCIA/PÉRDIDA/✓/✗)
        y_raw = d["y"]

        y_num = pd.to_numeric(y_raw, errors="coerce")
        y_txt = y_raw.astype(str).str.strip().str.upper()

        # Fallback por texto si no pudo convertirse a número
        y_num = y_num.where(
            ~y_num.isna(),
            np.where(
                y_txt.str.contains(r"GAN|WIN|✓"),
                1.0,
                np.where(y_txt.str.contains(r"PERD|PÉRD|LOSS|✗"), 0.0, np.nan)
            )
        )

        # Normalizar a 0/1 (todo lo >=0.5 se considera 1)
        d["y"] = np.where(pd.isna(y_num), np.nan, np.where(y_num >= 0.5, 1, 0))
        d = d[d["y"].isin([0, 1])].copy()
        if d.empty:
            return None

        # prob numérica (defensivo)
        d["prob"] = pd.to_numeric(d["prob"], errors="coerce").fillna(0.0).clip(0.0, 1.0)
        d["y"] = d["y"].astype(int)

        n_total_closed = int(len(d))

        # filtro por umbral
        d = d[d["prob"] >= float(min_prob)].copy()
        if d.empty:
            return {
                "n": 0,
                "n_total_closed": n_total_closed,
                "n_after_threshold": 0,
                "min_prob": float(min_prob),
                "win_rate": None,
                "avg_pred": None,
                "inflacion_pp": None,
                "factor": 1.0,
                "brier": None,
                "ece": None,
                "por_bot": {},
            }

        # limitar tamaño para no castigar IO/cpu
        try:
            if max_rows and len(d) > int(max_rows):
                d = d.iloc[-int(max_rows):].copy()
        except Exception:
            pass

        y = d["y"].to_numpy(dtype=float)
        p = d["prob"].to_numpy(dtype=float)

        # Guardas anti-vacío/NaN: evita RuntimeWarning de numpy en métricas
        try:
            m_valid = np.isfinite(y) & np.isfinite(p)
            y = y[m_valid]
            p = p[m_valid]
        except Exception:
            y = np.asarray([], dtype=float)
            p = np.asarray([], dtype=float)

        if y.size == 0 or p.size == 0:
            return {
                "n": 0,
                "n_total_closed": n_total_closed,
                "n_after_threshold": 0,
                "min_prob": float(min_prob),
                "win_rate": None,
                "avg_pred": None,
                "inflacion_pp": None,
                "factor": 1.0,
                "brier": None,
                "ece": 0.0,
                "stable_sample": False,
                "min_recommended_n": int(IA_CALIB_MIN_CLOSED),
                "por_bot": {},
            }

        def _ece(_y, _p, bins: int = 10) -> float:
            _y = np.asarray(_y, dtype=float)
            _p = np.asarray(_p, dtype=float)
            if _p.size == 0:
                return 0.0
            edges = np.linspace(0.0, 1.0, int(bins) + 1)
            ece = 0.0
            n = float(_p.size)
            for i in range(len(edges) - 1):
                lo, hi = edges[i], edges[i + 1]
                if i < len(edges) - 2:
                    m = (_p >= lo) & (_p < hi)
                else:
                    m = (_p >= lo) & (_p <= hi)
                cnt = int(m.sum())
                if cnt <= 0:
                    continue
                avg_p = float(_p[m].mean())
                avg_y = float(_y[m].mean())
                ece += abs(avg_p - avg_y) * (cnt / n)
            return float(ece)

        win_rate = _safe_mean_np(y, None)
        avg_pred = _safe_mean_np(p, None)
        infl_pp = (avg_pred - win_rate) * 100.0

        factor = 1.0
        if avg_pred > 1e-6 and len(d) >= 30:
            factor = win_rate / avg_pred
            factor = max(0.60, min(1.30, factor))  # clamp defensivo

        brier = _safe_mean_np((p - y) ** 2, None)
        ece = _ece(y, p, bins=n_bins)

        por_bot = {}
        try:
            for b, g in d.groupby("bot"):
                n = int(len(g))
                yb = g["y"].to_numpy(dtype=float)
                pb = g["prob"].to_numpy(dtype=float)

                wr = _safe_mean_np(yb, None) if n else None
                ap = _safe_mean_np(pb, None) if n else None
                inf = ((ap - wr) * 100.0) if (wr is not None and ap is not None) else None

                fb = 1.0
                if ap and ap > 1e-6 and n >= 20:
                    fb = wr / ap
                    fb = max(0.60, min(1.30, fb))

                por_bot[str(b)] = {
                    "n": n,
                    "win_rate": wr,
                    "avg_pred": ap,
                    "inflacion_pp": inf,
                    "factor": fb,
                    "brier": _safe_mean_np((pb - yb) ** 2, None) if n else None,
                    "ece": _ece(yb, pb, bins=n_bins) if n else None,
                }
        except Exception:
            por_bot = {}

        stable_sample = bool(len(d) >= int(IA_CALIB_MIN_CLOSED))

        return {
            "n": int(len(d)),
            "n_total_closed": n_total_closed,
            "n_after_threshold": int(len(d)),
            "min_prob": float(min_prob),
            "win_rate": win_rate,
            "avg_pred": avg_pred,
            "inflacion_pp": infl_pp,
            "factor": factor,
            "brier": brier,
            "ece": ece,
            "stable_sample": stable_sample,
            "min_recommended_n": int(IA_CALIB_MIN_CLOSED),
            "por_bot": por_bot,
        }
    except Exception:
        return None

# === FIN BLOQUE 10A ===
# ==========================================================
        
# ==========================================================
# ✅ HOTFIX IA: Prob IA REAL (no forzar a 0 si no hay señal)
# - Predice sobre la última fila PRE_TRADE/PENDIENTE si existe
# - Si no existe, cae a la última fila “no cierre” antes del último cierre
# - Alinea features con features.pkl (si existe) o FEATURE_NAMES_DEFAULT
# - Si falla, deja ia_ready=False y ia_last_err con el motivo
# ==========================================================

_IA_ASSETS_CACHE = {"loaded": False, "model": None, "scaler": None, "features": None, "meta": None}

def _find_first_pickle(regex_list, exts=(".pkl", ".joblib")):
    try:
        files = os.listdir(".")
        for fn in files:
            low = fn.lower()
            if not low.endswith(exts):
                continue
            for rx in regex_list:
                try:
                    if re.search(rx, low):
                        return fn
                except Exception:
                    continue
    except Exception:
        pass
    return None

def _load_ia_assets_once(force: bool = False):
    """
    Carga assets desde globals si existen; si no, autodetecta en disco.
    IMPORTANTE: si al arrancar no había modelo/scaler y luego aparecen (por entrenamiento),
    con force=True se recarga y no se queda “pegado”.
    """
    # Si ya se cargó y no pedimos fuerza, salimos
    if _IA_ASSETS_CACHE.get("loaded", False) and (not force):
        return

    g = globals()

    # 1) Preferir objetos en memoria (después de entrenar)
    model  = g.get("modelo_ia") or g.get("IA_MODELO") or g.get("modelo_oracle") or g.get("oracle_model") or None
    scaler = g.get("scaler_ia") or g.get("IA_SCALER") or g.get("oracle_scaler") or None
    feats  = g.get("feature_names_ia") or g.get("FEATURE_NAMES_USADAS") or g.get("FEATURE_NAMES_MODEL") or None
    meta   = g.get("meta_ia") or g.get("IA_META") or g.get("oracle_meta") or None

    # 2) Fallback: disco (tus “4 artefactos”)
    if model is None:
        mfile = globals().get("_MODEL_PATH", "modelo_xgb.pkl")
        if not os.path.exists(mfile):
            mfile = _find_first_pickle([r"modelo", r"model", r"xgb"])
        if mfile:
            try:
                model = joblib.load(mfile)
            except Exception:
                model = None

    if scaler is None:
        sfile = globals().get("_SCALER_PATH", "scaler.pkl")
        if not os.path.exists(sfile):
            sfile = _find_first_pickle([r"scaler"])
        if sfile:
            try:
                scaler = joblib.load(sfile)
            except Exception:
                scaler = None

    if feats is None:
        ffile = globals().get("_FEATURES_PATH", "feature_names.pkl")
        if not os.path.exists(ffile):
            ffile = _find_first_pickle([r"features", r"feature_names"])
        if ffile:
            try:
                feats = joblib.load(ffile)
            except Exception:
                feats = None

    if meta is None:
        metafile = _find_first_pickle([r"meta"])
        if metafile:
            try:
                meta = joblib.load(metafile)
            except Exception:
                meta = None

    _IA_ASSETS_CACHE.update({
        "loaded": True,
        "model": model,
        "scaler": scaler,
        "features": feats,
        "meta": meta
    })

def _features_model_list():
    _load_ia_assets_once()
    feats = _IA_ASSETS_CACHE.get("features")
    # features.pkl puede venir como list o dict
    if isinstance(feats, list) and feats:
        return list(feats)
    if isinstance(feats, dict) and feats.get("features"):
        try:
            return list(feats["features"])
        except Exception:
            pass
    # fallback canónico
    return list(FEATURE_NAMES_DEFAULT)

def _add_derived_for_model(d: dict):
    """Si el modelo espera features derivadas, créalas aquí."""
    try:
        racha = float(d.get("racha_actual", 0.0) or 0.0)
    except Exception:
        racha = 0.0

    d["racha_signo"] = 1.0 if racha > 0 else (-1.0 if racha < 0 else 0.0)
    d["racha_abs"] = abs(racha)
    d["rebote_fuerte"] = 1.0 if abs(racha) >= 6 else 0.0

    # Interacciones (si no existen, se arman igual)
    try:
        payout = float(d.get("payout", 0.0) or 0.0)
    except Exception:
        payout = 0.0
    try:
        pe = float(d.get("puntaje_estrategia", 0.0) or 0.0)
    except Exception:
        pe = 0.0
    try:
        vol = float(d.get("volatilidad", 0.0) or 0.0)
    except Exception:
        vol = 0.0
    try:
        brk = float(d.get("breakout", 0.0) or 0.0)
    except Exception:
        brk = 0.0
    try:
        hb = float(d.get("hora_bucket", 0.0) or 0.0)
    except Exception:
        hb = 0.0
    try:
        er = float(d.get("es_rebote", 0.0) or 0.0)
    except Exception:
        er = 0.0

    d["pay_x_puntaje"] = payout * pe
    d["vol_x_breakout"] = vol * brk
    d["hora_x_rebote"] = hb * er
    d["racha_x_rebote"] = racha * er
    try:
        rsi_rev = float(d.get("rsi_reversion", 0.0) or 0.0)
    except Exception:
        rsi_rev = 0.0
    d["rev_x_breakout"] = rsi_rev * brk

    return d

def leer_ultima_fila_features_para_pred(bot: str) -> dict | None:
    """
    Lee features para PREDICCIÓN (sin label):
    - Prefiere trade_status PRE_TRADE/PENDIENTE/OPEN/ABIERTO
    - Fallback: última fila “no cierre” antes del último cierre
    - Anti-leakage: elimina campos de cierre (ganancia/profit/resultado) del dict final
    """
    ruta = f"registro_enriquecido_{bot}.csv"
    if not os.path.exists(ruta):
        return None

    df = None
    for enc in ("utf-8", "latin-1", "windows-1252"):
        try:
            df = pd.read_csv(ruta, sep=",", encoding=enc, engine="python", on_bad_lines="skip")
            break
        except Exception:
            continue
    if df is None or df.empty:
        return None

    # Normalizar resultado si existe
    if "resultado" in df.columns:
        df["resultado_norm"] = df["resultado"].apply(normalizar_resultado)
    else:
        df["resultado_norm"] = "INDEFINIDO"

    # Normalizar trade_status de forma canónica (evita CLOSED/SETTLED vs CERRADO)
    has_trade_status = (("trade_status" in df.columns) or ("trade_status_norm" in df.columns))

    if has_trade_status:
        if "trade_status_norm" in df.columns:
            df["trade_status_norm"] = df["trade_status_norm"].apply(normalizar_trade_status)
        else:
            df["trade_status_norm"] = df["trade_status"].apply(normalizar_trade_status)
    else:
        df["trade_status_norm"] = ""

    # 1) preferir PRE_TRADE/PENDIENTE
    pre = None
    pre_idx = None
    if has_trade_status:
        df_pre = df[df["trade_status_norm"].isin(["PENDIENTE", "PRE_TRADE", "OPEN", "ABIERTO"])].copy()
        # evitar “filas basura”: no usar cierres
        if "resultado_norm" in df_pre.columns:
            df_pre = df_pre[~df_pre["resultado_norm"].isin(["GANANCIA", "PÉRDIDA"])].copy()
        if not df_pre.empty:
            pre_idx = int(df_pre.index[-1])
            pre = df_pre.iloc[-1].to_dict()

    # 2) fallback: tomar última fila antes del último cierre que no sea cierre
    if pre is None:
        df_cerr = df[df["resultado_norm"].isin(["GANANCIA", "PÉRDIDA"])].copy()
        if has_trade_status:
            df_cerr = df_cerr[df_cerr["trade_status_norm"].eq("CERRADO")].copy()
        if not df_cerr.empty:
            idx_close = df_cerr.index[-1]
            try:
                df_before = df.loc[df.index <= idx_close].copy()
            except Exception:
                df_before = df.copy()
        else:
            df_before = df.copy()

        cand = df_before[~df_before["resultado_norm"].isin(["GANANCIA", "PÉRDIDA"])].copy()
        if not cand.empty:
            pre_idx = int(cand.index[-1])
            pre = cand.iloc[-1].to_dict()
        else:
            pre_idx = int(df_before.index[-1])
            pre = df_before.iloc[-1].to_dict()

    if pre is None:
        return None

    row = dict(pre)

    # Señales evento desde historial (sin futuro) para evitar cruce/breakout pegados.
    try:
        if pre_idx is None:
            pre_idx = int(df.index[-1])
        row = _calcular_eventos_pretrade_desde_historial(df, int(pre_idx), row_base=row)
    except Exception:
        pass

    # Meta trazable del origen (diagnóstico anti-clonado por bot/tick)
    try:
        row["__src_path"] = str(ruta)
        row["__src_epoch"] = row.get("epoch", None)
        row["__src_ts"] = row.get("ts", row.get("timestamp", row.get("fecha", None)))
        row["__src_symbol"] = row.get("symbol", row.get("activo", row.get("market", row.get("underlying", ""))))
    except Exception:
        pass

    # 🔒 Anti-leakage duro
    for k in ("ganancia_perdida", "profit", "resultado", "resultado_norm"):
        try:
            row.pop(k, None)
        except Exception:
            pass

    # Completar y normalizar base 13 features como haces en leer_ultima_fila_con_resultado
    # payout feature (ROI 0..1.5)
    try:
        roi = calcular_payout_feature(row)
    except Exception:
        roi = None
    if roi is None:
        return None
    row["payout"] = float(max(0.0, min(float(roi), 1.5)))

    # volatilidad / hora_bucket / es_rebote / puntaje_estrategia
    try:
        vol = _safe_float(row.get("volatilidad"))
        if vol is None:
            vol = calcular_volatilidad_simple(row)
        try:
            volf = float(vol)
        except Exception:
            volf = float("nan")
        if (not math.isfinite(volf)) or volf <= 0.0:
            vol_hist = calcular_volatilidad_por_bot(bot, lookback=50)
            if vol_hist is not None:
                volf = float(vol_hist)
        if (not math.isfinite(volf)):
            return None
        row["volatilidad"] = float(max(0.0, min(float(volf), 1.0)))
    except Exception:
        return None

    try:
        hb = _safe_float(row.get("hora_bucket"))
        if hb is None:
            hb, hm = calcular_hora_features(row)
            row["hora_missing"] = float(hm)
        row["hora_bucket"] = float(max(0.0, min(float(hb), 1.0)))
    except Exception:
        return None

    # enriquecer señales evento (incluye es_rebote / cruce / breakout / rsi_reversion / puntaje)
    try:
        row = enriquecer_features_evento(row)
    except Exception:
        pass

    try:
        er = _safe_float(row.get("es_rebote"))
        if er is None:
            er = calcular_es_rebote(row)
        row["es_rebote"] = float(max(0.0, min(float(er), 1.0)))
    except Exception:
        return None

    try:
        pe = calcular_puntaje_estrategia_normalizado(row)
        row["puntaje_estrategia"] = float(max(0.0, min(float(pe), 1.0)))
    except Exception:
        # fallback a lo que exista
        pe_raw = _safe_float(row.get("puntaje_estrategia"))
        if pe_raw is None:
            return None
        row["puntaje_estrategia"] = float(max(0.0, min(float(pe_raw), 1.0)))

    # Derived extras (por si el modelo los espera)
    row = _add_derived_for_model(row)

    # Clip defensivo si existe tu helper
    try:
        # usa el set esperado por el modelo (solo recorta lo que exista)
        fnames = _features_model_list()
        row = clip_feature_values(row, fnames)
    except Exception:
        pass

    # Huella de fila para trazabilidad de lectura por bot
    try:
        core = ["rsi_9", "rsi_14", "sma_5", "sma_spread", "payout", "volatilidad", "hora_bucket"]
        parts = []
        for k in core:
            vv = row.get(k, None)
            try:
                vv = float(vv)
                if not math.isfinite(vv):
                    vv = 0.0
            except Exception:
                vv = 0.0
            parts.append(f"{k}={round(vv, 6)}")
        row["__src_row_hash"] = hashlib.sha1("|".join(parts).encode("utf-8", errors="ignore")).hexdigest()[:12]
    except Exception:
        row["__src_row_hash"] = ""

    return row

def _coerce_float_default(v, default=0.0) -> float:
    try:
        if v is None:
            return float(default)
        if isinstance(v, str):
            v = v.strip()
            if v == "":
                return float(default)
        x = float(v)
        if not np.isfinite(x):
            return float(default)
        return float(x)
    except Exception:
        return float(default)

def _predict_prob_low_data_from_row(row: dict) -> float:
    """Heurística estable para mostrar Prob IA en LOW_DATA cuando no hay modelo."""
    try:
        racha = float(row.get("racha_actual", 0.0) or 0.0)
    except Exception:
        racha = 0.0
    try:
        rsi9 = float(row.get("rsi_9", 50.0) or 50.0)
    except Exception:
        rsi9 = 50.0
    try:
        rev = float(row.get("rsi_reversion", 0.0) or 0.0)
    except Exception:
        rev = 0.0
    try:
        vol = float(row.get("volatilidad", 0.5) or 0.5)
    except Exception:
        vol = 0.5

    score = 0.50
    score += max(-0.08, min(0.10, 0.018 * racha))
    score += 0.06 if rev >= 0.5 else 0.0
    score += 0.04 if rsi9 <= 30 else (-0.03 if rsi9 >= 70 else 0.0)
    score += 0.02 if vol <= 0.35 else (-0.02 if vol >= 0.8 else 0.0)
    return float(max(0.20, min(0.80, score)))


def _polarizar_prob_simetrica(prob: float, reliable: bool = False) -> float:
    """Amplía contraste entre verdes/rojos de forma simétrica alrededor de 50%."""
    try:
        p = float(max(0.0, min(1.0, float(prob))))
        if not bool(IA_PROB_POLARIZE_ENABLE):
            return p
        c = float(max(0.35, min(0.65, float(IA_PROB_POLARIZE_CENTER))))
        f = float(IA_PROB_POLARIZE_FACTOR_RELIABLE if reliable else IA_PROB_POLARIZE_FACTOR_UNRELIABLE)
        f = float(max(1.0, min(2.5, f)))
        out = c + ((p - c) * f)
        return float(max(0.02, min(0.98, out)))
    except Exception:
        return float(max(0.0, min(1.0, float(prob))))


def predecir_prob_ia_bot(bot: str) -> tuple[float | None, str | None]:
    """
    Retorna (prob, err). prob en 0..1.
    NO devuelve 0 "por defecto": si falla, devuelve (None, CODIGO_ERROR).
    """
    try:
        # 1) Cargar assets (y recargar si aparecieron luego del boot)
        _load_ia_assets_once()
        model = _IA_ASSETS_CACHE.get("model")
        scaler = _IA_ASSETS_CACHE.get("scaler")

        if model is None:
            _load_ia_assets_once(force=True)
            model = _IA_ASSETS_CACHE.get("model")
            scaler = _IA_ASSETS_CACHE.get("scaler")

        # 2) Leer fila de features para pred (sin label)
        row = leer_ultima_fila_features_para_pred(bot)
        if row is None:
            return None, "NO_FEATURE_ROW"

        if model is None:
            # Modo LOW_DATA: aún sin modelo, pero entrega prob heurística para no quedar en OFF.
            try:
                global _IA_NO_MODEL_LOG_TS
                now_nm = time.time()
                if (now_nm - float(_IA_NO_MODEL_LOG_TS or 0.0)) >= float(IA_NO_MODEL_LOG_COOLDOWN_S):
                    _IA_NO_MODEL_LOG_TS = now_nm
                    agregar_evento("ℹ️ IA LOW_DATA activa: aún sin modelo; mostrando prob heurística temporal.")
            except Exception:
                pass
            p0 = _predict_prob_low_data_from_row(row)
            return float(p0), "LOW_DATA"

        # 3) Lista de features esperadas por el modelo (features.pkl si existe)
        feats = _features_model_list()
        if not feats:
            return None, "NO_FEATS"

        # 4) Armar X con orden exacto + detectar faltantes reales (evitar vector plano silencioso)
        values = []
        missing_feats = []
        present_feats = 0
        for k in feats:
            v = row.get(k, None)
            is_missing = False
            if v is None:
                is_missing = True
            else:
                try:
                    if isinstance(v, float) and np.isnan(v):
                        is_missing = True
                except Exception:
                    pass
                if isinstance(v, str) and v.strip() in ("", "--", "None", "nan", "NaN"):
                    is_missing = True

            if is_missing:
                missing_feats.append(k)
            else:
                present_feats += 1

            values.append(_coerce_float_default(v, default=0.0))

        total_feats = max(1, len(feats))
        present_ratio = float(present_feats) / float(total_feats)

        # Guardar snapshot técnico por bot para depuración de pipeline
        try:
            estado_bots[bot]["ia_debug_src_path"] = str(row.get("__src_path", ""))
            estado_bots[bot]["ia_debug_src_epoch"] = str(row.get("__src_epoch", ""))
            estado_bots[bot]["ia_debug_src_ts"] = str(row.get("__src_ts", ""))
            estado_bots[bot]["ia_debug_row_hash"] = str(row.get("__src_row_hash", ""))
            estado_bots[bot]["ia_debug_missing_feats"] = int(len(missing_feats))
            estado_bots[bot]["ia_debug_present_ratio"] = float(present_ratio)
        except Exception:
            pass

        # Si faltan demasiadas features esperadas, no inventar probabilidad.
        if present_ratio < 0.60:
            return None, f"FEAT_MISMATCH:{present_feats}/{total_feats}"

        X = pd.DataFrame([values], columns=list(feats))

        # 5) Escalado (si existe)
        X_in = X
        if scaler is not None:
            try:
                # Si el scaler fue fit con nombres, intentamos alinear
                if hasattr(scaler, "feature_names_in_") and scaler.feature_names_in_ is not None:
                    need = list(scaler.feature_names_in_)
                    # reindexa (si falta algo -> 0.0)
                    X_in = X.reindex(columns=need, fill_value=0.0)
                else:
                    X_in = X

                # StandardScaler no acepta NaN: blindaje final
                X_in = X_in.replace([np.inf, -np.inf], 0.0).fillna(0.0)

                X_scaled = scaler.transform(X_in)
            except Exception as e:
                return None, f"SCALER_FAIL:{type(e).__name__}"

        else:
            # sin scaler, usamos valores crudos
            X_scaled = X_in.replace([np.inf, -np.inf], 0.0).fillna(0.0).values

        # 6) Predict proba
        try:
            p_raw = None
            p_cal = None

            # Si el modelo está calibrado (wrapper), exponemos cruda vs calibrada.
            if hasattr(model, "modelo_base") and hasattr(model, "_calibrar_p"):
                proba_raw = model.modelo_base.predict_proba(X_scaled)
                p_raw = _extraer_probabilidad_clase_positiva(model.modelo_base, proba_raw, default_idx=1)
                if p_raw is None:
                    return None, "PRED_FAIL:BAD_PROBA_RAW"
                p_cal_arr = model._calibrar_p(np.asarray([float(p_raw)], dtype=float))
                p_cal = float(np.asarray(p_cal_arr, dtype=float).reshape(-1)[0])
                p = float(p_cal)
            else:
                proba = model.predict_proba(X_scaled)
                p = _extraer_probabilidad_clase_positiva(model, proba, default_idx=1)
                if p is None:
                    return None, "PRED_FAIL:BAD_PROBA"
                p_raw = float(p)
                p_cal = float(p)
        except Exception as e:
            return None, f"PRED_FAIL:{type(e).__name__}"

        if not np.isfinite(p):
            return None, "PROB_NAN"

        # clamp
        p = max(0.0, min(1.0, p))
        try:
            estado_bots[bot]["ia_prob_raw_model"] = float(max(0.0, min(1.0, float(p_raw if p_raw is not None else p))))
            estado_bots[bot]["ia_prob_cal_model"] = float(max(0.0, min(1.0, float(p_cal if p_cal is not None else p))))
        except Exception:
            pass
        return p, None

    except Exception as e:
        return None, f"IA_ERR:{type(e).__name__}"

def _extraer_probabilidad_clase_positiva(model, proba_arr, default_idx: int = 1) -> float | None:
    """Extrae P(y=1) respetando model.classes_ cuando exista."""
    try:
        arr = np.asarray(proba_arr, dtype=float)
        if arr.ndim == 1:
            arr = arr.reshape(1, -1)
        if arr.ndim != 2 or arr.shape[0] < 1 or arr.shape[1] < 1:
            return None

        idx = int(default_idx)
        try:
            classes = list(getattr(model, "classes_", []) or [])
            if classes:
                # Forzamos búsqueda de etiqueta positiva 1 (ganancia)
                if 1 in classes:
                    idx = int(classes.index(1))
                elif "1" in classes:
                    idx = int(classes.index("1"))
        except Exception:
            pass

        idx = max(0, min(int(idx), int(arr.shape[1]) - 1))
        p = float(arr[0][idx])
        if not np.isfinite(p):
            return None
        return float(max(0.0, min(1.0, p)))
    except Exception:
        return None


# --- Updater: NO fuerces prob_ia=0 cuando falla ---
IA_PRED_TTL_S = 180.0          # si falla por mucho tiempo, recién se limpia a None
IA_PRED_MIN_INTERVAL_S = 2.0   # anti-spam de predicción
_last_pred_ts = {b: 0.0 for b in BOT_NAMES}
_IA_CLONED_PROB_TICKS = 0
_IA_INPUT_DUP_INFO = {"signature": "", "ts": 0.0, "bots": []}
_LAST_AUTO_RETRAIN_TICK = 0.0
_IA_TRAIN_CLEAN_LOG = {"ts": 0.0, "sig": ""}
_IA_NO_MODEL_LOG_TS = 0.0
_IA_TIEBREAK_LOG_TS = 0.0

def actualizar_prob_ia_bot(bot: str):
    """
    Actualiza estado_bots[bot]['prob_ia'] de forma segura:
    - Si hay prob válida: la escribe, define modo_ia y marca ia_ready=True.
    - Si falla: NO pisa prob_ia a 0. Conserva último valor por TTL para no vaciar el HUD.
    """
    try:
        now = time.time()
        last = float(_last_pred_ts.get(bot, 0.0) or 0.0)
        if (now - last) < IA_PRED_MIN_INTERVAL_S:
            return
        _last_pred_ts[bot] = now

        # Guardrail duro: solo invalidar cuando se detecta CLON REAL de origen en este tick.
        if bool(estado_bots.get(bot, {}).get("ia_input_duplicado", False)):
            estado_bots[bot]["ia_ready"] = False
            estado_bots[bot]["ia_last_err"] = "INPUT_DUPLICADO"
            estado_bots[bot]["modo_ia"] = "input_dup"
            estado_bots[bot]["ia_senal_pendiente"] = False
            estado_bots[bot]["ia_prob_senal"] = None
            # Evita mostrar probabilidad stale (ej. 32.4% clonada) cuando la entrada es inválida.
            estado_bots[bot]["prob_ia"] = None
            estado_bots[bot]["prob_ia_oper"] = None
            return

        p, err = predecir_prob_ia_bot(bot)

        if p is not None:
            p = _aplicar_orientacion_prob(float(p))
            p = _ajustar_prob_operativa(float(p))
            p = _ajustar_prob_por_evidencia_bot(bot, float(p))
            p = _ajustar_prob_por_racha_reciente(bot, float(p))
            try:
                meta_local_pol = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
                reliable_pol = bool(meta_local_pol.get("reliable", False))
            except Exception:
                reliable_pol = False
            p = _polarizar_prob_simetrica(float(p), reliable=reliable_pol)
            try:
                estado_bots[bot]["ia_prob_pre_cap"] = float(max(0.0, min(1.0, float(p))))
            except Exception:
                pass
            p_diag = float(max(0.0, min(1.0, float(p))))
            p_oper = _cap_prob_por_madurez(float(p_diag), bot=bot)
            p_oper = _cap_prob_por_sobreconfianza(float(p_oper))
            p_oper = _cap_prob_por_guardrail_ia_fuerte(float(p_oper), bot=bot)
            # prob_ia = lectura diagnóstica visible (sin hard-cap); prob_ia_oper = valor operativo para AUTO/REAL.
            estado_bots[bot]["prob_ia"] = float(p_diag)
            estado_bots[bot]["prob_ia_oper"] = float(p_oper)
            estado_bots[bot]["ia_ready"] = True
            estado_bots[bot]["ia_last_err"] = None
            estado_bots[bot]["ia_last_prob_ts"] = now

            # FIX UI/AUTO: garantizar modo_ia distinto de OFF cuando hay predicción.
            try:
                if str(err or "").upper().startswith("LOW_DATA"):
                    estado_bots[bot]["modo_ia"] = "low_data"
                else:
                    meta_local = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
                    reliable = bool(meta_local.get("reliable", False))
                    n_samples = int(meta_local.get("n_samples", meta_local.get("n", 0)) or 0)
                    if reliable:
                        modo = "confiable"
                    elif n_samples >= int(MIN_FIT_ROWS_LOW):
                        modo = "modelo"
                    else:
                        modo = "low_data"
                    estado_bots[bot]["modo_ia"] = modo
            except Exception:
                estado_bots[bot]["modo_ia"] = "low_data" if str(err or "").upper().startswith("LOW_DATA") else "modelo"
            return

        # fallo: no mates la última prob, solo marca error
        estado_bots[bot]["ia_last_err"] = err or "ERR"

        # Fallback activo: si la predicción del modelo falla, intentamos prob exploratoria
        # para no dejar el HUD en "-- | OFF" durante warmup/desalineaciones temporales.
        try:
            row_fb = leer_ultima_fila_features_para_pred(bot)
        except Exception:
            row_fb = None
        if isinstance(row_fb, dict):
            try:
                p_fb = float(_predict_prob_low_data_from_row(row_fb))
            except Exception:
                p_fb = None
            if isinstance(p_fb, (int, float)) and np.isfinite(float(p_fb)):
                p_fb = float(max(0.0, min(1.0, float(p_fb))))
                estado_bots[bot]["prob_ia"] = p_fb
                estado_bots[bot]["prob_ia_oper"] = p_fb
                estado_bots[bot]["ia_ready"] = True
                estado_bots[bot]["ia_last_prob_ts"] = now
                estado_bots[bot]["modo_ia"] = "low_data"
                return

        # si hace demasiado que no hay prob válida, limpia a None
        last_ok = float(estado_bots[bot].get("ia_last_prob_ts", 0.0) or 0.0)
        age = (now - last_ok) if last_ok > 0 else 10**9

        err_txt = str(err or "")
        hard_invalid = err_txt.startswith("FEAT_MISMATCH") or err_txt.startswith("NO_FEATURE_ROW") or err_txt.startswith("SCALER_FAIL")

        if (not hard_invalid) and age <= IA_PRED_TTL_S and estado_bots[bot].get("prob_ia") is not None:
            # Mantener último dato útil para que la UI no quede en '--'.
            estado_bots[bot]["ia_ready"] = True
            estado_bots[bot]["modo_ia"] = _modo_ia_por_error(err, tiene_prob=True)
        else:
            estado_bots[bot]["ia_ready"] = False
            estado_bots[bot]["prob_ia"] = None
            estado_bots[bot]["modo_ia"] = _modo_ia_por_error(err, tiene_prob=False)

    except Exception:
        # ultra defensivo: no romper loop
        try:
            estado_bots[bot]["ia_ready"] = False
            estado_bots[bot]["ia_last_err"] = "UPD_ERR"
        except Exception:
            pass


def _modo_ia_por_error(err: str | None, tiene_prob: bool = False) -> str:
    """Mapea errores de predicción a un modo IA legible para HUD/operativa."""
    txt = str(err or "").strip().upper()
    if tiene_prob:
        return "stale"
    if not txt:
        return "low_data"
    if txt.startswith("LOW_DATA") or txt.startswith("NO_FEATURE_ROW") or txt.startswith("NO_FEATS"):
        return "low_data"
    if txt.startswith("IA_ERR"):
        return "low_data"
    if txt.startswith("INPUT_DUPLICADO"):
        return "input_dup"
    if txt.startswith("FEAT_MISMATCH") or txt.startswith("SCALER_FAIL") or txt.startswith("PRED_FAIL"):
        return "off"
    return "low_data"

def _desempatar_probs_ia_por_bot() -> None:
    """
    Si varias Prob IA quedan prácticamente idénticas en un tick,
    aplica un micro-ajuste por evidencia reciente del bot para romper empates.

    Objetivo: evitar que todos los bots muestren exactamente el mismo valor (p. ej. 78.1%)
    cuando el modelo queda temporalmente poco discriminante.
    """
    global _IA_TIEBREAK_LOG_TS
    try:
        live = []
        for b in BOT_NAMES:
            st = estado_bots.get(b, {})
            p = st.get("prob_ia", None)
            if not bool(st.get("ia_ready", False)):
                continue
            if not isinstance(p, (int, float)):
                continue
            pf = float(p)
            if not np.isfinite(pf):
                continue
            live.append((b, pf))

        if len(live) < 2:
            return

        try:
            meta = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
            n_samples = int(meta.get("n_samples", meta.get("n", 0)) or 0)
            warmup = bool(meta.get("warmup_mode", n_samples < int(TRAIN_WARMUP_MIN_ROWS)))
            if warmup:
                return
        except Exception:
            pass

        probs = [x[1] for x in live]
        spread = max(probs) - min(probs)
        uniq4 = len({round(v, 4) for v in probs})

        # Solo actuar en empate/casi empate real.
        if spread >= 0.002 and uniq4 >= 3:
            return

        changed = []
        for b, pb in live:
            st = estado_bots.get(b, {})
            g = int(st.get("ganancias", 0) or 0)
            d = int(st.get("perdidas", 0) or 0)
            # WR suavizado (Beta(1,1)) para no sobrecastigar n bajo.
            wr = float((g + 1.0) / (g + d + 2.0))
            edge = float(max(-0.5, min(0.5, wr - 0.5)))
            # Micro-ajuste: máximo ±1pp.
            delta = float(max(-0.01, min(0.01, edge * 0.02)))
            p_new = float(max(0.0, min(1.0, pb + delta)))
            estado_bots[b]["prob_ia"] = p_new
            changed.append((b, pb, p_new))

        now = time.time()
        if changed and ((now - float(_IA_TIEBREAK_LOG_TS or 0.0)) >= 20.0):
            _IA_TIEBREAK_LOG_TS = now
            top = sorted(changed, key=lambda x: x[2], reverse=True)[:3]
            txt = ", ".join([f"{b}:{o*100:.1f}→{n*100:.1f}%" for b, o, n in top])
            agregar_evento(f"🧭 IA tiebreak: desempate leve por evidencia ({txt}).")
    except Exception:
        pass


def actualizar_prob_ia_todos():
    """
    Tick único para el panel:
      1) Cierra señales en IA_SIGNALS_LOG (Real vs Ficción) usando los cierres del CSV del bot.
      2) Detecta input duplicado por fingerprint de features por bot.
      3) Actualiza Prob IA por bot (sin tocar la lógica de trading).
    """
    global _IA_CLONED_PROB_TICKS, _IA_INPUT_DUP_INFO

    # 0) Estado default por tick
    for b in BOT_NAMES:
        try:
            estado_bots[b]["ia_input_duplicado"] = False
            estado_bots[b]["ia_input_redundante"] = False
            estado_bots[b]["ia_input_dup_group"] = ""
        except Exception:
            pass

    # 1) Backfill / cierre de señales
    for b in BOT_NAMES:
        try:
            last = IA_AUDIT_LAST_CLOSE_EPOCH.get(b, None)
            tail_lines = 25000 if last is None else 6000
            max_events = 60 if last is None else 15
            ia_audit_scan_close(b, tail_lines=tail_lines, max_events=max_events)
        except Exception:
            pass

    # 2) Fingerprints por bot: detectar redundancia y SOLO invalidar si hay clon real de origen
    rows_by_bot = {}
    fp_map = {}
    try:
        for b in BOT_NAMES:
            row = leer_ultima_fila_features_para_pred(b)
            if row is None:
                continue
            rows_by_bot[b] = row
            fp = _fingerprint_features_row(row, feats=list(INCREMENTAL_FEATURES_V2))
            fp_map.setdefault(fp, []).append(b)

        dup_groups = [bots for bots in fp_map.values() if len(bots) >= 2]
        if dup_groups:
            now = time.time()
            for bots in dup_groups:
                sig = "+".join(sorted(bots))
                diag = _diagnosticar_inputs_duplicados(rows_by_bot, bots, feats=list(INCREMENTAL_FEATURES_V2))
                same_cols = diag.get("same_cols", [])
                expected = diag.get("expected_diff", [])
                src_info = diag.get("source_info", {}) if isinstance(diag, dict) else {}

                # Clon real SOLO si hay evidencia fuerte de misma lectura/fila (no por features iguales).
                clone_real = False
                source_keys_full = []
                source_keys_hash_ts_sym = []
                for bb in bots:
                    inf = src_info.get(bb, {}) if isinstance(src_info, dict) else {}
                    path = str(inf.get("path", "") or "")
                    hsh = str(inf.get("hash", "") or "")
                    tsv = str(inf.get("ts", "") or "")
                    sym = str(inf.get("symbol", "") or "")
                    source_keys_full.append((path, hsh, tsv))
                    source_keys_hash_ts_sym.append((hsh, tsv, sym))

                if source_keys_full:
                    ufull = set(source_keys_full)
                    uhash = set(source_keys_hash_ts_sym)
                    # Caso 1: misma fuente exacta (path/hash/ts) entre bots.
                    if len(ufull) == 1 and all(any(x for x in k) for k in ufull):
                        clone_real = True
                    # Caso 2: paths distintos pero misma fila/hash+timestamp+símbolo (clon probable por wiring).
                    elif len(uhash) == 1 and all(any(x for x in k) for k in uhash):
                        clone_real = True

                src_brief = []
                for bb in bots[:3]:
                    inf = src_info.get(bb, {}) if isinstance(src_info, dict) else {}
                    src_brief.append(f"{bb}:{inf.get('symbol','')}/{inf.get('hash','')}/{inf.get('ts','')}")

                msg_sig = f"{sig}|{','.join(same_cols[:6])}|clone={int(clone_real)}"
                should_emit = (
                    msg_sig != str(_IA_INPUT_DUP_INFO.get("signature", "")) or
                    (now - float(_IA_INPUT_DUP_INFO.get("ts", 0.0) or 0.0)) >= float(INPUT_DUP_DIAG_COOLDOWN_S)
                )

                for b in bots:
                    try:
                        estado_bots[b]["ia_input_duplicado"] = bool(clone_real)
                        estado_bots[b]["ia_input_dup_group"] = sig
                        estado_bots[b]["ia_input_redundante"] = not bool(clone_real)
                    except Exception:
                        pass

                if should_emit:
                    if clone_real:
                        agregar_evento(
                            "🛑 IA inválida por CLON REAL de input "
                            f"[{sig}] | cols_iguales={same_cols[:8]} | esperadas_diferir={expected} | src={src_brief}"
                        )
                    else:
                        agregar_evento(
                            "⚠️ IA redundante (NO invalida) "
                            f"[{sig}] | cols={same_cols[:4]}"
                        )
                    _IA_INPUT_DUP_INFO = {"signature": msg_sig, "ts": now, "bots": list(bots)}
    except Exception:
        pass

    # 3) Predicción / estado IA del bot
    for b in BOT_NAMES:
        try:
            actualizar_prob_ia_bot(b)
            p_live = estado_bots.get(b, {}).get("prob_ia", None)
            _actualizar_estado_suceso_bot(b, p_live if isinstance(p_live, (int, float)) else None)
        except Exception:
            pass

    # 3.5) Desempate leve cuando el modelo deja todas las probs casi idénticas.
    _desempatar_probs_ia_por_bot()

    # 4) Guardrail anti-clonado de probabilidades (síntoma downstream)
    try:
        div = _calcular_diversidad_prob_tick()
        if div.get("all_equal", False) and int(div.get("n_live", 0)) >= 2:
            _IA_CLONED_PROB_TICKS = int(_IA_CLONED_PROB_TICKS) + 1
        else:
            _IA_CLONED_PROB_TICKS = 0

        if int(_IA_CLONED_PROB_TICKS) >= int(CLONED_PROB_TICKS_ALERT):
            agregar_evento(
                f"🧪 DATA QUALITY: INPUT DUPLICADO (probs clonadas {div.get('n_live',0)}/{len(BOT_NAMES)} por {int(_IA_CLONED_PROB_TICKS)} ticks)."
            )
            _IA_CLONED_PROB_TICKS = 0
    except Exception:
        pass

    # 5) Checkpoint ligero de calibración cada bloque de cierres
    _maybe_emit_calibration_checkpoint(force=False)

def _sensor_plano_bot(bot: str, lookback: int = 80) -> tuple[bool, dict]:
    """Detecta si un bot tiene demasiadas features pegadas (dominancia alta)."""
    try:
        rep = _auditar_saturacion_features_bot(bot, lookback=int(lookback)) or {}
        dom = rep.get("dominance", {}) if isinstance(rep, dict) else {}
        n_rep = int(rep.get("n", 0) or 0) if isinstance(rep, dict) else 0
        hot = [k for k, v in dom.items() if isinstance(v, (int, float)) and float(v) >= float(IA_SENSOR_DOM_HOT)]
        if n_rep < int(IA_SENSOR_MIN_SAMPLE):
            return False, {"hot": hot, "dominance": dom, "n": n_rep, "warmup": True}
        return bool(len(hot) >= int(IA_SENSOR_MIN_HOT_FEATS)), {"hot": hot, "dominance": dom, "n": n_rep, "warmup": False}
    except Exception:
        return False, {"hot": [], "dominance": {}, "n": 0, "warmup": True}


def _calcular_indice_suceso_bot(bot: str, p_live: float | None = None, suceso_delta: float | None = None) -> float:
    """
    Índice Suceso 0..100 (momentum+ruptura+régimen+asimetría), robusto en warmup.
    """
    try:
        row = leer_ultima_fila_features_para_pred(bot) or {}

        def _f(k, d=0.0):
            try:
                return float(row.get(k, d) or d)
            except Exception:
                return float(d)

        breakout_strength = max(0.0, min(1.0, _f("breakout", 0.0)))
        rebote = max(0.0, min(1.0, _f("es_rebote", 0.0)))
        payout = max(0.0, min(1.5, _f("payout", 0.0))) / 1.5
        rsi14 = max(0.0, min(100.0, _f("rsi_14", 50.0)))
        momentum = abs(rsi14 - 50.0) / 50.0

        try:
            vol = max(0.0, min(1.0, _f("volatilidad", 0.0)))
        except Exception:
            vol = 0.0

        delta_term = 0.0
        if isinstance(suceso_delta, (int, float)):
            delta_term = max(0.0, min(1.0, float(suceso_delta) / max(1e-6, float(IA_SUCESO_DELTA_MIN))))

        p_term = 0.0
        if isinstance(p_live, (int, float)):
            p_term = max(0.0, min(1.0, (float(p_live) - 0.50) / 0.20))

        score = (
            0.26 * breakout_strength +
            0.20 * max(rebote, delta_term) +
            0.16 * momentum +
            0.14 * vol +
            0.14 * payout +
            0.10 * p_term
        )
        return float(max(0.0, min(100.0, score * 100.0)))
    except Exception:
        return 0.0


def _detectar_suceso_prob_bot(bot: str, p_now: float | None) -> tuple[bool, float]:
    """Detecta salto relativo de probabilidad vs su línea base reciente."""
    try:
        if not isinstance(p_now, (int, float)):
            return False, 0.0
        p = float(max(0.0, min(1.0, p_now)))
        st = estado_bots.get(bot, {})
        hist = st.get("ia_prob_hist_raw", None)
        if not isinstance(hist, list):
            hist = []
        hist.append(p)
        max_len = int(max(6, IA_SUCESO_LOOKBACK * 3))
        if len(hist) > max_len:
            hist = hist[-max_len:]
        st["ia_prob_hist_raw"] = hist
        estado_bots[bot] = st

        look = int(max(4, IA_SUCESO_LOOKBACK))
        prev = hist[:-1][-look:]
        if len(prev) < 4:
            return False, 0.0
        base = float(np.median(np.asarray(prev, dtype=float)))
        delta = float(p - base)
        return bool(delta >= float(IA_SUCESO_DELTA_MIN)), delta
    except Exception:
        return False, 0.0


def _evento_contexto_activo(bot: str) -> bool:
    """True si el contexto reciente sugiere evento en la escala real de features."""
    try:
        row = leer_ultima_fila_features_para_pred(bot) or {}
        brk = float(row.get("breakout", 0.0) or 0.0)
        reb = float(row.get("es_rebote", 0.0) or 0.0)

        vals = []
        rows = leer_features_bot(bot, n=int(IA_SUCESO_EVENTO_HIST))
        if isinstance(rows, list):
            for r in rows:
                if not isinstance(r, dict):
                    continue
                try:
                    vb = float(r.get("breakout", 0.0) or 0.0)
                    vr = float(r.get("es_rebote", 0.0) or 0.0)
                    v = max(vb, vr)
                    if np.isfinite(v):
                        vals.append(v)
                except Exception:
                    continue
        dyn_thr = float(IA_SUCESO_EVENTO_MIN)
        if vals:
            qv = float(np.quantile(np.asarray(vals, dtype=float), float(IA_SUCESO_EVENTO_Q)))
            dyn_thr = float(max(float(IA_SUCESO_EVENTO_MIN), min(0.95, qv)))

        return bool(max(brk, reb) >= dyn_thr)
    except Exception:
        return False


def _actualizar_estado_suceso_bot(bot: str, prob_live: float | None) -> None:
    """Ruta canónica única para actualizar telemetría/señal por suceso."""
    try:
        if prob_live is None or not isinstance(prob_live, (int, float)):
            estado_bots[bot]["ia_senal_pendiente"] = False
            estado_bots[bot]["ia_prob_senal"] = None
            estado_bots[bot]["ia_suceso_ok"] = False
            estado_bots[bot]["ia_suceso_delta"] = 0.0
            estado_bots[bot]["ia_suceso_idx"] = 0.0
            return

        p_live = float(prob_live)
        abs_gate = bool(p_live >= float(IA_VERDE_THR))
        suc_ok, suc_delta = _detectar_suceso_prob_bot(bot, p_live)
        evt_ok = _evento_contexto_activo(bot)
        redundante_tick = bool(estado_bots.get(bot, {}).get("ia_input_redundante", False))
        suceso_gate = bool(suc_ok and evt_ok)

        suceso_idx = _calcular_indice_suceso_bot(bot, p_live=p_live, suceso_delta=suc_delta)
        sensor_plano, sensor_meta = _sensor_plano_bot(bot, lookback=80)

        estado_bots[bot]["ia_suceso_delta"] = float(suc_delta)
        estado_bots[bot]["ia_suceso_ok"] = bool(suceso_gate)
        estado_bots[bot]["ia_suceso_idx"] = float(suceso_idx)
        estado_bots[bot]["ia_suceso_redundante"] = bool(redundante_tick)
        estado_bots[bot]["ia_sensor_plano"] = bool(sensor_plano)
        estado_bots[bot]["ia_sensor_hot_feats"] = list(sensor_meta.get("hot", []))
        estado_bots[bot]["ia_sensor_sample_n"] = int(sensor_meta.get("n", 0) or 0)
        estado_bots[bot]["ia_sensor_warmup"] = bool(sensor_meta.get("warmup", False))

        if abs_gate or suceso_gate:
            estado_bots[bot]["ia_senal_pendiente"] = True
            estado_bots[bot]["ia_prob_senal"] = float(p_live)
        else:
            estado_bots[bot]["ia_senal_pendiente"] = False
            estado_bots[bot]["ia_prob_senal"] = None
    except Exception:
        try:
            estado_bots[bot]["ia_senal_pendiente"] = False
            estado_bots[bot]["ia_prob_senal"] = None
        except Exception:
            pass


def actualizar_prob_ia_bots_tick():
    """Compat: ruta única de actualización IA (delegada)."""
    actualizar_prob_ia_todos()


def ia_prob_valida(bot: str, max_age_s: float = 10.0) -> bool:
    """
    True si:
    - ia_ready=True
    - prob_ia existe y es finita en [0..1]
    - timestamp reciente (<= max_age_s)
    """
    try:
        if bot not in estado_bots:
            return False

        if not bool(estado_bots[bot].get("ia_ready", False)):
            return False

        ts = float(estado_bots[bot].get("ia_last_prob_ts", 0.0) or 0.0)
        if ts <= 0:
            return False

        if (time.time() - ts) > float(max_age_s):
            return False

        p = estado_bots[bot].get("prob_ia", None)
        if p is None:
            return False

        p = float(p)
        if not np.isfinite(p):
            return False

        return (0.0 <= p <= 1.0)

    except Exception:
        return False
                                              
_AUTO_REAL_CACHE = {"ts": 0.0, "thr": float(IA_ACTIVACION_REAL_THR), "n": 0, "max": 0.0}


def _leer_probs_historicas_ia(max_rows: int = AUTO_REAL_LOG_MAX_ROWS) -> list[float]:
    """Lee probs históricas del log de señales IA cerradas para calibrar umbral REAL."""
    path = IA_SIGNALS_LOG
    if not os.path.exists(path):
        return []
    vals = []
    try:
        with open(path, "r", encoding="utf-8", newline="") as f:
            r = csv.DictReader(f)
            rows = list(r)
        if max_rows and len(rows) > int(max_rows):
            rows = rows[-int(max_rows):]
        for row in rows:
            try:
                p = float(str(row.get("prob", "")).replace(",", "."))
                if np.isfinite(p) and 0.0 <= p <= 1.0:
                    vals.append(p)
            except Exception:
                continue
    except Exception:
        return []
    return vals


def get_umbral_real_calibrado(force: bool = False) -> float:
    """
    Umbral adaptativo para activar REAL usando históricos + probabilidad viva actual.
    Reglas:
    - Histórico: cuantíl alto de ia_signals_log.prob (estabilidad).
    - Vivo: mejor prob IA actual de bots (sensibilidad al régimen actual).
    - Resultado: min(thr_hist, thr_live) acotado en [AUTO_REAL_THR_MIN .. AUTO_REAL_THR].
    """
    now = time.time()
    try:
        # En modo clásico, el umbral REAL debe mantenerse fijo al operativo (85%).
        if bool(REAL_CLASSIC_GATE):
            thr_fixed = float(IA_ACTIVACION_REAL_THR)
            _AUTO_REAL_CACHE["ts"] = now
            _AUTO_REAL_CACHE["thr"] = thr_fixed
            return thr_fixed

        if (not force) and ((now - float(_AUTO_REAL_CACHE.get("ts", 0.0) or 0.0)) < 8.0):
            return float(_AUTO_REAL_CACHE.get("thr", AUTO_REAL_THR_MIN))

        # 1) Histórico
        probs = _leer_probs_historicas_ia(AUTO_REAL_LOG_MAX_ROWS)
        if len(probs) >= 12:
            q_hist = float(np.quantile(np.array(probs, dtype=float), float(AUTO_REAL_TOP_Q)))
            thr_hist = q_hist - float(AUTO_REAL_MARGIN)
            pmax_hist = float(max(probs))
        else:
            thr_hist = float(AUTO_REAL_THR_MIN)
            pmax_hist = float(max(probs)) if probs else 0.0

        # 2) Vivo (último tick): si el mercado/modelo se aplana, el gate también baja
        live_probs = []
        for b in BOT_NAMES:
            try:
                if not ia_prob_valida(b, max_age_s=12.0):
                    continue
                p = float(_prob_ia_operativa_bot(b, default=0.0) or 0.0)
                if np.isfinite(p) and 0.0 <= p <= 1.0:
                    live_probs.append(p)
            except Exception:
                continue

        if len(live_probs) >= int(AUTO_REAL_LIVE_MIN_BOTS):
            pmax_live = float(max(live_probs))
            thr_live = pmax_live - float(AUTO_REAL_MARGIN)
        else:
            pmax_live = 0.0
            thr_live = float(AUTO_REAL_THR_MIN)

        thr_raw = min(float(thr_hist), float(thr_live))
        thr = max(float(AUTO_REAL_THR_MIN), min(float(AUTO_REAL_THR), float(thr_raw)))

        _AUTO_REAL_CACHE["ts"] = now
        _AUTO_REAL_CACHE["thr"] = float(thr)
        _AUTO_REAL_CACHE["n"] = int(len(probs))
        _AUTO_REAL_CACHE["max"] = float(max(pmax_hist, pmax_live))
        return float(thr)
    except Exception:
        return float(AUTO_REAL_THR_MIN)


def detectar_cierre_martingala(bot, min_fila=None, require_closed=True, require_real_token=False, expected_ciclo=None):
    """
    Devuelve: (resultado_norm, monto, ciclo, payout_total)
    - min_fila: solo acepta filas con número > min_fila (evita cierres viejos)
              Nota: min_fila se interpreta como "cantidad de filas de datos" (sin header),
              y cuadra con contar_filas_csv().
    - require_closed: si existe trade_status, exige CERRADO/CLOSED.
    - require_real_token: si hay columna de token/cuenta, ignora cierres DEMO.
    - expected_ciclo: si existe columna de ciclo, exige coincidencia con ese ciclo.
    """
    path = f"registro_enriquecido_{bot}.csv"
    if not os.path.exists(path):
        return None

    rows = None
    header = None

    for enc in ("utf-8", "latin-1", "windows-1252"):
        try:
            with open(path, "r", encoding=enc, errors="replace", newline="") as f:
                rows = list(csv.reader(f))
            if rows and len(rows) >= 2:
                header = rows[0]
                break
        except Exception:
            continue

    if not rows or not header or len(rows) < 2:
        return None

    # Mapa de columnas case-insensitive y con strip
    hmap = {}
    for i, h in enumerate(header):
        try:
            key = str(h).strip().lower()
            if key and key not in hmap:
                hmap[key] = i
        except Exception:
            pass

    def _col(*names):
        for n in names:
            k = str(n).strip().lower()
            if k in hmap:
                return hmap[k]
        return None

    i_res = _col("resultado", "result", "outcome")
    i_status = _col("trade_status", "status")
    i_monto = _col("monto", "stake", "buy_price", "amount")
    i_ciclo = _col("ciclo", "ciclo_martingala", "ciclo_actual", "marti_ciclo", "martingale_step")
    i_token = _col("token", "account", "account_type", "cuenta", "modo", "mode")
    # payout_total puede venir explícito o calculable
    # (extraer_payout_total ya se encarga, pero igual ayudamos con nombres)
    i_payout_total = _col("payout_total")
    i_payout_mult = _col("payout_multiplier")
    i_payout_dec = _col("payout_decimal_rounded")
    i_payout_legacy = _col("payout")  # legacy (ojo: a veces ROI feature, a veces ratio/total)

    if i_res is None:
        return None

    # Recorremos desde el final (último evento primero)
    for ridx in range(len(rows) - 1, 0, -1):
        row = rows[ridx]
        if not row:
            continue

        # ridx equivale a "número de fila de datos" (header está en 0)
        fila_num = ridx  # 1..N
        if min_fila is not None:
            try:
                if int(fila_num) <= int(min_fila):
                    break  # todo lo que sigue es más viejo todavía
            except Exception:
                pass

        # trade_status si aplica
        if require_closed and (i_status is not None) and (i_status < len(row)):
            st = str(row[i_status]).strip().upper()
            if st not in ("CERRADO", "CLOSED"):
                continue

        # Si el CSV informa token/cuenta, en REAL ignoramos cierres explícitos de DEMO.
        if require_real_token and (i_token is not None) and (i_token < len(row)):
            tok_raw = str(row[i_token] or "").strip().upper()
            if tok_raw:
                # Heurística robusta: DEMO en Deriv suele venir como VRTC*
                es_demo = ("DEMO" in tok_raw) or tok_raw.startswith("VRTC")
                es_real = ("REAL" in tok_raw) or tok_raw.startswith("CR")
                if es_demo and not es_real:
                    continue

        # resultado
        try:
            raw_res = row[i_res] if i_res < len(row) else ""
        except Exception:
            raw_res = ""
        res_norm = normalizar_resultado(raw_res)
        if res_norm not in ("GANANCIA", "PÉRDIDA"):
            continue

        # Armamos dict de fila para reutilizar tus extractores robustos
        row_dict_full = {}
        try:
            for j, h in enumerate(header):
                if j < len(row):
                    row_dict_full[str(h).strip()] = row[j]
        except Exception:
            row_dict_full = {}

        # Monto
        monto = None
        try:
            if i_monto is not None and i_monto < len(row):
                monto = _safe_float_local(row[i_monto])
        except Exception:
            monto = None

        # Ciclo
        ciclo = None
        try:
            if i_ciclo is not None and i_ciclo < len(row):
                ciclo = _safe_float_local(row[i_ciclo])
                ciclo = int(float(ciclo)) if ciclo is not None else None
        except Exception:
            ciclo = None

        # Si esperamos un ciclo concreto, exige que exista y coincida.
        if expected_ciclo is not None:
            try:
                if ciclo is None:
                    continue
                if int(ciclo) != int(expected_ciclo):
                    continue
            except Exception:
                continue

        # payout_total: preferimos extractor (maneja legacy y ratio)
        payout_total = None
        try:
            # Si el CSV trae explícito, dale prioridad
            if i_payout_total is not None and i_payout_total < len(row):
                payout_total = _safe_float_local(row[i_payout_total])
        except Exception:
            payout_total = None

        if payout_total is None:
            # Asegurar que el dict tenga keys útiles si existen en el CSV
            try:
                if i_payout_mult is not None and i_payout_mult < len(row):
                    row_dict_full["payout_multiplier"] = row[i_payout_mult]
                if i_payout_dec is not None and i_payout_dec < len(row):
                    row_dict_full["payout_decimal_rounded"] = row[i_payout_dec]
                if i_payout_legacy is not None and i_payout_legacy < len(row):
                    row_dict_full["payout"] = row[i_payout_legacy]
                if monto is not None:
                    row_dict_full["monto"] = monto
            except Exception:
                pass

            try:
                payout_total = extraer_payout_total(row_dict_full)
            except Exception:
                payout_total = None

        # Devolver lo encontrado (payout_total puede ser None si no hay info suficiente)
        try:
            monto_out = float(monto) if monto is not None else None
        except Exception:
            monto_out = None

        return (res_norm, monto_out, ciclo, payout_total)

    return None

def detectar_martingala_perdida_completa(bot):
    """
    Detecta si se perdió una Martingala completa:
    últimos MAX_CICLOS resultados definitivos son todos PÉRDIDA
    (con normalización robusta del resultado).
    """
    path = f"registro_enriquecido_{bot}.csv"
    if not os.path.exists(path):
        return False

    rows = None
    header = None
    for enc in ("utf-8", "latin-1", "windows-1252"):
        try:
            with open(path, "r", encoding=enc, errors="replace", newline="") as f:
                rows = list(csv.reader(f))
            if rows and len(rows) >= 2:
                header = rows[0]
                break
        except Exception:
            continue

    if not rows or not header or len(rows) < 2:
        return False

    def idx(col):
        return header.index(col) if col in header else None

    res_idx = idx("resultado")
    trade_idx = idx("trade_status")  # <- ahora sí existe siempre

    if res_idx is None:
        return False

    ult = []
    for row in reversed(rows[1:]):
        if not row or len(row) <= res_idx:
            continue

        # Si existe trade_status, exigir CERRADO para contar en rachas
        if trade_idx is not None:
            if len(row) <= trade_idx:
                continue
            ts = (row[trade_idx] or "").strip().upper()
            if ts != "CERRADO":
                continue

        res_norm = normalizar_resultado((row[res_idx] or "").strip())
        if res_norm not in ("GANANCIA", "PÉRDIDA"):
            continue

        ult.append(res_norm)
        if len(ult) >= MAX_CICLOS:
            break

    if len(ult) < MAX_CICLOS:
        return False

    return all(x == "PÉRDIDA" for x in ult)

# Reinicio completo - Corregido para no resetear métricas en modo suave
def reiniciar_completo(borrar_csv=False, limpiar_visual_segundos=15, modo_suave=True):
    global LIMPIEZA_PANEL_HASTA, marti_paso, marti_activa, marti_ciclos_perdidos, ultimo_bot_real, bots_usados_en_esta_marti, REAL_OWNER_LOCK
    with file_lock_required("real.lock", timeout=6.0, stale_after=30.0) as got:
        if got:
            write_token_atomic(TOKEN_FILE, "REAL:none")
        else:
            agregar_evento("⚠️ Reinicio: no se pudo escribir token_actual por lock ocupado (real.lock).")
    
    if borrar_csv and os.path.exists("dataset_incremental.csv"):
        os.remove("dataset_incremental.csv")

    for bot in BOT_NAMES:
        if borrar_csv:
            archivo = f"registro_enriquecido_{bot}.csv"
            if os.path.exists(archivo):
                os.remove(archivo)
            estado_bots[bot]["resultados"] = []
            huellas_usadas[bot] = set()
            estado_bots[bot]["ganancias"] = 0
            estado_bots[bot]["perdidas"] = 0
            estado_bots[bot]["porcentaje_exito"] = None
            estado_bots[bot]["tamano_muestra"] = 0
        elif not modo_suave:
            estado_bots[bot]["resultados"] = []
            estado_bots[bot]["ganancias"] = 0
            estado_bots[bot]["perdidas"] = 0
            estado_bots[bot]["porcentaje_exito"] = None
            estado_bots[bot]["tamano_muestra"] = 0
        estado_bots[bot].update({
            "token": "DEMO",
            "trigger_real": False,
            "prob_ia": None, "prob_ia_oper": None,
            "ia_ready": False,
            "ciclo_actual": 1,
            "modo_real_anunciado": False,
            "ultimo_resultado": None,
            "reintentar_ciclo": False,
            "remate_active": False,
            "remate_start": None,
            "remate_reason": "",
            "fuente": None,
            "real_activado_en": 0.0,  
            "ignore_cierres_hasta": 0.0,
            "real_timeout_first_warn": 0.0,
            "modo_ia": "low_data",
            "ia_seniales": 0,
            "ia_aciertos": 0,
            "ia_fallos": 0,
            "ia_senal_pendiente": False,
            "ia_prob_senal": None
        })
        SNAPSHOT_FILAS[bot] = contar_filas_csv(bot)
        OCULTAR_HASTA_NUEVO[bot] = False  # Cambiado para no ocultar
        IA53_TRIGGERED[bot] = False
        IA90_stats[bot] = {"n": 0, "ok": 0, "pct": 0.0, "pct_raw": 0.0, "pct_smooth": 50.0}
        if not isinstance(huellas_usadas.get(bot), set):
            huellas_usadas[bot] = set()
    eventos_recentes.clear()
    for b in BOT_NAMES:
        LAST_REAL_CLOSE_SIG[b] = None
    marti_paso = 0
    marti_activa = False
    marti_ciclos_perdidos = 0
    ultimo_bot_real = None
    bots_usados_en_esta_marti = []
    REAL_OWNER_LOCK = None
    LIMPIEZA_PANEL_HASTA = time.time() + limpiar_visual_segundos

# Reinicio de bot individual - Corregido similar
def reiniciar_bot(bot, borrar_csv=False):
    # Nunca reiniciar duro al owner REAL activo: durante una operación puede no
    # escribir filas por varios segundos y eso NO significa que deba volver a DEMO.
    owner_activo = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else None
    if owner_activo == bot or estado_bots.get(bot, {}).get("token") == "REAL":
        try:
            agregar_evento(f"🛡️ Reinicio omitido para {bot.upper()}: operación REAL en curso.")
        except Exception:
            pass
        return

    if borrar_csv:
        archivo = f"registro_enriquecido_{bot}.csv"
        if os.path.exists(archivo):
            os.remove(archivo)
        estado_bots[bot]["resultados"] = []
        huellas_usadas[bot] = set()
        estado_bots[bot]["ganancias"] = 0
        estado_bots[bot]["perdidas"] = 0
        estado_bots[bot]["porcentaje_exito"] = None
        estado_bots[bot]["tamano_muestra"] = 0
    estado_bots[bot].update({
        "token": "DEMO", 
        "trigger_real": False,
        "prob_ia": None, "prob_ia_oper": None,
        "ia_ready": False,
        "ciclo_actual": 1,
        "modo_real_anunciado": False,
        "ultimo_resultado": None,
        "reintentar_ciclo": False,
        "remate_active": False,
        "remate_start": None,
        "remate_reason": "",
        "fuente": None,
        "real_activado_en": 0.0,  
        "ignore_cierres_hasta": 0.0,
        "real_timeout_first_warn": 0.0,
        "modo_ia": "low_data",
        "ia_seniales": 0,
        "ia_aciertos": 0,
        "ia_fallos": 0,
        "ia_senal_pendiente": False,
        "ia_prob_senal": None
    })
    SNAPSHOT_FILAS[bot] = contar_filas_csv(bot)
    OCULTAR_HASTA_NUEVO[bot] = False  # Cambiado para no ocultar
    IA90_stats[bot] = {"n": 0, "ok": 0, "pct": 0.0, "pct_raw": 0.0, "pct_smooth": 50.0}
    LAST_REAL_CLOSE_SIG[bot] = None
    if not isinstance(huellas_usadas.get(bot), set):
        huellas_usadas[bot] = set()

def cerrar_por_fin_de_ciclo(bot: str, reason: str):
    global REAL_OWNER_LOCK, REAL_COOLDOWN_UNTIL_TS

    # Liberar token REAL en archivo primero (commit de salida)
    liberado = False
    try:
        with file_lock_required("real.lock", timeout=6.0, stale_after=30.0) as got:
            if got:
                liberado = bool(write_token_atomic(TOKEN_FILE, "REAL:none"))
                if not liberado:
                    agregar_evento("⚠️ Token REAL no liberado: fallo de persistencia en token_actual.txt.")
            else:
                agregar_evento("⚠️ Token REAL no liberado por lock ocupado (real.lock).")
    except Exception:
        liberado = False

    if not liberado:
        return

    # Liberación consolidada: recién aquí memoria/UI pasan a DEMO
    REAL_OWNER_LOCK = None
    REAL_COOLDOWN_UNTIL_TS = time.time() + float(_cooldown_post_trade_s())

    # Limpieza total de “estado REAL” para evitar HUD/estado fantasma
    try:
        estado_bots[bot]["token"] = "DEMO"
        estado_bots[bot]["trigger_real"] = False
        estado_bots[bot]["ciclo_actual"] = 1
        estado_bots[bot]["modo_real_anunciado"] = False
        estado_bots[bot]["fuente"] = None

        # ✅ Extra blindaje (evita “escudos” de cierre pegados en DEMO)
        estado_bots[bot]["real_activado_en"] = 0.0
        estado_bots[bot]["ignore_cierres_hasta"] = 0.0
        estado_bots[bot]["real_timeout_first_warn"] = 0.0

        # Flags IA/pending (si quedó algo colgado)
        estado_bots[bot]["ia_senal_pendiente"] = False
        estado_bots[bot]["ia_prob_senal"] = None

        # Remate limpio
        estado_bots[bot]["remate_active"] = False
        estado_bots[bot]["remate_start"] = None
        estado_bots[bot]["remate_reason"] = ""

    except Exception:
        pass

    # Limpiar orden REAL para evitar re-entradas fantasma (igual que cerrar_por_win)
    try:
        limpiar_orden_real(bot)
    except Exception:
        pass

    # Sync inmediato del HUD/token para evitar “REAL fantasma”
    try:
        _set_ui_token_holder(None)
    except Exception:
        pass

    # Actualizar snapshots para que no relea la misma fila
    try:
        REAL_ENTRY_BASELINE[bot] = 0
        SNAPSHOT_FILAS[bot] = contar_filas_csv(bot)
    except Exception:
        pass

    try:
        OCULTAR_HASTA_NUEVO[bot] = False
    except Exception:
        pass

    # Forzar refresco del loop principal
    try:
        reinicio_forzado.set()
    except Exception:
        pass

    # Log visual
    try:
        agregar_evento(f"🔓 Cuenta REAL liberada para {bot.upper()} ({reason})")
    except Exception:
        pass

def _marti_audit_record(kind: str, ciclo: int | None = None, bot: str | None = None, detalle: str = ""):
    """Guarda rastro compacto de la secuencia C1..C{MAX_CICLOS} para diagnóstico."""
    global marti_audit_historial
    try:
        c = int(ciclo) if ciclo is not None else None
    except Exception:
        c = None
    run = int(globals().get("marti_audit_run_id", 1) or 1)
    item = {
        "ts": time.strftime("%H:%M:%S"),
        "run": run,
        "kind": str(kind),
        "ciclo": c,
        "bot": str(bot) if bot else None,
        "detalle": str(detalle or ""),
    }
    try:
        marti_audit_historial.append(item)
    except Exception:
        pass


def _marti_audit_log_orden(ciclo: int, bot: str | None = None, origen: str = ""):
    """
    Verifica orden esperado C1->C{MAX_CICLOS} por corrida y deja eventos explícitos.
    No bloquea operación; solo audita y alerta desviaciones.
    """
    global marti_audit_run_id, marti_audit_desviaciones, marti_audit_ultimo_ciclo_ordenado
    try:
        c = max(1, min(int(MAX_CICLOS), int(ciclo)))
    except Exception:
        c = 1
    last = marti_audit_ultimo_ciclo_ordenado
    exp = 1 if last is None else (1 if int(last) >= int(MAX_CICLOS) else int(last) + 1)
    if int(c) != int(exp):
        marti_audit_desviaciones = int(marti_audit_desviaciones) + 1
        agregar_evento(
            f"🚨 MARTI-AUDIT run#{int(marti_audit_run_id)}: orden fuera de secuencia (esperado C{int(exp)}, llegó C{int(c)})."
        )
        _marti_audit_record("desvio", ciclo=c, bot=bot, detalle=f"esperado=C{exp} origen={origen}")
    else:
        _marti_audit_record("orden", ciclo=c, bot=bot, detalle=f"origen={origen}")
    marti_audit_ultimo_ciclo_ordenado = int(c)


def marti_audit_resumen_linea() -> str:
    """Línea compacta para HUD/eventos con estado de auditoría."""
    try:
        run = int(marti_audit_run_id)
        dv = int(marti_audit_desviaciones)
        ult = marti_audit_ultimo_ciclo_ordenado
        ult_txt = f"C{int(ult)}" if isinstance(ult, int) and ult > 0 else "--"
        return f"Audit run#{run} desvíos={dv} último={ult_txt}"
    except Exception:
        return "Audit run#? desvíos=? último=--"


def registrar_resultado_real(resultado: str, bot: str | None = None, ciclo_operado: int | None = None):
    """
    Actualiza el contador global de ciclos martingala para el HUD y la próxima
    autoasignación REAL.

    Reglas:
    - GANANCIA: resetea a ciclo #1 (contador de pérdidas = 0).
    - PÉRDIDA: incrementa ciclo hasta MAX_CICLOS (tope de blindaje).
    """
    global marti_ciclos_perdidos, marti_paso, ultimo_bot_real, bots_usados_en_esta_marti
    global marti_audit_run_id, marti_audit_ultimo_ciclo_ordenado

    res = normalizar_resultado(resultado)
    if bot in BOT_NAMES:
        ultimo_bot_real = bot

    if res == "GANANCIA":
        marti_ciclos_perdidos = 0
        marti_paso = 0
        bots_usados_en_esta_marti = []
        _marti_audit_record("cierre_ganancia", ciclo=ciclo_operado, bot=bot, detalle="reinicio_a_C1")
        marti_audit_run_id = int(marti_audit_run_id) + 1
        marti_audit_ultimo_ciclo_ordenado = None
        agregar_evento(f"✅ Martingala reiniciada en C1 por GANANCIA ({marti_audit_resumen_linea()}).")
    elif res == "PÉRDIDA":
        # Registrar el bot operado en la corrida activa para forzar rotación C2..C{MAX_CICLOS}.
        if bot in BOT_NAMES and bot not in bots_usados_en_esta_marti:
            bots_usados_en_esta_marti.append(bot)

        # Robustez anti-desincronización:
        # si conocemos el ciclo realmente operado, el próximo estado de pérdidas
        # debe ser al menos ese ciclo (p.ej. perder en C2 => pérdidas=2 => próximo C3).
        try:
            ciclo_ref = int(ciclo_operado) if ciclo_operado is not None else 0
        except Exception:
            ciclo_ref = 0
        marti_ciclos_perdidos = min(
            MAX_CICLOS,
            max(int(marti_ciclos_perdidos) + 1, max(0, ciclo_ref))
        )
        # Si ya culminó C{MAX_CICLOS}, reinicia a C1 para el siguiente turno.
        if int(marti_ciclos_perdidos) >= int(MAX_CICLOS):
            marti_ciclos_perdidos = 0
            marti_paso = 0
            bots_usados_en_esta_marti = []
            _marti_audit_record("cierre_tope", ciclo=ciclo_operado, bot=bot, detalle=f"tope=C{int(MAX_CICLOS)}")
            marti_audit_run_id = int(marti_audit_run_id) + 1
            marti_audit_ultimo_ciclo_ordenado = None
            try:
                agregar_evento(
                    f"🧯 Martingala C{int(MAX_CICLOS)}/C{int(MAX_CICLOS)} completada: reinicio automático a C1 ({marti_audit_resumen_linea()})."
                )
            except Exception:
                pass
        else:
            marti_paso = min(MAX_CICLOS - 1, int(marti_ciclos_perdidos))
    else:
        return

    ciclo_sig = int(marti_paso) + 1
    bot_msg = f" [{bot}]" if bot else ""
    if res == "PÉRDIDA" and bots_usados_en_esta_marti:
        try:
            usados = ",".join(bots_usados_en_esta_marti)
            agregar_evento(f"🔁 Rotación martingala activa: usados={usados} | próximo ciclo=C{ciclo_sig}")
        except Exception:
            pass
    agregar_evento(
        f"🔁 Martingala{bot_msg}: resultado={res} | pérdidas seguidas={marti_ciclos_perdidos}/{MAX_CICLOS} | próximo ciclo={ciclo_sig}"
    )
    agregar_evento(f"🧾 MARTI-AUDIT: {marti_audit_resumen_linea()}")

def ciclo_martingala_siguiente() -> int:
    """
    Fuente canónica del ciclo a abrir en REAL:
    - ciclo = pérdidas_consecutivas + 1, con límites [1..MAX_CICLOS]
    """
    try:
        return max(1, min(int(MAX_CICLOS), int(marti_ciclos_perdidos) + 1))
    except Exception:
        return 1



def reset_martingala_por_saldo(ciclo_objetivo: int, saldo_actual: float | None) -> bool:
    """
    Si no alcanza el saldo para el ciclo objetivo (C2..C{MAX_CICLOS}),
    reinicia la martingala en C1.
    """
    global marti_ciclos_perdidos, marti_paso, bots_usados_en_esta_marti

    try:
        ciclo = int(ciclo_objetivo)
    except Exception:
        ciclo = 1

    if ciclo <= 1:
        return False

    idx = max(0, min(len(MARTI_ESCALADO) - 1, ciclo - 1))
    monto_necesario = float(MARTI_ESCALADO[idx])

    try:
        saldo = float(saldo_actual) if saldo_actual is not None else None
    except Exception:
        saldo = None

    if saldo is not None and saldo >= monto_necesario:
        return False

    marti_ciclos_perdidos = 0
    marti_paso = 0
    bots_usados_en_esta_marti = []
    _marti_audit_record("reset_saldo", ciclo=ciclo_objetivo, detalle="reinicio_forzado")
    falta_msg = "saldo no disponible"
    if saldo is not None:
        falta_msg = f"faltan {(monto_necesario - saldo):.2f} USD"
    agregar_evento(
        f"🧯 Saldo insuficiente para C{ciclo} ({monto_necesario:.2f} USD): {falta_msg}. Reinicio automático a C1."
    )
    return True
def elegir_candidato_rotacion_marti(
    candidatos: list,
    ciclo_objetivo: int,
    allow_repeat_fallback: bool = False,
    repeat_min_prob: float = 0.70,
):
    """
    Rotación para REAL en C2..C{MAX_CICLOS}:
    - Prioriza bots no usados en la corrida activa.
    - Excluye además el último bot REAL operado para impedir repetición inmediata.
    - Si no hay bot nuevo elegible:
      * retorna None por defecto (modo estricto), o
      * permite repetir SOLO si `allow_repeat_fallback=True` y la probabilidad
        operativa del candidato cumple `repeat_min_prob`.

    El fallback protege continuidad de ciclo C2..C{MAX_CICLOS} sin abrir la compuerta a
    repeticiones indiscriminadas.
    """
    try:
        ciclo = int(ciclo_objetivo)
    except Exception:
        ciclo = 1

    if ciclo <= 1 or not candidatos:
        return candidatos[0] if candidatos else None

    usados = [b for b in bots_usados_en_esta_marti if b in BOT_NAMES]
    usados_set = set(usados)
    if ultimo_bot_real in BOT_NAMES:
        usados_set.add(str(ultimo_bot_real))

    candidatos_nuevos = [c for c in candidatos if c[1] not in usados_set]
    if candidatos_nuevos:
        return candidatos_nuevos[0]

    if bool(allow_repeat_fallback):
        try:
            min_prob = float(repeat_min_prob)
        except Exception:
            min_prob = 0.70
        # Blindaje defensivo: mantener umbral dentro de rango probabilístico.
        min_prob = max(0.0, min(1.0, min_prob))
        for c in candidatos:
            # Tupla esperada: (score, bot, p_model, p_oper, ...)
            if not isinstance(c, (tuple, list)):
                continue
            if len(c) <= 2:
                continue
            p_oper = c[3] if len(c) > 3 else c[2]
            try:
                p_val = float(p_oper)
                p_ok = (p_val == p_val) and (p_val >= min_prob)  # NaN-safe
            except Exception:
                p_ok = False
            if p_ok:
                return c

    return None

# === FIN BLOQUE 9 ===

# === BLOQUE 10 — IA: DATASET, MODELO Y PREDICCIÓN ===
# Caché y hot-reload de activos del oráculo
_MODEL_PATH = "modelo_xgb_v2.pkl"  # esquema v2
_SCALER_PATH = "scaler_v2.pkl"
_FEATURES_PATH = "feature_names_v2.pkl"
_META_PATH = "model_meta_v2.json"

_ORACLE_CACHE = {
    "model": None,
    "scaler": None,
    "features": None,
    "meta": None,
    "mtimes": {}  # {path: mtime}
}
# ============================
# PATCH IA (FIX): Label canónico + builder X/y ultra-robusto
# - NO asume columna 'y'
# - Filtra y a {0,1} (incluye GANANCIA/PÉRDIDA/✓/✗)
# - X por reindex => nunca KeyError
# - NaN/inf => 0.0
# ============================

# ============================
# IA — Label canónico (una sola vez)
# ============================
# ============================
# IA — Label canónico (FIX) + builder X/y ultra-robusto
# - NO asume columna 'y'
# - Filtra y a {0,1} (incluye GANANCIA/PÉRDIDA/✓/✗)
# - X por reindex => nunca KeyError
# - NaN/inf => 0.0
# ============================

LABEL_CANON = "result_bin"
SCHEMA_VERSION_ACTIVE = "core13_v2_scalping"
DATASET_SCHEMA_TAG = "dataset_incremental_v2"
LABEL_CANDIDATES = (
    "result_bin", "y", "label", "target", "resultado_bin", "result",
    "resultado", "win", "outcome"
)

def _pick_label_col_incremental(df: pd.DataFrame) -> str:
    """
    Devuelve el nombre REAL de la columna label dentro del DF (respetando el nombre original),
    aunque haya espacios/casos raros. Evita KeyError por "limpieza" de strings.
    """
    try:
        if df is None or df.empty or getattr(df, "columns", None) is None:
            return LABEL_CANON
    except Exception:
        return LABEL_CANON

    # mapa: "limpio_lower" -> "original"
    try:
        colmap = {str(c).strip().lower(): c for c in df.columns}
    except Exception:
        return LABEL_CANON

    for cand in LABEL_CANDIDATES:
        key = str(cand).strip().lower()
        if key in colmap:
            return colmap[key]

    # fallback defensivo: última columna real del DF
    try:
        return df.columns[-1]
    except Exception:
        return LABEL_CANON

def _y_to_bin(v) -> int | None:
    """
    Normaliza cualquier cosa a {0,1}. Si no se puede interpretar, devuelve None.
    Acepta: 0/1, "0"/"1", GANANCIA/PÉRDIDA, WIN/LOSS, ✓/✗, etc.
    """
    try:
        if v is None:
            return None
        # pandas NaN
        try:
            if pd.isna(v):
                return None
        except Exception:
            pass

        # numérico directo
        if isinstance(v, (int, np.integer)):
            return int(v) if int(v) in (0, 1) else None
        if isinstance(v, (float, np.floating)):
            if not math.isfinite(float(v)):
                return None
            iv = int(round(float(v)))
            return iv if iv in (0, 1) else None

        s = str(v).strip()
        if s == "":
            return None

        # "0"/"1"
        if s in ("0", "1"):
            return int(s)

        # símbolos / texto (reutiliza tu normalizador)
        rn = normalizar_resultado(s)
        if rn == "GANANCIA":
            return 1
        if rn == "PÉRDIDA":
            return 0

        # extra fallback simple por si llega raro
        up = s.upper()
        if "WIN" in up or "GAN" in up:
            return 1
        if "LOSS" in up or "PERD" in up:
            return 0

        return None
    except Exception:
        return None

def construir_Xy_incremental(
    df: pd.DataFrame,
    feature_names: list | None = None
) -> tuple[pd.DataFrame, np.ndarray, str, list]:
    """
    Construye X/y sin reventar:
    - y se infiere desde la mejor columna label detectada.
    - X se reindexa a feature_names => columnas faltantes se crean (NaN->0.0).
    - NaN/inf => 0.0
    Retorna: (X_df, y_np, label_col_real, features_usadas)
    """
    feats = list(feature_names) if feature_names else list(INCREMENTAL_FEATURES_V2)

    if df is None or df.empty:
        return pd.DataFrame(columns=feats), np.array([], dtype=int), LABEL_CANON, feats

    label_col = _pick_label_col_incremental(df)

    if label_col not in df.columns:
        # fallback brutal si algo raro pasó
        label_col = df.columns[-1] if len(df.columns) else LABEL_CANON

    y_series = df[label_col].apply(_y_to_bin)
    mask = y_series.notna()

    if not mask.any():
        return pd.DataFrame(columns=feats), np.array([], dtype=int), label_col, feats

    df2 = df.loc[mask].copy()
    y = y_series.loc[mask].astype(int).to_numpy()

    # X por reindex => nunca KeyError
    X = df2.reindex(columns=feats)

    # numeric coercion + limpieza
    for c in feats:
        try:
            X[c] = pd.to_numeric(X[c], errors="coerce")
        except Exception:
            X[c] = np.nan

    X = X.replace([np.inf, -np.inf], np.nan).fillna(0.0).astype(float)
    return X, y, label_col, feats

def cargar_incremental_Xy(
    ruta: str = "dataset_incremental.csv",
    feature_names: list | None = None
) -> tuple[pd.DataFrame, np.ndarray, str, list]:
    """
    Loader robusto:
    - Si el incremental está "mutante", intenta repararlo.
    - Lee con encodings fallback.
    - Devuelve X/y listos para entrenar.
    """
    if not os.path.exists(ruta):
        feats = list(feature_names) if feature_names else list(INCREMENTAL_FEATURES_V2)
        return pd.DataFrame(columns=feats), np.array([], dtype=int), LABEL_CANON, feats

    # Reparación preventiva (si quedó mutante)
    try:
        cols = _canonical_incremental_cols(feature_names if feature_names else INCREMENTAL_FEATURES_V2)
        reparar_dataset_incremental_mutante(ruta=ruta, cols=cols)
    except Exception:
        pass

    df = None
    for enc in ("utf-8", "latin-1", "windows-1252"):
        try:
            df = pd.read_csv(ruta, sep=",", encoding=enc, engine="python", on_bad_lines="skip")
            break
        except Exception:
            continue

    if df is None or df.empty:
        feats = list(feature_names) if feature_names else list(INCREMENTAL_FEATURES_V2)
        return pd.DataFrame(columns=feats), np.array([], dtype=int), LABEL_CANON, feats

    return construir_Xy_incremental(df, feature_names=feature_names)
# === FIN PATCH IA (FIX) ===

def _coerce_label_to_01(series: pd.Series) -> pd.Series:
    """
    Convierte etiquetas a 0/1:
    - acepta 0/1 numérico
    - acepta strings tipo 'GANANCIA', 'PÉRDIDA', 'WIN', 'LOSS', '✓', '✗'
    - lo demás => NaN
    """
    out = pd.Series(np.nan, index=series.index, dtype="float64")

    # 1) numérico directo (incluye "0", "1", 0.0, 1.0, True/False)
    y_num = pd.to_numeric(series, errors="coerce")
    ok01 = y_num.isin([0, 1])
    if ok01.any():
        out.loc[ok01] = y_num.loc[ok01].astype(float)

    # 2) strings/símbolos
    try:
        s = series.astype(str)
    except Exception:
        s = pd.Series([""] * len(series), index=series.index)

    def _map_one(x: str):
        try:
            raw = (x or "").strip()
            if raw == "" or raw.lower() == "nan":
                return np.nan

            # símbolos primero
            if any(sym in raw for sym in ("✓", "✔", "✅", "🟢")):
                return 1.0
            if any(sym in raw for sym in ("✗", "❌", "🔴", "🟥")):
                return 0.0

            t = raw.upper()
            if "GAN" in t or "WIN" in t:
                return 1.0
            if "PERD" in t or "LOSS" in t:
                return 0.0

            # admitir "1.0" / "0.0" como texto
            try:
                v = float(raw.replace(",", "."))
                if v in (0.0, 1.0):
                    return float(int(v))
            except Exception:
                pass

            return np.nan
        except Exception:
            return np.nan

    mapped = s.map(_map_one)
    out = out.fillna(mapped)
    return out


def _enriquecer_df_con_derivadas(df: pd.DataFrame, feats: list[str]) -> pd.DataFrame:
    """Genera columnas derivadas solo si el modelo las pide."""
    try:
        out = df.copy()
        row_proxy = pd.Series(False, index=out.index, dtype=bool)

        def _col_num(name, default=0.0):
            if name in out.columns:
                return pd.to_numeric(out[name], errors="coerce").fillna(default)
            return pd.Series([default] * len(out), index=out.index, dtype="float64")

        def _fill_proxy_if_missing(name: str, values: pd.Series):
            nonlocal row_proxy
            if name in out.columns:
                cur = pd.to_numeric(out[name], errors="coerce")
                miss = cur.isna()
                if bool(miss.any()):
                    out.loc[miss, name] = values.loc[miss]
                    if name in PROXY_FEATURES_BLOCK_TRAIN:
                        row_proxy = row_proxy | miss
            else:
                out[name] = values
                if name in PROXY_FEATURES_BLOCK_TRAIN:
                    row_proxy = row_proxy | pd.Series(True, index=out.index, dtype=bool)

        def _close_col_num(idx: int):
            cname = f"close_{idx}"
            if cname in out.columns:
                return pd.to_numeric(out[cname], errors="coerce")
            return pd.Series(np.nan, index=out.index, dtype="float64")

        if "pay_x_puntaje" in feats:
            out["pay_x_puntaje"] = _col_num("payout", 0.0) * _col_num("puntaje_estrategia", 0.0)
        if "vol_x_breakout" in feats:
            out["vol_x_breakout"] = _col_num("volatilidad", 0.0) * _col_num("breakout", 0.0)
        if "hora_x_rebote" in feats:
            out["hora_x_rebote"] = _col_num("hora_bucket", 0.0) * _col_num("es_rebote", 0.0)
        if "racha_x_rebote" in feats:
            out["racha_x_rebote"] = _col_num("racha_actual", 0.0) * _col_num("es_rebote", 0.0)
        if "rev_x_breakout" in feats:
            out["rev_x_breakout"] = _col_num("rsi_reversion", 0.0) * _col_num("breakout", 0.0)

        if "sma_spread" in feats:
            sma5 = _col_num("sma_5", 0.0)
            sma20 = _col_num("sma_20", 0.0)
            base = sma20.abs().clip(lower=1e-9)
            out["sma_spread"] = ((sma5 - sma20).abs() / base).clip(lower=0.0, upper=5.0)

        c0 = _close_col_num(0)
        c1 = _close_col_num(1)
        c2 = _close_col_num(2)
        c3 = _close_col_num(3)
        c4 = _close_col_num(4)
        close_real_2 = c0.notna() & c1.notna() & (c1.abs() > 1e-12)
        close_real_5 = close_real_2 & c2.notna() & c3.notna() & c4.notna()
        close_cols_20 = [_close_col_num(i) for i in range(20)]
        close_real_20 = pd.Series(True, index=out.index, dtype=bool)
        close_valid_20 = pd.Series(True, index=out.index, dtype=bool)
        for cc in close_cols_20:
            close_real_20 &= cc.notna()
            close_valid_20 &= cc.notna() & np.isfinite(cc) & (cc > 0.0)
        if any(f"close_{i}" in out.columns for i in range(20)):
            row_proxy = row_proxy | (~close_real_20)

        # CORE13_v2 scalping (backfill desde columnas legacy si existen)
        if "ret_1m" in feats:
            ret_real = ((c0 - c1) / c1).replace([np.inf, -np.inf], np.nan).clip(lower=-1.0, upper=1.0)
            if bool(close_real_2.any()):
                out.loc[close_real_2, "ret_1m"] = ret_real.loc[close_real_2]
            _fill_proxy_if_missing("ret_1m", ((_col_num("rsi_9", 50.0) - 50.0) / 50.0).clip(lower=-1.0, upper=1.0))
        if "ret_3m" in feats:
            _fill_proxy_if_missing("ret_3m", ((_col_num("rsi_14", 50.0) - 50.0) / 50.0).clip(lower=-1.0, upper=1.0))
        if "ret_5m" in feats:
            _fill_proxy_if_missing("ret_5m", (0.6 * _col_num("ret_3m", 0.0) + 0.4 * _col_num("ret_1m", 0.0)).clip(lower=-1.0, upper=1.0))
        if "slope_5m" in feats:
            if bool(close_real_5.any()):
                arr5 = np.vstack([c4.values, c3.values, c2.values, c1.values, c0.values]).T
                base5 = np.abs(arr5[:, 0])
                mean5 = np.abs(np.nanmean(arr5, axis=1))
                denom = np.where(base5 > 1e-9, base5, np.where(mean5 > 1e-9, mean5, 1.0))
                y5 = arr5 / denom[:, None]
                x5 = np.arange(5, dtype=float)
                xc = x5 - x5.mean()
                varx = float(np.sum(xc * xc))
                slopes = np.sum((y5 - np.nanmean(y5, axis=1)[:, None]) * xc[None, :], axis=1) / max(varx, 1e-9)
                slopes = np.clip(slopes, -1.0, 1.0)
                out.loc[close_real_5, "slope_5m"] = slopes[close_real_5.values]
            _fill_proxy_if_missing("slope_5m", (_col_num("sma_spread", 0.0) + 0.05 * _col_num("cruce_sma", 0.0)).clip(lower=-1.0, upper=1.0))
        if "rv_20" in feats:
            if bool(close_real_5.any()):
                rv_cols = [c0, c1, c2, c3, c4]
                if bool(close_real_20.any()):
                    rv_cols = close_cols_20
                rv_mat = np.vstack([cc.values for cc in rv_cols]).T
                den = rv_mat[:, 1:]
                num = rv_mat[:, :-1] - rv_mat[:, 1:]
                safe_den = np.where(np.abs(den) > 1e-12, den, np.nan)
                rv_rets = num / safe_den
                rv_vals = np.nanstd(rv_rets, axis=1, ddof=0)
                rv_vals = np.clip(np.nan_to_num(rv_vals, nan=0.0, posinf=1.0, neginf=0.0), 0.0, 1.0)
                out.loc[close_real_5, "rv_20"] = rv_vals[close_real_5.values]
            _fill_proxy_if_missing("rv_20", _col_num("volatilidad", 0.0).clip(lower=0.0, upper=1.0))
        if "range_norm" in feats:
            _fill_proxy_if_missing("range_norm", _col_num("breakout", 0.0).clip(lower=0.0, upper=1.0))
        if "bb_z" in feats:
            if bool(close_real_20.any()):
                bb_mat = np.vstack([cc.values for cc in close_cols_20]).T
                sma20 = np.nanmean(bb_mat, axis=1)
                std20 = np.nanstd(bb_mat, axis=1, ddof=0)
                den_bb = 2.0 * np.where(std20 > 1e-12, std20, np.nan)
                bb = (bb_mat[:, 0] - sma20) / den_bb
                bb = np.clip(np.nan_to_num(bb, nan=0.0, posinf=3.0, neginf=-3.0), -3.0, 3.0)
                out.loc[close_real_20, "bb_z"] = bb[close_real_20.values]
            _fill_proxy_if_missing("bb_z", ((2.0 * _col_num("rsi_reversion", 0.0)) - 1.0).clip(lower=-3.0, upper=3.0))
        if "body_ratio" in feats:
            _fill_proxy_if_missing("body_ratio", _col_num("ret_1m", 0.0).abs().clip(lower=0.0, upper=1.0))
        if "wick_imbalance" in feats:
            _fill_proxy_if_missing("wick_imbalance", ((2.0 * _col_num("es_rebote", 0.0)) - 1.0).clip(lower=-1.0, upper=1.0))
        if "micro_trend_persist" in feats:
            _fill_proxy_if_missing("micro_trend_persist", (_col_num("racha_actual", 0.0) / 10.0).clip(lower=-1.0, upper=1.0))

        out["row_has_proxy_features"] = row_proxy.astype(int)

        ret_1m_s = pd.to_numeric(out.get("ret_1m", np.nan), errors="coerce")
        slope_5m_s = pd.to_numeric(out.get("slope_5m", np.nan), errors="coerce")
        rv_20_s = pd.to_numeric(out.get("rv_20", np.nan), errors="coerce")
        bb_z_s = pd.to_numeric(out.get("bb_z", np.nan), errors="coerce")
        core_scalping_ready = (
            ret_1m_s.notna() & np.isfinite(ret_1m_s) & (ret_1m_s >= -1.0) & (ret_1m_s <= 1.0)
            & slope_5m_s.notna() & np.isfinite(slope_5m_s) & (slope_5m_s >= -1.0) & (slope_5m_s <= 1.0)
            & rv_20_s.notna() & np.isfinite(rv_20_s) & (rv_20_s >= 0.0) & (rv_20_s <= 1.0)
            & bb_z_s.notna() & np.isfinite(bb_z_s) & (bb_z_s >= -3.0) & (bb_z_s <= 3.0)
        )
        close_snapshot_issue = ~close_valid_20
        force_no_train = row_proxy & close_snapshot_issue & (~core_scalping_ready)
        out["row_train_eligible"] = (~force_no_train).astype(int)

        return out
    except Exception:
        return df


def build_xy_from_incremental(df: pd.DataFrame, feature_names: list | None = None):
    """
    Builder robusto con limpieza de calidad:
    - label col canónica (o fallback a última)
    - y a {0,1} con coerción
    - anti-duplicados exactos (features+label)
    - filtro de filas con features críticas vacías (cuando hay suficiente muestra)
    - X con reindex => jamás KeyError
    - NaN/inf => 0.0
    Devuelve: X, y, label_col
    """
    if df is None or getattr(df, "empty", True):
        return None, None, None

    feats = list(feature_names) if feature_names else list(INCREMENTAL_FEATURES_V2)
    df = _enriquecer_df_con_derivadas(df, feats)
    label_col = _pick_label_col_incremental(df)

    # y
    try:
        y01 = _coerce_label_to_01(df[label_col])
    except Exception:
        return None, None, label_col

    label_mask = y01.isin([0.0, 1.0])
    mask = label_mask.copy()
    mask_pre_proxy = mask.copy()
    if int(mask.sum()) <= 0:
        return None, None, label_col

    # Filtro de calidad para features críticas (volatilidad/hora_bucket)
    # Solo se aplica si deja muestra suficiente para no bloquear entrenamiento.
    quality_mask = pd.Series(True, index=df.index)
    for crit in ("volatilidad", "hora_bucket"):
        if crit in df.columns:
            vv = pd.to_numeric(df[crit], errors="coerce")
            quality_mask &= vv.notna()

    if int((mask & quality_mask).sum()) >= int(max(60, 0.50 * int(mask.sum()))):
        mask = mask & quality_mask

    if int(mask.sum()) <= 0:
        return None, None, label_col

    proxy_col = pd.to_numeric(df.get("row_has_proxy_features", pd.Series(0, index=df.index)), errors="coerce").fillna(0.0)
    train_elig_col = pd.to_numeric(df.get("row_train_eligible", pd.Series(1, index=df.index)), errors="coerce").fillna(1.0)
    proxy_mask = proxy_col > 0.0
    train_eligible_mask = train_elig_col > 0.0
    # Regla canónica: la elegibilidad final manda.
    # Si una fila trae proxy pero cumple row_train_eligible=1, se permite (proxy no crítico).
    mask = mask & train_eligible_mask

    # X (reindex = blindaje)
    feats_no_time = [c for c in feats if c != "ts_ingest"]
    X = df.reindex(columns=feats_no_time, fill_value=0.0).loc[mask].copy()
    X_num = X.apply(pd.to_numeric, errors="coerce")
    non_finite_mask = ~np.isfinite(X_num)
    nan_rows_excluded = int(non_finite_mask.any(axis=1).sum()) if len(X_num) else 0
    invalid_range_rows = 0
    try:
        invalid_range = pd.Series(False, index=X_num.index)
        if "ret_1m" in X_num.columns:
            s = X_num["ret_1m"]
            invalid_range |= (s < -1.0) | (s > 1.0)
        if "slope_5m" in X_num.columns:
            s = X_num["slope_5m"]
            invalid_range |= (s < -1.0) | (s > 1.0)
        if "rv_20" in X_num.columns:
            s = X_num["rv_20"]
            invalid_range |= (s < 0.0) | (s > 1.0)
        if "bb_z" in X_num.columns:
            s = X_num["bb_z"]
            invalid_range |= (s < -3.0) | (s > 3.0)
        invalid_range_rows = int(invalid_range.sum())
    except Exception:
        invalid_range_rows = 0
    X = X_num.replace([np.inf, -np.inf], np.nan).fillna(0.0)

    # y final
    y = y01.loc[mask].astype(int)

    # Anti-duplicados exactos (features+label) para reducir sobreconfianza artificial
    # keep='last' favorece estado más reciente cuando hay repeticiones.
    before_n = int(len(X))
    try:
        sig = X.round(6).astype(str).agg("|".join, axis=1) + "|" + y.astype(int).astype(str)
        keep = ~sig.duplicated(keep="last")
        X = X.loc[keep].copy()
        y = y.loc[keep].copy()
    except Exception:
        pass

    try:
        feat_fail = {}
        low_var = []
        for c in feats_no_time:
            try:
                s = pd.to_numeric(X[c], errors="coerce").fillna(0.0)
                nun = int(s.nunique(dropna=False))
                dom = float(s.value_counts(dropna=False).iloc[0] / max(1, len(s))) if len(s) else 1.0
                if nun <= 1:
                    feat_fail[c] = "nunique<=1"
                elif dom >= float(FEATURE_MAX_DOMINANCE):
                    feat_fail[c] = f"dominance={dom:.3f}"
                if nun <= 2:
                    low_var.append(c)
            except Exception:
                continue
        globals()["_LAST_XY_QUALITY"] = {
            "rows_before": before_n,
            "rows_after": int(len(X)),
            "duplicates_removed": max(0, before_n - int(len(X))),
            "used_quality_mask": bool(int((quality_mask & y01.isin([0.0, 1.0])).sum()) >= int(max(60, 0.50 * int(y01.isin([0.0, 1.0]).sum())))),
            "label_invalid_excluded": int((~label_mask).sum()),
            "proxy_rows_detected": int((mask_pre_proxy & proxy_mask).sum()),
            "proxy_rows_excluded": int((mask_pre_proxy & proxy_mask & (~train_eligible_mask)).sum()),
            "proxy_rows_kept_train_eligible": int((mask_pre_proxy & proxy_mask & train_eligible_mask).sum()),
            "train_ineligible_excluded": int((mask_pre_proxy & (~train_eligible_mask)).sum()),
            "nan_rows_detected": int(nan_rows_excluded),
            "invalid_range_rows_detected": int(invalid_range_rows),
            "low_variance_features": list(low_var[:12]),
            "feature_fail_counts": feat_fail,
            "rows_train_eligible": int(mask.sum()),
        }
    except Exception:
        pass

    return X, y, label_col

def _clean_X_df(X: pd.DataFrame) -> pd.DataFrame:
    # a numérico, NaN/inf => 0.0, float
    try:
        for c in X.columns:
            X[c] = pd.to_numeric(X[c], errors="coerce")
    except Exception:
        pass

    try:
        X = X.replace([np.inf, -np.inf], np.nan)
    except Exception:
        pass

    try:
        X = X.fillna(0.0)
    except Exception:
        pass

    try:
        X = X.astype("float64")
    except Exception:
        pass

    return X
    
def _build_Xy_incremental(df: pd.DataFrame, feature_names: list | None = None):
    """
    Wrapper canónico (compat):
    Devuelve: X_df, y_arr, feature_names_usadas, label_col_real

    Regla:
    - Internamente usa build_xy_from_incremental (única fuente de verdad).
    - Evita entrenar si queda 1 sola clase.
    """
    feats = list(feature_names) if feature_names else list(INCREMENTAL_FEATURES_V2)

    X, y, label_col = build_xy_from_incremental(df, feats)
    if X is None or y is None:
        return None, None, feats, (label_col or LABEL_CANON)

    # Evitar entrenos falsos con una sola clase
    try:
        if len(set(np.unique(y.to_numpy()))) < 2:
            return None, None, feats, (label_col or LABEL_CANON)
    except Exception:
        pass

    X = _clean_X_df(X)
    try:
        y_arr = y.astype(int).to_numpy()
    except Exception:
        y_arr = np.asarray(y, dtype=int)

    return X, y_arr, feats, (label_col or LABEL_CANON)

# Duplicado eliminado: se usa la versión canónica de _build_Xy_incremental definida arriba.
# Esto evita inconsistencias silenciosas en features/label durante entrenamiento y predicción.


# ============================================================
# COMPAT: FEATURES legacy (evita NameError en entreno)
# - Si existe dataset_incremental.csv, usa su header real
# - Si no existe, cae a FEATURE_NAMES_DEFAULT
# ============================================================
def _infer_features_from_incremental(path: str = "dataset_incremental.csv", fallback=None):
    try:
        if fallback is None:
            fallback = globals().get("FEATURE_NAMES_DEFAULT", None)

        if not os.path.exists(path):
            return list(fallback) if fallback else None

        for enc in ("utf-8", "utf-8-sig", "latin-1", "windows-1252"):
            try:
                with open(path, "r", newline="", encoding=enc, errors="replace") as f:
                    reader = csv.reader(f)
                    header = next(reader, [])
                header = [str(c).strip() for c in header if str(c).strip()]
                header = [c for c in header if c != "result_bin"]  # label fuera
                if header:
                    return header
            except Exception:
                continue

        return list(fallback) if fallback else None
    except Exception:
        return list(fallback) if fallback else None

# Si el código viejo usa FEATURES, aquí lo blindamos:
if "FEATURES" not in globals() or not globals().get("FEATURES"):
    FEATURES = _infer_features_from_incremental(fallback=globals().get("FEATURE_NAMES_DEFAULT", None))

# Último fallback ultra-defensivo
if not FEATURES:
    FEATURES = list(globals().get("FEATURE_NAMES_DEFAULT", []))

_META_CORRUPT_FLAG = False  # Nueva bandera para evitar reintentos en meta corrupto

def _safe_mtime(path):
    try:
        return os.path.getmtime(path)
    except Exception:
        return -1
def _as_list_feature_names(x):
    """Convierte feature names a list[str] de forma segura."""
    if x is None:
        return []
    if isinstance(x, list):
        return [str(a) for a in x]
    if isinstance(x, tuple):
        return [str(a) for a in list(x)]
    if isinstance(x, set):
        return [str(a) for a in list(x)]
    # string (ej: "['a','b']") no lo evaluamos; lo tratamos como 1 feature
    return [str(x)]


def _normalize_model_meta(meta: dict) -> dict:
    """
    Compatibilidad de meta:
    - rows_total -> n_samples
    - pos+neg -> n_samples (fallback)
    - crea alias n -> n_samples
    - normaliza tipos básicos
    """
    if not isinstance(meta, dict):
        return {}

    m = dict(meta)

    def _to_int(v):
        try:
            return int(float(v))
        except Exception:
            return 0

    def _to_float(v):
        try:
            return float(v)
        except Exception:
            return v

    # 1) n_samples
    ns = _to_int(m.get("n_samples"))
    if ns <= 0:
        ns = _to_int(m.get("rows_total"))
    if ns <= 0:
        ns = _to_int(m.get("pos")) + _to_int(m.get("neg"))
    m["n_samples"] = ns

    # 2) alias legacy
    if _to_int(m.get("n")) <= 0:
        m["n"] = ns

    # 3) floats útiles si existen
    for k in ("auc", "cv_auc", "f1", "threshold"):
        if k in m:
            m[k] = _to_float(m[k])

    # 4) reliable como bool
    m["reliable"] = bool(m.get("reliable", False))

    # 5) calibration string
    if "calibration" in m and m["calibration"] is None:
        m["calibration"] = "none"

    return m


def _resolve_oracle_feature_names(model, scaler, features, meta):
    """
    Prioridad EXACTA:
      1) scaler.feature_names_in_
      2) features (features.pkl)
      3) meta['feature_names']
      4) model.feature_names_in_ (fallback raro)
      5) None
    """
    # 1) scaler.feature_names_in_
    try:
        if scaler is not None and hasattr(scaler, "feature_names_in_"):
            fn = _as_list_feature_names(getattr(scaler, "feature_names_in_", None))
            if fn:
                return fn
    except Exception:
        pass

    # 2) features.pkl
    fn = _as_list_feature_names(features)
    if fn:
        return fn

    # 3) meta['feature_names']
    try:
        if meta and isinstance(meta, dict):
            fn = _as_list_feature_names(meta.get("feature_names"))
            if fn:
                return fn
    except Exception:
        pass

    # 4) model.feature_names_in_ (por si entrenaste con DataFrame directo al modelo)
    try:
        if model is not None and hasattr(model, "feature_names_in_"):
            fn = _as_list_feature_names(getattr(model, "feature_names_in_", None))
            if fn:
                return fn
    except Exception:
        pass

    return None


def get_oracle_assets():
    """
    Devuelve SIEMPRE: (model, scaler, features, meta)
    - model: modelo calibrado o None
    - scaler: StandardScaler o None
    - features: lista de nombres de features o None
    - meta: dict o None

    Blindaje:
    - Cache por mtime
    - Si meta se corrompe: renombra .corrupt y sigue con meta=None
    """
    changed = False
    for path in (_MODEL_PATH, _SCALER_PATH, _FEATURES_PATH, _META_PATH):
        mt = _safe_mtime(path)
        if _ORACLE_CACHE["mtimes"].get(path) != mt:
            _ORACLE_CACHE["mtimes"][path] = mt
            changed = True

    if _ORACLE_CACHE["model"] is None or changed:
        # Modelo
        try:
            _ORACLE_CACHE["model"] = joblib.load(_MODEL_PATH) if os.path.exists(_MODEL_PATH) else None
        except Exception as e:
            print(f"⚠️ IA: Error cargando modelo: {e}")
            _ORACLE_CACHE["model"] = None

        # Scaler
        try:
            _ORACLE_CACHE["scaler"] = joblib.load(_SCALER_PATH) if os.path.exists(_SCALER_PATH) else None
        except Exception as e:
            print(f"⚠️ IA: Error cargando scaler: {e}")
            _ORACLE_CACHE["scaler"] = None

        # Features
        try:
            _ORACLE_CACHE["features"] = joblib.load(_FEATURES_PATH) if os.path.exists(_FEATURES_PATH) else None
        except Exception as e:
            print(f"⚠️ IA: Error cargando features: {e}")
            _ORACLE_CACHE["features"] = None

        # Meta
        try:
            if os.path.exists(_META_PATH):
                with open(_META_PATH, "r", encoding="utf-8") as f:
                    _ORACLE_CACHE["meta"] = json.load(f)
            else:
                _ORACLE_CACHE["meta"] = None
        except Exception as e:
            print(f"⚠️ IA: Error cargando meta (archivo corrupto): {e}. Renombrando a .corrupt.")
            try:
                os.rename(_META_PATH, _META_PATH + ".corrupt")
            except Exception:
                pass
            _ORACLE_CACHE["meta"] = None

    # Normalización suave de features/meta (para evitar cosas raras)
    try:
        _ORACLE_CACHE["features"] = _as_list_feature_names(_ORACLE_CACHE.get("features"))
    except Exception:
        pass

    try:
        if isinstance(_ORACLE_CACHE.get("meta"), dict):
            _ORACLE_CACHE["meta"] = _normalize_model_meta(_ORACLE_CACHE["meta"])
        else:
            _ORACLE_CACHE["meta"] = None
    except Exception:
        _ORACLE_CACHE["meta"] = None

    return _ORACLE_CACHE["model"], _ORACLE_CACHE["scaler"], _ORACLE_CACHE["features"], _ORACLE_CACHE["meta"]

def oraculo_predict_visible(fila_dict):
    """
    Predicción para HUD:
    - Si hay modelo: usa oraculo_predict(modelo+scaler+meta/features)
    - Si no hay modelo y LOW_DATA_MODE: usa prob_exploratoria
    - Si no: 0.0
    """
    try:
        model, scaler, features, meta = get_oracle_assets()

        if model is not None:
            meta_local = dict(meta or {})
            fn = _resolve_oracle_feature_names(model, scaler, features, meta_local)
            if fn:
                meta_local["feature_names"] = fn
                prob = oraculo_predict(fila_dict, model, scaler, meta_local, bot_name="HUD")
                return prob, "modelo"

        # Sin modelo: fallback visual (NO opera, solo pinta)
        # En low_data mostramos prob exploratoria desde el inicio para evitar "--/OFF" confuso.
        if LOW_DATA_MODE:
            prob = prob_exploratoria(fila_dict)
            return prob, "low_data"

        # Modo exploración visual si existe la bandera
        if globals().get("MODO_EXPLORACION_IA", False):
            prob = prob_exploratoria(fila_dict)
            return prob, "exp"

        return None, "low_data"

    except Exception as e:
        print(f"⚠️ IA: Error en predict visible: {e}")
        return None, "low_data"

def get_threshold_sugerido(default_=0.60):
    global _META_CORRUPT_FLAG
    try:
        meta = _ORACLE_CACHE.get("meta")
        if meta is None and not _META_CORRUPT_FLAG:
            if os.path.exists(_META_PATH):
                with open(_META_PATH, "r", encoding="utf-8") as f:
                    meta = json.load(f)
                    _ORACLE_CACHE["meta"] = meta
        thr = meta.get("threshold") if meta else None
        if isinstance(thr, (int, float)):
            return float(thr)
    except Exception as e:
        if not _META_CORRUPT_FLAG:
            print(f"⚠️ IA: Error en threshold sugerido (meta corrupto): {e}. Renombrando archivo y usando default.")
            try:
                os.rename(_META_PATH, _META_PATH + ".corrupt")
            except Exception:
                pass
            _META_CORRUPT_FLAG = True  # Evita reintentos
    return float(default_)

def modelo_es_reliable(default=False):
    """
    Usa meta['reliable'] si existe; respalda en default si falta el meta.
    """
    try:
        meta = _ORACLE_CACHE.get("meta")
        if not meta and os.path.exists(_META_PATH):
            with open(_META_PATH, "r", encoding="utf-8") as f:
                meta = json.load(f)
                _ORACLE_CACHE["meta"] = meta
        return bool(meta and meta.get("reliable"))
    except Exception:
        return bool(default)


# Oráculo robusto
def oraculo_predict(fila_dict, modelo, scaler, meta, bot_name=""):
    """
    Predicción IA robusta.
    payout se trata como ROI [0..1.5].
    """
    try:
        if fila_dict is None:
            return 0.0

        feature_names = _resolve_oracle_feature_names(modelo, scaler, (meta or {}).get("feature_names"), meta or {})
        if not feature_names:
            # último fallback: si meta traía feature_names directo como lista
            feature_names = _as_list_feature_names((meta or {}).get("feature_names"))
        if not feature_names:
            return 0.0

        # =========================================================
        # Completar features derivados si el modelo los requiere
        # (para que inferencia = entrenamiento)
        # =========================================================
        ra = fila_dict.get("racha_actual", 0.0)
        try:
            ra = float(ra)
        except Exception:
            ra = 0.0

        if "racha_signo" in feature_names and "racha_signo" not in fila_dict:
            fila_dict["racha_signo"] = float(np.sign(ra))

        if "racha_abs" in feature_names and "racha_abs" not in fila_dict:
            fila_dict["racha_abs"] = float(abs(ra))

        if "rebote_fuerte" in feature_names and "rebote_fuerte" not in fila_dict:
            esr = fila_dict.get("es_rebote", 0.0)
            try:
                esr = float(esr)
            except Exception:
                esr = 0.0
            fila_dict["rebote_fuerte"] = 1.0 if (esr >= 0.5 and ra <= -4) else 0.0

        if "pay_x_puntaje" in feature_names and "pay_x_puntaje" not in fila_dict:
            fila_dict["pay_x_puntaje"] = float(fila_dict.get("payout", 0.0) or 0.0) * float(fila_dict.get("puntaje_estrategia", 0.0) or 0.0)

        if "vol_x_breakout" in feature_names and "vol_x_breakout" not in fila_dict:
            fila_dict["vol_x_breakout"] = float(fila_dict.get("volatilidad", 0.0) or 0.0) * float(fila_dict.get("breakout", 0.0) or 0.0)

        if "hora_x_rebote" in feature_names and "hora_x_rebote" not in fila_dict:
            fila_dict["hora_x_rebote"] = float(fila_dict.get("hora_bucket", 0.0) or 0.0) * float(fila_dict.get("es_rebote", 0.0) or 0.0)
        if "sma_spread" in feature_names and "sma_spread" not in fila_dict:
            try:
                sma5 = float(fila_dict.get("sma_5", 0.0) or 0.0)
                sma20 = float(fila_dict.get("sma_20", 0.0) or 0.0)
                sp = _calcular_sma_spread_robusto({"sma_5": sma5, "sma_20": sma20, "close": fila_dict.get("close", None)})
                fila_dict["sma_spread"] = float(sp) if sp is not None else 0.0
            except Exception:
                fila_dict["sma_spread"] = 0.0
        if "racha_x_rebote" in feature_names and "racha_x_rebote" not in fila_dict:
            fila_dict["racha_x_rebote"] = float(fila_dict.get("racha_actual", 0.0) or 0.0) * float(fila_dict.get("es_rebote", 0.0) or 0.0)
        if "rev_x_breakout" in feature_names and "rev_x_breakout" not in fila_dict:
            fila_dict["rev_x_breakout"] = float(fila_dict.get("rsi_reversion", 0.0) or 0.0) * float(fila_dict.get("breakout", 0.0) or 0.0)

        if not feature_names:
            return 0.0

        # Asegurar payout como ROI [0..1.5] (si falta, derivarlo)
        if "payout" in feature_names:
            if "payout" not in fila_dict or fila_dict.get("payout") in (None, "", 0, 0.0):
                roi_tmp = calcular_payout_feature(fila_dict)
                if roi_tmp is not None:
                    fila_dict["payout"] = roi_tmp

        # Clamp final por seguridad
        if "payout" in fila_dict:
            try:
                p = float(fila_dict["payout"])
            except Exception:
                p = 0.0
            if not math.isfinite(p):
                p = 0.0
            fila_dict["payout"] = max(0.0, min(p, 1.5))
        # Normalizar features faltantes (TRAIN vs INFER): volatilidad + hora_bucket
        try:
            fila_dict["volatilidad"] = float(calcular_volatilidad_simple(fila_dict))
        except Exception:
            fila_dict["volatilidad"] = 0.0

        try:
            hb, hm = calcular_hora_features(fila_dict)
            fila_dict["hora_bucket"] = float(hb)
            fila_dict["hora_missing"] = float(hm)
        except Exception:
            fila_dict["hora_bucket"] = 0.0
            fila_dict["hora_missing"] = 1.0

        # Enriquecer features CORE13_v2 si faltan (compat con filas legacy).
        fila_dict = _enriquecer_scalping_features_row(fila_dict)

        # Armar X en orden del modelo
        X = []
        for col in feature_names:
            v = fila_dict.get(col, 0.0)
            try:
                v = float(v)
            except Exception:
                v = 0.0
            if not math.isfinite(v):
                v = 0.0
            X.append(v)

        X = np.array(X, dtype=float).reshape(1, -1)

        # Escalar si existe scaler
        if scaler is not None:
            try:
                X = scaler.transform(X)
            except Exception:
                pass

        # Predecir proba
        if hasattr(modelo, "predict_proba"):
            proba = modelo.predict_proba(X)[0][1]
        else:
            # fallback
            proba = float(modelo.predict(X)[0])

        try:
            proba = float(proba)
        except Exception:
            proba = 0.0

        if not math.isfinite(proba):
            proba = 0.0
        return max(0.0, min(proba, 1.0))

    except Exception:
        return 0.0
def prob_exploratoria(fila):
    """
    Probabilidad simple (heurística) solo para VISUAL / fallback.
    payout = ROI [0..1.5]
    """
    try:
        # payout = ROI [0..1.5] (solo visual)
        pay = calcular_payout_feature(fila)
        try:
            pay = float(pay) if pay is not None else 0.0
        except Exception:
            pay = 0.0
        if not math.isfinite(pay):
            pay = 0.0
        pay = max(0.0, min(pay, 1.5))

        def _as01_cont(v):
            try:
                x = float(v)
            except Exception:
                s = str(v).strip().lower()
                if s in ("1", "true", "yes", "y"):
                    x = 1.0
                else:
                    x = 0.0
            if not math.isfinite(x):
                x = 0.0
            return max(0.0, min(1.0, x))

        # score básico (conservar simple pero continuo)
        score = 0.50
        score += 0.05 * _as01_cont(fila.get("breakout", 0.0))
        score += 0.05 * _as01_cont(fila.get("cruce_sma", 0.0))
        score += 0.04 * _as01_cont(fila.get("rsi_reversion", 0.0))

        # ROI alto ayuda un poco (sin convertir a %)
        score += (pay / 1.5) * 0.10

        if not math.isfinite(score):
            score = 0.0
        return max(0.0, min(score, 1.0))
    except Exception:
        return 0.0

# --- Nueva: leer_model_meta (blindado) ---
def leer_model_meta():
    global _META_CORRUPT_FLAG
    try:
        if _META_CORRUPT_FLAG:
            return {}

        if os.path.exists(_META_PATH):
            with open(_META_PATH, "r", encoding="utf-8") as f:
                meta = json.load(f) or {}
            if not isinstance(meta, dict):
                return {}
            return _normalize_model_meta(meta)

        return {}
    except Exception as e:
        try:
            corrupt = f"{_META_PATH}.corrupt_{int(time.time())}"
            if os.path.exists(_META_PATH):
                os.replace(_META_PATH, corrupt)
                agregar_evento(f"⚠️ META corrupta. Renombrada a {corrupt} ({e})")
        except Exception:
            pass
        _META_CORRUPT_FLAG = True
        return {}

# --- Nueva: guardar_model_meta (atómico) ---
def guardar_model_meta(meta: dict):
    try:
        tmp = _META_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(meta, f, ensure_ascii=False, indent=4)
            f.flush(); os.fsync(f.fileno())
        os.replace(tmp, _META_PATH)
        _ORACLE_CACHE["meta"] = meta
    except Exception as e:
        print(f"⚠️ IA: Falló guardar meta: {e}")
# =========================================================
# GUARDADO ATÓMICO DE ARTEFACTOS IA (modelo/scaler/features/meta)
# Evita corrupción y "archivos fantasma" al reiniciar.
# =========================================================
def _joblib_dump_atomic(obj, path: str):
    tmp = path + ".tmp"
    try:
        joblib.dump(obj, tmp)
        os.replace(tmp, path)
        return True
    except Exception:
        try:
            if os.path.exists(tmp):
                os.remove(tmp)
        except Exception:
            pass
        return False

def _json_dump_atomic(data: dict, path: str):
    tmp = path + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=4)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)
        return True
    except Exception:
        try:
            if os.path.exists(tmp):
                os.remove(tmp)
        except Exception:
            pass
        return False

def guardar_oracle_assets_atomico(modelo, scaler, feature_names, meta: dict | None):
    """
    Escribe de forma atómica:
      - artefacto de modelo   (_MODEL_PATH)
      - artefacto de scaler   (_SCALER_PATH)
      - artefacto de features (_FEATURES_PATH)
      - meta activa           (_META_PATH)
    """
    def _ensure_parent(path: str):
        try:
            d = os.path.dirname(path)
            if d:
                os.makedirs(d, exist_ok=True)
        except Exception:
            pass

    def _dump_atomic(obj, path: str):
        _ensure_parent(path)
        tmp = path + ".tmp"
        joblib.dump(obj, tmp)
        os.replace(tmp, path)

    def _json_atomic(obj, path: str):
        _ensure_parent(path)
        tmp = path + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(obj, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, path)

    try:
        if meta is None or not isinstance(meta, dict):
            meta = {}

        # asegurar feature_names dentro de meta
        try:
            meta["feature_names"] = list(feature_names) if feature_names else []
        except Exception:
            meta["feature_names"] = []

        # compat: asegurar n_samples/n y tipos básicos
        try:
            meta = _normalize_model_meta(meta)
        except Exception:
            pass

        _dump_atomic(modelo, _MODEL_PATH)
        _dump_atomic(scaler, _SCALER_PATH)
        _dump_atomic(list(feature_names) if feature_names else [], _FEATURES_PATH)
        _json_atomic(meta, _META_PATH)

        try:
            agregar_evento("💾 IA: artefactos guardados (modelo+scaler+features+meta)")
        except Exception:
            pass

        return True

    except Exception as e:
        # limpieza best-effort de temporales si quedaron
        for p in (_MODEL_PATH, _SCALER_PATH, _FEATURES_PATH, _META_PATH):
            try:
                tmp = p + ".tmp"
                if os.path.exists(tmp):
                    os.remove(tmp)
            except Exception:
                pass

        try:
            agregar_evento(f"⚠️ IA: fallo guardando artefactos: {e}")
        except Exception:
            pass
        return False
     
# --- Nueva: get_prob_ia_historica (estable) ---
def get_prob_ia_historica(bot: str) -> float:
    try:
        sig = estado_bots[bot]["ia_seniales"]
        acc = estado_bots[bot]["ia_aciertos"]
        if sig >= MIN_IA_SENIALES_CONF:
            return acc / sig
        return 0.0
    except Exception:
        return 0.0

# --- Nueva: calcular_confianza_ia (para HUD) ---
def calcular_confianza_ia(bot: str, meta: dict) -> float:
    try:
        auc = float(meta.get("auc", 0.0))
        n = int(meta.get("n_samples", 0))
        reliable = bool(meta.get("reliable", False))
        sig = estado_bots[bot]["ia_seniales"]
        acc = estado_bots[bot]["ia_aciertos"]
        pct = acc / sig if sig > 0 else 0.0
        conf = (auc * 0.4) + (pct * 0.3) + (0.2 if reliable else 0.0) + (0.1 if n >= MIN_FIT_ROWS_PROD else 0.0)
        return min(1.0, max(0.0, conf))
    except Exception:
        return 0.0

# --- Nueva: get_umbral_dinamico (para audio/HUD) ---
def get_umbral_dinamico(meta: dict, base_thr: float) -> float:
    try:
        auc = float(meta.get("auc", 0.0))
        delta = max(0.0, min(0.15, (auc - 0.75) * 0.2))
        return max(0.5, base_thr - delta)
    except Exception:
        return base_thr
def get_umbral_operativo(meta: dict | None = None) -> float:
    """
    Umbral único de operación IA (HUD, audio, selección).

    Regla dura:
    - Si el modelo NO es confiable, si el AUC es bajo, o si hay pocos samples,
      se bloquea cualquier señal (umbral ~ imposible).
    """
    base_thr = get_threshold_sugerido(IA_METRIC_THRESHOLD)
    if base_thr < IA_METRIC_THRESHOLD:
        base_thr = IA_METRIC_THRESHOLD
    if base_thr < ORACULO_THR_MIN:
        base_thr = ORACULO_THR_MIN

    if meta is None:
        try:
            meta = leer_model_meta()
        except Exception:
            meta = {}

    # Meta robusta
    try:
        auc = float((meta or {}).get("auc", 0.0) or 0.0)
    except Exception:
        auc = 0.0

    try:
        reliable = bool((meta or {}).get("reliable", False))
    except Exception:
        reliable = False

    try:
        n_samples = int((meta or {}).get("n_samples", (meta or {}).get("n", 0)) or 0)
    except Exception:
        n_samples = 0

    thr = get_umbral_dinamico(meta or {}, base_thr)

    # Endurecer umbral temporal si la muestra fuerte (>=70%) aún es baja.
    try:
        _, n70 = _leer_base_rate_y_n70(ttl_s=30.0)
        if int(n70) < int(IA_MIN_CLOSED_70_FOR_STRUCT):
            thr = max(float(thr), float(IA_TEMP_THR_HIGH))
    except Exception:
        pass

    # 🔒 BLOQUEO DE SEÑALES CUANDO ES EXPERIMENTAL / BAJO DATOS
    MIN_AUC_GREEN = 0.55  # “al menos no somos un dado”
    if (not reliable) or (n_samples < MIN_FIT_ROWS_PROD) or (auc < MIN_AUC_GREEN):
        return 0.99

    return thr
# =========================================================
# DISPARADOR ÚNICO DE ALERTA IA (AUDIO + FLAG)
# Regla dura pedida:
#   - SOLO dispara si prob >= umbral operativo (85% mínimo)
#   - Blindado contra prob en % (53) vs fracción (0.53)
#   - Cooldown + rearme por histéresis
# =========================================================
def _umbral_alerta_ia(meta: dict | None = None) -> float:
    """
    Umbral del aviso de audio IA (fijo, como definiste en config).
    Devuelve un float en [0..1].
    """
    try:
        thr = float(AUDIO_IA53_THR)
    except Exception:
        thr = IA_ACTIVACION_REAL_THR
    if thr < 0.0:
        thr = 0.0
    if thr > 1.0:
        thr = 1.0
    return thr

def evaluar_alerta_ia_y_disparar(bot: str, prob_ia: float, meta: dict | None = None, dentro_gatewin: bool = True):
    try:
        p = _norm_prob(prob_ia)
        thr = _umbral_alerta_ia(meta or {})

        now = time.time()

        # Rearme: si cae por debajo del umbral - hyst, se permite volver a disparar luego
        if p <= (thr - float(AUDIO_IA53_RESET_HYST)):
            IA53_TRIGGERED[bot] = False
            # limpiamos flag de señal pendiente si ya no califica
            estado_bots[bot]["ia_senal_pendiente"] = False
            estado_bots[bot]["ia_prob_senal"] = None
            return

        # Disparo: solo si cruza y no está ya disparado + respeta cooldown
        if (p >= thr) and (not IA53_TRIGGERED[bot]) and ((now - IA53_LAST_TS[bot]) >= float(AUDIO_IA53_COOLDOWN_S)):
            reproducir_evento("ia_53", es_demo=False, dentro_gatewin=dentro_gatewin)
            IA53_TRIGGERED[bot] = True
            IA53_LAST_TS[bot] = now

            # Flags para tu UI/decisión
            estado_bots[bot]["ia_senal_pendiente"] = True
            estado_bots[bot]["ia_prob_senal"] = float(p)

            # Evento claro (sin "53% suerte")
            agregar_evento(f"🔔 IA: {bot} {p*100:.0f}% >= {thr*100:.0f}% | ✅ ES HORA DE INVERTIR")
    except Exception:
        pass
# =========================================================
# UMBRAL VISUAL (HUD) — usa umbral operativo (85% por configuración)
# No depende de AUC/reliable/n_samples (eso solo bloquea "operar", no pintar).
# Evita fallos por redondeo: 0.699999 -> lo tratamos como 0.70.
# =========================================================
def _thr_visual_verde() -> float:
    try:
        return float(IA_VERDE_THR)
    except Exception:
        return IA_ACTIVACION_REAL_THR

def _thr_visual_amarillo() -> float:
    # Amarillo: zona previa (verde - 5pp)
    try:
        return max(0.0, float(_thr_visual_verde()) - 0.05)
    except Exception:
        return IA_ACTIVACION_REAL_THR

# =========================================================
# NORMALIZADOR ÚNICO DE PROBABILIDAD
# Acepta: 0.53, "0.53", 53, "53", 53.0
# Devuelve SIEMPRE en rango [0..1]
# =========================================================
def _norm_prob(p) -> float:
    try:
        if p is None:
            return 0.0
        if isinstance(p, str):
            p = p.strip().replace("%", "")
            if p == "" or p.lower() == "nan":
                return 0.0
        v = float(p)
        if not math.isfinite(v):
            return 0.0

        # Si viene en "porcentaje" (ej 53), convertirlo a 0.53
        if v > 1.0:
            if v <= 100.0:
                v = v / 100.0
            else:
                v = 1.0

        if v < 0.0:
            v = 0.0
        if v > 1.0:
            v = 1.0
        return v
    except Exception:
        return 0.0

def color_prob_ia(prob: float) -> str:
    """
    Colores SOLO para HUD:
      - VERDE si prob >= 0.70
      - AMARILLO si prob >= umbral operativo
      - ROJO si menor
    Blindado: si llega 53, lo convierte a 0.53.
    """
    p = _norm_prob(prob)

    # EPS anti-borde por flotantes (0.6999999)
    EPS = 1e-9
    tv = _thr_visual_verde()
    ty = _thr_visual_amarillo()

    if p + EPS >= tv:
        return Fore.GREEN
    if p + EPS >= ty:
        return Fore.YELLOW
    return Fore.RED


def icono_prob_ia(prob: float) -> str:
    """Icono SOLO para HUD (no altera lógica). Blindado a 53 vs 0.53."""
    p = _norm_prob(prob)
    EPS = 1e-9
    if p + EPS >= _thr_visual_verde():
        return "🟢"
    if p + EPS >= _thr_visual_amarillo():
        return "🟡"
    return "🔴"

# --- Nueva: anexar_incremental_desde_bot (completa 3 features + anti-duplicados) ---
def anexar_incremental_desde_bot(bot: str):
    """
    Anexa 1 fila al dataset incremental usando:
    - label (GANANCIA/PÉRDIDA) del último trade CERRADO
    - features del PRE_TRADE emparejado por epoch (evita leakage)
    Con lock cross-proceso y anti-duplicados por firma.
    """
    try:
        fila_dict, label = leer_ultima_fila_con_resultado(bot)
        if fila_dict is None or label is None:
            return

        try:
            label = int(label)
        except Exception:
            return
        if label not in (0, 1):
            return

        feature_names = list(INCREMENTAL_FEATURES_V2)
        cols = _canonical_incremental_cols(feature_names)
        ruta_inc = "dataset_incremental.csv"

        # Construir row completo + features derivadas (volatilidad/hora_bucket)
        row_dict_full = dict(fila_dict)
        row_dict_full["result_bin"] = label
        row_dict_full = _enriquecer_scalping_features_row(row_dict_full)

        # 1) Volatilidad: prioriza valor ya enriquecido; recalcula solo si falta/inválido.
        vol_calc = None
        try:
            v0 = row_dict_full.get("volatilidad", None)
            if v0 not in (None, ""):
                v0 = float(v0)
                if math.isfinite(v0) and v0 >= 0.0:
                    vol_calc = float(v0)
        except Exception:
            vol_calc = None

        if vol_calc is None:
            try:
                v1 = float(calcular_volatilidad_simple(row_dict_full))
                if math.isfinite(v1) and v1 >= 0.0:
                    vol_calc = float(v1)
            except Exception:
                vol_calc = None

        if vol_calc is None or vol_calc <= 0.0:
            try:
                vol_hist = calcular_volatilidad_por_bot(bot, lookback=50)
                if vol_hist is not None and math.isfinite(float(vol_hist)) and float(vol_hist) >= 0.0:
                    vol_calc = float(vol_hist)
            except Exception:
                pass

        # No matar incremental por vol no disponible: conservar fila y dejar traza.
        if (vol_calc is None) or (not math.isfinite(float(vol_calc))):
            vol_calc = 0.0
            agregar_evento(f"⚠️ Incremental: volatilidad no disponible ({bot}); se guarda fila con vol=0.0")
        row_dict_full["volatilidad"] = float(max(0.0, min(float(vol_calc), 1.0)))

        # 2) Hora bucket: prioriza valor ya enriquecido; fallback a parseo y luego neutro estable.
        hb = None
        hm = 0.0
        try:
            hb0 = row_dict_full.get("hora_bucket", None)
            if hb0 not in (None, ""):
                hb0 = float(hb0)
                if math.isfinite(hb0):
                    hb = float(max(0.0, min(1.0, hb0)))
                    hm = 0.0
        except Exception:
            hb = None

        if hb is None:
            try:
                hb1, hm1 = calcular_hora_features(row_dict_full)
                hb1 = float(hb1)
                hm1 = float(hm1)
                if math.isfinite(hb1) and hm1 < 1.0:
                    hb = float(max(0.0, min(1.0, hb1)))
                    hm = float(hm1)
            except Exception:
                hb = None

        if hb is None:
            # fallback final estable: no depende del reloj actual del sistema
            hb = 0.0
            hm = 1.0
            agregar_evento(f"⚠️ Incremental: hora no parseable ({bot}); fallback neutro aplicado")

        row_dict_full["hora_bucket"] = float(max(0.0, min(1.0, float(hb))))
        row_dict_full["hora_missing"] = float(hm)

        # Clip + validar
        row_dict_full = clip_feature_values(row_dict_full, feature_names)
        ok, reason = validar_fila_incremental(row_dict_full, feature_names)
        if not ok:
            agregar_evento(f"⚠️ Incremental: fila descartada ({bot}) => {reason}")
            return
        try:
            row_dict_full["row_has_proxy_features"] = int(float(row_dict_full.get("row_has_proxy_features", 0) or 0))
        except Exception:
            row_dict_full["row_has_proxy_features"] = 0
        try:
            row_dict_full["row_train_eligible"] = int(float(row_dict_full.get("row_train_eligible", 1) or 1))
        except Exception:
            row_dict_full["row_train_eligible"] = 1
        if int(row_dict_full.get("row_has_proxy_features", 0)) == 1:
            if (not _core_scalping_ready_from_row(row_dict_full)) and _close_snapshot_issue_from_row(row_dict_full):
                row_dict_full["row_train_eligible"] = 0

        # Firma anti-dup
        row_vals_sig = []
        for k in feature_names:
            v = row_dict_full.get(k, 0.0)
            try:
                v = float(v)
            except Exception:
                v = 0.0
            row_vals_sig.append(str(round(v, 6)))
        sig = "|".join(row_vals_sig) + "|" + str(label)

        last_sig = _load_last_sig(bot)
        if last_sig == sig:
            return

        try:
            huellas_usadas.setdefault(bot, set())
            if sig in huellas_usadas[bot]:
                return
        except Exception:
            pass

        max_retries = 8
        for attempt in range(max_retries):
            try:
                # LOCK ÚNICO: mismo que maybe_retrain/backfill
                with file_lock_required(INCREMENTAL_LOCK_FILE, timeout=6.0, stale_after=30.0) as got:
                    if not got:
                        agregar_evento("⚠️ Incremental: lock ocupado; se omite escritura para evitar corrupción.")
                        return
                    # Repara incremental mutante antes de escribir
                    try:
                        repaired = reparar_dataset_incremental_mutante(ruta=ruta_inc, cols=cols)
                        if repaired:
                            agregar_evento("🧹 IA: dataset_incremental reparado (mutante).")
                    except Exception:
                        pass

                    need_header = (not os.path.exists(ruta_inc)) or (os.path.getsize(ruta_inc) == 0)

                    with open(ruta_inc, "a", newline="", encoding="utf-8") as f:
                        writer = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
                        if need_header:
                            writer.writeheader()
                        writer.writerow(row_dict_full)
                        f.flush()
                        os.fsync(f.fileno())

                # Marcar firma solo si escribimos OK
                try:
                    huellas_usadas.setdefault(bot, set()).add(sig)
                except Exception:
                    pass
                _save_last_sig(bot, sig)

                # Log con throttle (1/min por bot) para que lo VEAS sin spamear
                try:
                    d = globals().setdefault("_INC_LAST_LOG_TS", {})
                    now = time.time()
                    if now - float(d.get(bot, 0.0)) >= 60.0:
                        d[bot] = now
                        agregar_evento(f"✅ Incremental: +1 fila desde {bot} ({'G' if label == 1 else 'P'}).")
                except Exception:
                    pass

                return

            except PermissionError:
                time.sleep(0.15 + 0.10 * attempt)
                continue
            except Exception as e:
                agregar_evento(f"⚠️ Incremental: excepción anexar ({bot}) => {type(e).__name__}: {e}")
                return

    except Exception as e:
        agregar_evento(f"⚠️ Incremental: excepción outer ({bot}) => {type(e).__name__}: {e}")
        return

# --- Nueva: maybe_retrain (con validaciones) ---
def _seleccionar_features_utiles_train(X_df: pd.DataFrame, feats: list[str]):
    """
    Reduce ruido de variables casi constantes/redundantes antes del fit.
    Mantiene al menos 6 columnas para evitar colapsar el modelo.
    """
    try:
        X = X_df.copy()
        keep = []
        dropped = []
        n = max(1, len(X))

        for c in feats:
            if c not in X.columns:
                dropped.append((c, "missing"))
                continue
            s = pd.to_numeric(X[c], errors="coerce").fillna(0.0)
            vc = s.value_counts(dropna=False)
            top_ratio = (float(vc.iloc[0]) / float(n)) if len(vc) else 1.0
            nun = int(s.nunique(dropna=False))
            if nun <= 1:
                dropped.append((c, f"ROTA:nunique={nun}"))
            elif top_ratio > float(FEATURE_MAX_DOMINANCE):
                dropped.append((c, f"CASI_CONSTANTE:dom={top_ratio:.3f}"))
            else:
                keep.append(c)

        # Evitar colinealidad extrema en SMA
        if ("sma_5" in keep) and ("sma_spread" in keep):
            try:
                corr = abs(pd.to_numeric(X["sma_5"], errors="coerce").fillna(0.0).corr(
                    pd.to_numeric(X["sma_spread"], errors="coerce").fillna(0.0)
                ))
                if pd.notna(corr) and float(corr) >= 0.9999:
                    keep.remove("sma_spread")
                    dropped.append(("sma_spread", f"collinear({corr:.5f})"))
            except Exception:
                pass

        if len(keep) < 1:
            keep = list(feats)
            dropped = []

        return X[keep].copy(), list(keep), dropped
    except Exception:
        return X_df, list(feats), []


def _seleccionar_features_calidad(X_df: pd.DataFrame, y_arr: np.ndarray, feats: list[str]):
    """
    Selección calidad-first (sin fuga temporal):
    - Conserva siempre FEATURE_ALWAYS_KEEP si existen.
    - Evalúa dominancia + AUC univariado SOLO en la ventana de entrenamiento.
    - Exige estabilidad temporal básica (mitad temprana vs mitad reciente del train).
    - Limita el set productivo para reducir ruido y sobreajuste.
    """
    try:
        if X_df is None or X_df.empty:
            return list(feats), []

        y = np.asarray(y_arr).astype(int)
        selected = []
        report = []
        scored = []

        n_all = len(X_df)
        cut = max(1, n_all // 2)

        for c in feats:
            if c not in X_df.columns:
                report.append((c, "missing"))
                continue

            s = pd.to_numeric(X_df[c], errors="coerce").fillna(0.0)
            nun = int(s.nunique(dropna=False))
            vc = s.value_counts(dropna=False)
            dom = float(vc.iloc[0]) / float(max(1, len(s))) if len(vc) else 1.0

            auc_uni = 0.5
            auc_delta = 0.0
            auc_early = 0.5
            auc_late = 0.5
            stable = False
            ok_auc = False
            try:
                if nun > 1 and len(np.unique(y)) == 2:
                    auc_uni = float(roc_auc_score(y, s.values))
                    auc_uni = max(min(auc_uni, 1.0), 0.0)
                    auc_delta = abs(auc_uni - 0.5)
                    ok_auc = True

                    y_early = y[:cut]
                    x_early = s.values[:cut]
                    y_late = y[cut:]
                    x_late = s.values[cut:]

                    early_has_2c = bool(len(y_early) >= 20 and len(np.unique(y_early)) == 2)
                    late_has_2c = bool(len(y_late) >= 20 and len(np.unique(y_late)) == 2)

                    if early_has_2c:
                        auc_early = float(roc_auc_score(y_early, x_early))
                    if late_has_2c:
                        auc_late = float(roc_auc_score(y_late, x_late))

                    d1 = abs(auc_early - 0.5)
                    d2 = abs(auc_late - 0.5)

                    # Regla anti-colapso: si una mitad no tiene ambas clases,
                    # no penalizar estabilidad por ese lado (muestra insuficiente).
                    if early_has_2c and late_has_2c:
                        stable = (d1 >= float(FEATURE_MIN_AUC_DELTA) * 0.60 and d2 >= float(FEATURE_MIN_AUC_DELTA) * 0.60)
                    elif early_has_2c or late_has_2c:
                        stable = (auc_delta >= float(FEATURE_MIN_AUC_DELTA))
                    else:
                        stable = True
            except Exception:
                pass

            if c in FEATURE_ALWAYS_KEEP:
                selected.append(c)
                report.append((c, f"KEEP_CORE dom={dom:.3f} auc={auc_uni:.4f}"))
                continue

            if nun <= 1:
                report.append((c, f"DROP nunique={nun}"))
                continue
            if dom > float(FEATURE_MAX_DOMINANCE_GATE):
                report.append((c, f"DROP dom={dom:.3f}"))
                continue

            if ok_auc and auc_delta >= float(FEATURE_MIN_AUC_DELTA) and stable:
                scored.append((auc_delta, c, dom, auc_uni, auc_early, auc_late))
            else:
                report.append((c, f"SHADOW auc_delta={auc_delta:.4f} early={auc_early:.4f} late={auc_late:.4f} dom={dom:.3f}"))

        scored.sort(reverse=True, key=lambda t: t[0])
        max_extra = max(0, int(FEATURE_MAX_PROD) - len(selected))
        for auc_delta, c, dom, auc_uni, auc_early, auc_late in scored[:max_extra]:
            selected.append(c)
            report.append((c, f"KEEP auc_delta={auc_delta:.4f} early={auc_early:.4f} late={auc_late:.4f} dom={dom:.3f} auc={auc_uni:.4f}"))

        if not selected:
            fallback = [f for f in FEATURE_ALWAYS_KEEP if f in X_df.columns]
            if not fallback and feats:
                fallback = [feats[0]]
            selected = fallback

        return selected, report
    except Exception:
        return list(feats), []


def _auditar_salud_features(X_df: pd.DataFrame, feats: list[str]):
    """Audita variación/dominancia por feature para decidir si entrena o se congela."""
    out = {}
    try:
        n = max(1, len(X_df))
        for c in feats:
            if c not in X_df.columns:
                out[c] = {"nunique": 0, "dominance": 1.0, "status": "MISSING"}
                continue
            s = pd.to_numeric(X_df[c], errors="coerce").fillna(0.0)
            nun = int(s.nunique(dropna=False))
            vc = s.value_counts(dropna=False)
            dom = (float(vc.iloc[0]) / float(n)) if len(vc) else 1.0
            if nun <= 1:
                status = "ROTA"
            elif dom > float(FEATURE_MAX_DOMINANCE):
                status = "CASI_CONSTANTE"
            else:
                status = "OK"
            out[c] = {"nunique": nun, "dominance": float(dom), "status": status}
    except Exception:
        return {}
    return out


def _dataset_quality_gate_for_training(X_df: pd.DataFrame, feats: list[str]):
    """
    Gate de calidad mínimo para entrenamiento IA.
    Retorna: (ok: bool, reasons: list[str], health: dict)
    """
    reasons = []
    health = {}
    try:
        if X_df is None or X_df.empty:
            return False, ["dataset_vacio"], {}

        n_rows = int(len(X_df))
        min_rows = int(max(4, MIN_FIT_ROWS_LOW))
        if n_rows < min_rows:
            reasons.append(f"filas_insuficientes:{n_rows}<{min_rows}")

        health = _auditar_salud_features(X_df, feats)
        if not isinstance(health, dict) or not health:
            reasons.append("health_unavailable")
            return (len(reasons) == 0), reasons, (health if isinstance(health, dict) else {})

        n_ok = 0
        n_bad = 0
        dom_hot = 0
        for c in feats:
            rep = health.get(c, {}) if isinstance(health.get(c, {}), dict) else {}
            st = str(rep.get("status", "")).upper()
            dom = float(rep.get("dominance", 1.0) or 1.0)
            if st == "OK":
                n_ok += 1
            else:
                n_bad += 1
            if dom >= float(FEATURE_MAX_DOMINANCE):
                dom_hot += 1

        # Exigimos al menos una base de columnas útiles para entrenar sin colapsar.
        min_ok_cfg = int(max(3, min(int(globals().get("FEATURE_DQ_MIN_OK", 5)), 6)))
        min_ok = max(3, min(min_ok_cfg, len(feats)))
        if n_ok < min_ok:
            reasons.append(f"features_ok_bajas:{n_ok}<{min_ok}")
            bad_feats = []
            for c in feats:
                rep = health.get(c, {}) if isinstance(health.get(c, {}), dict) else {}
                st = str(rep.get("status", "UNKNOWN")).upper()
                if st != "OK":
                    nun = int(rep.get("nunique", 0) or 0)
                    dom = float(rep.get("dominance", 1.0) or 1.0)
                    bad_feats.append(f"{c}:{st}(nun={nun},dom={dom:.3f})")
            if bad_feats:
                reasons.append("features_fallidas=" + ",".join(bad_feats[:8]))

        # Si casi todo está casi-constante, bloqueamos para evitar entrenos basura.
        if len(feats) > 0 and dom_hot >= max(1, int(len(feats) * 0.8)):
            reasons.append(f"dominancia_alta:{dom_hot}/{len(feats)}")

        return len(reasons) == 0, reasons, health
    except Exception as e:
        reasons.append(f"dq_gate_error:{type(e).__name__}")
        return False, reasons, (health if isinstance(health, dict) else {})


def _fingerprint_features_row(row: dict, feats: list[str] | None = None, decimals: int = INPUT_DUP_FINGERPRINT_DECIMALS) -> str:
    """Huella estable por bot/tick para detectar inputs duplicados entre bots."""
    base_feats = list(feats) if feats else list(INCREMENTAL_FEATURES_V2)
    base_feats = _features_vivas_para_redundancia(base_feats)
    parts = []
    for k in base_feats:
        v = (row or {}).get(k, 0.0)
        try:
            vf = float(v)
            if not np.isfinite(vf):
                vf = 0.0
        except Exception:
            vf = 0.0
        parts.append(f"{k}={round(vf, int(decimals))}")
    return "|".join(parts)


def _features_vivas_para_redundancia(base_feats: list[str]) -> list[str]:
    """Usa features activas del modelo, evitando filtrar de más por metadatos viejos."""
    try:
        base = list(base_feats)

        # 1) Priorizar feature_names.pkl (estado real más reciente del modelo)
        model_feats = None
        try:
            fpath = globals().get("_FEATURES_PATH", "feature_names.pkl")
            if os.path.exists(fpath):
                raw = joblib.load(fpath)
                if isinstance(raw, (list, tuple)):
                    mf = [str(x) for x in raw if str(x).strip()]
                    if len(mf) >= 4:
                        model_feats = mf
        except Exception:
            model_feats = None

        # 2) Fallback a meta
        if not model_feats:
            meta = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
            mf = meta.get("feature_names", []) if isinstance(meta, dict) else []
            if isinstance(mf, list) and len(mf) >= 4:
                model_feats = [str(x) for x in mf if str(x).strip()]

        if not model_feats:
            return base

        # 3) Excluir solo features explícitamente rotas
        health = {}
        try:
            meta2 = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
            health = meta2.get("feature_health", {}) if isinstance(meta2, dict) else {}
        except Exception:
            health = {}

        out = []
        for c in base:
            if c not in model_feats:
                continue
            st = str((health.get(c, {}) if isinstance(health, dict) else {}).get("status", "OK") or "OK").upper()
            if st == "ROTA":
                continue
            out.append(c)

        # Anti-colapso: no degradar redundancia a 1-2 columnas por metadata stale.
        return out if len(out) >= 4 else base
    except Exception:
        return list(base_feats)


def _diagnosticar_inputs_duplicados(rows_by_bot: dict, dup_bots: list[str], feats: list[str] | None = None) -> dict:
    """Diagnóstico compacto de columnas idénticas/variables en grupos duplicados."""
    base_feats = list(feats) if feats else list(INCREMENTAL_FEATURES_V2)
    base_feats = _features_vivas_para_redundancia(base_feats)
    same_cols, diff_cols = [], []

    for c in base_feats:
        vals = []
        for b in dup_bots:
            rv = rows_by_bot.get(b, {}) or {}
            try:
                vals.append(round(float(rv.get(c, 0.0) or 0.0), int(INPUT_DUP_FINGERPRINT_DECIMALS)))
            except Exception:
                vals.append(0.0)
        if len(set(vals)) <= 1:
            same_cols.append(c)
        else:
            diff_cols.append(c)

    expected_pref = ["payout", "ret_1m", "ret_3m", "ret_5m", "range_norm", "rv_20", "micro_trend_persist"]
    expected_diff = [c for c in expected_pref if c in base_feats]
    source_info = {}
    for b in dup_bots:
        rv = rows_by_bot.get(b, {}) or {}
        source_info[b] = {
            "path": str(rv.get("__src_path", "")),
            "ts": str(rv.get("__src_ts", rv.get("__src_epoch", ""))),
            "hash": str(rv.get("__src_row_hash", "")),
            "symbol": str(rv.get("__src_symbol", "")),
        }
    return {
        "same_cols": same_cols,
        "diff_cols": diff_cols,
        "expected_diff": expected_diff,
        "source_info": source_info,
    }


def _hay_modelo_ia_disponible() -> bool:
    """Chequea si hay modelo utilizable en cache o disco."""
    try:
        _load_ia_assets_once(force=False)
        if _IA_ASSETS_CACHE.get("model") is not None:
            return True
    except Exception:
        pass
    try:
        mfile = globals().get("_MODEL_PATH", "modelo_xgb.pkl")
        return bool(os.path.exists(mfile))
    except Exception:
        return False


def _maybe_retrain_fallback_sklearn(force: bool = False):
    """Fallback cuando XGBoost no está disponible: entrena LogisticRegression calibrada."""
    try:
        ruta = "dataset_incremental.csv"
        if not os.path.exists(ruta):
            agregar_evento("⚠️ IA fallback: dataset_incremental.csv no existe aún.")
            return False
        df = pd.read_csv(ruta, sep=",", encoding="utf-8", engine="python", on_bad_lines="skip")
        if df is None or df.empty:
            agregar_evento("⚠️ IA fallback: dataset incremental vacío.")
            return False

        if "result_bin" not in df.columns:
            agregar_evento("⚠️ IA fallback: falta result_bin en incremental.")
            return False

        y = pd.to_numeric(df["result_bin"], errors="coerce")
        mask = y.isin([0, 1])
        if int(mask.sum()) < int(MIN_FIT_ROWS_LOW):
            agregar_evento(f"⚠️ IA fallback: poca data útil ({int(mask.sum())}).")
            return False

        feats = [f for f in FEATURE_SET_PROD_WARMUP if f in df.columns]
        if len(feats) < int(FEATURE_MAX_PROD):
            feats = [f for f in FEATURE_NAMES_DEFAULT if f in df.columns]
        if not feats:
            feats = [f for f in INCREMENTAL_FEATURES_V2 if f in df.columns]
        if not feats:
            reserved = {"result_bin", "resultado", "resultado_norm", "trade_status", "trade_status_norm"}
            cand = []
            for c in df.columns:
                if c in reserved:
                    continue
                try:
                    sc = pd.to_numeric(df[c], errors="coerce")
                    if int(sc.notna().sum()) >= max(6, int(len(df) * 0.20)):
                        cand.append(c)
                except Exception:
                    continue
            feats = cand[:20]
        if not feats:
            agregar_evento("⚠️ IA fallback: no hay features numéricas utilizables en incremental.")
            return False

        df = _enriquecer_df_con_derivadas(df, feats)
        proxy_mask = pd.to_numeric(df.get("row_has_proxy_features", pd.Series(0, index=df.index)), errors="coerce").fillna(0.0) > 0.0
        train_eligible_mask = pd.to_numeric(df.get("row_train_eligible", pd.Series(1, index=df.index)), errors="coerce").fillna(1.0) > 0.0
        proxy_excluded = int((mask & proxy_mask & (~train_eligible_mask)).sum())
        proxy_kept = int((mask & proxy_mask & train_eligible_mask).sum())
        mask = mask & train_eligible_mask
        try:
            agregar_evento(
                f"🧪 IA fallback-clean: proxies excluidos={proxy_excluded} | proxies elegibles={proxy_kept} | elegibles={int(mask.sum())}."
            )
        except Exception:
            pass
        if int(mask.sum()) < int(MIN_FIT_ROWS_LOW):
            agregar_evento(f"⚠️ IA fallback: data elegible insuficiente tras filtrar proxies ({int(mask.sum())}).")
            return False

        X = df.loc[mask, feats].copy()
        yb = y.loc[mask].astype(int).values
        X = X.replace([np.inf, -np.inf], np.nan).fillna(0.0)

        # Si solo hay una clase, no se puede entrenar
        if len(set(list(yb))) < 2:
            agregar_evento("⚠️ IA fallback: una sola clase útil; esperando más cierres.")
            return False

        scaler = StandardScaler()
        Xs = scaler.fit_transform(X)

        clf = LogisticRegression(max_iter=800, class_weight="balanced")
        clf.fit(Xs, yb)

        try:
            p = clf.predict_proba(Xs)[:, 1]
            auc = float(roc_auc_score(yb, p)) if len(set(yb)) > 1 else 0.0
            brier = float(brier_score_loss(yb, p))
        except Exception:
            auc = 0.0
            brier = 0.0

        meta = {
            "trained_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "n_samples": int(len(X)),
            "rows_total": int(len(X)),
            "rows_train": int(len(X)),
            "pos": int(np.sum(yb == 1)),
            "neg": int(np.sum(yb == 0)),
            "auc": float(auc),
            "brier": float(brier),
            "threshold": float(THR_DEFAULT),
            "reliable": bool(len(X) >= int(MIN_FIT_ROWS_PROD)),
            "reliable_candidate": bool(len(X) >= int(MIN_FIT_ROWS_PROD)),
            "warmup_mode": bool(len(X) < int(TRAIN_WARMUP_MIN_ROWS)),
            "canary_mode": False,
            "refresh_policy": "fallback_logreg",
            "feature_names": list(feats),
            "model_family": "sklearn_logreg_fallback",
        }

        ok_save = False
        if "guardar_oracle_assets_atomico" in globals() and callable(guardar_oracle_assets_atomico):
            ok_save = bool(guardar_oracle_assets_atomico(clf, scaler, list(feats), meta))
        else:
            model_path = globals().get("_MODEL_PATH", "modelo_xgb.pkl")
            scaler_path = globals().get("_SCALER_PATH", "scaler.pkl")
            feats_path = globals().get("_FEATURES_PATH", "feature_names.pkl")
            meta_path = globals().get("_META_PATH", "model_meta.json")
            joblib.dump(clf, model_path)
            joblib.dump(scaler, scaler_path)
            joblib.dump(list(feats), feats_path)
            with open(meta_path, "w", encoding="utf-8") as f:
                json.dump(meta, f, ensure_ascii=False, indent=2)
            ok_save = True

        if ok_save:
            _IA_ASSETS_CACHE["loaded"] = False
            try:
                _ORACLE_CACHE["model"] = clf
                _ORACLE_CACHE["scaler"] = scaler
                _ORACLE_CACHE["features"] = list(feats)
                _ORACLE_CACHE["meta"] = dict(meta)
                _ORACLE_CACHE.setdefault("mtimes", {})
                for pth in (globals().get("_MODEL_PATH", "modelo_xgb_v2.pkl"), globals().get("_SCALER_PATH", "scaler_v2.pkl"), globals().get("_FEATURES_PATH", "feature_names_v2.pkl"), globals().get("_META_PATH", "model_meta_v2.json")):
                    _ORACLE_CACHE["mtimes"][pth] = _safe_mtime(pth)
            except Exception:
                pass
            agregar_evento(f"✅ IA fallback entrenada (LogReg) n={len(X)} AUC={auc:.3f}")
            try:
                auditar_refresh_campeon_stale(meta, force_log=True)
            except Exception:
                pass
            return True
        return False
    except Exception as e:
        agregar_evento(f"⚠️ IA fallback falló: {type(e).__name__}")
        return False


def maybe_retrain(force: bool = False):
    """
    Reentreno IA HONESTO (sin fuga temporal) + uso REAL de TimeSeriesSplit.

    - Split temporal: TRAIN_BASE (pasado) / CALIB (más reciente) / TEST (último)
    - StandardScaler FIT SOLO en TRAIN_BASE
    - Calibración SIN reentrenar base (sigmoid/isotonic) usando ModeloXGBCalibrado
    - TimeSeriesSplit sobre TRAIN_BASE para CV AUC (diagnóstico, no toca el split final)
    - Guardado atómico en los paths activos (_MODEL_PATH/_SCALER_PATH/_FEATURES_PATH/_META_PATH)
    """
    global last_retrain_count, last_retrain_ts, _ORACLE_CACHE, LAST_RETRAIN_ERROR

    LAST_RETRAIN_ERROR = ""

    # 0) XGBoost disponible
    if not _XGBOOST_OK or xgb is None:
        try:
            agregar_evento("⚠️ IA: xgboost no disponible. Activando fallback sklearn.")
        except Exception:
            pass
        return _maybe_retrain_fallback_sklearn(force=force)

    # 1) Anti re-entrada
    if not _entrenando_lock.acquire(blocking=False):
        return False

    try:
        now = time.time()

        # 2) Gatillos por filas/tiempo
        filas = contar_filas_incremental()

        if not force:
            new_rows = max(0, int(filas) - int(last_retrain_count or 0))
            mins = (now - float(last_retrain_ts or 0.0)) / 60.0
            modelo_presente = _hay_modelo_ia_disponible()

            # Si no hay modelo aún, reintentar entrenamiento aunque no se cumplan gatillos de filas/tiempo.
            if modelo_presente:
                quality_trigger = False
                quality_reason = ""
                try:
                    rep_q = auditar_calibracion_seniales_reales(min_prob=float(IA_CALIB_THRESHOLD)) or {}
                    infl_q = rep_q.get("inflacion_pp", None)
                    brier_q = rep_q.get("brier", None)
                    n_q = int(rep_q.get("n", 0) or 0)
                    if isinstance(infl_q, (int, float)) and n_q >= 20 and abs(float(infl_q)) >= 12.0:
                        quality_trigger = True
                        quality_reason = "calibracion_gap"
                    if isinstance(brier_q, (int, float)) and float(brier_q) >= 0.30:
                        quality_trigger = True
                        quality_reason = quality_reason or "brier"
                    dg = _leer_gate_desde_diagnostico(ttl_s=60.0) if "_leer_gate_desde_diagnostico" in globals() else {}
                    if isinstance(dg, dict) and float(dg.get("drift_score", 0.0) or 0.0) >= 0.18:
                        quality_trigger = True
                        quality_reason = quality_reason or "drift"
                except Exception:
                    quality_trigger = False

                if new_rows >= int(RETRAIN_INTERVAL_ROWS):
                    pass
                else:
                    if mins >= float(RETRAIN_INTERVAL_MIN) and new_rows >= int(MIN_NEW_ROWS_FOR_TIME):
                        pass
                    elif quality_trigger:
                        agregar_evento(f"🧪 IA reentreno por calidad: {quality_reason} (rows+={new_rows}, min={mins:.1f}).")
                    else:
                        return False

        # 3) Reparar incremental si quedó “mutante” + leer incremental (con LOCK)
        ruta_inc = "dataset_incremental.csv"
        if not os.path.exists(ruta_inc):
            try:
                agregar_evento("⚠️ IA: dataset_incremental.csv no existe aún. Esperando backfill incremental.")
            except Exception:
                pass
            return False
        try:
            with file_lock_required(INCREMENTAL_LOCK_FILE, timeout=6.0, stale_after=30.0) as got:
                if not got:
                    agregar_evento("⚠️ IA: incremental.lock ocupado; se pospone lectura/reentreno para evitar carreras.")
                    return False
                try:
                    reparar_dataset_incremental_mutante(
                        ruta=ruta_inc,
                        cols=_canonical_incremental_cols(INCREMENTAL_FEATURES_V2)
                    )
                except Exception:
                    pass

                df = None
                for enc in ("utf-8", "utf-8-sig", "latin-1", "windows-1252"):
                    try:
                        df = pd.read_csv(ruta_inc, encoding=enc, engine="python", on_bad_lines="skip")
                        break
                    except Exception:
                        continue
        except Exception:
            df = None

        if df is None or df.empty:
            return False

        # 4) Construir X/y robusto (usa tus builders)
        feats_pref = list(FEATURE_SET_PROD_WARMUP)

        X, y, feats_used, label_col = _build_Xy_incremental(df, feature_names=feats_pref)
        if X is None or y is None or feats_used is None:
            return False

        # Telemetría de limpieza (dedup + calidad mínima) para diagnóstico en vivo.
        try:
            q = globals().get("_LAST_XY_QUALITY", {}) or {}
            dup_rm = int(q.get("duplicates_removed", 0) or 0)
            rb = int(q.get("rows_before", len(X)) or len(X))
            ra = int(q.get("rows_after", len(X)) or len(X))
            proxy_exc = int(q.get("proxy_rows_excluded", 0) or 0)
            proxy_kept = int(q.get("proxy_rows_kept_train_eligible", 0) or 0)
            train_elig = int(q.get("rows_train_eligible", len(X)) or len(X))
            inelig_exc = int(q.get("train_ineligible_excluded", 0) or 0)
            nan_rows = int(q.get("nan_rows_detected", 0) or 0)
            range_rows = int(q.get("invalid_range_rows_detected", 0) or 0)
            feat_fail = q.get("feature_fail_counts", {}) if isinstance(q.get("feature_fail_counts", {}), dict) else {}
            low_var = q.get("low_variance_features", []) if isinstance(q.get("low_variance_features", []), list) else []
            if dup_rm > 0:
                sig_clean = f"{dup_rm}:{rb}->{ra}"
                last_clean = globals().get("_IA_TRAIN_CLEAN_LOG", {}) or {}
                now_clean = time.time()
                should_clean_log = (
                    sig_clean != str(last_clean.get("sig", "")) or
                    (now_clean - float(last_clean.get("ts", 0.0) or 0.0)) >= 25.0
                )
                if should_clean_log:
                    agregar_evento(f"🧹 IA train-clean: dedup {dup_rm} filas ({rb}->{ra}).")
                    globals()["_IA_TRAIN_CLEAN_LOG"] = {"sig": sig_clean, "ts": now_clean}
            if (proxy_exc > 0) or (proxy_kept > 0) or (inelig_exc > 0) or (nan_rows > 0) or (range_rows > 0):
                agregar_evento(
                    "🧪 IA embudo filas: "
                    f"proxy_excl={proxy_exc} proxy_ok={proxy_kept} no_entrenable={inelig_exc} "
                    f"nan={nan_rows} rango_invalido={range_rows} elegibles={train_elig}."
                )
            if feat_fail:
                det = ", ".join([f"{k}:{v}" for k, v in list(feat_fail.items())[:8]])
                agregar_evento(f"🧪 IA embudo features: fallidas={len(feat_fail)} [{det}]")
            if low_var:
                agregar_evento(f"🧪 IA embudo features: baja_var={','.join([str(x) for x in low_var[:8]])}")
        except Exception:
            pass

        # 4.1) Auditoría de salud (variación + dominancia) y descarte temporal
        health_before = _auditar_salud_features(X, feats_used)

        # 4.1.b) Data quality gate (si dataset no respira, no entrenar)
        dq_ok, dq_reasons, dq_health = _dataset_quality_gate_for_training(X, feats_used)
        health_before = dq_health if isinstance(dq_health, dict) and dq_health else health_before
        if not dq_ok:
            try:
                agregar_evento(f"🛑 IA DATA QUALITY: entrenamiento bloqueado ({'; '.join(dq_reasons)}).")
            except Exception:
                pass
            # Si no existe ningún modelo, intentar fallback simple para salir de OFF.
            if not _hay_modelo_ia_disponible():
                return _maybe_retrain_fallback_sklearn(force=True)
            return False

        # 4.2) Reducir features casi constantes/redundantes para subir eficiencia real
        X, feats_used, dropped_feats = _seleccionar_features_utiles_train(X, feats_used)
        if dropped_feats:
            try:
                txt = ", ".join([f"{k}:{r}" for k, r in dropped_feats[:8]])
                agregar_evento(f"🧪 IA: features filtradas pre-fit ({len(dropped_feats)}): {txt}")
            except Exception:
                pass

        # 4.3) Selección dinámica de calidad (features_prod vs shadow)
        freeze_core_warmup = bool(FEATURE_FREEZE_CORE_DURING_WARMUP) and (len(X) < int(FEATURE_FREEZE_CORE_MIN_ROWS))
        if FEATURE_DYNAMIC_SELECTION and (not freeze_core_warmup):
            try:
                feats_quality, quality_report = _seleccionar_features_calidad(X, y, feats_used)
                feats_quality = [c for c in feats_quality if c in X.columns]
                if feats_quality:
                    X = X[feats_quality].copy()
                    feats_used = list(feats_quality)

                    globals()["FEATURE_NAMES_PROD"] = list(feats_used)
                    globals()["FEATURE_NAMES_SHADOW"] = [f for f in FEATURE_NAMES_CORE_13 if f not in feats_used]

                    if quality_report:
                        txt = ", ".join([f"{k}:{r}" for k, r in quality_report[:8]])
                        agregar_evento(f"🎯 IA quality-gate: prod={feats_used} | {txt}")
            except Exception:
                pass
        elif freeze_core_warmup:
            try:
                keep_core = [f for f in FEATURE_SET_PROD_WARMUP if f in X.columns]
                if keep_core:
                    X = X[keep_core].copy()
                    feats_used = list(keep_core)
                    globals()["FEATURE_NAMES_PROD"] = list(feats_used)
                    globals()["FEATURE_NAMES_SHADOW"] = [f for f in FEATURE_NAMES_CORE_13 if f not in feats_used]
                    agregar_evento(f"🧱 IA warmup: freeze CORE ({len(feats_used)} feats) hasta n>={int(FEATURE_FREEZE_CORE_MIN_ROWS)}.")
            except Exception:
                pass

        # 4.4) Capa de madurez: evitar colapso a 1 feature durante warmup.
        try:
            n_rows_cur = int(len(X))
            if n_rows_cur < int(FEATURE_SET_CORE_EXT_MIN_ROWS):
                pref = [f for f in FEATURE_SET_PROD_WARMUP if f in X.columns]
                if len(pref) >= 3:
                    X = X[pref].copy()
                    feats_used = list(pref)
                    globals()["FEATURE_NAMES_PROD"] = list(feats_used)
                    globals()["FEATURE_NAMES_SHADOW"] = [f for f in FEATURE_NAMES_CORE_13 if f not in feats_used]
                    agregar_evento(f"🧩 IA capa warmup: prod={feats_used} (n={n_rows_cur}).")
            else:
                pref_ext = [f for f in FEATURE_SET_CORE_EXT if f in X.columns]
                if len(pref_ext) >= 5:
                    X = X[pref_ext].copy()
                    feats_used = list(pref_ext)
                    globals()["FEATURE_NAMES_PROD"] = list(feats_used)
                    globals()["FEATURE_NAMES_SHADOW"] = [f for f in FEATURE_NAMES_CORE_13 if f not in feats_used]
        except Exception:
            pass

        # 5) Recorte a MAX_DATASET_ROWS (manteniendo orden temporal)
        try:
            if int(MAX_DATASET_ROWS) > 0 and len(X) > int(MAX_DATASET_ROWS):
                X = X.iloc[-int(MAX_DATASET_ROWS):].copy()
                y = np.asarray(y)[-int(MAX_DATASET_ROWS):]
        except Exception:
            pass

        n_total = len(X)
        if n_total < int(MIN_FIT_ROWS_LOW):
            try:
                agregar_evento(f"⚠️ IA: muy poca data ({n_total}). Mínimo={MIN_FIT_ROWS_LOW}.")
            except Exception:
                pass
            return False

        # 5.1) Guardia anti-colapso de dataset:
        # evita machacar un modelo sano cuando el incremental se resetea/parcializa
        # y momentáneamente quedan muy pocas filas útiles (p.ej. n=6).
        if not force:
            try:
                meta_prev = leer_model_meta() or {}
                prev_n = int(meta_prev.get("n_samples", meta_prev.get("rows_total", meta_prev.get("n", 0))) or 0)
                prev_reliable = bool(meta_prev.get("reliable", False))
                prev_auc = float(meta_prev.get("auc", 0.0) or 0.0)
                drop_floor = int(max(MIN_FIT_ROWS_PROD, round(float(prev_n) * float(TRAIN_ROWS_DROP_GUARD_RATIO))))
                collapse_guard_on = bool((prev_n >= int(TRAIN_ROWS_DROP_GUARD_MIN_PREV)) or prev_reliable)

                # Si el campeón anterior ya era flojo/no confiable, permitimos refresh con menos filas
                # para evitar quedarse pegado a un modelo viejo por horas.
                stale_champion = bool((not prev_reliable) or (prev_auc < 0.51))
                allow_refresh_with_small = bool(stale_champion and int(n_total) >= int(MIN_FIT_ROWS_PROD))

                if collapse_guard_on and (int(n_total) < int(drop_floor)) and (not allow_refresh_with_small):
                    try:
                        agregar_evento(
                            f"🛡️ IA: NO actualizo (muestra cayó {prev_n}->{n_total}; mínimo guard={drop_floor})."
                        )
                    except Exception:
                        pass
                    return False
                elif collapse_guard_on and (int(n_total) < int(drop_floor)) and allow_refresh_with_small:
                    try:
                        agregar_evento(
                            f"♻️ IA refresh permitido: campeón previo flojo (reliable={prev_reliable}, auc={prev_auc:.3f}) con muestra {n_total}."
                        )
                    except Exception:
                        pass
            except Exception:
                pass

        # 6) Corte duro: una sola clase -> no entrenar
        try:
            pos = int(np.sum(np.asarray(y) == 1))
            neg = int(np.sum(np.asarray(y) == 0))
            if pos == 0 or neg == 0:
                try:
                    agregar_evento(f"⚠️ IA: solo una clase (pos={pos}, neg={neg}). Skip.")
                except Exception:
                    pass
                return False
        except Exception:
            pass

        # 7) Balance de clases (evita entrenar con 99% de una clase)
        try:
            pos = int(np.sum(y == 1))
            neg = int(np.sum(y == 0))
            if (pos + neg) > 0:
                frac = max(pos, neg) / float(pos + neg)
                if frac >= float(MAX_CLASS_IMBALANCE) and n_total >= int(MIN_FIT_ROWS_PROD):
                    try:
                        agregar_evento(f"⚠️ IA: clase desbalanceada (pos={pos}, neg={neg}). Skip.")
                    except Exception:
                        pass
                    return False
        except Exception:
            pass

        # 8) Split temporal TRAIN/CALIB/TEST
        def _calc_sizes(n):
            min_train_req = int(max(
                MIN_FIT_ROWS_LOW,
                MIN_TRAIN_ROWS_ADAPTIVE,
                int(round(float(n) * float(MIN_TRAIN_SHARE_ADAPTIVE))),
            ))
            n_test = int(max(MIN_TEST_ROWS, int(round(n * float(TEST_SIZE_FRAC)))))
            n_cal  = int(max(MIN_CALIB_ROWS, int(round(n * float(CALIB_SIZE_FRAC)))))

            if n < (MIN_TEST_ROWS + MIN_CALIB_ROWS + MIN_FIT_ROWS_LOW):
                n_test = max(5, int(round(n * 0.20)))
                n_cal  = max(0, int(round(n * 0.15)))

            n_train = n - n_cal - n_test
            if n_train < int(min_train_req):
                falta = int(min_train_req) - n_train
                if n_cal > 0:
                    cut = min(n_cal, falta)
                    n_cal -= cut
                    falta -= cut
                if falta > 0 and n_test > 5:
                    cut = min(n_test - 5, falta)
                    n_test -= cut
                    falta -= cut
                n_train = n - n_cal - n_test

            if n_train < int(min_train_req):
                return None

            return n_train, n_cal, n_test, min_train_req

        def _expand_test_hasta_doble_clase(y_all, n_train, n_cal, n_test, min_train_req):
            """
            Evita TEST degenerado de una sola clase cuando sí existe diversidad
            en histórico total. Conserva orden temporal moviendo frontera
            train/calib -> test (sin mezclar ni barajar).
            """
            try:
                y_np = np.asarray(y_all)
                if y_np.size <= 0:
                    return n_train, n_cal, n_test
                if len(np.unique(y_np)) < 2:
                    return n_train, n_cal, n_test

                min_test_floor = max(5, int(min(MIN_TEST_ROWS, max(5, y_np.size // 3))))
                n_test = max(int(n_test), int(min_test_floor))

                if len(np.unique(y_np[-n_test:])) >= 2:
                    return n_train, n_cal, n_test

                min_cal_keep = 0
                max_shift_from_cal = max(0, int(n_cal) - int(min_cal_keep))
                max_shift_from_train = max(0, int(n_train) - int(min_train_req))
                max_shift = max_shift_from_cal + max_shift_from_train

                while max_shift > 0 and len(np.unique(y_np[-n_test:])) < 2:
                    if n_cal > min_cal_keep:
                        n_cal -= 1
                    elif n_train > int(min_train_req):
                        n_train -= 1
                    else:
                        break
                    n_test += 1
                    max_shift -= 1

                return int(n_train), int(n_cal), int(n_test)
            except Exception:
                return n_train, n_cal, n_test

        sizes = _calc_sizes(n_total)
        if sizes is None:
            return False
        n_train, n_cal, n_test, min_train_req = sizes
        n_train, n_cal, n_test = _expand_test_hasta_doble_clase(y, n_train, n_cal, n_test, min_train_req)

        i0 = 0
        i1 = n_train
        i2 = n_train + n_cal
        i3 = n_total

        X_train = X.iloc[i0:i1].copy()
        y_train = np.asarray(y)[i0:i1]

        X_calib = X.iloc[i1:i2].copy() if n_cal > 0 else None
        y_calib = np.asarray(y)[i1:i2] if n_cal > 0 else None

        X_test  = X.iloc[i2:i3].copy()
        y_test  = np.asarray(y)[i2:i3]

        # 8.1) Selección dinámica de calidad (SIN fuga: solo con TRAIN_BASE)
        freeze_core_warmup_train = bool(FEATURE_FREEZE_CORE_DURING_WARMUP) and (n_total < int(FEATURE_FREEZE_CORE_MIN_ROWS))
        if FEATURE_DYNAMIC_SELECTION and (not freeze_core_warmup_train):
            try:
                feats_quality, quality_report = _seleccionar_features_calidad(X_train, y_train, feats_used)
                feats_quality = [c for c in feats_quality if c in X_train.columns]
                if feats_quality:
                    X_train = X_train[feats_quality].copy()
                    if X_calib is not None and len(X_calib) > 0:
                        X_calib = X_calib[feats_quality].copy()
                    X_test = X_test[feats_quality].copy()
                    feats_used = list(feats_quality)

                    globals()["FEATURE_NAMES_PROD"] = list(feats_used)
                    globals()["FEATURE_NAMES_SHADOW"] = [f for f in FEATURE_NAMES_CORE_13 if f not in feats_used]

                    if quality_report:
                        txt = ", ".join([f"{k}:{r}" for k, r in quality_report[:8]])
                        agregar_evento(f"🎯 IA quality-gate(train): prod={feats_used} | {txt}")
            except Exception:
                pass
        elif freeze_core_warmup_train:
            try:
                keep_core = [f for f in FEATURE_SET_PROD_WARMUP if f in X_train.columns]
                if keep_core:
                    X_train = X_train[keep_core].copy()
                    if X_calib is not None and len(X_calib) > 0:
                        X_calib = X_calib[keep_core].copy()
                    X_test = X_test[keep_core].copy()
                    feats_used = list(keep_core)
                    globals()["FEATURE_NAMES_PROD"] = list(feats_used)
                    globals()["FEATURE_NAMES_SHADOW"] = [f for f in FEATURE_NAMES_CORE_13 if f not in feats_used]
            except Exception:
                pass

        # 9) Escalado SOLO con TRAIN_BASE
        scaler = StandardScaler()
        Xtr_s = scaler.fit_transform(X_train)
        Xte_s = scaler.transform(X_test)
        Xcal_s = scaler.transform(X_calib) if X_calib is not None and len(X_calib) > 0 else None

        # 10) Entrenar modelo base
        pos_tr = int(np.sum(np.asarray(y_train) == 1))
        neg_tr = int(np.sum(np.asarray(y_train) == 0))
        if pos_tr > 0 and neg_tr > 0:
            scale_pos_weight = float(max(0.5, min(5.0, neg_tr / float(pos_tr))))
        else:
            scale_pos_weight = 1.0

        modelo_base = xgb.XGBClassifier(
            n_estimators=400,
            max_depth=4,
            learning_rate=0.05,
            subsample=0.9,
            colsample_bytree=0.9,
            reg_lambda=1.0,
            random_state=42,
            n_jobs=4,
            eval_metric="logloss",
            scale_pos_weight=scale_pos_weight,
        )
        modelo_base.fit(Xtr_s, y_train)

        # 11) Calibración (si hay calib y hay 2 clases)
        modelo_final = modelo_base
        calib_kind = "none"

        if Xcal_s is not None and y_calib is not None and len(y_calib) >= 10:
            try:
                if len(np.unique(y_calib)) == 2:
                    p_cal = modelo_base.predict_proba(Xcal_s)[:, 1]
                    p_cal = np.clip(np.asarray(p_cal, dtype=float), 1e-6, 1.0 - 1e-6)

                    if len(y_calib) >= 200:
                        calib_kind = "isotonic"
                        iso = IsotonicRegression(out_of_bounds="clip")
                        iso.fit(p_cal, y_calib)
                        modelo_final = ModeloXGBCalibrado(modelo_base, "isotonic", iso)
                    else:
                        calib_kind = "sigmoid"
                        z = np.log(p_cal / (1.0 - p_cal)).reshape(-1, 1)
                        lr = LogisticRegression(max_iter=200)
                        lr.fit(z, y_calib)
                        modelo_final = ModeloXGBCalibrado(modelo_base, "sigmoid", lr)
            except Exception:
                calib_kind = "none"
                modelo_final = modelo_base

        # 12) Threshold sugerido en CALIB (calidad > cantidad).
        # 1) Intentar cumplir precisión objetivo en zona alta (>=70%).
        # 2) Si no alcanza muestra mínima, fallback a F-beta (beta=0.5).
        thr = float(THR_DEFAULT)
        calib_prec_at_thr = None
        calib_n_at_thr = 0
        try:
            if Xcal_s is not None and y_calib is not None and len(y_calib) >= 20 and len(np.unique(y_calib)) == 2:
                p = modelo_final.predict_proba(Xcal_s)[:, 1]

                best_target_thr = None
                best_target_n = -1
                best_target_prec = 0.0

                best_fb_thr, best_fb = thr, -1.0
                for t in np.linspace(0.50, 0.90, 81):
                    yp = (p >= t).astype(int)
                    mask = (yp == 1)
                    n_sig = int(np.sum(mask))
                    if n_sig > 0:
                        prec = _safe_mean_np(np.asarray(y_calib)[mask] == 1, 0.0)
                    else:
                        prec = 0.0

                    # Candidato por objetivo de precisión
                    if n_sig >= int(IA_TARGET_MIN_SIGNALS) and prec >= float(IA_TARGET_PRECISION):
                        if n_sig > best_target_n:
                            best_target_thr = float(t)
                            best_target_n = int(n_sig)
                            best_target_prec = float(prec)

                    fb = fbeta_score(y_calib, yp, beta=0.5, zero_division=0)
                    if fb > best_fb:
                        best_fb = fb
                        best_fb_thr = float(t)

                if best_target_thr is not None:
                    thr = float(best_target_thr)
                    calib_prec_at_thr = float(best_target_prec)
                    calib_n_at_thr = int(best_target_n)
                else:
                    thr = float(best_fb_thr)
                    mask_fb = (p >= thr)
                    calib_n_at_thr = int(np.sum(mask_fb))
                    if calib_n_at_thr > 0:
                        calib_prec_at_thr = _safe_mean_np(np.asarray(y_calib)[mask_fb] == 1, 0.0)
        except Exception:
            thr = float(THR_DEFAULT)

        # 13) Métricas en TEST (último bloque, honesto)
        try:
            p_test = modelo_final.predict_proba(Xte_s)[:, 1]
            p_test = np.clip(np.asarray(p_test, dtype=float), 1e-6, 1.0 - 1e-6)
        except Exception:
            p_test = None

        auc = 0.0
        auc_applicable = False
        f1t = 0.0
        brier = 1.0
        try:
            if p_test is not None and len(np.unique(y_test)) == 2:
                auc = float(roc_auc_score(y_test, p_test))
                auc_applicable = True
            else:
                auc = 0.0
                auc_applicable = False
        except Exception:
            auc = 0.0
            auc_applicable = False

        try:
            if p_test is not None:
                yhat = (p_test >= float(thr)).astype(int)
                f1t = float(f1_score(y_test, yhat, zero_division=0))
                brier = float(brier_score_loss(y_test, p_test))
        except Exception:
            pass

        # 14) TimeSeriesSplit REAL (CV AUC) sobre TRAIN_BASE (diagnóstico)
        cv_auc = None
        try:
            if len(X_train) >= 200 and len(np.unique(y_train)) == 2:
                tscv = TimeSeriesSplit(n_splits=4)
                aucs = []

                cv_params = dict(
                    n_estimators=200,
                    max_depth=4,
                    learning_rate=0.05,
                    subsample=0.9,
                    colsample_bytree=0.9,
                    reg_lambda=1.0,
                    random_state=42,
                    n_jobs=4,
                    eval_metric="logloss",
                    scale_pos_weight=scale_pos_weight,
                )

                for tr_idx, va_idx in tscv.split(X_train):
                    Xtr = X_train.iloc[tr_idx]
                    ytr = y_train[tr_idx]
                    Xva = X_train.iloc[va_idx]
                    yva = y_train[va_idx]

                    if len(np.unique(ytr)) < 2 or len(np.unique(yva)) < 2:
                        continue

                    sc = StandardScaler()
                    Xtr_s2 = sc.fit_transform(Xtr)
                    Xva_s2 = sc.transform(Xva)

                    m = xgb.XGBClassifier(**cv_params)
                    m.fit(Xtr_s2, ytr)
                    pp = m.predict_proba(Xva_s2)[:, 1]
                    aucs.append(float(roc_auc_score(yva, pp)))

                if aucs:
                    cv_auc = _safe_mean_np(aucs, None)
        except Exception:
            cv_auc = None

        # 15) Reliable (criterio “producción”)
        # Además de AUC/base, exigimos que la zona de alta probabilidad no esté inflada.
        test_prec_at_thr = 0.0
        test_n_at_thr = 0
        try:
            if p_test is not None:
                mask_t = (p_test >= float(thr))
                test_n_at_thr = int(np.sum(mask_t))
                if test_n_at_thr > 0:
                    test_prec_at_thr = _safe_mean_np(np.asarray(y_test)[mask_t] == 1, 0.0)
        except Exception:
            test_prec_at_thr = 0.0
            test_n_at_thr = 0

        try:
            pos_all = int(np.sum(y == 1))
            neg_all = int(np.sum(y == 0))
            precision_gate_ok = (
                (test_n_at_thr < int(IA_TARGET_MIN_SIGNALS)) or
                (test_prec_at_thr >= float(IA_TARGET_PRECISION_FLOOR))
            )
            reliable = (
                (n_total >= int(MIN_FIT_ROWS_PROD)) and
                (n_total >= int(TRAIN_WARMUP_MIN_ROWS)) and
                (pos_all >= int(RELIABLE_POS_MIN)) and
                (neg_all >= int(RELIABLE_NEG_MIN)) and
                (auc >= float(MIN_AUC_CONF)) and
                precision_gate_ok
            )
        except Exception:
            reliable = False

        # 16) Política robusta Champion vs Challenger (anti-congelamiento por AUC ruidoso)
        prev_auc = None
        prev_brier = None
        prev_f1 = None
        prev_n_samples = 0
        prev_feat_count = 0
        prev_trained_at = None
        try:
            meta_path = globals().get("_META_PATH", "model_meta.json")
            if os.path.exists(meta_path):
                with open(meta_path, "r", encoding="utf-8") as f:
                    meta_old = json.load(f)
                if isinstance(meta_old, dict):
                    v_auc = meta_old.get("auc", None)
                    prev_auc = float(v_auc) if isinstance(v_auc, (int, float)) else None
                    v_brier = meta_old.get("brier", None)
                    prev_brier = float(v_brier) if isinstance(v_brier, (int, float)) else None
                    v_f1 = meta_old.get("f1", None)
                    prev_f1 = float(v_f1) if isinstance(v_f1, (int, float)) else None
                    prev_n_samples = int(meta_old.get("n_samples", meta_old.get("rows_total", meta_old.get("n", 0))) or 0)
                    prev_feats = meta_old.get("feature_names", meta_old.get("FEATURE_NAMES_USADAS", []))
                    if isinstance(prev_feats, list):
                        prev_feat_count = int(len(prev_feats))
                    ts_old = str(meta_old.get("trained_at", "") or "").strip()
                    if ts_old:
                        try:
                            prev_trained_at = datetime.strptime(ts_old, "%Y-%m-%d %H:%M:%S")
                        except Exception:
                            prev_trained_at = None
        except Exception:
            prev_auc = None
            prev_brier = None
            prev_f1 = None
            prev_n_samples = 0
            prev_feat_count = 0
            prev_trained_at = None

        allow_replace_collapsed = (
            (prev_feat_count > 0)
            and (prev_feat_count < int(FEATURE_MIN_ACCEPTED_COUNT))
            and (len(feats_used) >= int(FEATURE_MIN_ACCEPTED_COUNT))
        )

        # staleness override: evita quedarse pegado al campeón antiguo cuando crece la data
        min_abs_growth = int(TRAIN_REFRESH_MIN_ABS_ROWS)
        try:
            if int(prev_n_samples) <= int(TRAIN_REFRESH_LOWN_CUTOFF):
                min_abs_growth = int(TRAIN_REFRESH_MIN_ABS_ROWS_LOWN)
        except Exception:
            min_abs_growth = int(TRAIN_REFRESH_MIN_ABS_ROWS)

        stale_by_rows = bool(
            prev_n_samples > 0
            and (n_total >= int(prev_n_samples + min_abs_growth))
            and (n_total >= int(round(prev_n_samples * (1.0 + TRAIN_REFRESH_MIN_GROWTH))))
        )
        stale_by_time = False
        try:
            if prev_trained_at is not None:
                stale_by_time = (datetime.now() - prev_trained_at).total_seconds() >= float(TRAIN_REFRESH_STALE_MIN)
        except Exception:
            stale_by_time = False
        stale_override = bool(stale_by_rows or stale_by_time)

        # Score compuesto: bajar dependencia de AUC sola en tests pequeños/ruidosos
        auc_drop = (prev_auc is not None) and (auc < (prev_auc - float(AUC_DROP_TOL)))
        brier_not_worse = (prev_brier is None) or (brier <= (prev_brier + 0.01))
        f1_not_worse = (prev_f1 is None) or (f1t >= (prev_f1 - 0.03))
        small_test = int(n_test) < int(max(40, MIN_TEST_ROWS * 2))

        reject_hard = bool(
            (not force)
            and auc_drop
            and (not allow_replace_collapsed)
            and (not stale_override)
            and (not (small_test and brier_not_worse and f1_not_worse))
        )

        canary_mode = False
        if reject_hard:
            try:
                agregar_evento(f"🛡️ IA: NO actualizo (AUC bajó {prev_auc:.3f}→{auc:.3f}, sin evidencia de stale/canary).")
            except Exception:
                pass
            return False

        if allow_replace_collapsed:
            try:
                agregar_evento(
                    f"🛠️ IA: reemplazo permitido (modelo colapsado {prev_feat_count}f → nuevo {len(feats_used)}f)."
                )
            except Exception:
                pass

        if (not force) and auc_drop and (not allow_replace_collapsed):
            canary_mode = bool(TRAIN_CANARY_FORCE_UNRELIABLE and (stale_override or (small_test and brier_not_worse and f1_not_worse)))
            if canary_mode:
                try:
                    motivo = "stale" if stale_override else "test pequeño"
                    agregar_evento(
                        f"🟡 IA CANARY: AUC bajó ({prev_auc:.3f}→{auc:.3f}) pero se refresca en modo seguro ({motivo})."
                    )
                except Exception:
                    pass

        # 16.5) Guardia de promoción: si el candidato sale flojo, NO tomar volante.
        promote_ok = bool(True)
        promote_reasons = []
        try:
            if float(auc) < float(TRAIN_PROMOTE_MIN_AUC):
                promote_ok = False
                promote_reasons.append(f"auc<{float(TRAIN_PROMOTE_MIN_AUC):.2f}")
            if len(feats_used) < int(TRAIN_PROMOTE_MIN_FEATURES):
                promote_ok = False
                promote_reasons.append(f"feats<{int(TRAIN_PROMOTE_MIN_FEATURES)}")
            if float(test_prec_at_thr) < float(IA_TARGET_PRECISION_FLOOR):
                promote_ok = False
                promote_reasons.append(f"p@thr<{float(IA_TARGET_PRECISION_FLOOR):.2f}")
            if isinstance(brier, (int, float)) and float(brier) > 0.28:
                promote_ok = False
                promote_reasons.append("brier_alto")
            rep_prom = auditar_calibracion_seniales_reales(min_prob=float(IA_CALIB_THRESHOLD)) or {}
            infl_prom = rep_prom.get("inflacion_pp", None)
            if isinstance(infl_prom, (int, float)) and abs(float(infl_prom)) > 15.0:
                promote_ok = False
                promote_reasons.append("gap_pred_real")
            hg_train = _estado_guardrail_ia_fuerte(force=True)
            if bool(hg_train.get("hard_block", False)):
                promote_ok = False
                rh = hg_train.get("reasons", []) if isinstance(hg_train, dict) else []
                if isinstance(rh, list) and rh:
                    promote_reasons.append("hard_guard:" + ",".join([str(x) for x in rh[:3]]))
                else:
                    promote_reasons.append("hard_guard")
        except Exception:
            pass

        if (not force) and (not promote_ok):
            try:
                agregar_evento(
                    f"🧯 IA: candidato NO promovido ({', '.join(promote_reasons)}). Se mantiene campeón previo."
                )
            except Exception:
                pass
            return False

        # 17) Guardado atómico (compatible con tu función si existe)
        meta = {
            "trained_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "rows_total": int(n_total),
            "n_samples": int(n_total),
            "rows_train": int(n_train),
            "rows_calib": int(n_cal),
            "rows_test": int(n_test),
            "pos": int(np.sum(y == 1)),
            "neg": int(np.sum(y == 0)),
            "auc": float(auc),
            "f1": float(f1t),
            "brier": float(brier),
            "cv_auc": float(cv_auc) if isinstance(cv_auc, (int, float)) else None,
            "threshold": float(thr),
            "reliable": bool(False if canary_mode else reliable),
            "reliable_candidate": bool(reliable),
            "canary_mode": bool(canary_mode),
            "canary_started_at": datetime.now().strftime("%Y-%m-%d %H:%M:%S") if canary_mode else None,
            "canary_target_closed": int(CANARY_MIN_CLOSED_SIGNALS) if canary_mode else 0,
            "refresh_policy": "champion_canary" if canary_mode else "champion_direct",
            "calibration": str(calib_kind),
            "calib_precision_at_thr": float(calib_prec_at_thr) if isinstance(calib_prec_at_thr, (int, float)) else None,
            "calib_n_at_thr": int(calib_n_at_thr),
            "test_precision_at_thr": float(test_prec_at_thr),
            "test_n_at_thr": int(test_n_at_thr),
            "feature_names": list(feats_used),
            "label_col": str(label_col),
            "schema_version": str(SCHEMA_VERSION_ACTIVE),
            "trained_on_incremental": str(DATASET_SCHEMA_TAG),
            "feature_health": health_before,
            "dropped_features": [{"feature": k, "reason": r} for k, r in dropped_feats],
        }

        ok_save = False
        try:
            if "guardar_oracle_assets_atomico" in globals() and callable(guardar_oracle_assets_atomico):
                ok_save = bool(guardar_oracle_assets_atomico(modelo_final, scaler, list(feats_used), meta))
            else:
                # fallback por paths
                model_path = globals().get("_MODEL_PATH", "modelo_xgb.pkl")
                scaler_path = globals().get("_SCALER_PATH", "scaler.pkl")
                feats_path = globals().get("_FEATURES_PATH", "feature_names.pkl")
                meta_path = globals().get("_META_PATH", "model_meta.json")

                def _joblib_dump_atomic(obj, path):
                    tmp = path + ".tmp"
                    joblib.dump(obj, tmp)
                    os.replace(tmp, path)

                def _atomic_write_local(path, text):
                    tmp = path + ".tmp"
                    with open(tmp, "w", encoding="utf-8") as f:
                        f.write(text)
                    os.replace(tmp, path)

                with file_lock_required("oracle_assets.lock", timeout=8.0, stale_after=45.0) as got:
                    if not got:
                        raise RuntimeError("oracle_assets.lock ocupado")
                    _joblib_dump_atomic(modelo_final, model_path)
                    _joblib_dump_atomic(scaler, scaler_path)
                    _joblib_dump_atomic(list(feats_used), feats_path)
                    _atomic_write_local(meta_path, json.dumps(meta, ensure_ascii=False, indent=2))

                ok_save = True
        except Exception as e:
            try:
                agregar_evento(f"⚠️ IA: fallo guardado artefactos: {e}")
            except Exception:
                pass
            ok_save = False

        if not ok_save:
            return False

        # 18) Refrescar cache
        try:
            _ORACLE_CACHE["model"] = modelo_final
            _ORACLE_CACHE["scaler"] = scaler
            _ORACLE_CACHE["features"] = list(feats_used)
            _ORACLE_CACHE["meta"] = dict(meta)

            def _mt(p):
                try:
                    return os.path.getmtime(p)
                except Exception:
                    return None

            model_path = globals().get("_MODEL_PATH", "modelo_xgb.pkl")
            scaler_path = globals().get("_SCALER_PATH", "scaler.pkl")
            feats_path = globals().get("_FEATURES_PATH", "feature_names.pkl")
            meta_path = globals().get("_META_PATH", "model_meta.json")

            if "mtimes" not in _ORACLE_CACHE or not isinstance(_ORACLE_CACHE["mtimes"], dict):
                _ORACLE_CACHE["mtimes"] = {}
            _ORACLE_CACHE["mtimes"][model_path] = _mt(model_path)
            _ORACLE_CACHE["mtimes"][scaler_path] = _mt(scaler_path)
            _ORACLE_CACHE["mtimes"][feats_path] = _mt(feats_path)
            _ORACLE_CACHE["mtimes"][meta_path] = _mt(meta_path)
        except Exception:
            pass

        # 18.1) Verificación post-save de alineación meta/cache/artefactos (anti fósil n=22)
        try:
            meta_disk = leer_model_meta() or {}
            n_disk = int(meta_disk.get("rows_total", meta_disk.get("n_samples", 0)) or 0)
            if n_disk < int(max(1, n_total)):
                agregar_evento(f"⚠️ IA post-save: meta en disco desalineada (disk={n_disk} train={int(n_total)}). Forzando reload cache.")
            _ORACLE_CACHE["meta"] = _normalize_model_meta(meta_disk)
            _ORACLE_CACHE["model"], _ORACLE_CACHE["scaler"], _ORACLE_CACHE["features"], _ = get_oracle_assets()
            auditar_refresh_campeon_stale(meta_disk, force_log=True)
            auditar_degradacion_temporal_modelo()
        except Exception:
            pass

        # 19) Marcar “reentreno hecho”
        last_retrain_count = int(filas)
        last_retrain_ts = float(now)

        try:
            msg = f"✅ IA reentrenada | AUC={auc:.3f} F1={f1t:.3f} thr={thr:.2f} calib={calib_kind}"
            if cv_auc is not None:
                msg += f" | CV_AUC={cv_auc:.3f}"
            agregar_evento(msg)
        except Exception:
            pass

        return True

    except Exception as e:
        LAST_RETRAIN_ERROR = f"{type(e).__name__}: {e}"
        try:
            agregar_evento(f"⚠️ IA train fail: {LAST_RETRAIN_ERROR}")
        except Exception:
            pass
        return False

    finally:
        try:
            _entrenando_lock.release()
        except Exception:
            pass

# === FIN BLOQUE 10 ===

# === BLOQUE 11 — HUD Y PANEL VISUAL ===
RENDER_LOCK = threading.Lock()
RUNTIME_AUDIT_LOG_PATH = "runtime_log_ia.txt"
RUNTIME_AUDIT_ENABLE = True

# HUD observabilidad de rachas (solo diagnóstico; no altera trading/gates).
HUD_RACHA_WINDOWS = (5, 8, 12)
HUD_RACHA_MIN_MUESTRA = 8

def _runtime_audit_append(linea: str):
    try:
        if not bool(RUNTIME_AUDIT_ENABLE):
            return
        txt = str(linea or "").strip()
        if not txt:
            return
        with open(RUNTIME_AUDIT_LOG_PATH, "a", encoding="utf-8") as fh:
            fh.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {txt}\n")
    except Exception:
        pass

# Anti-spam conservador para telemetría ruidosa (no altera lógica operativa)
_EVENT_SPAM_STATE = {}


def _event_spam_policy(msg: str):
    """
    Devuelve (key, cooldown_s, material_sig) para categorías ruidosas.
    Si no aplica filtro, retorna None.
    """
    try:
        txt = str(msg or "")
    except Exception:
        return None

    # 1) IA audit tick orphan/unmatched: resumir por bot + severidad material
    if txt.startswith("🧾 IA audit tick "):
        try:
            m_bot = re.search(r"IA audit tick\s+([^:]+):", txt)
            bot = (m_bot.group(1).strip() if m_bot else "?")
            mu = re.search(r"unmatched=(\d+)", txt)
            mp = re.search(r"pending=(\d+)", txt)
            om = re.search(r"orphan_rate=([0-9]*\.?[0-9]+)", txt)
            unmatched = int(mu.group(1)) if mu else 0
            pending = int(mp.group(1)) if mp else 0
            orphan = float(om.group(1)) if om else 0.0
        except Exception:
            bot, unmatched, pending, orphan = "?", 0, 0, 0.0

        un_b = 0 if unmatched <= 0 else (1 if unmatched <= 2 else (2 if unmatched <= 5 else 3))
        pe_b = 0 if pending <= 0 else (1 if pending <= 3 else 2)
        or_b = int(max(0.0, min(1.0, orphan)) / 0.10)
        sev = max(un_b, pe_b, 1 if orphan >= 0.25 else 0)
        cooldown = 30.0 if sev >= 2 else 90.0
        return (f"audit:{bot}", cooldown, f"u{un_b}|p{pe_b}|o{or_b}")

    # 2) IA redundante no invalidante: no repetir misma firma por tick
    if "⚠️ IA redundante (NO invalida)" in txt:
        m = re.search(r"\[([^\]]+)\]", txt)
        sig = m.group(1).strip() if m else txt[:100]
        return (f"redund:{sig}", 180.0, sig)

    # 3) Input duplicado (data quality): reportar con ventana mayor salvo cambio material
    if "🧪 DATA QUALITY: INPUT DUPLICADO" in txt:
        m = re.search(r"probs clonadas\s+(\d+)/(\d+)\s+por\s+(\d+)\s+ticks", txt)
        if m:
            n_live = int(m.group(1)); n_tot = int(m.group(2)); ticks = int(m.group(3))
            sev = 0 if ticks < 4 else (1 if ticks < 8 else 2)
            return (f"dup_prob:{n_live}/{n_tot}", 120.0, f"sev{sev}")
        return ("dup_prob:generic", 120.0, txt[:80])

    # 4) Warmup/low-data/AUC mensajes repetitivos no fatales
    warmup_tags = (
        "IA LOW_DATA activa",
        "IA warmup:",
        "IA capa warmup",
        "AUC bajó",
        "NO actualizo (AUC bajó",
    )
    if any(t in txt for t in warmup_tags):
        base = re.sub(r"\d+(?:\.\d+)?", "#", txt)
        base = base[:120]
        return (f"warmup:{base}", 120.0, base)

    return None


def agregar_evento(texto: str):
    limpio = _normalizar_evento_texto(texto)

    pol = _event_spam_policy(limpio)
    if pol is not None:
        key, cooldown, material = pol
        now = float(time.time())
        st = _EVENT_SPAM_STATE.get(key, {}) if isinstance(_EVENT_SPAM_STATE, dict) else {}
        last_ts = float(st.get("ts", 0.0) or 0.0)
        last_mat = str(st.get("mat", ""))
        sup = int(st.get("sup", 0) or 0)

        changed = (material != last_mat)
        due = (now - last_ts) >= float(cooldown)
        if (not changed) and (not due):
            _EVENT_SPAM_STATE[key] = {"ts": last_ts, "mat": last_mat, "sup": sup + 1}
            return

        if sup > 0:
            limpio = f"{limpio} · (+{sup} similares)"
        _EVENT_SPAM_STATE[key] = {"ts": now, "mat": material, "sup": 0}

    eventos_recentes.append(f"[{time.strftime('%H:%M:%S')}] {limpio}")
    _runtime_audit_append(f"EVENTO: {limpio}")

def limpiar_consola():
    os.system("cls" if os.name == "nt" else "clear")

def _es_verde_resultado(x):
    return str(x or "").strip().upper() == "GANANCIA"

def _es_rojo_resultado(x):
    return str(x or "").strip().upper() == "PÉRDIDA"

def _resultado_to_mark(x):
    raw = str(x or "").strip().upper()
    if raw in {"GANANCIA", "G", "WIN", "W", "✓", "✔", "✅", "🟢"}:
        return "G"
    if raw in {"PÉRDIDA", "PERDIDA", "P", "LOSS", "L", "X", "✗", "❌", "🔴"}:
        return "R"
    return None

def _construir_matriz_resultados_columnas(estado: dict, bots: list[str], window: int = 40) -> list[dict]:
    """
    Construye matriz por columnas cerradas:
      - filas: bots
      - columnas: de más reciente [0] a más antigua [window-1]
    Cada columna incluye `cells` (bot->G/R/None) y métricas base.
    """
    cols = []
    w = max(1, int(window))
    for off in range(w):
        cells = {}
        validos = verdes = rojos = 0
        for b in list(bots or []):
            rr = list((estado.get(b, {}) or {}).get("resultados", []) or [])
            val = rr[-1 - off] if off < len(rr) else None
            mark = _resultado_to_mark(val)
            cells[b] = mark
            if mark == "G":
                validos += 1
                verdes += 1
            elif mark == "R":
                validos += 1
                rojos += 1
        ratio = (float(verdes) / float(validos)) if validos > 0 else None
        cols.append({
            "offset": int(off),
            "cells": cells,
            "total_validos": int(validos),
            "total_verdes": int(verdes),
            "total_rojos": int(rojos),
            "green_ratio": ratio,
        })
    return cols

def evaluar_patron_columna_verde(col_data: dict, thr80: float = 0.80, thr90: float = 0.90) -> dict:
    validos = int((col_data or {}).get("total_validos", 0) or 0)
    verdes = int((col_data or {}).get("total_verdes", 0) or 0)
    rojos = int((col_data or {}).get("total_rojos", 0) or 0)
    ratio = (float(verdes) / float(validos)) if validos > 0 else None
    es80 = bool((ratio is not None) and (float(ratio) >= float(thr80)))
    es90 = bool((ratio is not None) and (float(ratio) >= float(thr90)))
    return {
        "total_validos": validos,
        "total_verdes": verdes,
        "total_rojos": rojos,
        "green_ratio": ratio,
        "es_col80": es80,
        "es_col90": es90,
    }

def calcular_rebote_x_to_check_historico(columnas: list[dict], lookback: int = 12) -> dict:
    """
    Convención temporal de matriz:
      - offset 0 = columna operativa actual (más reciente cerrada)
      - offset creciente = columnas más antiguas
    Antifuga estricta:
      - NO se usa ningún par que toque offset 0
      - SOLO se usan pares históricos completos j -> j-1 con j >= 2
    """
    hist = []
    cols = list(columnas or [])
    max_j = min(len(cols) - 1, max(2, int(lookback)))
    for j in range(2, max_j + 1):
        col_j = cols[j] if j < len(cols) else {}
        col_next = cols[j - 1] if (j - 1) < len(cols) else {}
        cells_j = dict((col_j or {}).get("cells", {}) or {})
        cells_next = dict((col_next or {}).get("cells", {}) or {})
        x_total = 0
        x_rebota = 0
        for bot, mark in cells_j.items():
            if mark != "R":
                continue
            mark_next = cells_next.get(bot, None)
            if mark_next is None:
                continue
            x_total += 1
            if mark_next == "G":
                x_rebota += 1
        rate = (float(x_rebota) / float(x_total)) if x_total > 0 else None
        hist.append({"j": int(j), "x_totales": int(x_total), "x_rebotan": int(x_rebota), "rebote_rate_j": rate})
    total_x_hist = sum(int(h.get("x_totales", 0) or 0) for h in hist)
    total_x_rebote_hist = sum(int(h.get("x_rebotan", 0) or 0) for h in hist)
    rate_hist = (float(total_x_rebote_hist) / float(total_x_hist)) if total_x_hist > 0 else None
    rates_simple = [float(h["rebote_rate_j"]) for h in hist if h.get("rebote_rate_j") is not None]
    rate_simple = (sum(rates_simple) / float(len(rates_simple))) if rates_simple else None
    return {
        "pairs": hist,
        "rebote_rate_hist": rate_hist,
        "rebote_rate_hist_simple": rate_simple,  # solo debug
        "rebote_samples_hist": int(total_x_hist),
        "total_x_hist": int(total_x_hist),
        "total_x_rebote_hist": int(total_x_rebote_hist),
    }

def calcular_strong_streak(columnas_stats: list[dict], thr: float = 0.80) -> int:
    streak = 0
    for c in list(columnas_stats or []):
        ratio = c.get("green_ratio", None)
        if (ratio is None) or (float(ratio) < float(thr)):
            break
        streak += 1
    return int(streak)

def clasificar_estado_patron(col_actual: dict, col_anterior: dict, rebote_rate_hist: float | None, rebote_samples_hist: int) -> dict:
    ratio = col_actual.get("green_ratio", None)
    col80 = bool(col_actual.get("es_col80", False))
    col90 = bool(col_actual.get("es_col90", False))
    prev90 = bool((col_anterior or {}).get("es_col90", False))
    strong_streak_80 = int(col_actual.get("strong_streak_80", 0) or 0)
    strong_streak_90 = int(col_actual.get("strong_streak_90", 0) or 0)
    late_chase = bool(
        (strong_streak_80 >= int(PATTERN_STRONG_STREAK_BLOCK))
        or (strong_streak_90 >= 1)
    )
    sat_activa = bool(col90 or late_chase)
    rebote_ok = bool(
        col80
        and (not sat_activa)
        and (rebote_rate_hist is not None)
        and (float(rebote_rate_hist) >= float(PATTERN_REBOTE_MIN))
        and (int(rebote_samples_hist) >= int(PATTERN_REBOTE_MIN_SAMPLES))
    )
    continuidad_ok = bool(col80 and (not col90) and (not prev90) and (not late_chase))

    if sat_activa:
        state = "SATURACION"
    elif rebote_ok:
        state = "REBOTE"
    elif continuidad_ok:
        state = "CONTINUIDAD"
    else:
        state = "BLOQUEADO"
    return {
        "pattern_state": state,
        "late_chase": late_chase,
        "saturacion_activa": sat_activa,
        "continuidad_ok": continuidad_ok,
        "rebote_ok": rebote_ok,
        "green_ratio_col_actual": ratio,
        "strong_streak_80": strong_streak_80,
        "strong_streak_90": strong_streak_90,
    }

def aplicar_ajuste_patron_score(pattern_eval: dict) -> tuple[float, float, float]:
    state = str((pattern_eval or {}).get("pattern_state", "BLOQUEADO"))
    late_chase = bool((pattern_eval or {}).get("late_chase", False))
    bonus = 0.0
    penal = 0.0
    if state == "CONTINUIDAD":
        bonus += float(PATTERN_COL_BONUS_CONTINUIDAD)
    elif state == "REBOTE":
        bonus += float(PATTERN_COL_BONUS_REBOTE)
    elif state == "SATURACION":
        penal += float(PATTERN_COL_PENAL_SATURACION)
    if late_chase:
        penal += float(PATTERN_COL_PENAL_LATE_CHASE)
    return float(bonus), float(penal), float(bonus - penal)


def _racha_actual_color(resultados):
    r = list(resultados or [])
    largo = 0
    color = "N"
    for x in reversed(r):
        if _es_verde_resultado(x):
            if color in ("N", "V"):
                color = "V"
                largo += 1
            else:
                break
        elif _es_rojo_resultado(x):
            if color in ("N", "R"):
                color = "R"
                largo += 1
            else:
                break
        else:
            if largo > 0:
                break
    return color, int(largo)

def _densidad_verde(resultados, ventana=8):
    rr = [x for x in list(resultados or []) if _es_verde_resultado(x) or _es_rojo_resultado(x)]
    if not rr:
        return 0.0
    w = max(1, min(int(ventana), len(rr)))
    tail = rr[-w:]
    return float(sum(1 for x in tail if _es_verde_resultado(x))) / float(max(1, len(tail)))

def _compactacion_verde(resultados, ventana=12):
    rr = [x for x in list(resultados or []) if _es_verde_resultado(x) or _es_rojo_resultado(x)]
    if len(rr) < 2:
        return 0.0
    w = max(2, min(int(ventana), len(rr)))
    tail = rr[-w:]
    pos = [i for i, x in enumerate(tail) if _es_verde_resultado(x)]
    if len(pos) <= 1:
        return 0.0
    ady = sum(1 for i in range(1, len(pos)) if pos[i] == pos[i - 1] + 1)
    return float(ady) / float(max(1, len(pos) - 1))

def _persistencia_racha_verde(resultados):
    rr = [x for x in list(resultados or []) if _es_verde_resultado(x) or _es_rojo_resultado(x)]
    if len(rr) < 4:
        return None, None
    c2 = c3 = c4 = 0
    run = 0
    for x in rr:
        if _es_verde_resultado(x):
            run += 1
            if run == 2:
                c2 += 1
            elif run == 3:
                c3 += 1
            elif run == 4:
                c4 += 1
        else:
            run = 0
    p23 = (float(c3) / float(c2)) if c2 > 0 else None
    p34 = (float(c4) / float(c3)) if c3 > 0 else None
    return p23, p34

def _clasificar_regimen_racha(resultados):
    """
    Régimen observacional (solo contexto):
      - R0: ruido / sin estructura
      - R1: inicio (transición con aceleración)
      - R2: continuidad moderada
      - R3: continuidad fuerte
      - R4: zona madura/sobreextendida (fatiga)
    """
    rr = [x for x in list(resultados or []) if _es_verde_resultado(x) or _es_rojo_resultado(x)]
    if len(rr) < HUD_RACHA_MIN_MUESTRA:
        return "R0"
    d5 = _densidad_verde(rr, 5)
    d8 = _densidad_verde(rr, 8)
    d12 = _densidad_verde(rr, 12)
    acel = d5 - d12
    color, largo = _racha_actual_color(rr)
    comp = _compactacion_verde(rr, 12)

    if color == "V" and largo >= 6 and (d8 >= 0.65 or d12 >= 0.62):
        return "R4"
    if color == "V" and largo >= 4 and d8 >= 0.60 and comp >= 0.55 and acel >= -0.04:
        return "R3"
    if color == "V" and largo >= 3 and d8 >= 0.55 and comp >= 0.45 and acel >= -0.05:
        return "R2"
    if acel >= 0.15 and d5 >= 0.45:
        return "R1"
    return "R0"

def _edad_regimen_racha(resultados):
    """Edad aproximada del régimen actual (t1/t2/t3/t4+)."""
    try:
        _c, largo = _racha_actual_color(resultados)
        if largo <= 0:
            return "t0"
        if largo >= 4:
            return "t4+"
        return f"t{int(largo)}"
    except Exception:
        return "t0"

def _fmt_prob_pct(p):
    if p is None:
        return "--"
    try:
        return f"{float(p)*100:.0f}%"
    except Exception:
        return "--"

# Mostrar panel
def mostrar_panel():
    # === IA: actualizar Prob IA antes de render (NO afecta lógica de trading) ===
    try:
        actualizar_prob_ia_todos()
    except Exception:
        pass

    """
    HUD principal: muestra estado de los bots, saldos, IA y eventos recientes.
    """
    global meta_mostrada

    # Respetar ventana de limpieza (para mensajes especiales)
    if time.time() < LIMPIEZA_PANEL_HASTA:
        limpiar_consola()
        return

    # Limpiar consola con protección
    try:
        limpiar_consola()
    except Exception:
        pass

    # Margen a la izquierda para encuadrar mejor
    padding = " " * 4

    # ==========================
    # CABECERA SUPERIOR DEL HUD
    # ==========================

    # Línea de estado general
    actualizar_pause_state_maestro()
    if maestro_en_pausa():
        rem = tiempo_restante_pausa_maestro()
        mm, ss = divmod(max(0, int(rem)), 60)
        ref_txt = f"{float(maestro_pause_ref_balance):.2f}" if isinstance(maestro_pause_ref_balance, (int, float)) else "--"
        trg_txt = f"{float(maestro_pause_trigger_balance):.2f}" if isinstance(maestro_pause_trigger_balance, (int, float)) else "--"
        print(padding + Fore.LIGHTRED_EX + Style.BRIGHT + "⛔ MAESTRO EN PAUSA")
        print(padding + Fore.LIGHTRED_EX + "Protección por drawdown 20% activada desde monitor")
        print(padding + Fore.LIGHTRED_EX + f"⏳ Restante: {mm:02d}:{ss:02d} | reason={maestro_pause_reason or 'drawdown_20_monitor'}")
        print(padding + Fore.LIGHTRED_EX + f"📉 Ref={ref_txt} | Trigger={trg_txt}")
    else:
        print(padding + Fore.GREEN + "🟢 MODO OPERACIÓN ACTIVO – Escaneando…")
    if _purificacion_real_activa():
        print(padding + Fore.YELLOW + "🧪 IA REAL purificada | LXV_SYNC habilitado")

    # Etapa activa para depuración de flujo
    try:
        edad_etapa = max(0, int(time.time() - float(ETAPA_TS)))
        print(padding + Fore.YELLOW + f"🧭 ETAPA {ETAPA_ACTUAL}: {ETAPA_DETALLE} ({edad_etapa}s)")
    except Exception:
        pass

    # Saldo actual (archivo Deriv o saldo_real en memoria)
    try:
        valor = obtener_valor_saldo()
        if valor is None:
            valor = float(saldo_real)
        saldo_str = f"{float(valor):.2f}"
    except Exception:
        valor = None
        saldo_str = "--"

    print(padding + Fore.GREEN + f"💰 SALDO EN CUENTA REAL DERIV: {saldo_str}")

    # Saldo inicial y meta
    try:
        if SALDO_INICIAL is None and isinstance(valor, (int, float)):
            inicializar_saldo_real(float(valor))
        inicial_str = f"{float(SALDO_INICIAL):.2f}" if SALDO_INICIAL is not None else "--"
    except Exception:
        inicial_str = "--"

    try:
        meta_str = f"{float(META):.2f}" if META is not None else "--"
    except Exception:
        meta_str = "--"

    print(padding + Fore.GREEN + f"💰 SALDO INICIAL {inicial_str} 🎯 META {meta_str}")

    # Resumen rápido para que el HUD no se vea "vacío"
    try:
        bots_con_prob = 0
        umbral_real_vigente = float(get_umbral_real_calibrado())
        umbral_obs = float(globals().get("IA_OBSERVE_THR", 0.70) or 0.70)
        bots_real = 0
        bots_obs = 0
        mejor = None
        for b in BOT_NAMES:
            pb = _prob_ia_operativa_bot(b, default=None)
            if isinstance(pb, (int, float)):
                bots_con_prob += 1
                if float(pb) >= float(umbral_real_vigente):
                    bots_real += 1
                if float(pb) >= float(umbral_obs):
                    bots_obs += 1
                if (mejor is None) or (float(pb) > mejor[1]):
                    mejor = (b, float(pb))
        owner = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else leer_token_actual()
        owner_txt = "DEMO" if owner in (None, "none") else f"REAL:{owner}"
        mejor_txt = "--" if mejor is None else f"{mejor[0]} {mejor[1]*100:.1f}%"
        suceso_vals = [float(estado_bots.get(b, {}).get("ia_suceso_idx", 0.0) or 0.0) for b in BOT_NAMES]
        best_suceso = max(suceso_vals) if suceso_vals else 0.0
        sensores_planos = sum(1 for b in BOT_NAMES if bool(estado_bots.get(b, {}).get("ia_sensor_plano", False)))
        sensores_warmup = sum(1 for b in BOT_NAMES if bool(estado_bots.get(b, {}).get("ia_sensor_warmup", False)))
        n_min_real, n_req_real = _n_minimo_real_status()
        n_min_disp = min(int(n_min_real), int(n_req_real))
        n_min_extra = max(0, int(n_min_real) - int(n_req_real))
        n_min_txt = f"{n_min_disp}/{n_req_real}" + (f" (+{n_min_extra} acum)" if n_min_extra > 0 else "")
        print(padding + Fore.CYAN + f"📊 Prob IA visibles: {bots_con_prob}/{len(BOT_NAMES)} | OBS≥{umbral_obs*100:.1f}%: {bots_obs} | REAL≥{umbral_real_vigente*100:.1f}%: {bots_real} | Mejor: {mejor_txt} | Suceso↑: {best_suceso:5.1f} | SENSOR_PLANO: {sensores_planos}/{len(BOT_NAMES)} (warmup:{sensores_warmup}) | n_min_real: {n_min_txt} | Token: {owner_txt}")

        try:
            meta_live = resolver_canary_estado(leer_model_meta() or {})
            reliable = bool(meta_live.get("reliable", False))
            canary_live = bool(meta_live.get("canary_mode", False))
            n_samples_live = int(meta_live.get("n_samples", meta_live.get("n", 0)) or 0)
            warmup_live = bool(meta_live.get("warmup_mode", n_samples_live < int(TRAIN_WARMUP_MIN_ROWS)))
            cap_base = float(IA_WARMUP_LOW_EVIDENCE_CAP_BASE)
            cap_post = float(IA_WARMUP_LOW_EVIDENCE_CAP_POST_N15)
            post_n15 = bool(_todos_bots_con_n_minimo_real())
            cap_now = cap_post if post_n15 else cap_base
            mode_h = str(DYN_ROOF_STATE.get("last_gate_mode", "A") or "A")
            confirm_h = int(DYN_ROOF_STATE.get("confirm_streak", 0) or 0)
            confirm_need_h = int(DYN_ROOF_STATE.get("last_confirm_need", DYN_ROOF_CONFIRM_TICKS) or DYN_ROOF_CONFIRM_TICKS)
            confirm_disp_h = min(confirm_h, confirm_need_h)
            confirm_extra_h = max(0, confirm_h - confirm_need_h)
            confirm_txt_h = f"{confirm_disp_h}/{confirm_need_h}" + (f" (+{confirm_extra_h} acum)" if confirm_extra_h > 0 else "")
            trigger_ok_h = bool(DYN_ROOF_STATE.get("last_trigger_ok", False))
            clone_gate = bool(DYN_ROOF_STATE.get("gate_consumed", False))
            best_prob = float(mejor[1]) if isinstance(mejor, tuple) and len(mejor) >= 2 else 0.0
            unrel_thr_live = float(_umbral_unrel_operativo(mejor[0] if isinstance(mejor, tuple) else None, best_prob))
            auto_adapt_ok = bool(
                AUTO_REAL_ALLOW_UNRELIABLE_POST_N15
                and post_n15
                and (n_samples_live >= int(AUTO_REAL_UNRELIABLE_MIN_N))
                and (best_prob >= float(unrel_thr_live))
            )
            auto_state = "OK" if reliable else ("ADAPT" if auto_adapt_ok else "BLOCK")

            c_prog = int(meta_live.get('canary_closed_signals', 0) or 0)
            c_tgt = int(meta_live.get('canary_target_closed', 0) or 0)
            c_hit = float(meta_live.get('canary_hitrate', 0.0) or 0.0) * 100.0
            canary_prog_txt = f"{c_prog}/{c_tgt}" if canary_live else "-"

            why_reasons = []
            if warmup_live:
                why_reasons.append("warmup")
            if (not reliable) and (not canary_live) and (not auto_adapt_ok):
                if not bool(AUTO_REAL_ALLOW_UNRELIABLE_POST_N15):
                    why_reasons.append("adapt_off")
                if not post_n15:
                    why_reasons.append("n15_pending")
                if n_samples_live < int(AUTO_REAL_UNRELIABLE_MIN_N):
                    why_reasons.append(f"n<{int(AUTO_REAL_UNRELIABLE_MIN_N)}")
                if best_prob < float(unrel_thr_live):
                    why_reasons.append(f"p_best<{float(unrel_thr_live)*100:.1f}%")
            if confirm_h < confirm_need_h:
                why_reasons.append(f"confirm_pending({confirm_txt_h})")
            if not trigger_ok_h:
                why_reasons.append("trigger_no")
            try:
                ctt_status_h = str(CTT_STATE.get("status", "NEUTRAL") or "NEUTRAL")
                ctt_gate_h = str(CTT_STATE.get("gate", "NEUTRAL") or "NEUTRAL")
                ctt_reason_h = str(CTT_STATE.get("reason", "na") or "na")
                if ctt_gate_h == "BLOCK":
                    why_reasons.append(f"ctt_block({ctt_status_h.lower()}:{ctt_reason_h})")
                elif ctt_status_h in {"RED_WEAK", "GREEN_DIAGNOSTIC"}:
                    why_reasons.append(f"ctt_{ctt_status_h.lower()}({ctt_reason_h})")
            except Exception:
                pass
            why_txt = "none" if not why_reasons else ",".join(why_reasons)

            p_raw_best = None
            p_pre_best = None
            try:
                bb = DYN_ROOF_STATE.get("confirm_bot", None)
                if not (isinstance(bb, str) and bb in estado_bots):
                    live_best = []
                    for bname in BOT_NAMES:
                        stx = estado_bots.get(bname, {})
                        px = stx.get("prob_ia", None)
                        if bool(stx.get("ia_ready", False)) and isinstance(px, (int, float)) and np.isfinite(float(px)):
                            live_best.append((float(px), bname))
                    if live_best:
                        bb = max(live_best, key=lambda t: t[0])[1]
                if isinstance(bb, str) and bb in estado_bots:
                    stbb = estado_bots.get(bb, {})
                    pr = stbb.get("ia_prob_raw_model", None)
                    if isinstance(pr, (int, float)) and np.isfinite(float(pr)):
                        p_raw_best = float(pr)
                    else:
                        pc = stbb.get("ia_prob_cal_model", None)
                        if isinstance(pc, (int, float)) and np.isfinite(float(pc)):
                            p_raw_best = float(pc)
                        else:
                            pf = stbb.get("prob_ia", None)
                            if isinstance(pf, (int, float)) and np.isfinite(float(pf)):
                                p_raw_best = float(pf)
                    pp = stbb.get("ia_prob_pre_cap", None)
                    if isinstance(pp, (int, float)) and np.isfinite(float(pp)):
                        p_pre_best = float(pp)
                    elif isinstance(stbb.get("prob_ia", None), (int, float)) and np.isfinite(float(stbb.get("prob_ia", None))):
                        p_pre_best = float(stbb.get("prob_ia", None))
            except Exception:
                p_raw_best = None
                p_pre_best = None
            p_raw_txt = f"{p_raw_best*100:.1f}%" if isinstance(p_raw_best, (int, float)) else "--"
            p_pre_txt = f"{p_pre_best*100:.1f}%" if isinstance(p_pre_best, (int, float)) else "--"

            why_line = (
                f"🧩 WHY-NO: CAP≈{cap_now*100:.1f}% (warmup={'sí' if warmup_live else 'no'}) | "
                f"AUTO={auto_state} reliable={'sí' if reliable else 'no'} canary={'sí' if canary_live else 'no'} n={n_samples_live} p_raw={p_raw_txt} p_pre={p_pre_txt} p_cap={best_prob*100:.1f}% why={why_txt} | canary_prog={canary_prog_txt} hit={c_hit:.1f}% | "
                f"ROOF mode={mode_h} confirm={confirm_txt_h} trigger_ok={'sí' if trigger_ok_h else 'no'} trig_force={'sí' if bool(DYN_ROOF_STATE.get('last_trigger_force', False)) else 'no'} gate_consumed={'sí' if clone_gate else 'no'}"
            )
            print(padding + Fore.YELLOW + why_line)
            _runtime_audit_append(why_line)

            # ===== HUD DIAGNÓSTICO RÁPIDO (solo visual, no cambia lógica) =====
            roof_h = float(DYN_ROOF_STATE.get("roof", DYN_ROOF_FLOOR) or DYN_ROOF_FLOOR)
            floor_h = float(DYN_ROOF_STATE.get("last_floor_eff", _umbral_real_operativo_actual()) or _umbral_real_operativo_actual())
            floor_gate_h = float(DYN_ROOF_STATE.get("last_floor_gate", floor_h) or floor_h)
            live_peak_h = float(DYN_ROOF_STATE.get("last_live_peak", 0.0) or 0.0)
            live_peak_n_h = len(DYN_ROOF_STATE.get("live_peak_hist", []) or [])
            obs_ok = bool(best_prob >= float(umbral_obs))
            unrel_ok = bool(best_prob >= float(unrel_thr_live))
            roof_ok = bool(best_prob >= float(roof_h))
            confirm_ok = bool(confirm_h >= confirm_need_h)
            trig_ok = bool(trigger_ok_h)
            rel_ok = bool(reliable)
            can_ok = bool(canary_live)
            classic_ok = bool(best_prob >= float(AUTO_REAL_THR_MIN))

            p_diag = float(best_prob)
            p_model = float(best_prob)
            p_oper = float(best_prob) if (confirm_ok and trig_ok and (rel_ok or can_ok or auto_adapt_ok)) else 0.0
            modo_score = "MODEL" if str(estado_bots.get(mejor[0], {}).get("modo_ia", "off")).lower() == "modelo" else str(estado_bots.get(mejor[0], {}).get("modo_ia", "off")).upper()

            funnel_checks = [
                ("OBS70", obs_ok),
                (f"UNREL{int(round(unrel_thr_live*100))}", unrel_ok),
                ("ROOF", roof_ok),
                (f"CONF {confirm_txt_h}", confirm_ok),
                ("TRIG", trig_ok),
                ("REL", rel_ok),
                ("CAN", can_ok),
                (f"CLASS{int(round(AUTO_REAL_THR_MIN*100))}", classic_ok),
            ]
            funnel_txt = " | ".join([f"{k}{'✅' if v else '❌'}" for k, v in funnel_checks])

            bloqueos = [
                (f"UNREL{int(round(unrel_thr_live*100))}", unrel_ok, max(0.0, float(unrel_thr_live) - best_prob), "%"),
                ("ROOF", roof_ok, max(0.0, float(roof_h) - best_prob), "%"),
                (f"CONF {confirm_txt_h}", confirm_ok, float(max(0, confirm_need_h - confirm_h)), "ticks"),
                ("TRIGGER", trig_ok, 0.0, ""),
                ("RELIABLE", rel_ok, 0.0, ""),
                ("CANARY", can_ok, 0.0, ""),
                (f"CLASS{int(round(AUTO_REAL_THR_MIN*100))}", classic_ok, max(0.0, float(AUTO_REAL_THR_MIN) - best_prob), "%"),
            ]
            principal = next((b for b in bloqueos if not b[1]), None)
            if principal is None:
                principal_txt = "NONE"
            else:
                if principal[3] == "%":
                    principal_txt = f"{principal[0]} (faltan {principal[2]*100:.1f} pts)"
                elif principal[3] == "ticks":
                    principal_txt = f"{principal[0]} (faltan {int(principal[2])})"
                else:
                    principal_txt = principal[0]

            # Histograma compacto del bloqueo dominante para ventana reciente.
            try:
                principal_key = "ALLOW" if principal is None else str(principal[0])
                HUD_BLOQUEOS_RECIENTES.append(principal_key)
                agg = {}
                for k in HUD_BLOQUEOS_RECIENTES:
                    agg[k] = int(agg.get(k, 0)) + 1
                total_blk = max(1, len(HUD_BLOQUEOS_RECIENTES))
                top_blk = sorted(agg.items(), key=lambda kv: kv[1], reverse=True)[:3]
                top_txt = " | ".join([f"{k}:{(v*100.0/total_blk):.0f}%" for k, v in top_blk])
            except Exception:
                top_txt = "--"

            if bool(HUD_COMPACT_MODE):
                failed = [k for (k, ok) in funnel_checks if not ok]
                funnel_compact = ("OK" if not failed else ",".join(failed[:4]))
                if len(failed) > 4:
                    funnel_compact += f" +{len(failed)-4}"
                print(padding + Fore.CYAN + f"🧪 Embudo: {funnel_compact}")
            else:
                print(padding + Fore.CYAN + f"🧪 Embudo: {funnel_txt}")
            if owner in BOT_NAMES:
                principal_txt = f"{principal_txt} (solo nuevas entradas; REAL activo={owner})"
            decision_line = f"🧭 Decisión tick: P_diag={p_diag*100:.1f}% | P_model={p_model*100:.1f}% | P_oper={p_oper*100:.1f}% | modo={modo_score} | Bloqueo principal={principal_txt}"
            print(padding + Fore.CYAN + decision_line)
            _runtime_audit_append(decision_line)
            if bool(HUD_COMPACT_MODE):
                print(padding + Fore.CYAN + f"📏 Umbrales: UNREL={unrel_thr_live*100:.0f}% | ROOF={roof_h*100:.1f}% | FLOOR={floor_h*100:.1f}% | CLASSIC={AUTO_REAL_THR_MIN*100:.0f}%")
            else:
                print(padding + Fore.CYAN + f"📏 Umbrales activos: OBS={umbral_obs*100:.0f}% | UNREL={unrel_thr_live*100:.0f}% | ROOF={roof_h*100:.1f}% | FLOOR={floor_h*100:.1f}% | B-GATE={floor_gate_h*100:.1f}% | LIVE_MAX={live_peak_h*100:.1f}% (n={live_peak_n_h}) | CLASSIC={AUTO_REAL_THR_MIN*100:.0f}%")
            bloqueos_line = f"📉 Bloqueo dominante ({len(HUD_BLOQUEOS_RECIENTES)} ticks): {top_txt}"
            print(padding + Fore.CYAN + bloqueos_line)
            _runtime_audit_append(bloqueos_line)

            # Etiquetas separadas por bot: CONTABLE (calibración) vs OPERABLE (REAL).
            try:
                tags = []
                thr_oper = float(_umbral_real_operativo_actual())
                for b in BOT_NAMES:
                    st_b = estado_bots.get(b, {}) if isinstance(estado_bots, dict) else {}
                    p_diag_b = st_b.get("prob_ia", None)
                    p_oper_b = _prob_ia_operativa_bot(b, default=None)
                    c_ok = bool(isinstance(p_diag_b, (int, float)) and np.isfinite(float(p_diag_b)) and float(p_diag_b) >= float(IA_CALIB_THRESHOLD))
                    o_ok = bool(
                        isinstance(p_oper_b, (int, float))
                        and np.isfinite(float(p_oper_b))
                        and bool(st_b.get("ia_ready", False))
                        and str(st_b.get("modo_ia", "off")).lower() != "off"
                        and ia_prob_valida(b, max_age_s=12.0)
                        and (float(p_oper_b) >= float(thr_oper))
                    )
                    tags.append(f"{b}:C{'✅' if c_ok else '❌'}|O{'✅' if o_ok else '❌'}")
                tags_line = "🏷️ Etiquetas bot: " + " · ".join(tags)
                print(padding + Fore.CYAN + tags_line)
                _runtime_audit_append(tags_line)
            except Exception:
                pass

            # GO/NO-GO rápido para REAL continuo (disciplina operativa).
            try:
                meta_go = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
                n_samples_go = int(meta_go.get("n_samples", meta_go.get("n", 0)) or 0)
                auc_go = float(meta_go.get("auc", 0.0) or 0.0)
                rel_go = bool(meta_go.get("reliable", False))
                rep_go = auditar_calibracion_seniales_reales(min_prob=float(IA_CALIB_THRESHOLD)) or {}
                closed_go = int(rep_go.get("n_total_closed", rep_go.get("n", 0)) or 0)
                hg_go = _estado_guardrail_ia_fuerte(force=False)
                go_ok = bool(
                    (n_samples_go >= int(REAL_GO_N_MIN))
                    and (closed_go >= int(REAL_GO_CLOSED_MIN))
                    and rel_go
                    and (auc_go >= 0.53)
                    and (not bool(hg_go.get("hard_block", False)))
                )
                go_reasons = []
                if n_samples_go < int(REAL_GO_N_MIN):
                    go_reasons.append(f"n_samples<{int(REAL_GO_N_MIN)}")
                if closed_go < int(REAL_GO_CLOSED_MIN):
                    go_reasons.append(f"closed<{int(REAL_GO_CLOSED_MIN)}")
                if not rel_go:
                    go_reasons.append("reliable=false")
                if auc_go < 0.53:
                    go_reasons.append("auc<0.53")
                if bool(hg_go.get("hard_block", False)):
                    go_reasons.append("hard_guard=RED")
                go_line = (
                    f"🧭 GO/NO-GO REAL: {'GO ✅' if go_ok else 'NO-GO ❌'} "
                    f"(n={n_samples_go}, closed={closed_go}, auc={auc_go:.3f}, rel={'sí' if rel_go else 'no'}, HG={hg_go.get('level','GREEN')})"
                )
                if go_reasons:
                    go_line += " | why=" + ",".join(go_reasons[:5])
                print(padding + Fore.CYAN + go_line)
                _runtime_audit_append(go_line)
            except Exception:
                pass

            # Diagnóstico por bot (top-3) para ver exactamente qué compuerta frena.
            try:
                global _LAST_HUD_BOT_GATE_DIAG_TS
                now_dbg = time.time()
                if (now_dbg - float(_LAST_HUD_BOT_GATE_DIAG_TS or 0.0)) >= float(HUD_BOT_GATE_DIAG_EVERY_S):
                    _LAST_HUD_BOT_GATE_DIAG_TS = now_dbg
                    live_diag = []
                    for b in BOT_NAMES:
                        pb = estado_bots.get(b, {}).get("prob_ia", None)
                        if isinstance(pb, (int, float)) and np.isfinite(float(pb)):
                            live_diag.append((b, float(pb)))
                    live_diag.sort(key=lambda x: x[1], reverse=True)

                    roof_dbg = float(DYN_ROOF_STATE.get("roof", DYN_ROOF_FLOOR) or DYN_ROOF_FLOOR)
                    confirm_bot_dbg = DYN_ROOF_STATE.get("confirm_bot")
                    confirm_st_dbg = int(DYN_ROOF_STATE.get("confirm_streak", 0) or 0)
                    confirm_need_dbg = int(DYN_ROOF_STATE.get("last_confirm_need", DYN_ROOF_CONFIRM_TICKS) or DYN_ROOF_CONFIRM_TICKS)

                    dbg_chunks = []
                    for b, pb in live_diag[:3]:
                        unrel_b = float(_umbral_unrel_operativo(b, pb))
                        unrel_ok_b = bool(pb >= unrel_b)
                        roof_ok_b = bool(pb >= roof_dbg)
                        suceso_ok_b = bool(estado_bots.get(b, {}).get("ia_suceso_ok", False))
                        clone_b = bool(estado_bots.get(b, {}).get("ia_input_duplicado", False))

                        if b == confirm_bot_dbg:
                            conf_txt = f"{min(confirm_st_dbg, confirm_need_dbg)}/{confirm_need_dbg}"
                        else:
                            conf_txt = f"0/{confirm_need_dbg}"

                        dbg_chunks.append(
                            f"{b}:{pb*100:.1f}% UNR{'✅' if unrel_ok_b else f'❌({max(0.0,(unrel_b-pb))*100:.1f})'} "
                            f"ROOF{'✅' if roof_ok_b else f'❌({max(0.0,(roof_dbg-pb))*100:.1f})'} "
                            f"CONF{conf_txt} SUC{'✅' if suceso_ok_b else '❌'} CLN{'🛑' if clone_b else 'ok'}"
                        )

                    if dbg_chunks and bool(HUD_SHOW_TOP3_GATES):
                        print(padding + Fore.CYAN + f"🔬 Gates(top3): {' | '.join(dbg_chunks)}")
            except Exception:
                pass

            emb = EMBUDO_DECISION_STATE if isinstance(EMBUDO_DECISION_STATE, dict) else {}
            print(
                padding + Fore.CYAN +
                f"🧪 Embudo: final={emb.get('decision_final','--')} risk={emb.get('risk_mode','--')} gate={emb.get('gate_quality','--')} "
                f"top1={emb.get('top1_bot') or '--'}({float(emb.get('top1_prob',0.0) or 0.0)*100:.1f}%) "
                f"top2={emb.get('top2_bot') or '--'} gap={float(emb.get('gap_value',0.0) or 0.0)*100:.1f}pp "
                f"why={emb.get('decision_reason','--')} wait={emb.get('soft_wait_reason','') or '--'} "
                f"hard={emb.get('hard_block_reason','') or '--'} deg={emb.get('degrade_from','--')}"
            )
            owner_state = globals().get("LAST_REAL_OWNER_STATE", {}) if isinstance(globals().get("LAST_REAL_OWNER_STATE", {}), dict) else {}
            if owner_state:
                print(
                    padding + Fore.CYAN +
                    f"🧾 REAL owner: {owner_state.get('owner_bot','--')} | ciclo C{owner_state.get('ciclo','--')} | source={owner_state.get('source','--')}"
                )
            close_state = globals().get("LAST_REAL_CLOSE_TRACE", {}) if isinstance(globals().get("LAST_REAL_CLOSE_TRACE", {}), dict) else {}
            if close_state:
                print(
                    padding + Fore.CYAN +
                    f"🧾 Último cierre REAL: {close_state.get('bot','--')} {close_state.get('resultado','--')} "
                    f"{float(close_state.get('saldo_real_antes', 0.0) or 0.0):,.2f} -> {float(close_state.get('saldo_real_despues', 0.0) or 0.0):,.2f}"
                )

            ref_racha = ultimo_bot_real if ultimo_bot_real in BOT_NAMES else "--"
            elegido_tick = mejor[0] if isinstance(mejor, tuple) and len(mejor) >= 1 else "--"
            print(padding + Fore.CYAN + f"🧾 Contexto racha: ref={ref_racha} | elegido_tick={elegido_tick} | token_real={owner_txt}")
        except Exception:
            pass

        # Diagnóstico de rachas por bot: detecta transición/continuidad sin usarlo como señal directa.
        try:
            resumen_racha = []
            score_racha = []
            for b in BOT_NAMES:
                rr = estado_bots.get(b, {}).get("resultados", [])
                reg = _clasificar_regimen_racha(rr)
                col, lar = _racha_actual_color(rr)
                p23, p34 = _persistencia_racha_verde(rr)
                d8 = _densidad_verde(rr, 8)
                d12 = _densidad_verde(rr, 12)
                acel = d8 - d12
                lbl = ("V" if col == "V" else ("R" if col == "R" else "N"))
                edad = _edad_regimen_racha(rr)
                d4 = _densidad_verde(rr, 4)
                resumen_racha.append(f"{b}:{reg}@{edad} {lbl}{lar} d4={d4*100:.0f}% d8={d8*100:.0f}% P23={_fmt_prob_pct(p23)} P34={_fmt_prob_pct(p34)}")
                score = (2.6 if reg == "R3" else 2.1 if reg == "R2" else 1.0 if reg == "R1" else 0.4 if reg == "R4" else 0.0) + max(0.0, acel) + max(0.0, d8 - 0.5)
                score_racha.append((b, score, reg, lar, acel))

            if resumen_racha and bool(HUD_SHOW_RACHA_BLOQUES):
                print(padding + Fore.CYAN + "🧩 Régimen racha (obs): " + " | ".join(resumen_racha[:3]))
                if len(resumen_racha) > 3:
                    print(padding + Fore.CYAN + "                          " + " | ".join(resumen_racha[3:]))

            if score_racha:
                score_racha.sort(key=lambda t: t[1], reverse=True)
                b0, _, reg0, lar0, acel0 = score_racha[0]
                print(padding + Fore.MAGENTA + f"🎯 Oportunidad racha (obs): {b0} {reg0} V{lar0 if lar0 > 0 else 0} Δdens={acel0:+.2f} (solo contexto)")
        except Exception:
            pass

        if owner not in (None, "none") and mejor is not None and owner != mejor[0]:
            print(padding + Fore.YELLOW + f"⛓️ Token bloqueado en {owner}; mejor IA actual es {mejor[0]} ({mejor[1]*100:.1f}%).")
    except Exception:
        pass
    try:
        pat = dict(globals().get("PATTERN_COL_LAST_STATE", {}) or {})
        ratio = pat.get("green_ratio_col_actual", None)
        ratio_txt = "--" if ratio is None else f"{float(ratio)*100:.1f}%"
        reb_txt = "--"
        if pat.get("rebote_rate_hist", None) is not None:
            reb_txt = f"{float(pat.get('rebote_rate_hist', 0.0))*100:.1f}%"
        print(
            padding
            + Fore.CYAN
            + "🧠 PatternCol: "
            + f"ratio={ratio_txt} V={int(pat.get('total_verdes_col_actual', 0) or 0)} "
            + f"R={int(pat.get('total_rojos_col_actual', 0) or 0)} "
            + f"reb_hist={reb_txt} "
            + f"X={int(pat.get('total_x_hist', 0) or 0)} "
            + f"X→✓={int(pat.get('total_x_rebote_hist', 0) or 0)} "
            + f"state={str(pat.get('pattern_state', 'BLOQUEADO'))} "
            + f"st80={int(pat.get('strong_streak_80', 0) or 0)} "
            + f"st90={int(pat.get('strong_streak_90', 0) or 0)} "
            + f"late={'sí' if bool(pat.get('late_chase', False)) else 'no'} "
            + f"Δ={float(pat.get('pattern_delta', 0.0) or 0.0):+.2f}"
        )
    except Exception:
        pass

    # Marcar meta_mostrada si ya se alcanzó la META y todavía no fue aceptada
    try:
        if valor is not None and META is not None and valor >= META and not META_ACEPTADA:
            meta_mostrada = True
    except Exception:
        # No tocamos meta_mostrada si hay algún problema de conversión
        pass

    # ==========================
    # TABLA PRINCIPAL DE BOTS
    # ==========================

    print(padding + Fore.CYAN + "┌────────┬────────────────────────────────────────────────────────────────────────────────┬─────────┬──────────┬──────────┬──────────┬──────────┬──────────┐")
    print(padding + Fore.CYAN + Style.BRIGHT + "│ ✨ ESTADO INTELIGENTE DE BOTS · ÚLTIMOS 40 · TOKEN · IA · RENDIMIENTO      │" + Style.RESET_ALL)
    print(padding + Fore.CYAN + "├────────┼────────────────────────────────────────────────────────────────────────────────┼─────────┬──────────┬──────────┬──────────┬──────────┬──────────┤")
    print(padding + Fore.CYAN + "│ BOT    │ Últimos 40 Resultados                                                  │ Token   │ GANANCIAS│ PÉRDIDAS │ % ÉXITO  │ Prob IA  │ Modo IA  │")
    print(padding + Fore.CYAN + "├────────┼────────────────────────────────────────────────────────────────────────────────┼─────────┬──────────┬──────────┬──────────┬──────────┬──────────┤")

    # Meta IA para colorear Prob IA (estado global del modelo)
    model_meta_live = resolver_canary_estado(leer_model_meta() or {})
    n_model_live = int(model_meta_live.get("n_samples", model_meta_live.get("n", 0)) or 0)
    warmup_model_live = bool(model_meta_live.get("warmup_mode", n_model_live < int(TRAIN_WARMUP_MIN_ROWS)))
    reliable_model_live = bool(model_meta_live.get("reliable", False))
    umbral_ia = get_umbral_dinamico(model_meta_live, ORACULO_THR_MIN)

    # Sincronía visual dura: si hay owner REAL en memoria, la tabla SIEMPRE lo refleja.
    owner_visual = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else leer_token_actual()

    for bot in BOT_NAMES:
        r = estado_bots[bot]["resultados"]
        token = "REAL" if owner_visual == bot else "DEMO"
        estado_bots[bot]["token"] = token
        src = estado_bots[bot].get("fuente")

        # Token + origen
        token_text = token
        if src and str(src).strip().upper() != "MANUAL":
            token_text += f" ({src})"
        token_color = Fore.GREEN if token_text.startswith("REAL") else Fore.CYAN
        token_text = token_color + token_text + Fore.RESET

        # Últimos 40 resultados visuales
        visual = []
        for x in r[-40:]:
            if x == "GANANCIA":
                visual.append(Fore.GREEN + "✓")
            elif x == "PÉRDIDA":
                visual.append(Fore.RED + "✗")
            elif x == "INDEFINIDO":
                visual.append(Fore.YELLOW + "·")
            else:
                visual.append(Fore.LIGHTBLACK_EX + "─")
        while len(visual) < 40:
            visual.insert(0, Fore.LIGHTBLACK_EX + "─")
        col_resultados = " ".join(visual)

        # Ganancias / Pérdidas / % éxito
        g = estado_bots[bot]["ganancias"]
        p = estado_bots[bot]["perdidas"]
        ganancias = Fore.GREEN + f"{g}"
        perdidas = Fore.RED + f"{p}"
        porc = estado_bots[bot].get("porcentaje_exito")
        total = estado_bots[bot].get("tamano_muestra", 0)

        if porc is not None:
            exito = f"{porc:.1f}% (n={total})"
            exito_color = (
                Fore.YELLOW if total < 10
                else (Fore.GREEN if porc >= 50 else Fore.RED)
            )
            if total < 10:
                exito += " ⚠"
            exito = exito_color + exito + Fore.RESET
        else:
            exito = "--"

        # --- Modo IA ---
        # HUD: por defecto asumimos low_data (warmup) y reservamos OFF para fallos duros reales.
        modo_raw = estado_bots.get(bot, {}).get("modo_ia", "low_data")
        modo = str(modo_raw or "low_data").strip().lower()

        # Normalizar variantes típicas que vienen del CSV/estado
        if modo in ("0", "false", "none", "null", ""):
            modo = "low_data"
        # (extra) por si llega tipo "off algo" o "off-xyz"
        if modo.startswith("off"):
            err_ui = str(estado_bots.get(bot, {}).get("ia_last_err", "") or "").upper()
            hard_off = err_ui.startswith("FEAT_MISMATCH") or err_ui.startswith("SCALER_FAIL") or err_ui.startswith("PRED_FAIL")
            modo = "off" if hard_off else "low_data"

        # Meta IA por bot (umbrales UI, etc.) — evita NameError y mantiene tu semáforo estable
        meta = IA_META.get(bot, {}) if "IA_META" in globals() else {}

        # --- Stats IA (solo telemetría) ---
        ia_sen   = estado_bots[bot].get("ia_seniales", 0)
        ia_acc   = estado_bots[bot].get("ia_aciertos", 0)
        ia_fal   = estado_bots[bot].get("ia_fallos", 0)
        ia_ready = estado_bots[bot].get("ia_ready", False)

        # ==========================================================
        # ✅ Prob IA = probabilidad ACTUAL del modelo (ya calibrada/ajustada)
        #    - NO mezclar con IA90_stats (eso es histórico)
        #    - OFF / inválida / vieja => "--" (gris)
        # ==========================================================

        prob_hist = get_prob_ia_historica(bot)  # se conserva por si lo usas en telemetría externa
        prob_ok = False
        prob = 0.0
        prob_str = "--"

        # 1) IA OFF => "--"
        # 2) IA ON pero prob no fresca/valida => "--"
        # 3) IA ON + prob fresca => mostrar %
        try:
            if modo != "off" and ia_prob_valida(bot, max_age_s=120.0):
                p_now = estado_bots[bot].get("prob_ia", None)
                try:
                    import math
                    if p_now is not None:
                        p = float(p_now)
                        # si viene en % (ej 53), convertir a 0.53
                        if p > 1.0 and p <= 100.0:
                            p = p / 100.0
                        if math.isfinite(p) and 0.0 <= p <= 1.0:
                            prob_ok = True
                            prob = p
                            prob_str = f"{prob*100.0:.1f}%"
                except Exception:
                    prob_ok = False
                    prob = 0.0
                    prob_str = "--"
        except Exception:
            prob_ok = False
            prob = 0.0
            prob_str = "--"

        # Fallback visual: si hay última prob reciente pero no cumplió gate, mostrarla con *
        if not prob_ok:
            try:
                p_last = estado_bots[bot].get("prob_ia", None)
                ts_last = float(estado_bots[bot].get("ia_last_prob_ts", 0.0) or 0.0)
                if isinstance(p_last, (int, float)) and ts_last > 0 and (time.time() - ts_last) <= IA_PRED_TTL_S:
                    p_aux = float(p_last)
                    if p_aux > 1.0 and p_aux <= 100.0:
                        p_aux = p_aux / 100.0
                    if 0.0 <= p_aux <= 1.0:
                        prob_ok = True
                        prob = p_aux
                        prob_str = f"{p_aux*100.0:.1f}%*"
            except Exception:
                pass

        # Confianza IA (NECESARIA: se usa para colorear modo_str)
        confianza = calcular_confianza_ia(bot, meta)

        # Decoración SOLO cuando hay prob real
        if prob_ok:
            flags = ""
            if modo == "low_data":
                flags += "l"   # low-data
            elif modo == "exp":
                flags += "e"   # experimental

            # Evita lectura "premium" cuando el modelo está en warmup/no confiable.
            if warmup_model_live or (not reliable_model_live):
                flags += "r"   # raw / no confiable

            # Penalización visual de recencia (no cambia lógica de trading).
            try:
                ult = list(estado_bots.get(bot, {}).get("resultados", []))[-2:]
                if len(ult) == 2 and all(str(x) == "PÉRDIDA" for x in ult):
                    flags += "d"   # drawdown reciente
            except Exception:
                pass

            if flags:
                prob_str += f"[{flags}]"

            # Mantener ancho de columna estable para no romper la tabla.
            if len(prob_str) > 10:
                prob_str = prob_str[:10]

        # Semáforo IA (UI FIJA)
        # ----------------------------------------------
        # Regla anti-confusión:
        # Si este bot es el que tiene el token REAL (trigger_real=True o token="REAL"),
        # NO mostramos Prob IA en vivo (puede cambiar mientras corre el contrato).
        # En su lugar mostramos: "-- | OFF" para evitar decisiones “en caliente”.
        try:
            st_ui = estado_bots.get(bot, {}) if isinstance(estado_bots, dict) else {}
        except Exception:
            st_ui = {}

        token_ui = str(st_ui.get("token") or "DEMO").strip().upper()
        ui_hide_ia = bool(st_ui.get("trigger_real", False)) or token_ui.startswith("REAL")

        # ✅ FIX: high_thr_ui SIEMPRE definido (aunque ui_hide_ia=True)
        try:
            _fn = globals().get("get_umbral_ia_vigente", None)
            if callable(_fn):
                high_thr_ui = float(_fn())
            else:
                high_thr_ui = float(IA_VERDE_THR)
        except Exception:
            high_thr_ui = float(IA_VERDE_THR)

        mid_thr_ui = max(0.0, high_thr_ui - 0.05)

        if ui_hide_ia:
            prob_ok = False
            prob_str = Fore.LIGHTBLACK_EX + "--" + Fore.RESET
            modo_str = Fore.LIGHTBLACK_EX + "OFF" + Fore.RESET
        else:
            if (modo != "off") and prob_ok:
                if (modo == "low_data") or warmup_model_live or (not reliable_model_live):
                    # En warmup/no-confiable no pintar como "verde premium".
                    prob_color = Fore.YELLOW if prob >= mid_thr_ui else Fore.LIGHTBLACK_EX
                elif prob >= high_thr_ui:
                    prob_color = Fore.GREEN
                elif prob >= mid_thr_ui:
                    prob_color = Fore.YELLOW
                else:
                    prob_color = Fore.RED
            else:
                prob_color = Fore.LIGHTBLACK_EX

            prob_str = prob_color + prob_str + Fore.RESET

            modo_map = {
                "low_data": "LWDATA",
                "exp": "EXP",
                "modelo": "MODELO",
                "off": "OFF",
            }
            modo_base = modo_map.get(modo, (modo.upper() if modo != "off" else "OFF"))

            if modo != "off":
                if confianza >= AUTO_REAL_THR_MIN:
                    modo_color = Fore.GREEN
                elif confianza >= 0.55:
                    modo_color = Fore.YELLOW
                else:
                    modo_color = Fore.LIGHTBLACK_EX
            else:
                modo_color = Fore.LIGHTBLACK_EX

            su_idx = int(round(float(estado_bots.get(bot, {}).get("ia_suceso_idx", 0.0) or 0.0)))
            is_plano = bool(estado_bots.get(bot, {}).get("ia_sensor_plano", False))
            modo_tag = f"S{max(0, min(99, su_idx)):02d}" + ("!" if is_plano else "")
            modo_txt = f"{modo_base} {modo_tag}" if modo_base != "OFF" else "OFF"
            if len(modo_txt) > 10:
                modo_txt = modo_txt[:10]
            modo_str = modo_color + modo_txt + Fore.RESET

        # --- Audio IA "es hora de invertir" (umbral fijo) ---
        audio_thr = float(globals().get("AUDIO_IA53_THR", high_thr_ui))


        token_local = (estado_bots.get(bot, {}).get("token") or "DEMO")
        es_demo_local = (str(token_local).strip().upper() == "DEMO")

        if (modo != "off") and prob_ok and (prob >= audio_thr) and not IA53_TRIGGERED[bot]:
            reproducir_evento("ia_53", es_demo=es_demo_local, dentro_gatewin=True)
            IA53_TRIGGERED[bot] = True
        elif (not prob_ok) or (modo == "off") or (prob < audio_thr):
            IA53_TRIGGERED[bot] = False


        # Línea completa del bot
        linea_bot = (
            padding + f"│ {bot:<6} │ {col_resultados:<80} │ "
            f"{token_text:<9} │ "
            f"{ganancias:<10} │ "
            f"{perdidas:<10} │ "
            f"{exito:<10} │ "
            f"{prob_str:<10} │ "
            f"{modo_str:<10} │"
        )
        print(linea_bot)

    print(padding + Fore.CYAN + "└────────┴────────────────────────────────────────────────────────────────────────────────┴─────────┴──────────┴──────────┴──────────┴──────────┴──────────┘")

    # ==========================
    # EVENTOS + TELEMETRÍA IA
    # ==========================

    # Eventos recientes
    mostrar_eventos()

    # Telemetría IA (modelo XGBoost)
    ruta_inc = "dataset_incremental.csv"
    dataset_rows = contar_filas_incremental()
    meta = _ORACLE_CACHE.get("meta") or {}
    try:
        # Normalizar SIEMPRE el meta en memoria
        if isinstance(meta, dict) and meta:
            meta = _normalize_model_meta(meta)
        else:
            meta = {}
        # Fallback duro: si el cache está incompleto, lee disco
        if (int(meta.get("n_samples", meta.get("n", 0)) or 0) == 0) and os.path.exists(_META_PATH):
            meta_disk = leer_model_meta() or {}
            if isinstance(meta_disk, dict) and meta_disk:
                meta = meta_disk
                _ORACLE_CACHE["meta"] = meta_disk
    except Exception:
        meta = meta if isinstance(meta, dict) else {}

    if dataset_rows == 0 and not meta:
        print(Fore.CYAN + " IA ▶ sin dataset_incremental.csv (n=0). Esperando que los bots generen datos...")
    elif dataset_rows < MIN_FIT_ROWS_LOW and not meta:
        faltan = max(0, MIN_FIT_ROWS_LOW - dataset_rows)
        print(Fore.CYAN + f" IA ▶ dataset con n={dataset_rows}, pero sin modelo entrenado aún.")
        print(Fore.CYAN + f"      Faltan {faltan} filas para el primer entrenamiento.")
    elif not meta:
        print(Fore.CYAN + f" IA ▶ dataset listo (n={dataset_rows}), pero sin modelo entrenado todavía.")
        print(Fore.CYAN + "      Se entrenará automáticamente por tick o al usar [E].")
        print(Fore.CYAN + f"      Requisitos mínimos: filas útiles >= {MIN_FIT_ROWS_LOW}, 2 clases (GAN/PERD), y features válidas.")
        print(Fore.CYAN + f"      Modo confiable recomendado desde n >= {TRAIN_WARMUP_MIN_ROWS}.")
        try:
            df_diag = pd.read_csv(ruta_inc, encoding="utf-8", on_bad_lines="skip") if os.path.exists(ruta_inc) else pd.DataFrame()
            y_diag = pd.to_numeric(df_diag.get("result_bin", pd.Series(dtype=float)), errors="coerce")
            pos_diag = int((y_diag == 1).sum())
            neg_diag = int((y_diag == 0).sum())
            feats_validas = int(len([c for c in df_diag.columns if c in INCREMENTAL_FEATURES_V2]))
            last_err = str(globals().get("LAST_RETRAIN_ERROR", "") or "--")
            print(Fore.CYAN + f"      Diagnóstico: clases pos/neg={pos_diag}/{neg_diag} | features válidas={feats_validas}/{len(INCREMENTAL_FEATURES_V2)} | último error train={last_err}")
        except Exception:
            pass
    else:
        pos = int(meta.get("pos", meta.get("n_pos", 0)) or 0)
        neg = int(meta.get("neg", meta.get("n_neg", 0)) or 0)
        n   = int(meta.get("n_samples", meta.get("n", 0)) or 0)

        # Fallback final: si no hay n, usa pos+neg
        if n == 0 and (pos + neg) > 0:
            n = pos + neg

        auc = float(meta.get("auc", 0.0) or 0.0)
        thr = float(meta.get("threshold", ORACULO_THR_MIN))
        reliable = bool(meta.get("reliable", False))
        auc_applicable = bool(meta.get("auc_applicable", False))
        warmup_mode = bool(meta.get("warmup_mode", n < int(TRAIN_WARMUP_MIN_ROWS)))

        modo_txt = "CONFIABLE ✅" if (reliable and n >= MIN_FIT_ROWS_PROD and not warmup_mode) else "EXPERIMENTAL ⚠"
        auc_txt = f"{auc:.3f}" if auc_applicable else "N/A (clases insuficientes en TEST)"

        print(Fore.CYAN + f" IA ▶ modelo XGBoost entrenado: n={n} (GAN={pos}, PERD={neg})")
        print(Fore.CYAN + f"      AUC={auc_txt}  | Thr={thr:.2f}  | Modo={modo_txt}")
        datos_utiles = int(max(0, pos + neg))
        mismatch = int(max(0, n - datos_utiles))
        if mismatch > 0:
            print(Fore.YELLOW + f"      ⚠️ Data quality IA: n-meta={n} pero cierres útiles={datos_utiles} (delta={mismatch}).")
        if warmup_mode:
            print(Fore.CYAN + f"      Confianza IA: BAJA (Warmup n={n}<{int(TRAIN_WARMUP_MIN_ROWS)} | cierres útiles={datos_utiles}).")
            print(Fore.CYAN + f"      Warmup activo: n={n}<{int(TRAIN_WARMUP_MIN_ROWS)} (solo monitoreo/calibración).")
        else:
            print(Fore.CYAN + f"      Confianza IA: {'MEDIA/ALTA' if reliable else 'MEDIA'} | cierres útiles={datos_utiles}.")

    # Mostrar contadores de aciertos IA por bot (resumen compacto para reducir ruido)
    resumen_hits = []
    for bot in BOT_NAMES:
        sig = int(estado_bots[bot].get("ia_seniales", 0) or 0)
        if sig <= 0:
            continue
        ac = int(estado_bots[bot].get("ia_aciertos", 0) or 0)
        pct = (ac / sig * 100.0) if sig > 0 else 0.0
        resumen_hits.append((pct, bot, ac, sig))

    if resumen_hits:
        top_hits = sorted(resumen_hits, key=lambda x: x[0], reverse=True)[:3]
        txt = " | ".join([f"{b}:{ac}/{sg} ({pc:.1f}%)" for pc, b, ac, sg in top_hits])
        print(Fore.CYAN + f" IA ACIERTOS (Top): {txt}")
    else:
        print(Fore.CYAN + " IA ACIERTOS: sin cierres auditados todavía.")

    # HISTÓRICO: señales IA que llegaron a ejecutarse y cerraron con resultado
    # (se mantiene con IA_METRIC_THRESHOLD para comparabilidad histórica de auditoría)
    print(Fore.YELLOW + f" IA HISTÓRICO (señales cerradas, ≥{IA_METRIC_THRESHOLD*100:.0f}%):")
    has_hist = False
    for bot in BOT_NAMES:
        stats = IA90_stats.get(bot)
        if stats and stats.get("n", 0) > 0:
            has_hist = True
            okh = int(stats.get("ok", 0) or 0)
            nh = int(stats.get("n", 0) or 0)
            pct_raw_h = float((okh / nh) * 100.0) if nh > 0 else 0.0
            print(Fore.YELLOW + f"   {bot}: {okh}/{nh} ({pct_raw_h:.1f}%)")
    if not has_hist:
        print(Fore.YELLOW + f"   (Aún no hay operaciones cerradas con señal IA ≥{IA_METRIC_THRESHOLD*100:.0f}%.)")

    # ACTUAL: quién está >= umbral vigente para compuerta REAL en este tick.
    umbral_actual_hud = float(_umbral_senal_actual_hud())
    print(Fore.YELLOW + f"\nIA SEÑALES OBSERVACIÓN (≥{umbral_actual_hud*100:.0f}% ahora):")
    now = []
    for bot in BOT_NAMES:
        st = estado_bots.get(bot, {}) if isinstance(estado_bots, dict) else {}

        # Anti-confusión: si este bot tiene token REAL, no lo consideramos “señal actual”
        token_ui = str(st.get("token") or "DEMO").strip().upper()
        if bool(st.get("trigger_real", False)) or token_ui.startswith("REAL"):
            continue

        modo = (st.get("modo_ia") or "off").lower()
        p = st.get("prob_ia", None)
        if modo != "off" and isinstance(p, (int, float)) and p >= float(umbral_actual_hud):
            now.append((bot, float(p)))

    if bool(REAL_CLASSIC_GATE):
        try:
            roof_h = float(DYN_ROOF_STATE.get("roof", DYN_ROOF_FLOOR) or DYN_ROOF_FLOOR)
            cbot_h = DYN_ROOF_STATE.get("confirm_bot")
            cst_h = int(DYN_ROOF_STATE.get("confirm_streak", 0) or 0)
            mode_h = str(DYN_ROOF_STATE.get("last_gate_mode", "A") or "A")
            floor_eff_h = float(DYN_ROOF_STATE.get("last_floor_eff", _umbral_real_operativo_actual()) or _umbral_real_operativo_actual())
            confirm_need_h = int(DYN_ROOF_STATE.get("last_confirm_need", DYN_ROOF_CONFIRM_TICKS) or DYN_ROOF_CONFIRM_TICKS)
            trigger_ok_h = bool(DYN_ROOF_STATE.get("last_trigger_ok", False))
            crowd_h = int(DYN_ROOF_STATE.get("crowd_count", 0) or 0)
            n_min_real, n_req_real = _n_minimo_real_status()
            bloqueado_txt = "bloqueado" if n_min_real < n_req_real else "ok"
            cst_disp_h = min(cst_h, confirm_need_h)
            cst_extra_h = max(0, cst_h - confirm_need_h)
            cst_txt_h = f"{cst_disp_h}/{confirm_need_h}" + (f" (+{cst_extra_h} acum)" if cst_extra_h > 0 else "")
            n_disp_h = min(int(n_min_real), int(n_req_real))
            n_extra_h = max(0, int(n_min_real) - int(n_req_real))
            n_txt_h = f"{n_disp_h}/{n_req_real}" + (f" (+{n_extra_h} acum)" if n_extra_h > 0 else "")
            print(
                Fore.YELLOW
                + f" Compuerta REAL (operativa): mode={mode_h} | roof={roof_h*100:.1f}% | floor={floor_eff_h*100:.1f}% | "
                  f"confirm={cst_txt_h}" + (f" ({cbot_h})" if cbot_h else "")
                  + f" | trigger_ok={'sí' if trigger_ok_h else 'no'} | crowd={crowd_h}"
                  + f" | n_min_real={n_txt_h} ({bloqueado_txt})"
            )
        except Exception:
            pass

    if not now:
        print(Fore.YELLOW + f"(Ningún bot ≥{umbral_actual_hud*100:.0f}% en este tick.)")
    else:
        for b, p in sorted(now, key=lambda x: x[1], reverse=True):
            print(Fore.YELLOW + f"  {b}: {p*100:.1f}%")

    try:
        hot_rows = []
        for b in BOT_NAMES:
            st = estado_bots.get(b, {})
            hot = list(st.get("ia_sensor_hot_feats", []) or [])[:3]
            if hot:
                hot_rows.append(f"{b}:{','.join(hot)}")
        if hot_rows:
            hot_msg = " SENSOR_PLANO hot-features: " + " | ".join(hot_rows)
            try:
                term_cols_clip = os.get_terminal_size().columns
            except Exception:
                term_cols_clip = 140
            # Mantener esta línea lejos del HUD/panel derecho (evita solapado visual).
            # Tope fijo corto para consolas angostas o con zoom/fuentes variables.
            max_hot_len = 72
            if len(hot_msg) > max_hot_len:
                hot_msg = hot_msg[:max(0, max_hot_len - 3)] + "..."
            print(Fore.YELLOW + hot_msg)
    except Exception:
        pass

        # Calibración detallada movida a reporte externo (menos ruido en HUD principal)
    print(Fore.MAGENTA + "\nℹ️ Calibración IA detallada desactivada en HUD (usar: python reporte_real_vs_ficticio_ia.py --session debug).")

    panel_lines = [
        "┌────────────────────────────────────────────┐",
        "│ 🎮 PANEL DE CONTROL TECLADO               │",
        "├────────────────────────────────────────────┤",
        "│ [S] Salir  [P] Pausar  [C] Continuar      │",
        "│ [R] Reiniciar ciclo  [T] Ver token        │",
        "│ [L] Limpiar visual  [D] Limpieza dura     │",
        "│ [G] Probar audio  [E] Entrenar IA ya      │",
        "├────────────────────────────────────────────┤",
        "│ 🤖 ¿CÓMO INVIERTES?                        │",
        "│ [5–0] Elige bot (p.ej. 7 = fulll47)       │",
        "│ [1–6] Elige ciclo [p.ej. 3 = Marti #3)    │",
    ]

    token_file = leer_token_actual()
    token_hud  = "DEMO" if (token_file in (None, "none")) else f"REAL:{token_file}"
    activo_real = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else next((b for b in BOT_NAMES if estado_bots[b]["token"] == "REAL"), None)
    fuente = estado_bots.get(activo_real, {}).get("fuente") or "AUTO" if activo_real else "--"
    panel_lines.append(f"│ Fuente={fuente} → Token={token_hud:<12}          │")

    panel_lines.append("└────────────────────────────────────────────┘")

    if PENDIENTE_FORZAR_BOT:
        rest = 0
        if PENDIENTE_FORZAR_EXPIRA:
            rest = max(0, int(PENDIENTE_FORZAR_EXPIRA - time.time()))
        panel_lines += [
            "┌────────────────────────────────────────────┐",
            f"│ Bot seleccionado: {PENDIENTE_FORZAR_BOT:<22}│",
            f"│ Tiempo para decidir: {rest:>3}s               │",
            f"│ Elige ciclo [1..{MAX_CICLOS}] o ESC          │",
            "└────────────────────────────────────────────┘",
        ]


    if HUD_VISIBLE:
        dibujar_hud_gatewin(len(panel_lines), HUD_LAYOUT)
    def _strip_ansi(s: str) -> str:
        return re.sub(r'\x1b\[[0-9;]*m', '', s)
    panel_width = max(len(_strip_ansi(l)) for l in panel_lines)
    panel_height = len(panel_lines)
    try:
        term_cols, term_rows = os.get_terminal_size()
    except:
        term_cols, term_rows = 140, 50
    start_col = max(1, term_cols - panel_width - 1)
    start_row = max(1, term_rows - panel_height - 1)
    for i, line in enumerate(panel_lines):
        print(f"\x1b[{start_row + i};{start_col}H" + Fore.MAGENTA + line + Fore.RESET)
    print(f"\x1b[{term_rows};1H", end="")

# Mostrar advertencia meta
def mostrar_advertencia_meta():
    global salir, pausado, MODAL_ACTIVO, META_ACEPTADA, meta_mostrada, SALDO_INICIAL, META

    pausado = True
    MODAL_ACTIVO = True

    try:
        terminal_width = max(os.get_terminal_size().columns, 100)
        terminal_height = max(os.get_terminal_size().lines, 32)
    except Exception:
        terminal_width, terminal_height = 100, 32

    # Área del modal para refresco incremental (sin limpiar toda la consola en cada tick)
    box_w = min(max(terminal_width - 6, 80), 140)
    box_h = min(max(terminal_height - 6, 22), 30)
    left = max(1, (terminal_width - box_w) // 2)
    top = max(2, (terminal_height - box_h) // 2)

    # Sonido meta en loop hasta [S] o [C]
    if AUDIO_AVAILABLE:
        if pygame.mixer.get_init() and "meta_15" in SOUND_CACHE:
            try:
                SOUND_CACHE["meta_15"].play(loops=-1)
            except Exception:
                pass
        elif winsound:
            try:
                base_dir = os.path.dirname(__file__)
                sound_path = os.path.join(base_dir, "meta15%.wav")
                winsound.PlaySound(sound_path, winsound.SND_LOOP | winsound.SND_ASYNC)
            except Exception:
                pass

    # Confetti + shake suave
    palette = [Fore.YELLOW, Fore.CYAN, Fore.MAGENTA, Fore.GREEN, Fore.RED, Fore.WHITE]
    glyphs = ['|', '!', ':', '*', '+']
    particles = []
    max_particles = max(30, box_w // 2)

    def _stop_meta_sound():
        if AUDIO_AVAILABLE:
            if pygame.mixer.get_init() and "meta_15" in SOUND_CACHE:
                try:
                    SOUND_CACHE["meta_15"].stop()
                except Exception:
                    pass
            elif winsound:
                try:
                    winsound.PlaySound(None, winsound.SND_PURGE)
                except Exception:
                    pass

    def _center_in_box(msg: str) -> str:
        pad = max(0, box_w - 2 - len(msg))
        left_pad = pad // 2
        right_pad = pad - left_pad
        return " " * left_pad + msg + " " * right_pad

    def _draw_frame(tick: int):
        # borde
        print(f"[{top};{left}H" + Fore.YELLOW + "█" * box_w + Fore.RESET, end='')
        for r in range(1, box_h - 1):
            print(f"[{top+r};{left}H" + Fore.YELLOW + "█" + Fore.RESET, end='')
            print(f"[{top+r};{left+box_w-1}H" + Fore.YELLOW + "█" + Fore.RESET, end='')
        print(f"[{top+box_h-1};{left}H" + Fore.YELLOW + "█" * box_w + Fore.RESET, end='')

        # limpiar interior
        blank = " " * (box_w - 2)
        for r in range(1, box_h - 1):
            print(f"[{top+r};{left+1}H{blank}", end='')

        shake = -1 if (tick % 4 in (0, 1)) else 1
        title = "🎉 ¡¡¡FELICIDADES!!! 🎉"
        y = top + 2
        x = left + 1 + max(0, (box_w - 2 - len(title)) // 2 + shake)
        print(f"[{y};{x}H" + Fore.CYAN + title + Fore.RESET, end='')

        lines = [
            "✅ Has alcanzado tu meta diaria del +20% de ganancia.",
            "",
            "💡 Recomendación:",
            "EvaBot busca una ganancia diaria aproximada del 20% de tu capital.",
            "Puedes seguir invirtiendo bajo tu responsabilidad o esperar al siguiente día.",
            "",
            "⚠️ Importante:",
            "Ningún sistema es infalible y siempre existe riesgo de pérdida.",
            "Lee el Manual de Usuario para horarios recomendados y detalles clave.",
            "",
            "Presiona [S] para SALIR y asegurar beneficios, o [C] para continuar invirtiendo.",
        ]
        row = top + 4
        for msg in lines:
            if row >= top + box_h - 2:
                break
            print(f"[{row};{left+1}H" + _center_in_box(msg), end='')
            row += 1

        # confetti cayendo
        if len(particles) < max_particles and random.random() < 0.55:
            particles.append({
                "x": left + 2 + random.randint(0, max(1, box_w - 6)),
                "y": top + 1,
                "v": random.choice((1, 1, 2)),
                "ch": random.choice(glyphs),
                "color": random.choice(palette),
            })

        alive = []
        for part in particles:
            part["y"] += part["v"]
            if part["y"] < top + box_h - 1:
                alive.append(part)
                if left + 1 <= part["x"] <= left + box_w - 2 and top + 1 <= part["y"] <= top + box_h - 2:
                    print(f"[{int(part['y'])};{int(part['x'])}H" + part["color"] + part["ch"] + Fore.RESET, end='')
        particles[:] = alive

        print(f"[{terminal_height};1H", end='', flush=True)

    limpiar_consola()
    tick = 0
    while True:
        tick += 1
        _draw_frame(tick)

        if HAVE_MSVCRT and msvcrt.kbhit():
            try:
                t = msvcrt.getch()
                if t in (b'\x00', b'\xe0'):
                    msvcrt.getch()
                    continue
                tecla = t.decode("utf-8", errors="ignore").lower()
            except Exception:
                tecla = ""

            if tecla in ("s",):
                print("\n🛑 Cerrando EvaBot...")
                _stop_meta_sound()
                salir = True
                MODAL_ACTIVO = False
                break

            if tecla in ("c", "\r"):
                print("\n✔️ Continuando bajo responsabilidad del usuario...")
                _stop_meta_sound()
                try:
                    if MAIN_LOOP:
                        fut = asyncio.run_coroutine_threadsafe(refresh_saldo_real(forzado=True), MAIN_LOOP)
                        fut.result(timeout=15)
                    valor = obtener_valor_saldo()
                    if valor is not None:
                        SALDO_INICIAL = round(valor, 2)
                        META = round(SALDO_INICIAL * 1.20, 2)
                        inicializar_saldo_real(SALDO_INICIAL)
                except Exception as e:
                    print(f"⚠️ Error reiniciando meta: {e}")
                pausado = False
                META_ACEPTADA = True
                meta_mostrada = False
                MODAL_ACTIVO = False
                break

        time.sleep(0.08)

# Dibujar HUD
def dibujar_hud_gatewin(panel_height=8, layout=None):
    if not sys.stdout.isatty():
        return
    HUD_INNER_WIDTH = 50
    HUD_WIDTH = HUD_INNER_WIDTH + 2
    activo_real = next((b for b in BOT_NAMES if estado_bots[b]["token"] == "REAL"), None)
    try:
        term_cols, term_rows = os.get_terminal_size()
    except:
        term_cols, term_rows = 140, 50
    hud_lines = [
        "┌" + "─" * HUD_INNER_WIDTH + "┐",
        "│ ⏱️  HUD: Oráculo evaluando bots..." + " " * (HUD_INNER_WIDTH - 32) + " │",
        "├" + "─" * HUD_INNER_WIDTH + "┤",
    ]
    emoji, estado, detalle = evaluar_semaforo()
    hud_lines += [
        f"│ Estado: {emoji} {estado:<{HUD_INNER_WIDTH-10}}│",
        f"│ {detalle:<{HUD_INNER_WIDTH}}│",
        "├" + "─" * HUD_INNER_WIDTH + "┤",
        f"│ {'🤖 ¿CÓMO INVIERTES?':<{HUD_INNER_WIDTH}}│",
        f"│ {'[5–0] Elige bot (p.ej. 7 = fulll47)':<{HUD_INNER_WIDTH}}│",
        f"│ {[f'[1–{MAX_CICLOS}] Elige ciclo (p.ej. 3 = Marti #3)'][0]:<{HUD_INNER_WIDTH}}│",
    ]
    activo_real = next((b for b in BOT_NAMES if estado_bots[b]["token"] == "REAL"), None)
    if activo_real:
        cyc = estado_bots[activo_real].get("ciclo_actual", 1)
        hud_lines.insert(-1, f"│ Bot REAL: {activo_real} · Ciclo {cyc}/{MAX_CICLOS}".ljust(HUD_INNER_WIDTH) + " │")
    prox_ciclo = ciclo_martingala_siguiente()
    prox_txt = f"C{prox_ciclo}"
    if int(prox_ciclo) == 1:
        prox_txt = "C1 (reinicio)"
    hud_lines.insert(-1, f"│ Martingala: {marti_ciclos_perdidos}/{MAX_CICLOS} pérdidas seguidas · Próx {prox_txt}".ljust(HUD_INNER_WIDTH) + " │")
    hud_lines.insert(-1, f"│ {marti_audit_resumen_linea():<{HUD_INNER_WIDTH}}│")
    # HUD muestra ciclo actual/siguiente de martingala; sin bloqueo duro de anti-repetición.
    hud_lines.append("└" + "─" * HUD_INNER_WIDTH + "┘")
    layout = (layout or HUD_LAYOUT).lower()
    hud_height = len(hud_lines)
    start_col = max(1, (term_cols - HUD_WIDTH) // 2)
    start_row = max(2, term_rows - hud_height - 1)
    for i, line in enumerate(hud_lines):
        print(f"\x1b[{start_row + i};{start_col}H" + Fore.YELLOW + line + Fore.RESET)

def _hud_trim_line(txt: str, max_chars: int | None = None) -> str:
    try:
        m = int(max_chars or HUD_EVENT_MAX_CHARS)
        s = str(txt)
        return s if len(s) <= m else (s[: max(0, m - 1)] + "…")
    except Exception:
        return str(txt)


def mostrar_eventos():
    if eventos_recentes:
        print(Fore.MAGENTA + "\nEventos recientes:")
        for ev in list(eventos_recentes)[-int(HUD_EVENTS_MAX):]:
            print(Fore.MAGENTA + " - " + _hud_trim_line(ev, HUD_EVENT_MAX_CHARS))
# === FIN BLOQUE 11 ===

# === BLOQUE 12 — CONTROL MANUAL REAL Y CONDICIONES SEGURAS ===
MAIN_LOOP = None

def set_main_loop(loop):
    global MAIN_LOOP
    MAIN_LOOP = loop

# ==================== VENTANA DE DECISIÓN IA ====================
# Debe empatar con el BOT (VENTANA_DECISION_IA_S) para que el humano alcance a elegir ciclo.
VENTANA_DECISION_IA_S = 30

PENDIENTE_FORZAR_BOT = None
PENDIENTE_FORZAR_INICIO = 0.0
PENDIENTE_FORZAR_EXPIRA = 0.0

FORZAR_LOCK = threading.Lock()

def condiciones_seguras_para(bot: str) -> bool:
    # Fuente operativa única: prob_ia_oper + estado final del embudo
    thr = float(get_umbral_operativo())
    prob = float(_prob_ia_operativa_bot(bot, default=0.0) or 0.0)
    n = int(estado_bots.get(bot, {}).get("tamano_muestra", 0) or 0)
    emb = EMBUDO_DECISION_STATE if isinstance(EMBUDO_DECISION_STATE, dict) else {}
    dec = str(emb.get("decision_final", EMBUDO_FINAL_WAIT_SOFT))
    top1 = str(emb.get("top1_bot") or "")
    if top1 and bot != top1:
        return False
    return (n >= ORACULO_N_MIN) and (prob >= thr) and (dec in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO))

# forzar_real_manual
def forzar_real_manual(bot: str, ciclo: int):
    if not FORZAR_LOCK.acquire(blocking=False):
        agregar_evento("🔒 Forzar REAL: ya en progreso; espera.")
        return
    try:
        ciclo = max(1, min(int(ciclo), MAX_CICLOS))

        # Añadido: Confirmación en rojo si no es seguro (para evitar cierres forzados por malas decisiones)
        CONFIRMAR_EN_ROJO = True  # Activado por defecto para seguridad
        if CONFIRMAR_EN_ROJO and HAVE_MSVCRT and not condiciones_seguras_para(bot):
            global MODAL_ACTIVO
            MODAL_ACTIVO = True
            try:
                with RENDER_LOCK:
                    print(Fore.YELLOW + f"⚠️ Semáforo no verde para {bot}. ¿Forzar de todos modos? [Y/N]")
                while True:
                    if msvcrt.kbhit():
                        k = msvcrt.getch().decode("utf-8", errors="ignore").lower()
                        if k == "y":
                            break
                        elif k == "n":
                            agregar_evento("❎ Forzar REAL cancelado (no confirmado).")
                            return
                    time.sleep(0.05)
            finally:
                MODAL_ACTIVO = False

        # Nueva lógica: Marcar como señal IA si prob >= thr_ia
        prob = float(_prob_ia_operativa_bot(bot, default=0.0) or 0.0)
        thr_ia = float(get_umbral_operativo())

        if prob >= thr_ia and not estado_bots[bot]["ia_senal_pendiente"]:
            estado_bots[bot]["ia_senal_pendiente"] = True
            estado_bots[bot]["ia_prob_senal"] = prob

            # ✅ FIX REAL: registrar APERTURA de señal con epoch PRE real (para contabilidad correcta)
            # Esto sí “lo consume” el cierre automático posterior (log_ia_close vía ia_audit_scan_close).
            try:
                epoch_sig = None
                try:
                    epoch_sig = ia_audit_get_last_pre_epoch(bot)
                except Exception:
                    epoch_sig = None

                if epoch_sig is not None:
                    log_ia_open(
                        bot,
                        int(epoch_sig),
                        float(prob),
                        float(thr_ia),
                        "MANUAL"
                    )
            except Exception:
                pass


        if not emitir_real_autorizado(bot, ciclo, source="MANUAL"):
            agregar_evento(f"🔒 Forzar REAL bloqueado para {bot.upper()}: ya hay otro bot en REAL.")
            return

        estado_bots[bot]["reintentar_ciclo"] = True
        estado_bots[bot]["ciclo_actual"] = ciclo
        global marti_paso
        marti_paso = ciclo - 1
        estado_bots[bot]["fuente"] = "MANUAL"

        requerido = float(MARTI_ESCALADO[ciclo - 1])
        val = obtener_valor_saldo()
        if val is None or val < requerido:
            agregar_evento(f"⚠️ Saldo < requerido para ciclo #{ciclo} en {bot} (pide {requerido}). Intentando igual.")

        # escribir_orden_real(...) ya dejó token+HUD sincronizados; evitamos doble token_sync.
        agregar_evento(f"⚡ Forzar REAL: {bot} → ciclo #{ciclo} (fuente=MANUAL)")
        with RENDER_LOCK:
            mostrar_panel()
    except Exception as e:
        agregar_evento(f"⛔ Forzar REAL falló en {bot}: {e}")
    finally:
        FORZAR_LOCK.release()

def evaluar_semaforo():
    thr = float(get_umbral_operativo())
    emb = EMBUDO_DECISION_STATE if isinstance(EMBUDO_DECISION_STATE, dict) else {}
    dec = str(emb.get("decision_final", EMBUDO_FINAL_WAIT_SOFT))
    reason = str(emb.get("decision_reason", "--"))
    top1 = str(emb.get("top1_bot") or "")
    prob = float(emb.get("top1_prob", 0.0) or 0.0)
    n = int(estado_bots.get(top1, {}).get("tamano_muestra", 0) or 0) if top1 else 0

    owner = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else leer_token_actual()
    try:
        saldo_val = float(obtener_valor_saldo() or 0.0)
    except Exception:
        saldo_val = 0.0
    costo = float(sum(MARTI_ESCALADO[:max(1, int(MAX_CICLOS))]))
    costo_c1 = float(MARTI_ESCALADO[0]) if MARTI_ESCALADO else 0.0

    if owner and owner not in (None, "none"):
        return "🟡", "AVISO", f"Token en uso por {owner}."
    if saldo_val < costo_c1:
        falta = costo_c1 - saldo_val
        return "🟡", "AVISO", f"Saldo < C1 ({costo_c1:.2f}). Faltan {falta:.2f} USD."
    if saldo_val < costo:
        return "🟡", "AVISO", f"Saldo parcial: cubre C1 pero no C1..C{int(MAX_CICLOS)} ({costo:.2f})."

    if dec == EMBUDO_FINAL_BLOCK_HARD:
        return "🔴", "BLOQUEO", f"{emb.get('hard_block_reason') or reason}"
    if dec == EMBUDO_FINAL_WAIT_SOFT:
        return "🟡", "EN ESPERA", f"{emb.get('soft_wait_reason') or reason}"
    if dec == EMBUDO_FINAL_SHADOW_OK:
        return "🔵", "SHADOW", f"{reason} (no ejecuta REAL)"
    if dec in (EMBUDO_FINAL_REAL_MICRO, EMBUDO_FINAL_REAL_NORMAL):
        if (not top1) or (prob < thr):
            return "🟡", "EN ESPERA", f"Top1 no operativo ({top1 or '--'} p={prob:.0%}<{int(thr*100)}%)."
        modo = "MICRO" if dec == EMBUDO_FINAL_REAL_MICRO else "NORMAL"
        return "🟢", "SEÑAL LISTA", f"{top1} • ProbOper={prob:.0%} • n={n} • modo={modo}"

    return "🟡", "EN ESPERA", f"Sin decisión embudo ({reason})."

# NUEVAS FUNCIONES PARA RESET
RESET_ON_START = False  # Cambiado a False para mantener historial entre sesiones
AUTO_REPAIR_ON_START = True  # Repara estructura de CSVs al iniciar sin borrar historial completo

def _csv_header_bot():
    return [
        "fecha","ts","epoch","activo","direction","monto","resultado","ganancia_perdida","trade_status",
        "rsi_9","rsi_14","sma_5","sma_20","sma_spread","cruce_sma","breakout",
        "rsi_reversion","racha_actual","payout","puntaje_estrategia",
        "volatilidad","es_rebote","hora_bucket","result_bin",
        "payout_decimal_rounded","payout_multiplier","payout_total","close","high","low"
    ]

def resetear_csv_bot(nombre_bot: str):
    ruta = f"registro_enriquecido_{nombre_bot}.csv"
    try:
        with open(ruta, "w", newline="", encoding="utf-8") as f:
            csv.writer(f).writerow(_csv_header_bot())
    except Exception as e:
        print(f"⚠️ No pude resetear {ruta}: {e}")

def resetear_incremental_y_modelos(borrar_modelos: bool = True):
    try:
        if os.path.exists("dataset_incremental.csv"):
            os.remove("dataset_incremental.csv")
    except Exception as e:
        print(f"⚠️ No pude borrar dataset_incremental.csv: {e}")

    if borrar_modelos:
        for f in ("modelo_xgb.pkl","scaler.pkl","feature_names.pkl","model_meta.json","modelo_xgb_v2.pkl","scaler_v2.pkl","feature_names_v2.pkl","model_meta_v2.json"):
            try:
                if os.path.exists(f):
                    os.remove(f)
            except Exception as e:
                print(f"⚠️ No pude borrar {f}: {e}")

def resetear_estado_hud(estado_bots: dict):
    for bot in list(estado_bots.keys()):
        estado_bots[bot].update({
            "resultados": [], "ganancias": 0, "perdidas": 0,
            "porcentaje_exito": None, "tamano_muestra": 0,
            "prob_ia": None, "prob_ia_oper": None, "token": "DEMO",
            "fuente": None, "modo_ia": "low_data",
            "ia_seniales": 0, "ia_aciertos": 0, "ia_fallos": 0, "ia_senal_pendiente": False,
            "ia_prob_senal": None
        })

def limpieza_dura():
    for nb in BOT_NAMES:
        resetear_csv_bot(nb)
    resetear_incremental_y_modelos(borrar_modelos=True)
    resetear_estado_hud(estado_bots)
    print("🧨 Limpieza dura ejecutada. Ok.")

def _asegurar_estructura_datos_inicio() -> list[str]:
    """
    Verifica y corrige desalineaciones comunes al arranque sin borrar histórico completo.

    Objetivo:
    - Evitar que una estructura vieja/mixta deje al bot en estado incoherente al iniciar.
    - Reparar incremental mutante usando el flujo existente.
    - Reencuadrar CSVs enriquecidos de bots al header canónico cuando detecta desvíos.
    """
    msgs = []

    # 1) Incremental: usa el reparador robusto ya existente (no-op si está sano).
    try:
        if reparar_dataset_incremental_mutante(ruta="dataset_incremental.csv", cols=_canonical_incremental_cols()):
            msgs.append("🧹 Inicio seguro: dataset_incremental reparado automáticamente.")
    except Exception as e:
        msgs.append(f"⚠️ Inicio seguro: no se pudo validar/reparar dataset_incremental ({e}).")

    # 2) CSVs enriquecidos por bot:
    #    - Si falta, se crea con header canónico (evita arranques en LOW_DATA por ausencia de archivo base).
    #    - Si existe y está roto, se respalda y se reescribe solo el header.
    header_ref = _csv_header_bot()
    required = {"resultado", "trade_status", "epoch", "monto"}
    for bot in BOT_NAMES:
        ruta = f"registro_enriquecido_{bot}.csv"
        if not os.path.exists(ruta):
            try:
                with open(ruta, "w", newline="", encoding="utf-8") as f:
                    csv.writer(f).writerow(header_ref)
                msgs.append(f"🧱 Inicio seguro: creado {ruta} con header canónico.")
            except Exception as e:
                msgs.append(f"⚠️ Inicio seguro: no se pudo crear {ruta} ({e}).")
            continue
        try:
            header = None
            for enc in ("utf-8", "latin-1", "windows-1252"):
                try:
                    with open(ruta, "r", encoding=enc, errors="replace") as f:
                        first = f.readline().strip()
                    header = [c.strip() for c in first.split(",")] if first else []
                    break
                except Exception:
                    continue

            header_set = set(header or [])
            malformed = (not header) or (not required.issubset(header_set))

            # También tratar como incompatible si trae una sola columna "mutante" gigante.
            if (not malformed) and len(header) <= 2:
                malformed = True

            if malformed:
                bak = f"{ruta}.bak_startfix_{int(time.time())}"
                try:
                    shutil.copy2(ruta, bak)
                except Exception:
                    bak = None
                with open(ruta, "w", newline="", encoding="utf-8") as f:
                    csv.writer(f).writerow(header_ref)
                if bak:
                    msgs.append(f"🧹 Inicio seguro: {bot} tenía estructura inválida; reiniciado header (backup: {os.path.basename(bak)}).")
                else:
                    msgs.append(f"🧹 Inicio seguro: {bot} tenía estructura inválida; reiniciado header.")
        except Exception as e:
            msgs.append(f"⚠️ Inicio seguro: no se pudo validar {bot} ({e}).")

    return msgs

# Backfill seguro
def backfill_incremental(ultimas=500):
    try:
        try:
            feature_names = joblib.load(globals().get("_FEATURES_PATH", "feature_names_v2.pkl"))
            feature_names = [c for c in feature_names if c != "result_bin"]
        except Exception:
            feature_names = list(INCREMENTAL_FEATURES_V2)
        inc = "dataset_incremental.csv"
        cols = _canonical_incremental_cols(feature_names)

        # 0) Reparar incremental si quedó "mutante" (header corrupto / columnas extra / mezcla de campos)
        with file_lock_required(INCREMENTAL_LOCK_FILE, timeout=6.0, stale_after=30.0) as got:
            if not got:
                agregar_evento("⚠️ Backfill: incremental.lock ocupado; se omite ejecución en este tick.")
                return
            if reparar_dataset_incremental_mutante(inc, cols):
                agregar_evento("🧹 Incremental: esquema reparado (header/filas inconsistentes).")
            if not os.path.exists(inc) or os.stat(inc).st_size == 0:
                with open(inc, "w", newline="", encoding="utf-8") as f:
                    csv.DictWriter(f, fieldnames=cols).writeheader()

        firmas_existentes = set()
        if os.path.exists(inc):
            df_inc = pd.read_csv(inc, encoding="utf-8", on_bad_lines="skip")
            if not df_inc.empty:
                sigs = df_inc[feature_names].round(6).astype(str).agg("|".join, axis=1) + "|" + df_inc["result_bin"].astype(int).astype(str)
                firmas_existentes = set(sigs.tolist())


        for bot in BOT_NAMES:
            ruta = f"registro_enriquecido_{bot}.csv"
            if not os.path.exists(ruta):
                continue
            df = None
            for enc in ("utf-8","latin-1","windows-1252"):
                try:
                    df = pd.read_csv(ruta, encoding=enc, on_bad_lines="skip")
                    break
                except Exception as e:
                    print(f"⚠️ Error en backfill para {bot}: {e}")
                    continue
            if df is None or df.empty:
                continue

            req = [
                "rsi_9","rsi_14","sma_5","sma_20","cruce_sma","breakout",
                "rsi_reversion","racha_actual","puntaje_estrategia"
            ]
            if not set(req).issubset(df.columns) or "resultado" not in df.columns:
                continue

            for c in req + ["payout","payout_decimal_rounded"]:
                if c in df.columns:
                    df[c] = pd.to_numeric(df[c], errors="coerce")

            df["resultado_norm"] = df["resultado"].apply(normalizar_resultado)

            sub = df[df["resultado_norm"].isin(["GANANCIA","PÉRDIDA"])]
            sub = sub[sub[req].notna().all(axis=1)].tail(ultimas)
            if sub.empty:
                continue

            nuevas_filas = []
            descartadas = 0
            
            nuevas_filas = []
            for _, r in sub.iterrows():
                # base mínima
                fila = {k: float(r[k]) for k in req}
                sp = _calcular_sma_spread_robusto({
                    "sma_5": r.get("sma_5", 0.0),
                    "sma_20": r.get("sma_20", 0.0),
                    "close": r.get("close", r.get("cierre", None)),
                })
                if sp is None or not np.isfinite(float(sp)):
                    descartadas += 1
                    continue
                fila["sma_spread"] = float(sp)

                # Diccionario completo para helpers enriquecidos
                row_dict_full = r.to_dict()
                for i in range(20):
                    ck = f"close_{i}"
                    try:
                        cv = row_dict_full.get(ck, None)
                        if cv is None or (isinstance(cv, str) and cv.strip() == ""):
                            continue
                        cf = float(cv)
                        if math.isfinite(cf) and cf > 0.0:
                            fila[ck] = float(cf)
                    except Exception:
                        continue

                                # ==========================
                # payout normalizado (ROI 0–1.5 aprox)
                # ==========================
                pay = calcular_payout_feature(row_dict_full)
                # Si falta payout, NO lo inventamos como 0.0: descartamos la fila
                # (backfill es entrenamiento, aquí ser conservador = IA más estable)
                if pay is None or pay < 0.05:
                    descartadas += 1
                    continue

                # ✅ FIX: estas asignaciones DEBEN ocurrir antes del continue
                fila["payout"] = float(pay)
                row_dict_full["payout"] = float(pay)

                # Enriquecer señales evento antes de extraer features finales
                row_dict_full = enriquecer_features_evento(row_dict_full)

                # ==========================
                # puntaje_estrategia normalizado 0–1
                # ==========================
                pe = calcular_puntaje_estrategia_normalizado(row_dict_full)
                if pe is None and "puntaje_estrategia" in r:
                    pe = _norm_01(r.get("puntaje_estrategia"))
                if pe is not None:
                    fila["puntaje_estrategia"] = pe

                # ==========================
                # volatilidad: normalizada a [0,1]
                # - si viene en el CSV y es válida, la usamos
                # - si falta / NaN, la calculamos con calcular_volatilidad_simple (proxy SMA5 vs SMA20)
                # ==========================
                vol_raw = row_dict_full.get("volatilidad", None)
                try:
                    vol = float(vol_raw) if vol_raw not in (None, "") else np.nan
                except Exception:
                    vol = np.nan
                if pd.isna(vol):
                    vol = calcular_volatilidad_simple(row_dict_full)
                try:
                    vol_f = float(vol)
                except Exception:
                    vol_f = float("nan")
                if (not math.isfinite(vol_f)) or vol_f <= 0.0:
                    vol_hist = calcular_volatilidad_por_bot(bot, lookback=50)
                    if vol_hist is not None:
                        vol_f = float(vol_hist)
                if (not math.isfinite(vol_f)):
                    vol_f = 0.0

                fila["volatilidad"] = max(0.0, min(float(vol_f), 1.0))

                # ==========================
                # nuevas features: rebote y hora (0–1)
                # ==========================
                fila["es_rebote"]   = float(max(0.0, min(1.0, _safe_float_local(row_dict_full.get("es_rebote")) or calcular_es_rebote(row_dict_full))))
                hb, hm = calcular_hora_features(row_dict_full)
                if float(hm) >= 1.0:
                    hb = 0.0
                fila["hora_bucket"] = float(max(0.0, min(1.0, float(hb))))

                # ==========================
                # label final (GANANCIA / PÉRDIDA)
                # ==========================
                label = 1 if r["resultado_norm"] == "GANANCIA" else 0
                fila_dict = fila.copy()
                fila_dict["result_bin"] = label
                fila_dict = _enriquecer_scalping_features_row(fila_dict)

                # Validación defensiva
                valid, reason = validar_fila_incremental(fila_dict, feature_names)
                if not valid:
                    agregar_evento(f"⚠️ Incremental: fila descartada en backfill ({reason})")
                    descartadas += 1
                    continue

                # Clipping defensivo
                fila_dict = clip_feature_values(fila_dict, feature_names)
                try:
                    fila_dict["row_has_proxy_features"] = int(float(fila_dict.get("row_has_proxy_features", 0) or 0))
                except Exception:
                    fila_dict["row_has_proxy_features"] = 0
                try:
                    fila_dict["row_train_eligible"] = int(float(fila_dict.get("row_train_eligible", 1) or 1))
                except Exception:
                    fila_dict["row_train_eligible"] = 1
                if int(fila_dict.get("row_has_proxy_features", 0)) == 1:
                    if (not _core_scalping_ready_from_row(fila_dict)) and _close_snapshot_issue_from_row(fila_dict):
                        fila_dict["row_train_eligible"] = 0

                # Evitar duplicados vía firma
                sig = _make_sig(fila_dict)
                if sig in firmas_existentes:
                    continue
                firmas_existentes.add(sig)

                nuevas_filas.append(fila_dict)

            if nuevas_filas:
                with file_lock_required(INCREMENTAL_LOCK_FILE, timeout=6.0, stale_after=30.0) as got:
                    if not got:
                        agregar_evento("⚠️ Backfill: lock ocupado al anexar incremental; bloque omitido.")
                        continue
                    with open(inc, "a", newline="", encoding="utf-8") as f:
                        w = csv.DictWriter(f, fieldnames=cols)
                        for rd in nuevas_filas:
                            w.writerow(rd)
                        f.flush(); os.fsync(f.fileno())
        agregar_evento("✅ IA: backfill incremental completado.")
    except Exception as e:
        agregar_evento(f"⚠️ IA: fallo en backfill: {e}")
# === FIN BLOQUE 12 ===

# === BLOQUE 13 — LOOP PRINCIPAL, WEBSOCKET Y TECLADO ===
# Orden operativo por etapas (solo trazabilidad/depuración; no altera trading)
ETAPAS_PROGRAMA = {
    "BOOT_01": "Arranque y validación de entorno",
    "BOOT_02": "Carga de audio/tokens y reset opcional",
    "BOOT_03": "Backfill + primer entrenamiento IA",
    "BOOT_04": "Sincronización inicial HUD/CSV",
    "TICK_01": "Lectura de token y carga incremental por bot",
    "TICK_02": "Watchdog REAL + detección de cierre",
    "TICK_03": "Selección IA / ventana manual / asignación REAL",
    "TICK_04": "Refresh saldo + render HUD",
    "STOP": "Salida controlada",
}
ETAPA_ACTUAL = "BOOT_01"
ETAPA_DETALLE = ETAPAS_PROGRAMA[ETAPA_ACTUAL]
ETAPA_TS = time.time()

def set_etapa(codigo, detalle_extra=None, anunciar=False):
    """
    Marca etapa actual del programa para facilitar diagnóstico en vivo.
    No modifica ninguna decisión de trading.
    """
    global ETAPA_ACTUAL, ETAPA_DETALLE, ETAPA_TS

    codigo = str(codigo or "").strip().upper()
    if codigo not in ETAPAS_PROGRAMA:
        return

    base = ETAPAS_PROGRAMA[codigo]
    detalle = f"{base} | {detalle_extra}" if detalle_extra else base

    ETAPA_ACTUAL = codigo
    ETAPA_DETALLE = detalle
    ETAPA_TS = time.time()

    if anunciar:
        agregar_evento(f"🧭 ETAPA {codigo}: {detalle}")

# Nueva constante para watchdog de REAL - Bajado para más reactividad
REAL_TIMEOUT_S = 120  # 2 minutos sin actividad para aviso/rearme
REAL_STUCK_FORCE_RELEASE_S = 90  # segundos extra tras aviso para liberar REAL si no hay cierre
REAL_TRIGGER_MIN = AUTO_REAL_THR_MIN  # alineado al piso base de 70% para arranque REAL

# =========================================================
# TECHO DINÁMICO + COMPUERTA REAL (anti-bug de activación baja)
# =========================================================
# Lote de actualización del maestro (ticks de lectura IA)
DYN_ROOF_BATCH_TICKS = 15
# Paciencia dura antes de empezar a bajar el techo (4 lotes = 60 ticks)
DYN_ROOF_HOLD_BATCHES = 2
DYN_ROOF_HOLD_TICKS = DYN_ROOF_BATCH_TICKS * DYN_ROOF_HOLD_BATCHES
# Derretido lento del techo: -0.5pp por lote tras la paciencia
DYN_ROOF_STEP = 0.010
# Piso duro para REAL
DYN_ROOF_FLOOR = AUTO_REAL_THR_MIN
# Ventaja mínima del mejor vs segundo mejor
DYN_ROOF_GAP = 0.02
# Confirmación mínima (ticks consecutivos del MISMO bot)
DYN_ROOF_CONFIRM_TICKS = 1
DYN_ROOF_TRIGGER_FORCE_STREAK = 1
DYN_ROOF_TRIGGER_FORCE_MARGIN = 0.005
# Tolerancia para considerar "tocado" el techo (near-roof)
DYN_ROOF_NEAR_TOL = 0.005
# Penalización por evidencia corta (n < 30): requiere +2pp al techo
DYN_ROOF_LOW_N_MIN = 30
DYN_ROOF_LOW_N_PENALTY = 0.01
PROB_CLONE_STD_MIN = 0.01
PROB_CLONE_GAP_MIN = 0.005
REAL_POST_TRADE_COOLDOWN_S = 45
REAL_POST_TRADE_COOLDOWN_CROWDED_S = 240
DYN_ROOF_CROWD_P_MIN = 0.90
DYN_ROOF_CROWD_MIN_BOTS = 3
DYN_ROOF_CROWD_EXTRA_ROOF = 0.02
DYN_ROOF_CROWD_EXTRA_GAP = 0.02
# Clustering en zona 70-80%: evita seleccionar bots con margen mínimo "fake".
DYN_ROOF_CLUSTER_P_MIN = 0.70
DYN_ROOF_CLUSTER_MIN_BOTS = 3
DYN_ROOF_CLUSTER_EXTRA_GAP = 0.01
# Si el top está empatado/prácticamente empatado, mantener bot en confirmación
# para no reiniciar confirm_streak en cada tick por micro-ruido.
DYN_ROOF_TIE_KEEP_CONFIRM_TOL = 0.003
DYN_ROOF_GATE_REARM_HYST = 0.02
DYN_ROOF_GATE_REARM_TICKS = 2
DYN_ROOF_LOW_BAL_WARN_COOLDOWN_S = 60
DYN_ROOF_STALL_TO_MODE_C_S = 2 * 60 * 60
DYN_ROOF_MODE_C_FLOOR = 0.60
DYN_ROOF_MODE_C_CONFIRM_TICKS = 2
DYN_ROOF_MODE_C_MIN_EVIDENCE_N = 20
DYN_ROOF_MODE_C_MIN_EVIDENCE_LB = 0.60
# Techo vivo del mercado (ticks HUD): evita perseguir picos históricos irreales.
DYN_ROOF_LIVE_PEAK_WINDOW = 120
DYN_ROOF_LIVE_PEAK_MIN_SAMPLES = 20
DYN_ROOF_LIVE_PEAK_MARGIN = 0.05
DYN_ROOF_LIVE_PEAK_MARGIN_UNRELIABLE = 0.07
DYN_ROOF_LIVE_PEAK_ONLY_RELIABLE = True
# Trigger suave en modo unreliable para no perder entradas de alta calidad por 1 tick de latencia.
DYN_ROOF_UNRELIABLE_TRIGGER_SOFT_ENABLE = True
DYN_ROOF_UNRELIABLE_TRIGGER_SOFT_MARGIN = 0.05
DYN_ROOF_UNRELIABLE_TRIGGER_SOFT_MIN_SUCESO = 20.0
DYN_ROOF_UNRELIABLE_TRIGGER_SOFT_MIN_PATTERN = 3.0
DYN_ROOF_RELIABLE_TRIGGER_SOFT_ENABLE = True
DYN_ROOF_RELIABLE_TRIGGER_SOFT_MARGIN = 0.02
DYN_ROOF_RELIABLE_TRIGGER_SOFT_MIN_SUCESO = 22.0
DYN_ROOF_RELIABLE_TRIGGER_SOFT_MIN_PATTERN = 3.0
DYN_ROOF_UNRELIABLE_ROOF_OFFSET = 0.03
# Cap superior dinámico del techo: mantiene límites altos pero evita quedarse en 85-99% sin ejecuciones.
DYN_ROOF_MAX_CAP = 0.82
DYN_ROOF_MAX_CAP_UNRELIABLE = 0.80
DYN_ROOF_MAX_CAP_WARMUP = 0.78
REAL_COOLDOWN_UNTIL_TS = 0.0
LAST_RETRAIN_ERROR = ""

DYN_ROOF_STATE = {
    "tick": 0,
    "roof": float(max(DYN_ROOF_FLOOR, IA_OBJETIVO_REAL_THR)),
    "last_touch_tick": 0,
    "melt_batches_applied": 0,
    "confirm_bot": None,
    "confirm_streak": 0,
    "last_open_tick": 0,
    "last_floor": None,
    "allow_real_prev": False,
    "gate_consumed": False,
    "gate_rearm_streak": 0,
    "crowd_count": 0,
    "last_low_balance_warn_ts": 0.0,
    "last_p_best": 0.0,
    "last_live_peak": 0.0,
    "last_floor_gate": float(max(DYN_ROOF_FLOOR, IA_OBJETIVO_REAL_THR)),
    "live_peak_hist": deque(maxlen=int(DYN_ROOF_LIVE_PEAK_WINDOW)),
    "prev_probs": {},
    "last_real_open_ts": 0.0,
}


def _cooldown_post_trade_s() -> float:
    """Cooldown dinámico post-trade: más largo si el mercado está saturado de probabilidades altas."""
    try:
        crowd_count = int(DYN_ROOF_STATE.get("crowd_count", 0) or 0)
        p_best = float(DYN_ROOF_STATE.get("last_p_best", 0.0) or 0.0)
        if crowd_count >= int(DYN_ROOF_CROWD_MIN_BOTS) and p_best >= float(DYN_ROOF_CROWD_P_MIN):
            return float(REAL_POST_TRADE_COOLDOWN_CROWDED_S)
    except Exception:
        pass
    return float(REAL_POST_TRADE_COOLDOWN_S)


def _marcar_compuerta_real_consumida() -> None:
    """Consume la apertura de compuerta REAL para evitar ráfagas mientras la señal siga pegada."""
    try:
        DYN_ROOF_STATE["gate_consumed"] = True
    except Exception:
        pass


def _todos_bots_con_n_minimo_real(min_n: int | None = None) -> bool:
    """True si TODOS los bots alcanzaron el mínimo de muestra para habilitar umbral REAL reducido."""
    try:
        n_req = int(IA_ACTIVACION_REAL_MIN_N_POR_BOT if min_n is None else min_n)
        for b in BOT_NAMES:
            n_b = int(estado_bots.get(b, {}).get("tamano_muestra", 0) or 0)
            if n_b < n_req:
                return False
        return True
    except Exception:
        return False


def _umbral_real_operativo_actual() -> float:
    """
    Umbral REAL dinámico con piso inteligente:
    - En modo confiable: mantiene piso AUTO_REAL_THR_MIN.
    - En unreliable con n mínimo por bot: habilita piso moderado temporal.
    """
    piso_conf = float(AUTO_REAL_THR_MIN)
    try:
        if _todos_bots_con_n_minimo_real():
            meta = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
            n_samples = int(meta.get("n_samples", meta.get("n", 0)) or 0)
            warmup = bool(meta.get("warmup_mode", n_samples < int(TRAIN_WARMUP_MIN_ROWS)))
            reliable = bool(meta.get("reliable", False)) and (not warmup)

            if (not reliable):
                piso_unrel = float(max(0.50, float(AUTO_REAL_UNRELIABLE_FLOOR)))
                if n_samples >= int(IA_ACTIVACION_REAL_THR_POST_N15_UNREL_MIN_SAMPLES):
                    return float(max(piso_unrel, float(IA_ACTIVACION_REAL_THR_POST_N15_UNREL)))
                return float(max(piso_unrel, float(IA_ACTIVACION_REAL_THR)))

            return float(max(piso_conf, float(IA_ACTIVACION_REAL_THR_POST_N15)))
    except Exception:
        pass
    return float(max(piso_conf, float(IA_ACTIVACION_REAL_THR)))




def _umbral_real_por_bot_contexto(bot: str, ctx: dict | None, base_thr: float | None = None) -> tuple[float, str]:
    """Umbral REAL conservador por bot/contexto con fallback seguro al umbral global."""
    thr = float(_umbral_real_operativo_actual() if base_thr is None else base_thr)
    reason = "base"
    try:
        b = str(bot or "")
        ev = _evidencia_bot_umbral_objetivo(b)
        ev_n = int(ev.get("n", 0) or 0)
        ev_lb = float(ev.get("lb", 0.0) or 0.0)
        c = ctx if isinstance(ctx, dict) else {}
        hb = float(c.get("hora_bucket", 0.0) or 0.0)
        pay = float(c.get("payout", 0.0) or 0.0)
        vol = float(c.get("volatilidad", 0.0) or 0.0)

        if ev_n >= int(EVIDENCE_MIN_N_HARD) and ev_lb >= float(EVIDENCE_MIN_LB_HARD):
            thr = max(0.50, thr - 0.01)
            reason = "evidence_strong"
        elif ev_n < int(EVIDENCE_MIN_N_SOFT):
            thr = min(0.99, thr + 0.02)
            reason = "evidence_low"

        # Contexto riesgoso: subir ligeramente el umbral
        if (pay < 0.25) or (vol > 0.85) or (hb <= 0.05):
            thr = min(0.99, thr + 0.01)
            reason = reason + "+ctx_risk"
    except Exception:
        pass
    return float(max(0.0, min(0.99, thr))), str(reason)

def _n_minimo_real_status() -> tuple[int, int]:
    """Retorna (mínimo n actual entre bots, n requerido) para diagnóstico en HUD."""
    try:
        n_req = int(IA_ACTIVACION_REAL_MIN_N_POR_BOT)
        n_vals = [int(estado_bots.get(b, {}).get("tamano_muestra", 0) or 0) for b in BOT_NAMES]
        n_min = min(n_vals) if n_vals else 0
        return int(n_min), int(n_req)
    except Exception:
        return 0, int(IA_ACTIVACION_REAL_MIN_N_POR_BOT)


def _smart_clone_override_ok(best_bot: str, p_best: float, p_second: float, clone_flat: bool) -> bool:
    """
    Permite destrabar el candado clone_flat SOLO cuando hay evidencia real fuerte.

    Objetivo:
    - Evitar falsos bloqueos por planicie de probabilidades en ticks donde
      el mejor bot realmente ya demostró edge consistente.
    - Mantener conservadurismo: exige N, límite inferior (LB), prob alta y
      micro-GAP positivo frente al segundo.
    """
    try:
        if not bool(SMART_LOCKS_ENABLE):
            return False
        if not bool(clone_flat):
            return False
        if not best_bot:
            return False

        ev = _evidencia_bot_umbral_objetivo(best_bot)
        ev_n = int(ev.get("n", 0) or 0)
        ev_lb = float(ev.get("lb", 0.0) or 0.0)
        p1 = float(p_best or 0.0)
        p2 = float(p_second or 0.0)
        gap = float(p1 - p2)

        return bool(
            (ev_n >= int(SMART_CLONE_OVERRIDE_MIN_N))
            and (ev_lb >= float(SMART_CLONE_OVERRIDE_MIN_LB))
            and (p1 >= float(SMART_CLONE_OVERRIDE_MIN_PROB))
            and (gap >= float(SMART_CLONE_OVERRIDE_MIN_GAP))
        )
    except Exception:
        return False


_UNREL_MICRO_RELAX_CACHE = {"ts": 0.0, "delta": 0.0, "n": 0, "wr": 0.0, "sig": ""}
_UNREL_MICRO_RELAX_LOG_TS = 0.0


def _calcular_micro_relax_unrel(force: bool = False) -> dict:
    """Calcula una relajación pequeña y segura del umbral UNREL desde ia_signals_log."""
    global _UNREL_MICRO_RELAX_CACHE, _UNREL_MICRO_RELAX_LOG_TS
    out = {"delta": 0.0, "n": 0, "wr": 0.0, "active": False, "why": "off"}
    try:
        if not bool(AUTO_REAL_UNREL_MICRO_RELAX_ENABLE):
            return out

        now = time.time()
        cache = _UNREL_MICRO_RELAX_CACHE if isinstance(_UNREL_MICRO_RELAX_CACHE, dict) else {}
        if (not force) and ((now - float(cache.get("ts", 0.0) or 0.0)) <= 20.0):
            return {
                "delta": float(cache.get("delta", 0.0) or 0.0),
                "n": int(cache.get("n", 0) or 0),
                "wr": float(cache.get("wr", 0.0) or 0.0),
                "active": bool(float(cache.get("delta", 0.0) or 0.0) > 0.0),
                "why": str(cache.get("why", "cache") or "cache"),
            }

        p = Path(IA_SIGNALS_LOG)
        if not p.exists():
            out["why"] = "no_log"
            _UNREL_MICRO_RELAX_CACHE = {"ts": now, **out}
            return out

        rows = deque(maxlen=1200)
        with open(p, "r", encoding="utf-8", newline="") as fh:
            rd = csv.DictReader(fh)
            for r in rd:
                rows.append(r)
        if not rows:
            out["why"] = "empty"
            _UNREL_MICRO_RELAX_CACHE = {"ts": now, **out}
            return out

        # Usar cierres reales con barrera fuerte (thr>=85%) para no relajar por ruido.
        closed = []
        for r in rows:
            try:
                yv = str(r.get("y", "")).strip()
                if yv not in {"0", "1"}:
                    continue
                thr = float(r.get("thr", 0.0) or 0.0)
                modo = str(r.get("modo", "")).strip().upper()
                if thr < 0.85:
                    continue
                if modo not in {"ORDEN_REAL", "IA_AUTO", "REAL"}:
                    continue
                closed.append((int(yv), thr))
            except Exception:
                continue

        n = len(closed)
        if n < int(AUTO_REAL_UNREL_MICRO_RELAX_MIN_CLOSED):
            out.update({"n": n, "why": "n_low"})
            _UNREL_MICRO_RELAX_CACHE = {"ts": now, **out}
            return out

        wins = sum(y for y, _thr in closed)
        wr = float(wins / max(1, n))
        if wr < float(AUTO_REAL_UNREL_MICRO_RELAX_MIN_WINRATE):
            out.update({"n": n, "wr": wr, "why": "wr_low"})
            _UNREL_MICRO_RELAX_CACHE = {"ts": now, **out}
            return out

        # Delta gradual por muestra + calidad, acotado por MAX_DELTA.
        wr_excess = max(0.0, wr - float(AUTO_REAL_UNREL_MICRO_RELAX_MIN_WINRATE))
        wr_gain = min(1.0, wr_excess / 0.20)
        n_gain = min(1.0, float(n) / 80.0)
        delta = float(min(float(AUTO_REAL_UNREL_MICRO_RELAX_MAX_DELTA), float(AUTO_REAL_UNREL_MICRO_RELAX_MAX_DELTA) * wr_gain * n_gain))

        out.update({"delta": delta, "n": n, "wr": wr, "active": bool(delta > 0.0), "why": "ok" if delta > 0.0 else "flat"})
        _UNREL_MICRO_RELAX_CACHE = {"ts": now, **out}

        if out["active"] and ((now - float(_UNREL_MICRO_RELAX_LOG_TS or 0.0)) >= float(AUTO_REAL_UNREL_MICRO_RELAX_LOG_COOLDOWN_S)):
            _UNREL_MICRO_RELAX_LOG_TS = now
            try:
                agregar_evento(f"🧪 UNREL micro-relax activo: -{delta*100:.1f}pp (n={n}, wr={wr*100:.1f}%).")
            except Exception:
                pass

        return out
    except Exception:
        return out


def _umbral_unrel_operativo(best_bot: str | None, best_prob: float | None = None) -> float:
    """
    Umbral UNREL operativo con 2 capas:
    - base conservadora (AUTO_REAL_UNRELIABLE_MIN_PROB).
    - ajuste por lateral + percentil de prob reciente del bot (anti-congelamiento).

    Objetivo: no exigir 63% fijo cuando el modelo está bien discriminado en un rango
    más bajo (ej. 55-60%), evitando inflar artificialmente la probabilidad.
    """
    try:
        base = float(AUTO_REAL_UNRELIABLE_MIN_PROB)
        mr = _calcular_micro_relax_unrel(force=False)
        base = float(max(0.50, base - float(mr.get("delta", 0.0) or 0.0)))
        if not bool(AUTO_REAL_UNREL_LATERAL_ADAPT_ENABLE):
            return base
        if not isinstance(best_bot, str) or (best_bot not in BOT_NAMES):
            return base

        st = estado_bots.get(best_bot, {}) if isinstance(estado_bots, dict) else {}
        n_bot = int(st.get("tamano_muestra", 0) or 0)
        wr_bot = float((st.get("porcentaje_exito", 0.0) or 0.0) / 100.0)
        p_best = float(best_prob or 0.0)

        # Capa 1: lateral clásico
        lateral_ok = bool(
            (n_bot >= int(AUTO_REAL_UNREL_LATERAL_MIN_N))
            and (wr_bot >= float(AUTO_REAL_UNREL_LATERAL_MIN_WR))
            and (p_best >= float(AUTO_REAL_UNREL_LATERAL_MIN_PROB))
        )
        if lateral_ok:
            return float(max(float(AUTO_REAL_UNREL_LATERAL_MIN_PROB), min(base, p_best)))

        # Capa 2: adaptación por distribución viva del bot (percentil robusto)
        hist = st.get("ia_prob_hist_raw", [])
        vals = []
        if isinstance(hist, list):
            for v in hist[-120:]:
                try:
                    x = float(v)
                    if np.isfinite(x) and 0.0 <= x <= 1.0:
                        vals.append(x)
                except Exception:
                    continue

        # Requiere evidencia mínima y WR no negativo para evitar sesgo optimista
        if (len(vals) >= 24) and (n_bot >= 40) and (wr_bot >= 0.48):
            q80 = float(np.quantile(np.asarray(vals, dtype=float), 0.80))
            # margen pequeño: pedimos estar cerca del percentil alto reciente
            thr_q = float(max(0.50, min(base, q80 - 0.01)))
            if p_best >= (thr_q - 0.01):
                return float(thr_q)

        return base
    except Exception:
        return float(AUTO_REAL_UNRELIABLE_MIN_PROB)


def _actualizar_compuerta_techo_dinamico() -> dict:
    """
    Actualiza el techo dinámico y evalúa la compuerta REAL del mejor bot del tick.

    Reglas clave:
    - roof sube rápido por máximos (roof=max(roof, p_best)).
    - roof baja lento tras paciencia (hold), por lotes de batch ticks.
    - compuerta REAL exige: piso duro, techo efectivo, GAP y confirmación doble.
    """
    floor_now = float(_umbral_real_operativo_actual())
    modo_relajado_n15 = bool(_todos_bots_con_n_minimo_real())
    meta_live = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
    n_samples_meta = int(meta_live.get("n_samples", meta_live.get("n", 0)) or 0)
    warmup_mode = bool(meta_live.get("warmup_mode", n_samples_meta < int(TRAIN_WARMUP_MIN_ROWS)))
    reliable_mode = bool(meta_live.get("reliable", False)) and (not warmup_mode)
    last_real_open_ts = float(DYN_ROOF_STATE.get("last_real_open_ts", 0.0) or 0.0)
    stall_s = max(0.0, time.time() - last_real_open_ts) if last_real_open_ts > 0 else float(DYN_ROOF_STALL_TO_MODE_C_S + 1)
    mode_c_candidate = bool(
        modo_relajado_n15
        and reliable_mode
        and (stall_s >= float(DYN_ROOF_STALL_TO_MODE_C_S))
    )
    out = {
        "best_bot": None,
        "p_best": 0.0,
        "p_second": 0.0,
        "gap_ok": False,
        "roof": float(DYN_ROOF_STATE.get("roof", floor_now)),
        "roof_eff": float(DYN_ROOF_STATE.get("roof", floor_now)),
        "confirm_streak": int(DYN_ROOF_STATE.get("confirm_streak", 0) or 0),
        "allow_real": False,
        "n_best": 0,
        "new_open": False,
        "gate_mode": "A",
        "stall_s": float(stall_s),
        "trigger_ok_micro_soft": False,
    }
    try:
        DYN_ROOF_STATE["tick"] = int(DYN_ROOF_STATE.get("tick", 0) or 0) + 1
        tick_now = int(DYN_ROOF_STATE["tick"])

        live = []
        for b in BOT_NAMES:
            try:
                if str(estado_bots.get(b, {}).get("modo_ia", "off")).lower() == "off":
                    continue
                if not ia_prob_valida(b, max_age_s=12.0):
                    continue
                p = float(estado_bots.get(b, {}).get("prob_ia", 0.0) or 0.0)
                n = int(estado_bots.get(b, {}).get("tamano_muestra", 0) or 0)
                if np.isfinite(p):
                    live.append((b, p, n))
            except Exception:
                continue

        if not live:
            DYN_ROOF_STATE["confirm_bot"] = None
            DYN_ROOF_STATE["confirm_streak"] = 0
            return out

        live.sort(key=lambda x: x[1], reverse=True)
        best_bot, p_best, n_best = live[0]
        p_second = float(live[1][1]) if len(live) > 1 else 0.0

        # Empates prácticos del top (ej. 85.0%/85.0%/85.0%) pueden alternar
        # best_bot por ruido mínimo y reiniciar confirmación. Si el bot ya en
        # confirmación sigue prácticamente empatado con el top, lo mantenemos.
        try:
            tie_tol = float(DYN_ROOF_TIE_KEEP_CONFIRM_TOL)
            confirm_bot_prev = DYN_ROOF_STATE.get("confirm_bot")
            if isinstance(confirm_bot_prev, str) and confirm_bot_prev in {b for b, _p, _n in live}:
                p_confirm_prev = None
                n_confirm_prev = 0
                for b_live, p_live, n_live in live:
                    if b_live == confirm_bot_prev:
                        p_confirm_prev = float(p_live)
                        n_confirm_prev = int(n_live)
                        break
                if isinstance(p_confirm_prev, (int, float)) and abs(float(p_best) - float(p_confirm_prev)) <= float(tie_tol):
                    best_bot = str(confirm_bot_prev)
                    p_best = float(p_confirm_prev)
                    n_best = int(n_confirm_prev)
                    rest = [float(p) for b, p, _n in live if b != best_bot]
                    p_second = max(rest) if rest else 0.0
        except Exception:
            pass

        crowd_count = sum(1 for _b, p, _n in live if float(p) >= float(DYN_ROOF_CROWD_P_MIN))
        probs_live = [float(x[1]) for x in live]
        spread_std = float(np.std(probs_live)) if probs_live else 0.0

        live_peak_hist = DYN_ROOF_STATE.get("live_peak_hist")
        if not isinstance(live_peak_hist, deque):
            live_peak_hist = deque(maxlen=int(DYN_ROOF_LIVE_PEAK_WINDOW))
        live_peak_hist.append(float(p_best))
        DYN_ROOF_STATE["live_peak_hist"] = live_peak_hist
        live_peak = float(max(live_peak_hist)) if len(live_peak_hist) > 0 else float(p_best)
        enough_live_peak = bool(len(live_peak_hist) >= int(DYN_ROOF_LIVE_PEAK_MIN_SAMPLES))

        prev_floor = DYN_ROOF_STATE.get("last_floor", None)
        if not isinstance(prev_floor, (int, float)) or abs(float(prev_floor) - float(floor_now)) > 1e-12:
            DYN_ROOF_STATE["roof"] = float(floor_now)
            DYN_ROOF_STATE["last_floor"] = float(floor_now)
            DYN_ROOF_STATE["last_touch_tick"] = int(tick_now)
            DYN_ROOF_STATE["melt_batches_applied"] = 0

        roof = float(DYN_ROOF_STATE.get("roof", floor_now) or floor_now)
        last_touch = int(DYN_ROOF_STATE.get("last_touch_tick", 0) or 0)

        # Regla A: tocar/romper techo resetea paciencia; romperlo además lo eleva.
        near_touch = float(p_best) >= float(roof - DYN_ROOF_NEAR_TOL)
        if near_touch:
            roof = max(float(roof), float(p_best))
            DYN_ROOF_STATE["roof"] = float(roof)
            DYN_ROOF_STATE["last_touch_tick"] = int(tick_now)
            DYN_ROOF_STATE["melt_batches_applied"] = 0
            last_touch = int(tick_now)
        else:
            # Regla B: derretido lento solo después de hold y por lotes.
            elapsed = int(tick_now - last_touch)
            if elapsed > int(DYN_ROOF_HOLD_TICKS):
                batches_now = int((elapsed - int(DYN_ROOF_HOLD_TICKS)) // int(DYN_ROOF_BATCH_TICKS))
                batches_applied = int(DYN_ROOF_STATE.get("melt_batches_applied", 0) or 0)
                if batches_now > batches_applied:
                    delta_batches = int(batches_now - batches_applied)
                    roof = max(float(floor_now), float(roof - (delta_batches * DYN_ROOF_STEP)))
                    DYN_ROOF_STATE["roof"] = float(roof)
                    DYN_ROOF_STATE["melt_batches_applied"] = int(batches_now)

        roof = float(DYN_ROOF_STATE.get("roof", floor_now) or floor_now)
        max_cap = float(DYN_ROOF_MAX_CAP)
        if warmup_mode:
            max_cap = min(max_cap, float(DYN_ROOF_MAX_CAP_WARMUP))
        elif not reliable_mode:
            max_cap = min(max_cap, float(DYN_ROOF_MAX_CAP_UNRELIABLE))
        roof = float(max(float(floor_now), min(float(roof), float(max_cap))))
        DYN_ROOF_STATE["roof"] = float(roof)
        penalty = float(DYN_ROOF_LOW_N_PENALTY) if int(n_best) < int(DYN_ROOF_LOW_N_MIN) else 0.0
        roof_eff = float(roof + penalty)
        crowding = bool(crowd_count >= int(DYN_ROOF_CROWD_MIN_BOTS))
        if crowding:
            roof_eff = float(roof_eff + float(DYN_ROOF_CROWD_EXTRA_ROOF))
        if modo_relajado_n15 and (not reliable_mode):
            roof_eff = float(max(float(floor_now), float(roof_eff - float(DYN_ROOF_UNRELIABLE_ROOF_OFFSET))))

        # GAP dinámico:
        # - Si solo hay 1 bot válido, no se bloquea por GAP.
        # - En modo relajado (n>=15 en todos) pedimos micro-GAP cuando hay
        #   clustering en 70-80% para evitar márgenes casi idénticos persistentes.
        if len(live) <= 1:
            gap_ok = True
        else:
            cluster_count = sum(1 for _b, p, _n in live if float(p) >= float(DYN_ROOF_CLUSTER_P_MIN))
            clustering_soft = bool(cluster_count >= int(DYN_ROOF_CLUSTER_MIN_BOTS))
            gap_req = float(DYN_ROOF_GAP)
            if crowding:
                gap_req += float(DYN_ROOF_CROWD_EXTRA_GAP)
            if modo_relajado_n15 and clustering_soft:
                gap_req = max(float(DYN_ROOF_CLUSTER_EXTRA_GAP), gap_req)
            elif modo_relajado_n15 and (not crowding):
                # Mantener modo B fluido cuando no hay clustering real.
                gap_req = 0.0
            gap_ok = bool((float(p_best) - float(p_second)) >= float(gap_req))

        clone_flat = bool(
            (len(live) >= 2)
            and (
                (spread_std < float(PROB_CLONE_STD_MIN))
                or ((float(p_best) - float(p_second)) < float(PROB_CLONE_GAP_MIN))
            )
        )
        smart_clone_override = _smart_clone_override_ok(best_bot, p_best, p_second, clone_flat)
        if clone_flat:
            gap_ok = False
        if smart_clone_override:
            gap_ok = True

        mode_c_active = bool(mode_c_candidate and float(p_best) < float(floor_now))
        gate_mode = "C" if mode_c_active else ("B" if modo_relajado_n15 else "A")
        floor_eff = float(DYN_ROOF_MODE_C_FLOOR) if mode_c_active else float(floor_now)

        # En modo relajado (n>=15 en todos): usar piso dinámico basado en el
        # mayor p_best reciente (techo vivo) con margen y candados de GAP/confirm.
        floor_gate_live = float(floor_eff if mode_c_active else floor_now)
        if modo_relajado_n15 and (not mode_c_active) and enough_live_peak:
            if bool(DYN_ROOF_LIVE_PEAK_ONLY_RELIABLE) and (not reliable_mode):
                floor_gate_live = float(floor_gate_live)
            else:
                margin_lp = float(DYN_ROOF_LIVE_PEAK_MARGIN if reliable_mode else DYN_ROOF_LIVE_PEAK_MARGIN_UNRELIABLE)
                floor_gate_live = float(max(floor_gate_live, live_peak - margin_lp))

        if modo_relajado_n15:
            pass_gate = bool((float(p_best) >= float(floor_gate_live)) and bool(gap_ok))
        else:
            pass_gate = (
                (float(p_best) >= float(roof_eff))
                and (float(p_best) >= float(floor_eff))
                and bool(gap_ok)
            )

        if mode_c_active:
            ev = _evidencia_bot_umbral_objetivo(best_bot)
            ev_n = int(ev.get("n", 0) or 0)
            ev_lb = float(ev.get("lb", 0.0) or 0.0)
            suceso_ok_mode_c = bool(estado_bots.get(best_bot, {}).get("ia_suceso_ok", False))
            pass_gate = bool(
                pass_gate
                and suceso_ok_mode_c
                and (ev_n >= int(DYN_ROOF_MODE_C_MIN_EVIDENCE_N))
                and (ev_lb >= float(DYN_ROOF_MODE_C_MIN_EVIDENCE_LB))
            )

        # Confirmación: 2 ticks consecutivos del mismo bot.
        confirm_bot = DYN_ROOF_STATE.get("confirm_bot")
        confirm_streak = int(DYN_ROOF_STATE.get("confirm_streak", 0) or 0)
        if pass_gate:
            if confirm_bot == best_bot:
                confirm_streak += 1
            else:
                confirm_bot = best_bot
                confirm_streak = 1
        else:
            confirm_bot = None
            confirm_streak = 0

        DYN_ROOF_STATE["confirm_bot"] = confirm_bot
        DYN_ROOF_STATE["confirm_streak"] = int(confirm_streak)

        confirm_need = int(DYN_ROOF_MODE_C_CONFIRM_TICKS if mode_c_active else DYN_ROOF_CONFIRM_TICKS)
        allow_real = bool(pass_gate and (confirm_streak >= int(confirm_need)))
        allow_real_prev = bool(DYN_ROOF_STATE.get("allow_real_prev", False))
        gate_consumed = bool(DYN_ROOF_STATE.get("gate_consumed", False))
        rearm_streak = int(DYN_ROOF_STATE.get("gate_rearm_streak", 0) or 0)
        prev_probs = DYN_ROOF_STATE.get("prev_probs", {})
        if not isinstance(prev_probs, dict):
            prev_probs = {}
        prev_p_best = prev_probs.get(best_bot, None)
        crossed_up = bool(
            (isinstance(prev_p_best, (int, float)) and (float(prev_p_best) < float(floor_eff)) and (float(p_best) >= float(floor_eff)))
            or ((prev_p_best is None) and (float(p_best) >= float(floor_eff)))
        )
        suceso_ok = bool(estado_bots.get(best_bot, {}).get("ia_suceso_ok", False))

        if not allow_real:
            gate_consumed = False
            rearm_streak = 0
        elif gate_consumed:
            if float(p_best) <= float(roof_eff - DYN_ROOF_GATE_REARM_HYST):
                rearm_streak += 1
                if rearm_streak >= int(DYN_ROOF_GATE_REARM_TICKS):
                    gate_consumed = False
                    rearm_streak = 0
            else:
                rearm_streak = 0

        # Trigger de apertura:
        # - Modo A: exige cruce al alza (anti-ráfaga estricto).
        # - Modo B (post-n15): si ya hubo confirmación sostenida, usar suceso_ok
        #   para no quedar "pegado" cuando p_best orbita el mismo nivel sin nuevo cruce.
        # - Modo C: mantiene criterio conservador basado en suceso_ok + evidencia.
        trigger_force = bool(
            modo_relajado_n15
            and (int(confirm_streak) >= int(max(confirm_need, DYN_ROOF_TRIGGER_FORCE_STREAK)))
            and (float(p_best) >= float(floor_eff - DYN_ROOF_TRIGGER_FORCE_MARGIN))
        )

        trigger_pattern = False
        trigger_soft = False
        trigger_ok_micro_soft = False
        if modo_relajado_n15 and (not reliable_mode):
            try:
                ctx_best = _ultimo_contexto_operativo_bot(str(best_bot))
                ok_pat, _why_pat = _micro_pattern_gate_ok(str(best_bot), ctx_best)
                trigger_pattern = bool(ok_pat and (float(p_best) >= float(floor_eff)))

                if bool(DYN_ROOF_UNRELIABLE_TRIGGER_SOFT_ENABLE):
                    q3p, q2p = _pattern_v1_thresholds_proxy()
                    _ps, _pb, _pp, _pt = pattern_score_operativo_v1(ctx_best or {}, q3p, q2p)
                    suceso_idx_best = float(estado_bots.get(str(best_bot), {}).get("ia_suceso_idx", 0.0) or 0.0)
                    near_roof_soft = bool(float(p_best) >= float(max(float(floor_eff), float(roof_eff - DYN_ROOF_UNRELIABLE_TRIGGER_SOFT_MARGIN))))
                    confirm_soft = bool(int(confirm_streak) >= max(1, int(confirm_need) - 1))
                    trigger_soft = bool(
                        near_roof_soft
                        and confirm_soft
                        and ((suceso_idx_best >= float(DYN_ROOF_UNRELIABLE_TRIGGER_SOFT_MIN_SUCESO)) or (float(_pt) >= float(DYN_ROOF_UNRELIABLE_TRIGGER_SOFT_MIN_PATTERN)))
                    )
            except Exception:
                trigger_pattern = False
                trigger_soft = False
        if modo_relajado_n15 and reliable_mode and bool(DYN_ROOF_RELIABLE_TRIGGER_SOFT_ENABLE):
            try:
                ctx_best_rel = _ultimo_contexto_operativo_bot(str(best_bot))
                q3p_rel, q2p_rel = _pattern_v1_thresholds_proxy()
                _ps_rel, _pb_rel, _pp_rel, _pt_rel = pattern_score_operativo_v1(ctx_best_rel or {}, q3p_rel, q2p_rel)
                suceso_idx_best_rel = float(estado_bots.get(str(best_bot), {}).get("ia_suceso_idx", 0.0) or 0.0)
                pat_state_rel = str(estado_bots.get(str(best_bot), {}).get("ia_pattern_col_state", "BLOQUEADO") or "BLOQUEADO")
                near_roof_soft_rel = bool(
                    float(p_best) >= float(max(float(floor_eff), float(roof_eff - DYN_ROOF_RELIABLE_TRIGGER_SOFT_MARGIN)))
                )
                confirm_soft_rel = bool(int(confirm_streak) >= max(1, int(confirm_need) - 1))
                context_soft_rel = bool(
                    (suceso_idx_best_rel >= float(DYN_ROOF_RELIABLE_TRIGGER_SOFT_MIN_SUCESO))
                    or (float(_pt_rel) >= float(DYN_ROOF_RELIABLE_TRIGGER_SOFT_MIN_PATTERN))
                    or (pat_state_rel == "CONTINUIDAD")
                )
                trigger_ok_micro_soft = bool(
                    (n_samples_meta >= 300)
                    and near_roof_soft_rel
                    and confirm_soft_rel
                    and bool(gap_ok)
                    and context_soft_rel
                )
            except Exception:
                trigger_ok_micro_soft = False

        if mode_c_active:
            trigger_ok = bool(suceso_ok)
        elif modo_relajado_n15:
            trigger_ok = bool(suceso_ok or crossed_up or trigger_force or trigger_pattern or trigger_soft)
        else:
            trigger_ok = bool(crossed_up)
        if warmup_mode and (not mode_c_active):
            # Modo precisión conservador: bloquear REAL en warmup.
            if bool(AUTO_REAL_BLOCK_WHEN_WARMUP):
                trigger_ok = False
            else:
                if not modo_relajado_n15:
                    trigger_ok = bool(trigger_ok and suceso_ok)
                else:
                    trigger_ok = bool(trigger_ok)

        last_open_tick = int(DYN_ROOF_STATE.get("last_open_tick", 0) or 0)
        new_open = bool(
            allow_real
            and (not allow_real_prev)
            and trigger_ok
            and (not gate_consumed)
            and (last_open_tick != tick_now)
        )
        if new_open:
            DYN_ROOF_STATE["last_open_tick"] = int(tick_now)
        DYN_ROOF_STATE["allow_real_prev"] = bool(allow_real)
        DYN_ROOF_STATE["gate_consumed"] = bool(gate_consumed)
        DYN_ROOF_STATE["gate_rearm_streak"] = int(rearm_streak)
        DYN_ROOF_STATE["crowd_count"] = int(crowd_count)
        DYN_ROOF_STATE["last_p_best"] = float(p_best)
        DYN_ROOF_STATE["last_live_peak"] = float(live_peak)
        DYN_ROOF_STATE["last_floor_gate"] = float(floor_gate_live)
        DYN_ROOF_STATE["last_gate_mode"] = str(gate_mode)
        DYN_ROOF_STATE["last_floor_eff"] = float(floor_eff)
        DYN_ROOF_STATE["last_confirm_need"] = int(confirm_need)
        DYN_ROOF_STATE["last_trigger_ok"] = bool(trigger_ok)
        DYN_ROOF_STATE["last_trigger_ok_micro_soft"] = bool(trigger_ok_micro_soft)
        DYN_ROOF_STATE["last_trigger_force"] = bool(trigger_force)
        for b_live, p_live, _n_live in live:
            prev_probs[str(b_live)] = float(p_live)
        DYN_ROOF_STATE["prev_probs"] = prev_probs

        out.update({
            "best_bot": best_bot,
            "p_best": float(p_best),
            "p_second": float(p_second),
            "gap_ok": bool(gap_ok),
            "roof": float(roof),
            "roof_eff": float(roof_eff),
            "confirm_streak": int(confirm_streak),
            "allow_real": bool(allow_real),
            "n_best": int(n_best),
            "new_open": bool(new_open),
            "crowd_count": int(crowd_count),
            "crowding": bool(crowding),
            "crossed_up": bool(crossed_up),
            "suceso_ok": bool(suceso_ok),
            "trigger_ok": bool(trigger_ok),
            "trigger_ok_micro_soft": bool(trigger_ok_micro_soft),
            "trigger_force": bool(trigger_force),
            "gate_mode": str(gate_mode),
            "stall_s": float(stall_s),
            "floor_eff": float(floor_eff),
            "floor_gate": float(floor_gate_live),
            "live_peak": float(live_peak),
            "live_peak_n": int(len(live_peak_hist)),
            "confirm_need": int(confirm_need),
            "clone_flat": bool(clone_flat),
            "smart_clone_override": bool(smart_clone_override),
            "spread_std": float(spread_std),
        })
        return out
    except Exception:
        return out


def _registrar_estado_embudo(data: dict | None = None) -> dict:
    """Persistencia del estado unificado del embudo para HUD/eventos."""
    global EMBUDO_DECISION_STATE
    base = {
        "decision_final": EMBUDO_FINAL_WAIT_SOFT,
        "decision_reason": "init",
        "gate_quality": "weak",
        "risk_mode": "WAIT_SOFT",
        "hard_block_reason": "",
        "soft_wait_reason": "",
        "top1_bot": None,
        "top2_bot": None,
        "gap_value": 0.0,
        "top1_prob": 0.0,
        "top2_prob": 0.0,
        "degrade_from": "none",
        "ia_real_backed": 0,
        "real_source": "IA",
        "ia_model_mature": 0,
    }
    try:
        if isinstance(EMBUDO_DECISION_STATE, dict):
            base.update(EMBUDO_DECISION_STATE)
    except Exception:
        pass
    if isinstance(data, dict):
        base.update(data)
    EMBUDO_DECISION_STATE = base
    return EMBUDO_DECISION_STATE


def _resolver_embudo_final(candidatos: list, dyn_gate: dict | None, estado_real: str, meta_live: dict | None) -> dict:
    """Embudo unificado: selección -> calidad blanda -> modulación -> estado final."""
    if _purificacion_real_activa():
        _emitir_marca_purificacion_real()
        lxv_on = bool(globals().get("LXV_SYNC_REAL_ROUTE_ENABLE", False))
        top1_bot = str(candidatos[0][1]) if candidatos else None
        top1_prob = float(candidatos[0][2] or 0.0) if candidatos else 0.0
        top2_bot = str(candidatos[1][1]) if len(candidatos) > 1 else None
        top2_prob = float(candidatos[1][2] or 0.0) if len(candidatos) > 1 else 0.0
        gap_value = float(top1_prob - top2_prob) if candidatos else 0.0
        return _registrar_estado_embudo({
            "decision_final": "LXV_ONLY" if lxv_on else "REAL_DISABLED",
            "decision_reason": "ia_purificada_lxv_activo" if lxv_on else "purificacion_real",
            "gate_quality": "disabled",
            "risk_mode": "LXV_ONLY" if lxv_on else "REAL_DISABLED",
            "hard_block_reason": "ia_purificada_lxv_activo" if lxv_on else "purificacion_real",
            "soft_wait_reason": "ia_purificada_lxv_activo" if lxv_on else "purificacion_real",
            "top1_bot": top1_bot,
            "top2_bot": top2_bot,
            "gap_value": gap_value,
            "top1_prob": top1_prob,
            "top2_prob": top2_prob,
            "degrade_from": "ia_purificada_lxv_activo" if lxv_on else "purificacion_real",
            "ia_real_backed": 0,
            "real_source": "LXV_SYNC" if lxv_on else "PURIFICACION_REAL",
            "ia_model_mature": 0,
        })
    out = _registrar_estado_embudo({
        "decision_final": EMBUDO_FINAL_WAIT_SOFT,
        "decision_reason": "sin_candidatos",
        "gate_quality": "weak",
        "risk_mode": "WAIT_SOFT",
        "soft_wait_reason": "sin_candidatos",
        "hard_block_reason": "",
        "top1_bot": None,
        "top2_bot": None,
        "gap_value": 0.0,
        "top1_prob": 0.0,
        "top2_prob": 0.0,
        "degrade_from": "none",
        "ia_real_backed": 0,
        "real_source": "IA",
        "ia_model_mature": 0,
    })
    if not candidatos:
        return out
    try:
        ordered = sorted(candidatos, key=lambda x: float(x[2] if len(x) > 2 else 0.0), reverse=True)
        top1 = ordered[0]
        top2 = ordered[1] if len(ordered) > 1 else None
        top1_bot = str(top1[1])
        top1_prob = float(top1[2] or 0.0)
        top2_bot = str(top2[1]) if top2 else None
        top2_prob = float(top2[2] or 0.0) if top2 else 0.0
        gap_value = float(top1_prob - top2_prob)

        dgate = dyn_gate if isinstance(dyn_gate, dict) else {}
        allow_real = bool(dgate.get("allow_real", False))
        trigger_ok = bool(dgate.get("trigger_ok", False))
        gap_ok = bool(dgate.get("gap_ok", False))
        floor_eff = float(dgate.get("floor_eff", 0.0) or 0.0)
        confirm_need = int(dgate.get("confirm_need", DYN_ROOF_CONFIRM_TICKS) or DYN_ROOF_CONFIRM_TICKS)
        confirm_streak = int(dgate.get("confirm_streak", 0) or 0)
        confirm_ok = bool(confirm_streak >= confirm_need)

        quality = "weak"
        if allow_real and trigger_ok and confirm_ok:
            quality = "strong"
        elif (allow_real and trigger_ok) or (allow_real and confirm_ok):
            quality = "medium"
        elif allow_real or trigger_ok or confirm_streak > 0:
            quality = "weak"
        else:
            quality = "wait"

        decision = EMBUDO_FINAL_WAIT_SOFT
        reason = f"gate:{quality}"
        risk_mode = "WAIT_SOFT"
        soft_wait_reason = ""

        if quality == "strong":
            decision = EMBUDO_FINAL_REAL_NORMAL
            risk_mode = "REAL_NORMAL"
        elif quality == "medium":
            decision = EMBUDO_FINAL_REAL_MICRO
            risk_mode = "REAL_MICRO"
        elif quality == "weak":
            decision = EMBUDO_FINAL_SHADOW_OK
            risk_mode = "SHADOW_OK"
        else:
            soft_wait_reason = "gate_wait"

        meta = meta_live if isinstance(meta_live, dict) else {}
        n_samples = int(meta.get("n_samples", meta.get("n", 0)) or 0)
        reliable = bool(meta.get("reliable", False))
        canary = bool(meta.get("canary_mode", False))
        auc = float(meta.get("auc", 0.0) or 0.0)
        warmup_mode = bool(meta.get("warmup_mode", n_samples < int(TRAIN_WARMUP_MIN_ROWS)))
        model_family = str(meta.get("model_family", "") or "").strip().lower()
        ia_model_mature = bool((not warmup_mode) and reliable and (model_family != "sklearn_logreg_fallback"))
        degrade_from = "none"

        if canary and decision == EMBUDO_FINAL_REAL_NORMAL:
            decision = EMBUDO_FINAL_REAL_MICRO
            risk_mode = "REAL_MICRO"
            degrade_from = "canary"
            reason = "canary->micro"

        if bool(AUTO_REAL_BLOCK_WHEN_WARMUP) and warmup_mode and decision in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO):
            decision = EMBUDO_FINAL_SHADOW_OK
            risk_mode = "SHADOW_OK"
            degrade_from = "warmup"
            reason = "warmup->shadow"
        if not reliable:
            if decision == EMBUDO_FINAL_REAL_NORMAL:
                decision = EMBUDO_FINAL_REAL_MICRO
                risk_mode = "REAL_MICRO"
                degrade_from = "unreliable"
                reason = "unreliable->micro"
            elif decision == EMBUDO_FINAL_REAL_MICRO:
                decision = EMBUDO_FINAL_SHADOW_OK
                risk_mode = "SHADOW_OK"
                degrade_from = "unreliable"
                reason = "unreliable->shadow"

        if (not ia_model_mature) and decision in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO):
            decision = EMBUDO_FINAL_SHADOW_OK
            risk_mode = "SHADOW_OK"
            if warmup_mode:
                degrade_from = "ia_immature_warmup"
                reason = "ia_immature_warmup->shadow"
            elif model_family == "sklearn_logreg_fallback":
                degrade_from = "ia_immature_fallback"
                reason = "ia_fallback->shadow"
            else:
                degrade_from = "ia_immature_unreliable"
                reason = "ia_unreliable->shadow"

        if (not ia_model_mature) and decision in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO):
            decision = EMBUDO_FINAL_SHADOW_OK
            risk_mode = "SHADOW_OK"
            if warmup_mode:
                degrade_from = "ia_immature_warmup"
                reason = "ia_immature_warmup->shadow"
            elif model_family == "sklearn_logreg_fallback":
                degrade_from = "ia_immature_fallback"
                reason = "ia_fallback->shadow"
            else:
                degrade_from = "ia_immature_unreliable"
                reason = "ia_unreliable->shadow"

        if (not ia_model_mature) and decision in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO):
            decision = EMBUDO_FINAL_SHADOW_OK
            risk_mode = "SHADOW_OK"
            if warmup_mode:
                degrade_from = "ia_immature_warmup"
                reason = "ia_immature_warmup->shadow"
            elif model_family == "sklearn_logreg_fallback":
                degrade_from = "ia_immature_fallback"
                reason = "ia_fallback->shadow"
            else:
                degrade_from = "ia_immature_unreliable"
                reason = "ia_unreliable->shadow"

        if (not ia_model_mature) and decision in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO):
            decision = EMBUDO_FINAL_SHADOW_OK
            risk_mode = "SHADOW_OK"
            if warmup_mode:
                degrade_from = "ia_immature_warmup"
                reason = "ia_immature_warmup->shadow"
            elif model_family == "sklearn_logreg_fallback":
                degrade_from = "ia_immature_fallback"
                reason = "ia_fallback->shadow"
            else:
                degrade_from = "ia_immature_unreliable"
                reason = "ia_unreliable->shadow"

        # Prudencia extra en Martingala avanzada C2..C{MAX_CICLOS}: exigir contexto vivo.
        try:
            ciclo_adv = int(ciclo_martingala_siguiente())
        except Exception:
            ciclo_adv = 1
        if ciclo_adv > 1 and decision in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO):
            confirm_bot = str(dgate.get("confirm_bot", DYN_ROOF_STATE.get("confirm_bot", "")) or "")
            confirm_streak_adv = int(dgate.get("confirm_streak", DYN_ROOF_STATE.get("confirm_streak", 0)) or 0)
            trigger_adv = bool(dgate.get("trigger_ok", False))
            allow_adv = bool(dgate.get("allow_real", False))
            if (not allow_adv) or (not trigger_adv) or (confirm_streak_adv < max(1, confirm_need)) or (confirm_bot and confirm_bot != top1_bot):
                decision = EMBUDO_FINAL_WAIT_SOFT
                risk_mode = "WAIT_SOFT"
                soft_wait_reason = "marti_contexto_degradado"
                degrade_from = "marti_context"
                reason = f"marti_C{ciclo_adv}_contexto"

        # Consistencia explícita: no permitir doble ganador entre dyn_gate y embudo.
        best_dyn = str(dgate.get("best_bot", "") or "").strip()
        if best_dyn and (best_dyn != top1_bot):
            decision = EMBUDO_FINAL_WAIT_SOFT
            risk_mode = "WAIT_SOFT"
            soft_wait_reason = "best_bot_mismatch"
            reason = f"best_bot_mismatch:{best_dyn}!={top1_bot}"

        # Modulador Pattern V1: aporta contexto/calidad, no veto principal.
        try:
            ctx_top = _ultimo_contexto_operativo_bot(top1_bot)
            ok_pat, why_pat = _micro_pattern_gate_ok(top1_bot, ctx_top)
            if not ok_pat and decision == EMBUDO_FINAL_REAL_NORMAL:
                decision = EMBUDO_FINAL_REAL_MICRO
                risk_mode = "REAL_MICRO"
                degrade_from = "pattern_v1"
                reason = f"pattern->{why_pat}"
            elif (not ok_pat) and decision == EMBUDO_FINAL_REAL_MICRO:
                decision = EMBUDO_FINAL_SHADOW_OK
                risk_mode = "SHADOW_OK"
                degrade_from = "pattern_v1"
                reason = f"pattern_shadow:{why_pat}"
        except Exception:
            pass

        # CTT (fase previa): completamente neutralizado en decisión operativa.
        hard_guard_state = _estado_guardrail_ia_fuerte(force=False)
        hard_guard_hard_block = bool(hard_guard_state.get("hard_block", False))
        cooldown_active = bool(time.time() < float(REAL_COOLDOWN_UNTIL_TS))

        if hard_guard_hard_block and (not reliable) and (auc < 0.50) and (n_samples < int(TRAIN_WARMUP_MIN_ROWS)):
            decision = EMBUDO_FINAL_BLOCK_HARD
            risk_mode = "BLOCK_HARD"
            reason = "guardrail_hard"
            out_hard = "guardrail_hard"
        else:
            out_hard = ""

        if cooldown_active and decision in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO):
            decision = EMBUDO_FINAL_WAIT_SOFT
            risk_mode = "WAIT_SOFT"
            soft_wait_reason = "cooldown"
            reason = "cooldown"

        confirm_deficit = int(max(0, int(confirm_need) - int(confirm_streak)))
        near_prob_floor = float(max(float(floor_eff), float(AUTO_REAL_UNRELIABLE_GATE_MIN_PROB) - float(AUTO_REAL_MICRO_EARLY_CONFIRM_MARGIN)))
        denied_by_early_confirm_only = bool(
            decision in (EMBUDO_FINAL_WAIT_SOFT, EMBUDO_FINAL_SHADOW_OK)
            and (not allow_real)
            and trigger_ok
            and gap_ok
            and (confirm_streak < confirm_need)
            and (soft_wait_reason not in ("marti_contexto_degradado", "best_bot_mismatch", "cooldown"))
        )
        if (
            bool(AUTO_REAL_MICRO_EARLY_CONFIRM_ENABLE)
            and (estado_real in ("SHADOW", "MICRO"))
            and bool(top1_bot)
            and denied_by_early_confirm_only
            and (confirm_deficit <= int(AUTO_REAL_MICRO_EARLY_CONFIRM_DEFICIT_MAX))
            and (int(confirm_streak) >= max(0, int(confirm_need) - 1))
            and (top1_prob >= near_prob_floor)
            and (not cooldown_active)
            and (not hard_guard_hard_block)
        ):
            decision = EMBUDO_FINAL_REAL_MICRO
            risk_mode = "REAL_MICRO"
            reason = "oper_override_micro_early_confirm"
            soft_wait_reason = ""
            degrade_from = "oper_override_micro_early_confirm"

        trigger_ok_micro_soft = bool(
            bool(dgate.get("trigger_ok_micro_soft", False))
            and (decision in (EMBUDO_FINAL_WAIT_SOFT, EMBUDO_FINAL_SHADOW_OK))
            and (estado_real in ("MICRO", "SHADOW"))
            and (not cooldown_active)
            and (not hard_guard_hard_block)
            and (soft_wait_reason not in ("marti_contexto_degradado", "best_bot_mismatch", "cooldown"))
        )
        if trigger_ok_micro_soft:
            decision = EMBUDO_FINAL_REAL_MICRO
            risk_mode = "REAL_MICRO"
            reason = "micro_soft_context_ok"
            soft_wait_reason = ""
            if degrade_from == "none":
                degrade_from = "micro_soft_context_ok"

        if estado_real == "SHADOW" and decision in (EMBUDO_FINAL_WAIT_SOFT, EMBUDO_FINAL_SHADOW_OK):
            ok_shadow_micro, why_shadow_micro = _shadow_micro_gate_ok(candidatos, dgate)
            if ok_shadow_micro:
                decision = EMBUDO_FINAL_REAL_MICRO
                risk_mode = "REAL_MICRO"
                reason = "shadow_micro_gate"
                soft_wait_reason = ""
                if degrade_from == "none":
                    degrade_from = "shadow_micro_gate"

        if estado_real == "SHADOW" and decision in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO):
            decision = EMBUDO_FINAL_REAL_MICRO if decision == EMBUDO_FINAL_REAL_NORMAL else decision
            risk_mode = "REAL_MICRO"
            if degrade_from == "none":
                degrade_from = "shadow_mode"
        if estado_real == "MICRO" and decision == EMBUDO_FINAL_REAL_NORMAL:
            decision = EMBUDO_FINAL_REAL_MICRO
            risk_mode = "REAL_MICRO"
            if degrade_from == "none":
                degrade_from = "micro_mode"

        ia_real_backed = int(decision in (EMBUDO_FINAL_REAL_NORMAL, EMBUDO_FINAL_REAL_MICRO) and ia_model_mature)
        real_source = "IA" if ia_real_backed else "OPERATIVO_NO_IA"

        return _registrar_estado_embudo({
            "decision_final": decision,
            "decision_reason": reason,
            "gate_quality": quality,
            "risk_mode": risk_mode,
            "hard_block_reason": out_hard,
            "soft_wait_reason": soft_wait_reason,
            "top1_bot": top1_bot,
            "top2_bot": top2_bot,
            "gap_value": gap_value,
            "top1_prob": top1_prob,
            "top2_prob": top2_prob,
            "degrade_from": degrade_from,
            "ia_real_backed": int(ia_real_backed),
            "real_source": str(real_source),
            "ia_model_mature": int(ia_model_mature),
        })
    except Exception:
        return _registrar_estado_embudo({"decision_final": EMBUDO_FINAL_WAIT_SOFT, "decision_reason": "embudo_err", "soft_wait_reason": "embudo_err"})


def _umbral_senal_actual_hud() -> float:
    """
    Umbral visual para "IA SEÑALES ACTUALES".
    - En compuerta clásica dinámica: el candado duro es FLOOR (70%).
    - Fuera de ese modo: conserva IA_METRIC_THRESHOLD.
    """
    try:
        if bool(REAL_CLASSIC_GATE):
            return float(DYN_ROOF_FLOOR)
        return float(IA_METRIC_THRESHOLD)
    except Exception:
        return float(IA_METRIC_THRESHOLD)

# Cargar datos bot
def _to_epoch_ctt(v) -> float | None:
    try:
        if v is None:
            return None
        if isinstance(v, (int, float)):
            x = float(v)
            if x > 1e12:
                x /= 1000.0
            return x if x > 0 else None
        txt = str(v).strip()
        if not txt:
            return None
        if txt.isdigit():
            x = float(txt)
            if x > 1e12:
                x /= 1000.0
            return x if x > 0 else None
        dt = pd.to_datetime(txt, errors="coerce", utc=True)
        if pd.isna(dt):
            return None
        return float(dt.timestamp())
    except Exception:
        return None


def _infer_close_ts_ctt(fila_dict: dict) -> float:
    keys = ("close_time", "timestamp_cierre", "epoch_cierre", "exit_epoch", "sell_time", "fecha_cierre", "timestamp", "epoch")
    for k in keys:
        ts = _to_epoch_ctt(fila_dict.get(k))
        if isinstance(ts, (int, float)) and ts > 0:
            return float(ts)
    return float(time.time())


def _close_sig_ctt(bot: str, fila_dict: dict, ts_close: float, result_bin: int) -> str:
    parts = [str(bot), str(int(ts_close)), str(int(result_bin))]
    for k in ("contract_id", "buy_contract_id", "transaction_id", "id", "epoch"):
        v = fila_dict.get(k)
        if v not in (None, ""):
            parts.append(f"{k}:{v}")
            break
    parts.append(str(fila_dict.get("activo", "")))
    return "|".join(parts)


def _registrar_cierre_ctt(bot: str, fila_dict: dict, resultado: str):
    try:
        result_bin = 1 if str(resultado).upper() == "GANANCIA" else 0
        ts_close = float(_infer_close_ts_ctt(fila_dict))
        asset = str(fila_dict.get("activo", "") or "").strip().upper()
        sig = _close_sig_ctt(bot, fila_dict, ts_close, result_bin)
        if sig in CTT_CLOSE_SEEN:
            return
        CTT_CLOSE_SEEN.add(sig)
        CTT_CLOSE_EVENTS.append({"ts": ts_close, "bot": str(bot), "asset": asset, "result": int(result_bin), "sig": sig})
        cutoff_seen = float(time.time()) - float(CTT_CIERRE_LOOKBACK_MAX)
        if len(CTT_CLOSE_SEEN) > 12000:
            # rebuild seen desde deque para evitar crecimiento indefinido
            CTT_CLOSE_SEEN.clear()
            for ev in CTT_CLOSE_EVENTS:
                try:
                    if float(ev.get("ts", 0.0)) >= cutoff_seen:
                        CTT_CLOSE_SEEN.add(str(ev.get("sig")))
                except Exception:
                    continue
    except Exception:
        return


def evaluar_ctt_fase(candidatos: list) -> tuple[list, dict]:
    now = float(time.time())
    W = float(CTT_WAVE_WINDOW_S)
    ttl_wave = float(max(1.0, min(CTT_WAVE_TTL_S, CTT_WAVE_WINDOW_S)))
    lag_min = float(max(0.0, CTT_LAG_MIN_S))
    lag_max = float(max(lag_min, CTT_LAG_MAX_S))
    cutoff = now - max(W, float(CTT_CIERRE_LOOKBACK_MAX))

    eventos = []
    for ev in list(CTT_CLOSE_EVENTS):
        try:
            ts = float(ev.get("ts", 0.0) or 0.0)
            if ts >= cutoff:
                eventos.append(ev)
        except Exception:
            continue

    if not eventos:
        st = {
            "status": "NEUTRAL",
            "regime": "NEUTRAL",
            "gate": "NEUTRAL",
            "reason": "sin_eventos",
            "sample": 0,
            "rezagados_validos": [],
            "no_participantes": list(BOT_NAMES),
            "green_mode": "none",
            "density_cpm": 0.0,
            "diversity_ratio": 0.0,
            "redundancy_high": False,
            "wave_ttl_ok": False,
            "roof_policy": "not_evaluated",
            "roof_delta": 0.0,
        }
        CTT_STATE.update(st)
        return list(candidatos), st

    eventos.sort(key=lambda x: float(x.get("ts", 0.0)), reverse=True)
    base = eventos[0]
    asset_target = str(CTT_ACTIVO_UNICO or "").strip().upper()
    asset = asset_target if asset_target else str(base.get("asset", "") or "").upper()
    t_front = float(base.get("ts", 0.0) or 0.0)

    # Ola activa anclada al frente temporal del grupo.
    ola = []
    for ev in eventos:
        ts = float(ev.get("ts", 0.0) or 0.0)
        if (t_front - ts) > W:
            continue
        ev_asset = str(ev.get("asset", "") or "").upper()
        if asset and ev_asset != asset:
            continue
        ola.append(ev)

    bots_wave = {str(ev.get("bot")) for ev in ola}
    confirmadores = len(bots_wave)
    sample = len(ola)
    wins = sum(int(ev.get("result", 0) or 0) for ev in ola)
    ratio = (wins / sample) if sample > 0 else 0.0
    wave_age_s = max(0.0, now - t_front) if t_front > 0 else None
    ts_min = min((float(ev.get("ts", 0.0) or 0.0) for ev in ola), default=t_front)
    span_s = max(1.0, float(t_front - ts_min)) if sample > 1 else 1.0
    density_cpm = float(sample * 60.0 / span_s)
    wave_ttl_ok = bool((wave_age_s is None) or (wave_age_s <= ttl_wave))

    # Diversidad aproximada: confirmadores únicos sobre tamaño de muestra.
    diversity_ratio = float(confirmadores / max(1, sample))
    redundancy_high = bool(sample >= max(4, int(_ctt_min_confirmadores())) and diversity_ratio < 0.45)

    regime = "NEUTRAL"
    gate = "NEUTRAL"
    status = "NEUTRAL"
    green_mode = "none"
    roof_policy = "normal"
    roof_delta = 0.0
    reason = "muestra_insuficiente"

    enough_evidence = bool(sample > 0 and confirmadores >= int(_ctt_min_confirmadores()) and wave_ttl_ok)
    if enough_evidence:
        if ratio <= float(CTT_THR_RED):
            regime = "RED"
            status = "RED_STRONG"
            gate = "BLOCK"
            roof_policy = "not_evaluated"
            roof_delta = 0.0
            reason = "regime_red_strong"
        elif ratio <= float(CTT_THR_RED_WEAK):
            regime = "RED"
            status = "RED_WEAK"
            gate = "NEUTRAL"
            roof_policy = "harden"
            roof_delta = -abs(float(CTT_RED_WEAK_SCORE_PENALTY))
            reason = "regime_red_weak"
        elif ratio >= float(CTT_THR_GREEN):
            regime = "GREEN"
            advanced_marti = bool(int(ciclo_martingala_siguiente()) > 1)
            green_operable = (
                ratio >= float(CTT_THR_GREEN_OPERABLE)
                and density_cpm >= float(CTT_DENSITY_MIN_CPM)
                and (not redundancy_high)
            )
            if (not CTT_ENABLE_GREEN_IN_MARTI_ADVANCED) and advanced_marti:
                status = "GREEN_DIAGNOSTIC"
                green_mode = "diagnostic"
                gate = "NEUTRAL"
                roof_policy = "normal"
                reason = "green_marti_brake"
            elif green_operable:
                status = "GREEN_OPERABLE"
                green_mode = "operable"
                gate = "ALLOW_REZAGADOS"
                roof_policy = "soften"
                roof_delta = abs(float(CTT_GREEN_OPERABLE_SCORE_BONUS))
                reason = "green_operable"
            else:
                status = "GREEN_DIAGNOSTIC"
                green_mode = "diagnostic"
                gate = "NEUTRAL"
                roof_policy = "normal"
                reason = "green_diagnostic"
        elif ratio >= float(CTT_THR_GREEN_WEAK):
            regime = "GREEN"
            status = "GREEN_DIAGNOSTIC"
            green_mode = "diagnostic"
            gate = "NEUTRAL"
            roof_policy = "normal"
            reason = "green_weak"
        else:
            status = "NEUTRAL"
            reason = "zona_neutral"
    else:
        if not wave_ttl_ok:
            reason = "wave_ttl_expirada"
        elif sample < 1 or confirmadores < int(_ctt_min_confirmadores()):
            reason = "muestra_insuficiente"

    status = regime

    last_ts_bot = {}
    for ev in eventos:
        b = str(ev.get("bot"))
        if b not in last_ts_bot:
            last_ts_bot[b] = float(ev.get("ts", 0.0) or 0.0)

    rezagados_validos = []
    for b in BOT_NAMES:
        tsb = float(last_ts_bot.get(str(b), 0.0) or 0.0)
        if tsb <= 0:
            continue
        lag = max(0.0, t_front - tsb)
        if lag_min <= lag <= lag_max and wave_ttl_ok:
            rezagados_validos.append(str(b))

    no_participantes = [str(b) for b in BOT_NAMES if str(b) not in bots_wave and str(b) not in set(rezagados_validos)]

    def _adj_score(cand, delta):
        if not isinstance(cand, tuple) or len(cand) < 1:
            return cand
        try:
            sc = float(cand[0])
        except Exception:
            return cand
        sc2 = float(max(0.0, min(1.0, sc + float(delta))))
        tmp = list(cand)
        tmp[0] = sc2
        return tuple(tmp)

    filtrados = list(candidatos)
    if gate == "BLOCK":
        filtrados = []
    elif gate == "ALLOW_REZAGADOS":
        rez_set = set(rezagados_validos)
        filtrados = [_adj_score(c, roof_delta) for c in candidatos if len(c) > 1 and str(c[1]) in rez_set]
    else:
        if roof_policy == "harden" and abs(roof_delta) > 0:
            filtrados = [_adj_score(c, roof_delta) for c in candidatos]
        if str(CTT_NEUTRAL_POLICY).lower() == "block":
            filtrados = []

    st = {
        "status": status,
        "regime": regime,
        "gate": gate,
        "asset": asset or None,
        "t_front": t_front,
        "wave_start": ts_min,
        "wave_age_s": wave_age_s,
        "wave_ttl_ok": wave_ttl_ok,
        "wave_ratio": float(ratio),
        "wave_total": int(sample),
        "confirmadores": int(confirmadores),
        "density_cpm": float(density_cpm),
        "diversity_ratio": float(diversity_ratio),
        "redundancy_high": bool(redundancy_high),
        "green_mode": green_mode,
        "rezagados_validos": list(rezagados_validos),
        "no_participantes": list(no_participantes),
        "sample": int(sample),
        "roof_policy": roof_policy,
        "roof_delta": float(roof_delta),
        "reason": reason,
    }
    CTT_STATE.update(st)
    return filtrados, st

# Cargar datos bot
# Cargar datos bot
async def cargar_datos_bot(bot, token_actual):
    ruta = f"registro_enriquecido_{bot}.csv"
    if not os.path.exists(ruta):
        return

    try:
        snapshot = SNAPSHOT_FILAS.get(bot, 0)

        # Fuente de verdad de owner REAL para no pintar DEMO transitorio en HUD/tabla.
        effective_owner = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else (token_actual if token_actual in BOT_NAMES else next((b for b in BOT_NAMES if estado_bots.get(b, {}).get("token") == "REAL"), None))

        # Sincroniza token visual SIEMPRE, incluso si no entran filas nuevas este tick.
        estado_bots[bot]["token"] = "REAL" if effective_owner == bot else "DEMO"

        # Gate rápido (opcional): si el archivo no creció, salimos sin leer todo el CSV
        actual = contar_filas_csv(bot)
        if actual <= snapshot:
            try:
                _sync_round_apply_visual_heartbeat(bot)
            except NameError:
                pass
            except Exception:
                pass
            return

        df = pd.read_csv(ruta, encoding="utf-8", on_bad_lines="skip")
        if df.empty:
            # Lectura temporalmente vacía (archivo en escritura / parse falló).
            # NO resetees SNAPSHOT_FILAS porque provoca re-procesos y ruido.
            return

        # Si snapshot quedó desfasado frente al df real, lo corregimos
        if snapshot >= len(df):
            SNAPSHOT_FILAS[bot] = len(df)
            return

        nuevas = df.iloc[snapshot:]
        # IMPORTANTE: el snapshot debe seguir a df (no a contar_filas_csv),
        # porque read_csv puede saltarse líneas malas con on_bad_lines="skip".
        SNAPSHOT_FILAS[bot] = len(df)

        required_cols = [
            "rsi_9", "rsi_14", "sma_5", "cruce_sma", "breakout",
            "rsi_reversion", "racha_actual", "puntaje_estrategia"
        ]
        try:
            _, _, features_live, _ = get_oracle_assets()
            if isinstance(features_live, list) and features_live:
                for feat in features_live:
                    if isinstance(feat, str) and feat and feat not in required_cols:
                        required_cols.append(feat)
            elif "sma_20" not in required_cols:
                required_cols.append("sma_20")
        except Exception:
            if "sma_20" not in required_cols:
                required_cols.append("sma_20")

        for _, row in nuevas.iterrows():
            fila_dict = canonicalizar_campos_bot_maestro(row.to_dict())

            try:
                if fila_dict.get("payout") in (None, ""):
                    payout_feat = calcular_payout_feature(fila_dict)
                    if payout_feat is not None:
                        fila_dict["payout"] = float(payout_feat)
                if fila_dict.get("volatilidad") in (None, ""):
                    fila_dict["volatilidad"] = float(calcular_volatilidad_simple(fila_dict))
                if fila_dict.get("hora_bucket") in (None, ""):
                    fila_dict["hora_bucket"] = float(calcular_hora_bucket(fila_dict))
                if fila_dict.get("sma_spread") in (None, ""):
                    sp = _calcular_sma_spread_robusto(fila_dict)
                    if sp is not None:
                        fila_dict["sma_spread"] = float(sp)
            except Exception:
                pass

            # Completa proxies CORE13_v2 para evitar falsos "PRE_TRADE incompleto"
            # cuando el bot aún publica formato legacy en filas no cerradas.
            try:
                fila_dict = _enriquecer_scalping_features_row(fila_dict)
            except Exception:
                pass

            trade_status = str(fila_dict.get("trade_status", "")).strip().upper()
            resultado = normalizar_resultado(fila_dict.get("resultado", ""))

            try:
                ep_dec = int(float(fila_dict.get("epoch", 0) or 0))
                cyc_dec = int(float(fila_dict.get("ciclo_martingala", fila_dict.get("ciclo", 1)) or 1))
            except Exception:
                ep_dec, cyc_dec = 0, 1
            token_dec = "REAL" if effective_owner == bot else "DEMO"
            act_dec = str(fila_dict.get("activo", ""))
            dir_dec = str(fila_dict.get("direction", fila_dict.get("direccion", "")) or "")
            estado_bots[bot]["ia_decision_id"] = f"{bot}|{ep_dec}|C{cyc_dec}|{act_dec}|{dir_dec}|{token_dec}"

            # =========================
            # 1) FILAS NO-CERRADAS (PRE_TRADE / incompletas)
            #    - Calculamos Prob IA para el HUD
            #    - NO tocamos historial, n, ni %éxito (evita los “·” intercalados)
            # =========================
            if resultado not in ("GANANCIA", "PÉRDIDA"):
                # Guarda epoch PRE más reciente para heartbeat ACK (sin depender de filas nuevas constantes)
                try:
                    ep_pre = fila_dict.get("epoch", 0)
                    ep_pre = int(float(ep_pre)) if str(ep_pre).strip() != "" else 0
                    if ep_pre > 0:
                        estado_bots[bot]["ultimo_epoch_pretrade"] = ep_pre
                except Exception:
                    pass

                # Si el bot marcó CERRADO pero no trajo resultado válido,
                # cerramos señal pendiente (si existía) sin contaminar historial.
                if trade_status == "CERRADO":
                    if estado_bots[bot].get("ia_senal_pendiente"):
                        estado_bots[bot]["ia_senal_pendiente"] = False
                        estado_bots[bot]["ia_prob_senal"] = None

                    estado_bots[bot]["token"] = "REAL" if effective_owner == bot else "DEMO"
                    last_update_time[bot] = time.time()
                    continue

                missing = [col for col in required_cols if pd.isna(fila_dict.get(col))]
                if missing:
                    agregar_evento(f"⚠️ {bot}: PRE_TRADE incompleto, faltan {len(missing)} cols: {missing[:5]}")
                    # IMPORTANTE: si falta data, no inventamos 0.0 (queda sin predicción)
                    estado_bots[bot]["prob_ia"] = None
                    estado_bots[bot]["modo_ia"] = "low_data"
                    estado_bots[bot]["ia_ready"] = False

                    meta = leer_model_meta() or {}
                    escribir_ia_ack(bot, fila_dict.get("epoch"), None, "LOW_DATA", meta)

                else:
                    try:
                        prob_ia, modo_ia = oraculo_predict_visible(fila_dict)

                        # Normaliza (evita 'OFF' vs 'off' y valores fuera de rango)
                        modo_norm = str(modo_ia or "low_data").strip().lower()
                        prob_norm = None
                        try:
                            if prob_ia is not None:
                                p = float(prob_ia)
                                if 0.0 <= p <= 1.0:
                                    prob_norm = p
                        except Exception:
                            prob_norm = None

                        prob_norm = _ajustar_prob_operativa(prob_norm)
                        estado_bots[bot]["prob_ia"] = prob_norm
                        estado_bots[bot]["modo_ia"] = modo_norm

                        meta = leer_model_meta() or {}
                        reliable = bool(meta.get("reliable", False))
                        n_inc = contar_filas_incremental()
                        rows = int(n_inc or 0)
                        estado_bots[bot]["ia_ready"] = bool(
                            reliable and (rows >= MIN_FIT_ROWS_LOW) and (modo_norm != "off") and (prob_norm is not None)
                        )

                        escribir_ia_ack(bot, fila_dict.get("epoch"), prob_norm, modo_norm.upper(), meta)

                    except Exception as e:
                        agregar_evento(f"⚠️ {bot}: PRED_FAIL pretrade: {type(e).__name__}")
                        estado_bots[bot]["prob_ia"] = None
                        estado_bots[bot]["modo_ia"] = "low_data"
                        estado_bots[bot]["ia_ready"] = False

                        meta = leer_model_meta() or {}
                        escribir_ia_ack(bot, fila_dict.get("epoch"), None, "LOW_DATA", meta)



                estado_bots[bot]["token"] = "REAL" if effective_owner == bot else "DEMO"
                last_update_time[bot] = time.time()
                continue

            # =========================
            # 2) FILAS CERRADAS (GANANCIA / PÉRDIDA)
            #    - Aquí sí actualizamos historial y estadísticas reales
            # =========================
            _registrar_cierre_ctt(bot, fila_dict, resultado)
            estado_bots[bot]["ultimo_resultado"] = resultado
            estado_bots[bot]["resultados"].append(resultado)
            estado_bots[bot]["tamano_muestra"] += 1

            if resultado == "GANANCIA":
                estado_bots[bot]["ganancias"] += 1
            elif resultado == "PÉRDIDA":
                estado_bots[bot]["perdidas"] += 1

            total = estado_bots[bot]["tamano_muestra"]
            if total > 0:
                estado_bots[bot]["porcentaje_exito"] = (estado_bots[bot]["ganancias"] / total) * 100

            # Cierre especial para REAL manual: SIEMPRE 1 sola operación
            if (
                MODO_REAL_MANUAL
                and estado_bots[bot].get("fuente") == "MANUAL"
                and resultado in ("GANANCIA", "PÉRDIDA")
            ):
                reason = f"REAL manual: {resultado} → una operación y regreso a DEMO"
                cerrar_por_fin_de_ciclo(bot, reason)
                agregar_evento(f"✅ REAL MANUAL cerrado para {bot.upper()} tras {resultado}. Volviendo a DEMO.")

            # --- Contadores de IA: SOLO cuando llega un cierre real ---
            if estado_bots[bot].get("ia_senal_pendiente"):
                prob_senal = estado_bots[bot].get("ia_prob_senal")
                thr_ia = get_umbral_operativo()

                if prob_senal is not None and prob_senal >= thr_ia:
                    estado_bots[bot]["ia_seniales"] += 1
                    if resultado == "GANANCIA":
                        estado_bots[bot]["ia_aciertos"] += 1
                    elif resultado == "PÉRDIDA":
                        estado_bots[bot]["ia_fallos"] += 1

                if prob_senal is not None and prob_senal >= float(AUTO_REAL_THR_MIN):
                    IA90_stats[bot]["n"] += 1
                    if resultado == "GANANCIA":
                        IA90_stats[bot]["ok"] += 1

                n_ia90 = IA90_stats[bot]["n"]
                ok_ia90 = IA90_stats[bot]["ok"]
                if n_ia90 > 0:
                    pct_raw = (ok_ia90 / n_ia90) * 100.0
                    pct_suav = (ok_ia90 + 1) / (n_ia90 + 2) * 100.0
                    IA90_stats[bot]["pct_raw"] = pct_raw
                    IA90_stats[bot]["pct_smooth"] = pct_suav
                    # En HUD principal usamos el porcentaje crudo para mantener
                    # consistencia exacta con la fracción ok/n.
                    IA90_stats[bot]["pct"] = pct_raw
                else:
                    IA90_stats[bot]["pct_raw"] = 0.0
                    IA90_stats[bot]["pct_smooth"] = 50.0
                    IA90_stats[bot]["pct"] = 0.0

                # Cerramos señal pendiente SOLO aquí (en cierre)
                estado_bots[bot]["ia_senal_pendiente"] = False
                estado_bots[bot]["ia_prob_senal"] = None

            estado_bots[bot]["token"] = "REAL" if effective_owner == bot else "DEMO"
            last_update_time[bot] = time.time()

        # Mantén tu pipeline incremental como estaba
        anexar_incremental_desde_bot(bot)

    except Exception as e:
        print(f"⚠️ Error cargando datos para {bot}: {e}")

# Obtener saldo real
async def obtener_saldo_real():
    global saldo_real, ULTIMA_ACT_SALDO
    token_demo, token_real = leer_tokens_usuario()
    if not token_real:
        return
    if not WEBSOCKETS_OK:
        return
    try:
        async with websockets.connect(DERIV_WS_URL) as ws:
            auth_msg = json.dumps({"authorize": token_real})
            await ws.send(auth_msg)
            resp = json.loads(await ws.recv())
            if "error" in resp:
                print(f"⚠️ Error en auth: {resp['error']['message']}")
                return
            bal_msg = json.dumps({"balance": 1, "subscribe": 1})
            await ws.send(bal_msg)
            resp = json.loads(await ws.recv())
            if "error" in resp:
                print(f"⚠️ Error en balance: {resp['error']['message']}")
                return
            if "balance" in resp:
                saldo_real = f"{resp['balance']['balance']:.2f}"
                ULTIMA_ACT_SALDO = time.time()
                _update_saldo_monitor_feed(float(resp["balance"]["balance"]))
    except Exception as e:
        print(f"⚠️ Error obteniendo saldo: {e}")

async def refresh_saldo_real(forzado=False):
    global ULTIMA_ACT_SALDO
    if forzado or time.time() - ULTIMA_ACT_SALDO > REFRESCO_SALDO:
        await obtener_saldo_real()

def obtener_valor_saldo():
    global saldo_real
    try:
        return float(saldo_real)
    except:
        return None

def inicializar_saldo_real(valor):
    global SALDO_INICIAL, META
    SALDO_INICIAL = round(valor, 2)
    META = round(SALDO_INICIAL * 1.20, 2)

# Escuchar teclas
def escuchar_teclas():
    global pausado, salir, reinicio_manual, LIMPIEZA_PANEL_HASTA, HUD_VISIBLE
    global PENDIENTE_FORZAR_BOT, PENDIENTE_FORZAR_INICIO, PENDIENTE_FORZAR_EXPIRA

    bot_map = {'5': 'fulll45', '6': 'fulll46', '7': 'fulll47', '8': 'fulll48', '9': 'fulll49', '0': 'fulll50'}
    last_key_time = 0  # debounce 200 ms

    while True:
        if MODAL_ACTIVO:
            time.sleep(0.1); continue

        now = time.time()
        if HAVE_MSVCRT and msvcrt.kbhit():
            if now - last_key_time < 0.2:
                time.sleep(0.05); continue
            last_key_time = now

            try:
                k = msvcrt.getch()
                if k in (b'\x00', b'\xe0'):  
                    msvcrt.getch(); continue
                k = k.decode("utf-8", errors="ignore").lower()
            except:
                continue

            if k == "s":
                print("\n\n🔴 Saliendo del programa..."); salir = True; break
            elif k == "p":
                pausado = True; print("\n⏸️ Programa pausado. Presiona [C] para continuar.")
            elif k == "c":
                pausado = False; print("\n▶️ Programa reanudado.")
            elif k == "r":
                reinicio_manual = True; print("\n🔁 Reinicio de Martingala solicitado.")
            elif k == "t":
                tok = leer_token_actual(); print(f"\n🔍 TOKEN ACTUAL: {tok or 'none'}")
            elif k == "l":
                LIMPIEZA_PANEL_HASTA = time.time() + 15; print("\n🎹 Limpieza visual…")
            elif k == "d":
                reiniciar_completo(borrar_csv=False, limpiar_visual_segundos=15, modo_suave=True); print("\n🧽 Limpieza dura ejecutada.")
            elif k == "g":
                reproducir_evento("test", es_demo=True, dentro_gatewin=True); print("\n🎵 Test de audio…")
            elif k == "e":
                try:
                    # Cooldown anti-repetición (Windows repite tecla y entrena 2 veces)
                    if "LAST_MANUAL_RETRAIN_TS" not in globals():
                        globals()["LAST_MANUAL_RETRAIN_TS"] = 0.0
                    nowt = time.time()
                    if (nowt - float(globals()["LAST_MANUAL_RETRAIN_TS"])) < 30.0:
                        agregar_evento("🧠 Entrenamiento ignorado (cooldown 30s).")
                    else:
                        globals()["LAST_MANUAL_RETRAIN_TS"] = nowt
                        maybe_retrain(force=True)
                        print("\n🧠 Entrenamiento forzado.")
                except Exception as e:
                    print(f"\n⚠️ No se pudo entrenar: {e}")

            elif k in bot_map:
                PENDIENTE_FORZAR_BOT = bot_map[k]
                PENDIENTE_FORZAR_INICIO = time.time()
                PENDIENTE_FORZAR_EXPIRA = PENDIENTE_FORZAR_INICIO + VENTANA_DECISION_IA_S
                agregar_evento(f"🎯 Bot seleccionado: {PENDIENTE_FORZAR_BOT}. Elige ciclo [1..{MAX_CICLOS}] o ESC.")
                with RENDER_LOCK:
                    mostrar_panel()

            elif PENDIENTE_FORZAR_BOT and k.isdigit() and k in [str(i) for i in range(1, MAX_CICLOS+1)]:
                ciclo = int(k)
                bot_sel = PENDIENTE_FORZAR_BOT
                PENDIENTE_FORZAR_BOT = None
                PENDIENTE_FORZAR_INICIO = 0.0
                PENDIENTE_FORZAR_EXPIRA = 0.0
                forzar_real_manual(bot_sel, ciclo)

            elif PENDIENTE_FORZAR_BOT and k == "\x1b":  # ESC
                agregar_evento("❎ Forzar REAL cancelado.")
                PENDIENTE_FORZAR_BOT = None
                PENDIENTE_FORZAR_INICIO = 0.0
                PENDIENTE_FORZAR_EXPIRA = 0.0
                with RENDER_LOCK:
                    mostrar_panel()

        else:
            time.sleep(0.05)

if sys.stdout.isatty():
    threading.Thread(target=escuchar_teclas, daemon=True).start()

# Main - Añadida pasada inicial para sincronizar HUD con CSV existentes
DIAGNOSTIC_MODE = ("--diagnostico" in sys.argv) or (os.getenv("MAESTRO_DIAGNOSTICO", "0") == "1")


def _log_exception(tag: str, exc: Exception | None = None):
    try:
        ts = time.strftime('%F %T')
        detail = traceback.format_exc()
        if exc is not None and (not detail or detail.strip() == "NoneType: None"):
            detail = f"{type(exc).__name__}: {exc}"
        with open("crash.log", "a", encoding="utf-8") as f:
            f.write(f"[{ts}] {tag}\n{detail}\n")
    except Exception:
        pass



def _auditar_saturacion_features_bot(bot: str, lookback: int = 800) -> dict:
    """Diagnóstico ligero de features casi-constantes en CERRADO."""
    out = {"ok": False, "bot": bot, "n": 0, "dominance": {}}
    ruta = f"registro_enriquecido_{bot}.csv"
    if not os.path.exists(ruta):
        return out
    try:
        df = pd.read_csv(ruta, sep=",", encoding="utf-8", engine="python", on_bad_lines="skip")
    except Exception:
        return out
    if df is None or df.empty:
        return out
    try:
        if "resultado" in df.columns:
            rr = df["resultado"].astype(str).str.upper().str.strip()
            df = df[rr.isin(["GANANCIA", "PÉRDIDA", "PERDIDA"])].copy()
    except Exception:
        pass
    if df.empty:
        return out
    if int(lookback) > 0 and len(df) > int(lookback):
        df = df.tail(int(lookback)).copy()

    cols = ["cruce_sma", "breakout", "rsi_reversion", "puntaje_estrategia"]
    out["n"] = int(len(df))
    out["ok"] = True
    for c in cols:
        if c not in df.columns:
            continue
        s = pd.to_numeric(df[c], errors="coerce").dropna()
        if s.empty:
            continue
        vc = s.value_counts(dropna=False)
        dom = float(vc.iloc[0]) / float(max(1, len(s)))
        out["dominance"][c] = float(dom)
    return out


def _auditar_saturacion_todos_bots(lookback: int = 800) -> dict:
    """Resume saturación de señales por bot (no bloqueante)."""
    out = {"bots": {}, "hot_bots": []}
    for b in BOT_NAMES:
        rep = _auditar_saturacion_features_bot(b, lookback=lookback)
        out["bots"][b] = rep
        dom = rep.get("dominance", {}) if isinstance(rep, dict) else {}
        hot = [k for k, v in dom.items() if isinstance(v, (int, float)) and v >= 0.90]
        if hot:
            out["hot_bots"].append({"bot": b, "features": hot, "dominance": dom})
    return out


def _auditar_calidad_incremental(path: str = "dataset_incremental.csv") -> dict:
    """Chequeo liviano de calidad de labels para detectar n-meta inflado."""
    out = {"ok": False, "rows": 0, "valid": 0, "invalid": 0, "path": path}
    if not os.path.exists(path):
        return out
    try:
        df = pd.read_csv(path, sep=",", encoding="utf-8", engine="python", on_bad_lines="skip")
    except Exception:
        return out
    if df is None or df.empty:
        out["ok"] = True
        return out
    out["rows"] = int(len(df))
    if "result_bin" not in df.columns:
        out["invalid"] = int(len(df))
        out["ok"] = True
        return out
    rb = pd.to_numeric(df["result_bin"], errors="coerce")
    valid_mask = rb.isin([0, 1])
    out["valid"] = int(valid_mask.sum())
    out["invalid"] = int((~valid_mask).sum())
    out["ok"] = True
    return out

def _auditar_salud_features_incremental(path: str = "dataset_incremental.csv") -> dict:
    """Diagnóstico de presencia/variación para core-13 en incremental."""
    core13 = [
        "rsi_9","rsi_14","sma_5","sma_spread","cruce_sma","breakout",
        "rsi_reversion","racha_actual","payout","puntaje_estrategia",
        "volatilidad","es_rebote","hora_bucket",
    ]
    out = {"ok": False, "path": path, "rows": 0, "missing": [], "dominance": {}, "low_var": []}
    if not os.path.exists(path):
        return out
    try:
        df = pd.read_csv(path, sep=",", encoding="utf-8", engine="python", on_bad_lines="skip")
    except Exception:
        return out
    if df is None or df.empty:
        out["ok"] = True
        return out

    out["rows"] = int(len(df))
    out["missing"] = [c for c in core13 if c not in df.columns]
    for c in core13:
        if c not in df.columns:
            continue
        s = pd.to_numeric(df[c], errors="coerce").dropna()
        if s.empty:
            out["low_var"].append(c)
            out["dominance"][c] = 1.0
            continue
        top = float(s.value_counts(normalize=True, dropna=True).iloc[0])
        uniq = int(s.nunique(dropna=True))
        out["dominance"][c] = top
        if uniq <= 2:
            out["low_var"].append(c)

    out["ok"] = True
    return out



def _boot_health_check():
    msgs = []
    try:
        if not WEBSOCKETS_OK:
            msgs.append("⚠️ Dependencia faltante: websockets (sin WS/saldo, resto del HUD sigue).")
        if not PYGAME_OK:
            msgs.append("⚠️ Dependencia faltante: pygame (audio desactivado, ejecución continúa).")
        csv_presentes = [b for b in BOT_NAMES if os.path.exists(f"registro_enriquecido_{b}.csv")]
        if not csv_presentes:
            msgs.append("⚠️ No hay CSV enriquecidos de bots todavía; esperando generación de datos.")
        if not os.access(os.getcwd(), os.W_OK):
            msgs.append("⚠️ Sin permisos de escritura en cwd (no se podrán persistir logs/modelos).")

        # Señales congeladas: diagnóstico operativo rápido por bot (no bloqueante)
        sat_all = _auditar_saturacion_todos_bots(lookback=900)
        hot_bots = sat_all.get("hot_bots", []) if isinstance(sat_all, dict) else []
        sat_parts = []
        for hb in hot_bots[:6]:
            bot = hb.get("bot", "?")
            dom = hb.get("dominance", {}) if isinstance(hb.get("dominance", {}), dict) else {}
            feats = hb.get("features", []) if isinstance(hb.get("features", []), list) else []
            hot = [f"{k}={float(dom.get(k, 0.0))*100:.1f}%" for k in feats]
            if hot:
                sat_parts.append(f"{bot}: " + ", ".join(hot))
        if sat_parts:
            msgs.append("⚠️ Features saturadas detectadas: " + " | ".join(sat_parts))

        # Calidad de labels del incremental (si hay inválidas, la IA aprende con humo)
        incq = _auditar_calidad_incremental("dataset_incremental.csv")
        if incq.get("ok", False):
            rows = int(incq.get("rows", 0) or 0)
            invalid = int(incq.get("invalid", 0) or 0)
            valid = int(incq.get("valid", 0) or 0)
            if rows > 0 and invalid > 0:
                msgs.append(f"⚠️ Incremental con labels inválidas: valid={valid}, invalid={invalid}, total={rows}.")

        # Salud de features core-13: presencia + variación + dominancia
        featq = _auditar_salud_features_incremental("dataset_incremental.csv")
        if featq.get("ok", False):
            miss = featq.get("missing", []) or []
            low = featq.get("low_var", []) or []
            dom = featq.get("dominance", {}) or {}
            hot = [k for k, v in dom.items() if isinstance(v, (int, float)) and v >= FEATURE_MAX_DOMINANCE]
            if miss:
                msgs.append("⚠️ Incremental core-13 faltantes: " + ", ".join(miss))
            if low:
                msgs.append("⚠️ Incremental features con baja variación (nunique<=2): " + ", ".join(low))
            if hot:
                tops = [f"{k}={float(dom.get(k, 0.0))*100:.1f}%" for k in hot]
                msgs.append("⚠️ Incremental features dominantes (>90%): " + ", ".join(tops))
    except Exception as e:
        msgs.append(f"⚠️ Health-check parcial con error: {e}")
    return msgs


async def main():
    global salir, pausado, reinicio_manual, SALDO_INICIAL
    global PENDIENTE_FORZAR_BOT, PENDIENTE_FORZAR_INICIO, PENDIENTE_FORZAR_EXPIRA, REAL_OWNER_LOCK
    global REAL_LOCK_MISMATCH_SINCE

    try:
        set_etapa("BOOT_01", "Inicializando main()", anunciar=True)
        # Seguridad: NO borrar real.lock al arrancar; evita carreras entre instancias.
        set_etapa("BOOT_02", "Leyendo tokens de usuario")
        tokens = leer_tokens_usuario()
        if tokens == (None, None):
            print("⚠️ Tokens ausentes. Modo sin-saldo activo (HUD/IA continúan).")
        init_audio()
        for _msg in _boot_health_check():
            print(_msg)
            try:
                agregar_evento(_msg)
            except Exception:
                pass

        if DIAGNOSTIC_MODE:
            print("🧪 MODO DIAGNÓSTICO activo: sin auto-operación REAL.")
            globals()["MODO_REAL_MANUAL"] = True

        if RESET_ON_START:
            for nb in BOT_NAMES:
                resetear_csv_bot(nb)
            resetear_incremental_y_modelos(borrar_modelos=True)
            resetear_estado_hud(estado_bots)
            print("🧼 Sesión limpia: CSVs de bots, dataset incremental y estado HUD reiniciados.")
        elif AUTO_REPAIR_ON_START:
            for _msg in _asegurar_estructura_datos_inicio():
                print(_msg)
                try:
                    agregar_evento(_msg)
                except Exception:
                    pass
        reiniciar_completo(borrar_csv=False, limpiar_visual_segundos=15, modo_suave=True)
        loop = asyncio.get_running_loop()
        set_main_loop(loop)
        await refresh_saldo_real(forzado=True)
        valor = obtener_valor_saldo()
        if valor is not None:
            inicializar_saldo_real(valor)

        set_etapa("BOOT_03", "Backfill y primer entrenamiento")
        # Backfill IA desde los logs enriquecidos
        try:
            backfill_incremental(ultimas=1500)
        except Exception as e:
            agregar_evento(f"⚠️ IA: error en backfill inicial: {e}")

        # Intentar un primer entrenamiento, si ya hay suficientes filas
        try:
            maybe_retrain(force=True)
        except Exception as e:
            agregar_evento(f"⚠️ IA: error al intentar entrenar tras el backfill: {e}")

        # Diagnóstico BOOT de desalineación campeón/dataset + degradación temporal (no bloquea operativa)
        try:
            meta_boot = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
            audit_boot = auditar_refresh_campeon_stale(meta_boot, force_log=True)
            if bool(audit_boot.get("needs_review", False)):
                maybe_retrain(force=True)
            auditar_degradacion_temporal_modelo()
        except Exception as e:
            agregar_evento(f"⚠️ IA: auditoría boot parcial con error: {e}")

        set_etapa("BOOT_04", "Sincronizando HUD con CSV")
        # Pasada inicial para sincronizar HUD con CSV existentes
        _sync_round_bootstrap_state(force=False)
        token_actual_loop = "--"  # Dummy para carga inicial
        for bot in BOT_NAMES:
            await cargar_datos_bot(bot, token_actual_loop)

        while True:
            if salir:
                set_etapa("STOP", "Señal de salida detectada", anunciar=True)
                break
            actualizar_pause_state_maestro()
            if maestro_en_pausa():
                try:
                    _maybe_log_pause_state(force=False)
                    await refresh_saldo_real(forzado=False)
                    with RENDER_LOCK:
                        mostrar_panel()
                except Exception:
                    pass
                await asyncio.sleep(0.8)
                continue
            if pausado:
                await asyncio.sleep(1)
                continue
            if reinicio_manual:
                reinicio_manual = False
                reiniciar_completo(borrar_csv=False, limpiar_visual_segundos=15, modo_suave=True)
                await refresh_saldo_real(forzado=True)

            try:  
                set_etapa("TICK_01")
                token_actual_loop = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else (leer_token_actual() or next((b for b in BOT_NAMES if estado_bots.get(b, {}).get("token") == "REAL"), None))

                # Reconciliación anti-desincronía maestro↔bots:
                # si memoria dice REAL pero token_actual.txt ya está en none por varios segundos,
                # liberamos lock fantasma para permitir nuevas asignaciones REAL correctas.
                owner_mem_now = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else None
                owner_file_now = leer_token_archivo_raw()
                if owner_mem_now and (owner_file_now is None):
                    if REAL_LOCK_MISMATCH_SINCE <= 0.0:
                        REAL_LOCK_MISMATCH_SINCE = time.time()
                    elif (time.time() - REAL_LOCK_MISMATCH_SINCE) >= float(REAL_LOCK_RECONCILE_S):
                        agregar_evento(f"🩹 Reconciliación lock REAL: liberando owner fantasma {owner_mem_now.upper()} (archivo token ya está en none).")
                        try:
                            _set_ui_token_holder(None)
                        except Exception:
                            pass
                        REAL_OWNER_LOCK = None
                        REAL_LOCK_MISMATCH_SINCE = 0.0
                        token_actual_loop = leer_token_actual() or None
                else:
                    REAL_LOCK_MISMATCH_SINCE = 0.0
                # Heartbeat: mantiene ACK alineado al HUD aunque no entren filas nuevas ese tick.
                refrescar_ia_ack_desde_hud(intervalo_s=1.0)
                _sync_round_tick_maestro()

                try:
                    last_a = globals().get("_IA_BOOT_STALE_AUDIT_TS", 0.0) or 0.0
                    if (time.time() - float(last_a)) >= 90.0:
                        globals()["_IA_BOOT_STALE_AUDIT_TS"] = float(time.time())
                        meta_tick = _ORACLE_CACHE.get("meta") or leer_model_meta() or {}
                        audit_tick = auditar_refresh_campeon_stale(meta_tick, force_log=False)
                        if bool(audit_tick.get("needs_review", False)):
                            maybe_retrain(force=True)
                        auditar_degradacion_temporal_modelo()
                except Exception:
                    pass
                owner_mem = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else None
                owner_file = token_actual_loop if token_actual_loop in BOT_NAMES else None
                activo_real = owner_mem or owner_file or next((b for b in BOT_NAMES if estado_bots[b]["token"] == "REAL"), None)
                if activo_real in BOT_NAMES:
                    _set_ui_token_holder(activo_real)
                    _enforce_single_real_standby(activo_real)
                for bot in BOT_NAMES:
                    try:  # Aislamiento per-bot para evitar skips globales
                        if reinicio_forzado.is_set():
                            # Menos ruido: no agregar evento si repetido
                            reinicio_forzado.clear()
                            # No mostrar_panel inmediato; dejar al tick
                            break
                        await cargar_datos_bot(bot, token_actual_loop)
                        # Evita desincronizar REAL por inactividad normal durante contrato.
                        # El owner REAL se vigila en TICK_02 (watchdog sin salida a DEMO).
                        if time.time() - last_update_time[bot] > 60:
                            if estado_bots.get(bot, {}).get("token") != "REAL":
                                reiniciar_bot(bot)
                    except Exception as e_bot:
                        agregar_evento(f"⚠️ Error en {bot}: {e_bot}")
                else:
                    # Reentreno periódico no bloqueante (evita quedarse en OFF si boot ocurrió con pocos datos)
                    try:
                        now_rt = time.time()
                        if (now_rt - float(globals().get("_LAST_AUTO_RETRAIN_TICK", 0.0) or 0.0)) >= float(AUTO_RETRAIN_TICK_S):
                            globals()["_LAST_AUTO_RETRAIN_TICK"] = now_rt
                            maybe_retrain(force=False)
                    except Exception:
                        pass

                    set_etapa("TICK_02")
                    # Watchdog para REAL pegado
                    ahora = time.time()
                    for bot in BOT_NAMES:
                        if estado_bots[bot]["token"] == "REAL":
                            t_last = last_update_time.get(bot, 0)
                            t_real = estado_bots[bot].get("real_activado_en", 0.0)
                            # Si lleva demasiado sin actualizarse desde que entró a REAL:
                            # NO salir a DEMO aquí: la salida solo ocurre con cierre GANANCIA/PÉRDIDA.
                            if t_real > 0 and (ahora - max(t_last, t_real) > REAL_TIMEOUT_S):
                                first_warn = float(estado_bots[bot].get("real_timeout_first_warn", 0.0) or 0.0)
                                if first_warn <= 0.0:
                                    estado_bots[bot]["real_timeout_first_warn"] = ahora
                                    agregar_evento(f"⏱️ Seguridad: {bot} sin actividad reciente en REAL. Esperando cierre por {REAL_STUCK_FORCE_RELEASE_S}s antes de liberar.")
                                elif (ahora - first_warn) > REAL_STUCK_FORCE_RELEASE_S:
                                    agregar_evento(f"🧯 Timeout REAL en {bot}: sin cierre confirmado. Liberando a DEMO sin avanzar martingala.")
                                    cerrar_por_fin_de_ciclo(bot, "Timeout sin cierre")
                                    activo_real = None
                                    break

                    for bot in BOT_NAMES:
                        if estado_bots[bot]["token"] == "REAL":
                            # Detecta el último cierre REAL de forma robusta (sin depender de SNAPSHOT_FILAS,
                            # porque TICK_01 ya puede haber avanzado el snapshot antes de este bloque).
                            cierre_info = detectar_cierre_martingala(
                                bot,
                                min_fila=REAL_ENTRY_BASELINE.get(bot, 0),
                                require_closed=True,
                                require_real_token=True,
                                expected_ciclo=estado_bots.get(bot, {}).get("ciclo_actual", None),
                            )

                            # Ventana anti-stale tras activar REAL (protección vigente)
                            if time.time() < (estado_bots[bot].get("ignore_cierres_hasta") or 0):
                                cierre_info = None

                            # Cierre inmediato: en REAL siempre 1 operación y vuelve a DEMO (gane o pierda)
                            if cierre_info and isinstance(cierre_info, tuple) and len(cierre_info) >= 4:
                                res, monto, ciclo, payout_total = cierre_info
                                sig = (res, round(float(monto or 0.0), 2), int(ciclo or 0), round(float(payout_total or 0.0), 4))

                                # Evita reprocesar el mismo cierre en ticks consecutivos
                                if sig == LAST_REAL_CLOSE_SIG.get(bot):
                                    continue

                                LAST_REAL_CLOSE_SIG[bot] = sig

                                if res in ("GANANCIA", "PÉRDIDA"):
                                    saldo_antes = obtener_valor_saldo()
                                    registrar_resultado_real(res, bot=bot, ciclo_operado=ciclo)
                                    try:
                                        await refresh_saldo_real(forzado=True)
                                    except Exception:
                                        pass
                                    saldo_despues = obtener_valor_saldo()
                                    try:
                                        _registrar_real_close_trace({
                                            "bot": bot,
                                            "contract_id": estado_bots.get(bot, {}).get("id_contrato"),
                                            "resultado": res,
                                            "saldo_real_antes": float(saldo_antes) if isinstance(saldo_antes, (int, float)) else None,
                                            "saldo_real_despues": float(saldo_despues) if isinstance(saldo_despues, (int, float)) else None,
                                            "ciclo": int(ciclo or 0),
                                            "source_real": estado_bots.get(bot, {}).get("fuente"),
                                        })
                                    except Exception:
                                        pass
                                    if res == "GANANCIA":
                                        cerrar_por_fin_de_ciclo(bot, "Ganancia en REAL (fin de turno)")
                                    else:
                                        cerrar_por_fin_de_ciclo(bot, "Pérdida en REAL (fin de turno)")
                                    activo_real = None
                                    break

                    if not activo_real:
                        set_etapa("TICK_03")

                        # 🔒 Lock estricto: una sola inversión REAL a la vez.
                        # Si token_actual.txt o el estado en memoria ya tienen dueño REAL,
                        # no evaluamos ni promovemos otro bot aunque cumpla umbral.
                        owner_lock = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else leer_token_actual()
                        holder_memoria = next((b for b in BOT_NAMES if estado_bots.get(b, {}).get("token") == "REAL"), None)
                        lock_activo = (owner_lock in BOT_NAMES) or (holder_memoria in BOT_NAMES)
                        if lock_activo:
                            activo_real = owner_lock if owner_lock in BOT_NAMES else holder_memoria
                            _enforce_single_real_standby(activo_real)

                        # Umbral maestro calibrado con históricos de Prob IA (top quantil),
                        # acotado por [AUTO_REAL_THR_MIN .. AUTO_REAL_THR] para activar REAL
                        # usando los valores altos observados recientemente.
                        if REAL_CLASSIC_GATE:
                            umbral_ia_real = float(_umbral_real_operativo_actual())
                            dyn_gate = _actualizar_compuerta_techo_dinamico()
                            if isinstance(dyn_gate, dict) and bool(dyn_gate.get("new_open", False)):
                                agregar_evento(
                                    "🧭 Compuerta REAL abierta: "
                                    f"{dyn_gate.get('best_bot','--')} | "
                                    f"p_best={float(dyn_gate.get('p_best',0.0))*100:.1f}% "
                                    f"roof_eff={float(dyn_gate.get('roof_eff',0.0))*100:.1f}% "
                                    f"floor={float(dyn_gate.get('floor_eff',0.0))*100:.1f}% "
                                    f"gap_ok={'sí' if dyn_gate.get('gap_ok') else 'no'} "
                                    f"cross={'sí' if dyn_gate.get('crossed_up') else 'no'} "
                                    f"suceso={'sí' if dyn_gate.get('suceso_ok') else 'no'} "
                                    f"mode={dyn_gate.get('gate_mode','A')} "
                                    f"stall={int(float(dyn_gate.get('stall_s',0.0))//60)}m "
                                    f"confirm={int(dyn_gate.get('confirm_streak',0))}/{int(dyn_gate.get('confirm_need', DYN_ROOF_CONFIRM_TICKS))}"
                                )
                        else:
                            umbral_ia_real = max(float(REAL_TRIGGER_MIN), float(get_umbral_real_calibrado()))
                            dyn_gate = None

                        # Saldo informativo: no bloquear por colchón completo, solo por ciclo ejecutable.
                        try:
                            saldo_val = float(obtener_valor_saldo() or 0.0)
                        except Exception:
                            saldo_val = 0.0
                        costo_ciclo1 = float(MARTI_ESCALADO[0])
                        costo_plan = float(sum(MARTI_ESCALADO[:max(1, int(MAX_CICLOS))]))

                        # Candidatos: prob válida, reciente, IA activa (no OFF)
                        candidatos = []
                        raw_rank_scores = []
                        pattern_col_eval = dict(PATTERN_COL_LAST_STATE)
                        if bool(PATTERN_ENABLE):
                            try:
                                cols = _construir_matriz_resultados_columnas(estado_bots, BOT_NAMES, window=int(PATTERN_COL_WINDOW))
                                cols_stats = [
                                    evaluar_patron_columna_verde(c, thr80=float(PATTERN_COL80_THRESHOLD), thr90=float(PATTERN_COL90_THRESHOLD))
                                    for c in cols
                                ]
                                col_actual = dict(cols_stats[0]) if cols_stats else {}
                                col_anterior = dict(cols_stats[1]) if len(cols_stats) > 1 else {}
                                streak80 = calcular_strong_streak(cols_stats, thr=float(PATTERN_COL80_THRESHOLD))
                                streak90 = calcular_strong_streak(cols_stats, thr=float(PATTERN_COL90_THRESHOLD))
                                col_actual["strong_streak_80"] = int(streak80)
                                col_actual["strong_streak_90"] = int(streak90)
                                rebote_hist = calcular_rebote_x_to_check_historico(cols, lookback=int(PATTERN_REBOTE_LOOKBACK))
                                pattern_col_eval = clasificar_estado_patron(
                                    col_actual=col_actual,
                                    col_anterior=col_anterior,
                                    rebote_rate_hist=rebote_hist.get("rebote_rate_hist", None),
                                    rebote_samples_hist=int(rebote_hist.get("rebote_samples_hist", 0) or 0),
                                )
                                _b_pat, _p_pat, _d_pat = aplicar_ajuste_patron_score(pattern_col_eval)
                                pattern_col_eval.update({
                                    "total_verdes_col_actual": int(col_actual.get("total_verdes", 0) or 0),
                                    "total_rojos_col_actual": int(col_actual.get("total_rojos", 0) or 0),
                                    "rebote_rate_hist": rebote_hist.get("rebote_rate_hist", None),
                                    "rebote_samples_hist": int(rebote_hist.get("rebote_samples_hist", 0) or 0),
                                    "total_x_hist": int(rebote_hist.get("total_x_hist", 0) or 0),
                                    "total_x_rebote_hist": int(rebote_hist.get("total_x_rebote_hist", 0) or 0),
                                    "pattern_delta": float(_d_pat),
                                    "pattern_bonus_penalty": float(_d_pat),
                                })
                            except Exception:
                                pattern_col_eval = dict(PATTERN_COL_LAST_STATE)
                        globals()["PATTERN_COL_LAST_STATE"] = dict(pattern_col_eval)
                        diag_gate = _leer_gate_desde_diagnostico(ttl_s=60.0)
                        # CTT como autoridad contextual superior: si hay veto duro,
                        # no se evalúan señales individuales/techo en este tick.
                        ctt_pre_eval = None
                        try:
                            _dummy, ctt_pre_eval = evaluar_ctt_fase([])
                        except Exception:
                            ctt_pre_eval = None

                        if str((ctt_pre_eval or {}).get("gate", "NEUTRAL")) == "BLOCK":
                            ctt_status_pre = str((ctt_pre_eval or {}).get("status", "RED_STRONG"))
                            ctt_reason_pre = str((ctt_pre_eval or {}).get("reason", "ctt_block"))
                            agregar_evento(
                                f"🟫 CTT modo prudente ({ctt_status_pre}): embudo pasa a evaluación blanda ({ctt_reason_pre})."
                            )
                        _log_operational_degradation_runtime(ttl_s=60.0)

                        for b in BOT_NAMES:
                            try:
                                modo_b = str(estado_bots.get(b, {}).get("modo_ia", "off")).lower()
                                if modo_b == "off":
                                    continue
                                if not ia_prob_valida(b, max_age_s=12.0):
                                    continue
                                # Redundancia: no bloquear en seco; aplicar penalización de score y desempate posterior.
                                redundante_tick = bool(estado_bots.get(b, {}).get("ia_input_redundante", False))

                                p = _prob_ia_operativa_bot(b, default=None)
                                if not isinstance(p, (int, float)):
                                    continue
                                # Primer filtro suave: alinear con el mismo umbral operativo/adaptativo del embudo real.
                                ctx_pre = _ultimo_contexto_operativo_bot(b)
                                piso_operativo, _piso_reason = _umbral_real_por_bot_contexto(b, ctx_pre, umbral_ia_real)
                                if float(p) < float(piso_operativo):
                                    continue

                                # Embudo refactor v1:
                                # - Fase 1 selecciona campeón provisional por prob operativa.
                                # - Los candados blandos/moduladores se evalúan después sobre top-1.
                                regime_score = _score_regimen_contexto(ctx_pre)
                                ctx = ctx_pre

                                # 1) Gate de calidad por racha/rebote (priorizar precisión real)
                                ctx = _ultimo_contexto_operativo_bot(b)
                                racha_now = float(ctx.get("racha_actual", 0.0) or 0.0)
                                rebote_now = float(ctx.get("es_rebote", 0.0) or 0.0)
                                if racha_now <= float(GATE_RACHA_NEG_BLOQUEO):
                                    if not (bool(GATE_PERMITE_REBOTE_EN_NEG) and rebote_now >= 0.5):
                                        continue

                                # 2) Validación por régimen/activo (evita mezclar HZ con mal tramo reciente)
                                activo_now = str(ctx.get("activo", "") or "").strip()
                                ok_reg, wr_reg, n_reg = _gate_regimen_activo_ok(b, activo=activo_now)
                                if not ok_reg:
                                    agregar_evento(
                                        f"🧯 Gate régimen: {b}/{activo_now or 'NA'} bloqueado "
                                        f"(WR{n_reg}={wr_reg*100:.1f}% < {GATE_ACTIVO_MIN_WR*100:.1f}%)."
                                    )
                                    continue

                                # 3) Gate por segmento (payout/vol/hora) para ejecutar donde hay más señal estable
                                ok_seg, wr_seg, n_seg, seg_key = _gate_segmento_ok(b, ctx)
                                if not ok_seg:
                                    agregar_evento(
                                        f"🧱 Gate segmento: {b}/{seg_key} bloqueado "
                                        f"(WR{n_seg}={wr_seg*100:.1f}% < {GATE_SEGMENTO_MIN_WR*100:.1f}%)."
                                    )
                                    continue

                                # 4) Capa A del embudo: score de régimen
                                regime_score = _score_regimen_contexto(ctx)
                                if regime_score < float(REGIME_GATE_MIN_SCORE):
                                    continue

                                # 5) Índice de evidencia por bot en umbral objetivo (evita inflar 0.70+ sin soporte)
                                ev = _evidencia_bot_umbral_objetivo(b)
                                ev_n = int(ev.get("n", 0) or 0)
                                ev_wr = float(ev.get("wr", 0.0) or 0.0)
                                ev_lb = float(ev.get("lb", 0.0) or 0.0)
                                if (ev_n >= int(EVIDENCE_MIN_N_HARD)) and (not bool(ev.get("ok_hard", True))):
                                    agregar_evento(
                                        f"🧪 Evidencia: {b} bloqueado (n={ev_n}, WR={ev_wr*100:.1f}%, LB={ev_lb*100:.1f}% < LB_min {EVIDENCE_MIN_LB_HARD*100:.1f}%)."
                                    )
                                    continue

                                # Candado blando: con muestra intermedia exigimos LB mínimo intermedio.
                                if (ev_n >= int(EVIDENCE_MIN_N_SOFT)) and (ev_lb < float(EVIDENCE_MIN_LB_SOFT)):
                                    continue

                                # 6) Prob REAL posterior (modelo + régimen + evidencia + bound)
                                p_post = _prob_real_posterior(float(p), float(regime_score), int(ev_n), float(ev_wr), float(ev_lb))

                                # Guardas por bot (alineadas al HUD): evitar promoción cuando hay
                                # desalineación severa entre probabilidad y performance real reciente.
                                if (ev_n >= int(EVIDENCE_MIN_N_SOFT)) and (ev_wr < float(IA_PROMO_MIN_WR_POR_BOT)):
                                    agregar_evento(
                                        f"🧱 Guarda WR bot: {b} bloqueado (WR={ev_wr*100:.1f}% < {IA_PROMO_MIN_WR_POR_BOT*100:.1f}%, n={ev_n})."
                                    )
                                    continue
                                overconf_gap = float(p_post) - float(ev_wr)
                                if (ev_n >= int(EVIDENCE_MIN_N_SOFT)) and (overconf_gap > float(IA_PROMO_MAX_OVERCONF_GAP)):
                                    agregar_evento(
                                        f"🧯 Guarda calibración: {b} bloqueado (p_real-WR={overconf_gap*100:.1f}pp > {IA_PROMO_MAX_OVERCONF_GAP*100:.1f}pp)."
                                    )
                                    continue

                                # Guardas por bot (alineadas al HUD): evitar promoción cuando hay
                                # desalineación severa entre probabilidad y performance real reciente.
                                if (ev_n >= int(EVIDENCE_MIN_N_SOFT)) and (ev_wr < float(IA_PROMO_MIN_WR_POR_BOT)):
                                    agregar_evento(
                                        f"🧱 Guarda WR bot: {b} bloqueado (WR={ev_wr*100:.1f}% < {IA_PROMO_MIN_WR_POR_BOT*100:.1f}%, n={ev_n})."
                                    )
                                    continue
                                overconf_gap = float(p_post) - float(ev_wr)
                                if (ev_n >= int(EVIDENCE_MIN_N_SOFT)) and (overconf_gap > float(IA_PROMO_MAX_OVERCONF_GAP)):
                                    agregar_evento(
                                        f"🧯 Guarda calibración: {b} bloqueado (p_real-WR={overconf_gap*100:.1f}pp > {IA_PROMO_MAX_OVERCONF_GAP*100:.1f}pp)."
                                    )
                                    continue

                                # Candado final: umbral REAL por bot/contexto con fallback global
                                thr_post, thr_reason = _umbral_real_por_bot_contexto(b, ctx, umbral_ia_real)
                                estado_bots[b]["ia_thr_real_bot"] = float(thr_post)
                                estado_bots[b]["ia_thr_real_reason"] = str(thr_reason)
                                if ev_n < int(EVIDENCE_MIN_N_SOFT):
                                    thr_post = min(0.99, thr_post + float(EVIDENCE_LOW_N_EXTRA_MARGIN))
                                # Pattern por columnas = CONTEXTO GLOBAL (no score diferencial por bot).
                                # Se usa como modulador de elegibilidad común, sin reordenar bots por sí solo.
                                pat_state = dict(pattern_col_eval if isinstance(pattern_col_eval, dict) else {})
                                pat_bonus_col, pat_penal_col, pat_delta_col = aplicar_ajuste_patron_score(pat_state)
                                k_pts_pat = float(PATTERN_V1_HYBRID_PTS_TO_PROB)
                                thr_post_ctx = float(thr_post)
                                if bool(PATTERN_ENABLE):
                                    if float(pat_delta_col) < 0.0:
                                        thr_post_ctx = min(0.99, float(thr_post_ctx) + abs(float(pat_delta_col)) * k_pts_pat)
                                    elif float(pat_delta_col) > 0.0:
                                        thr_post_ctx = max(0.0, float(thr_post_ctx) - min(0.02, float(pat_delta_col) * k_pts_pat))
                                estado_bots[b]["ia_pattern_col_state"] = str(pat_state.get("pattern_state", "BLOQUEADO"))
                                estado_bots[b]["ia_pattern_col_ratio"] = pat_state.get("green_ratio_col_actual", None)
                                estado_bots[b]["ia_pattern_rebote_hist"] = pat_state.get("rebote_rate_hist", None)
                                estado_bots[b]["ia_pattern_strong80"] = int(pat_state.get("strong_streak_80", 0) or 0)
                                estado_bots[b]["ia_pattern_strong90"] = int(pat_state.get("strong_streak_90", 0) or 0)
                                estado_bots[b]["ia_pattern_late_chase"] = bool(pat_state.get("late_chase", False))
                                estado_bots[b]["ia_pattern_col_bonus"] = float(pat_bonus_col)
                                estado_bots[b]["ia_pattern_col_penal"] = float(pat_penal_col)
                                estado_bots[b]["ia_pattern_col_delta"] = float(pat_delta_col)
                                estado_bots[b]["ia_pattern_thr_ctx"] = float(thr_post_ctx)
                                if float(p_post) < float(thr_post_ctx):
                                    continue

                                # Candado anti-overconfidence global: si el diagnóstico reporta gap alto,
                                # solo promover con evidencia fuerte (LB + N) aunque p_post supere umbral.
                                if bool(diag_gate.get("force_evidence", False)):
                                    if not ((ev_n >= int(EVIDENCE_MIN_N_HARD)) and (ev_lb >= float(EVIDENCE_MIN_LB_HARD))):
                                        continue

                                # 7) Ranking final (Capa B + régimen + evidencia)
                                evidence_score = min(1.0, p_post + min(0.15, ev_n / 400.0))
                                suceso_idx_b = float(estado_bots.get(b, {}).get("ia_suceso_idx", 0.0) or 0.0) / 100.0
                                sensor_plano_b = bool(estado_bots.get(b, {}).get("ia_sensor_plano", False))
                                score_final = (
                                    float(REGIME_GATE_WEIGHT_PROB) * float(p_post)
                                    + float(REGIME_GATE_WEIGHT_REGIME) * float(regime_score)
                                    + float(REGIME_GATE_WEIGHT_EVIDENCE) * float(evidence_score)
                                    + float(IA_SUCESO_SCORE_WEIGHT) * float(max(0.0, min(1.0, suceso_idx_b)))
                                )
                                if redundante_tick:
                                    score_final = float(score_final) - float(IA_REDUNDANCY_SCORE_PENALTY)
                                if sensor_plano_b:
                                    score_final = float(score_final) - float(IA_SENSOR_PLANO_SCORE_PENALTY)

                                # Pattern V1 (gradual): score híbrido detrás de flag.
                                pattern_score_b = 0.0
                                pattern_bonus_b = 0.0
                                pattern_penal_b = 0.0
                                score_hibrido = float(score_final)
                                if bool(PATTERN_V1_ENABLE) and bool(PATTERN_V1_USE_HYBRID_RANKING):
                                    q3_proxy, q2_proxy = _pattern_v1_thresholds_proxy()
                                    pattern_score_b, pattern_bonus_b, pattern_penal_b, pattern_total_b = pattern_score_operativo_v1(ctx, q3_proxy, q2_proxy)
                                    # Ajuste en escala probabilística (evita mezclar puntos de pattern con prob 0..1)
                                    k_pts = float(PATTERN_V1_HYBRID_PTS_TO_PROB)
                                    delta_hibrido = 0.0
                                    if float(pattern_total_b) >= float(PATTERN_V1_SCORE_THR):
                                        delta_hibrido = k_pts * (float(pattern_bonus_b) - float(pattern_penal_b))
                                    else:
                                        delta_hibrido = -k_pts * float(pattern_penal_b)
                                    score_hibrido = float(score_final) + float(delta_hibrido)
                                    score_hibrido = float(max(0.0, min(1.0, score_hibrido)))
                                    _pattern_v1_log_bot(
                                        b,
                                        pattern_score=float(pattern_score_b),
                                        bonus_dual=float(pattern_bonus_b),
                                        penal_tardia=float(pattern_penal_b),
                                        score_hibrido=float(score_hibrido),
                                    )

                                estado_bots[b]["ia_pattern_score"] = float(pattern_score_b)
                                estado_bots[b]["ia_pattern_bonus"] = float(pattern_bonus_b)
                                estado_bots[b]["ia_pattern_penal"] = float(pattern_penal_b)
                                estado_bots[b]["ia_score_hibrido"] = float(score_hibrido)
                                estado_bots[b]["ia_score_hibrido_delta"] = float(score_hibrido - float(score_final))
                                estado_bots[b]["ia_regime_score"] = float(regime_score)
                                estado_bots[b]["ia_evidence_n"] = int(ev_n)
                                estado_bots[b]["ia_evidence_wr"] = float(ev_wr)
                                raw_rank_scores.append((float(score_final), b))

                                candidatos.append((float(score_hibrido), b, float(p), float(p_post), float(regime_score), int(ev_n), float(ev_wr), float(ev_lb)))
                            except Exception:
                                continue

                            candidatos.sort(key=lambda x: x[0], reverse=True)
                            if bool(PATTERN_V1_ENABLE) and bool(PATTERN_V1_USE_HYBRID_RANKING) and candidatos and raw_rank_scores:
                                try:
                                    raw_rank_scores.sort(key=lambda x: x[0], reverse=True)
                                    top_raw = str(raw_rank_scores[0][1])
                                    top_hyb = str(candidatos[0][1])
                                    ts_last = float(globals().get("_PATTERN_RANK_SHIFT_LAST_TS", 0.0) or 0.0)
                                    if top_raw != top_hyb and (time.time() - ts_last) >= float(PATTERN_V1_RANK_SHIFT_LOG_COOLDOWN_S):
                                        globals()["_PATTERN_RANK_SHIFT_LAST_TS"] = float(time.time())
                                        agregar_evento(f"🧠 PatternV1 reordenó top: raw={top_raw} -> híbrido={top_hyb}.")
                                except Exception:
                                    pass

                            ctt_eval = evaluar_ctt_fase([])[1]
                            if candidatos:
                                ctt_status = str(ctt_eval.get("status", "NEUTRAL"))
                                ctt_gate = str(ctt_eval.get("gate", "NEUTRAL"))
                                ctt_reason = str(ctt_eval.get("reason", "na"))
                                if ctt_gate == "BLOCK":
                                    agregar_evento(
                                        f"🟥 CTT telemetría ({ctt_status}): {ctt_reason} | sin efecto operativo en esta fase."
                                    )
                                elif ctt_status in ("GREEN_DIAGNOSTIC", "RED_WEAK"):
                                    agregar_evento(
                                        f"🟨 CTT telemetría ({ctt_status}): {ctt_reason}."
                                    )

                            # Selección automática: tomar la mejor señal elegible >= umbral REAL vigente.

                        # Si hay señal y el saldo no cubre el plan completo, solo avisar (no bloquear).
                        if candidatos and saldo_val < costo_plan:
                            ahora_warn = time.time()
                            last_warn = float(DYN_ROOF_STATE.get("last_low_balance_warn_ts", 0.0) or 0.0)
                            if (ahora_warn - last_warn) >= float(DYN_ROOF_LOW_BAL_WARN_COOLDOWN_S):
                                if saldo_val >= costo_ciclo1:
                                    agregar_evento(
                                        f"ℹ️ Saldo parcial: cubre C1 ({costo_ciclo1:.2f}) pero no C1..C{int(MAX_CICLOS)} ({costo_plan:.2f})."
                                    )
                                else:
                                    falta = costo_ciclo1 - saldo_val
                                    agregar_evento(
                                        f"⚠️ Saldo insuficiente para C1: faltan {falta:.2f} USD (C1={costo_ciclo1:.2f})."
                                    )
                                DYN_ROOF_STATE["last_low_balance_warn_ts"] = float(ahora_warn)

                        # Estado operativo REAL (SOMBRA -> MICRO -> NORMAL)
                        try:
                            estado_real = _resolver_estado_real(None)
                        except Exception:
                            estado_real = "SHADOW"

                        if candidatos and estado_real == "SHADOW":
                            candidatos.sort(key=lambda x: float(x[2]), reverse=True)
                            candidatos = candidatos[:max(1, int(REAL_SHADOW_MICRO_TOP_K))]
                        elif candidatos and estado_real == "MICRO":
                            candidatos.sort(key=lambda x: float(x[2]), reverse=True)
                            candidatos = candidatos[:max(1, int(REAL_MICRO_TOP_K))]

                        embudo = _resolver_embudo_final(candidatos, dyn_gate, estado_real, resolver_canary_estado(leer_model_meta() or {}))
                        decision_final = str(embudo.get("decision_final", EMBUDO_FINAL_WAIT_SOFT))
                        if decision_final == EMBUDO_FINAL_BLOCK_HARD:
                            agregar_evento(f"🛑 EMBUDO {decision_final}: {embudo.get('hard_block_reason') or embudo.get('decision_reason')}")
                            candidatos = []
                        elif decision_final == EMBUDO_FINAL_WAIT_SOFT:
                            agregar_evento(f"⏳ EMBUDO WAIT: {embudo.get('soft_wait_reason') or embudo.get('decision_reason')}")
                            candidatos = []
                        elif decision_final == EMBUDO_FINAL_SHADOW_OK:
                            agregar_evento(f"🕶️ EMBUDO SHADOW_OK: {embudo.get('decision_reason')}")
                            candidatos = []
                        elif decision_final == EMBUDO_FINAL_REAL_MICRO:
                            candidatos = candidatos[:1]
                        elif decision_final == "LXV_ONLY":
                            agregar_evento("🧪 IA REAL purificada | LXV_SYNC habilitado (embudo en telemetría).")
                            candidatos = []

                        # LXV como ruta única de decisión REAL: el embudo legacy queda en telemetría.
                        if bool(LXV_SYNC_REAL_ROUTE_ENABLE):
                            if candidatos and _print_once("lxv-route-only", ttl=20.0):
                                agregar_evento("🧊 Modo LXV_SYNC_REAL: legado REAL en telemetría (sin emisión).")
                            candidatos = []

                        # ==================== AUTO-PRESELECCIÓN (MODO MANUAL) ====================
                        # Si la IA detecta señal y tú estás en manual, preselecciona el mejor bot y abre la ventana
                        # para que solo elijas el ciclo (1..MAX_CICLOS) dentro del tiempo.
                        if MODO_REAL_MANUAL:
                            ahora = time.time()

                            # Si expiró, limpiamos
                            if PENDIENTE_FORZAR_BOT and PENDIENTE_FORZAR_EXPIRA and ahora > PENDIENTE_FORZAR_EXPIRA:
                                agregar_evento("⌛ Ventana de decisión expirada. Señal descartada.")
                                PENDIENTE_FORZAR_BOT = None
                                PENDIENTE_FORZAR_INICIO = 0.0
                                PENDIENTE_FORZAR_EXPIRA = 0.0

                            owner = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else leer_token_actual()
                            if candidatos and (PENDIENTE_FORZAR_BOT is None) and (owner in (None, "none")):
                                ciclo_auto = ciclo_martingala_siguiente()
                                if reset_martingala_por_saldo(ciclo_auto, saldo_val):
                                    ciclo_auto = 1
                                emb = EMBUDO_DECISION_STATE if isinstance(EMBUDO_DECISION_STATE, dict) else {}
                                mejor_bot = str(emb.get("top1_bot") or "").strip()
                                mejor = next((c for c in candidatos if str(c[1]) == mejor_bot), None)
                                if mejor is not None:
                                    score_top, mejor_bot, prob, p_post, reg_score, ev_n, ev_wr, ev_lb = mejor
                                    agregar_evento(f"🧠 Embudo IA (manual): ganador único={mejor_bot} | p_oper={prob*100:.1f}% | risk={emb.get('risk_mode','--')}")
                                    PENDIENTE_FORZAR_BOT = mejor_bot
                                    PENDIENTE_FORZAR_INICIO = ahora
                                    PENDIENTE_FORZAR_EXPIRA = ahora + VENTANA_DECISION_IA_S

                                    # marcamos señal pendiente (sirve para contabilidad IA luego)
                                    estado_bots[mejor_bot]["ia_senal_pendiente"] = True
                                    estado_bots[mejor_bot]["ia_prob_senal"] = prob

                                    agregar_evento(
                                        f"🟢 Señal IA en {mejor_bot} ({prob*100:.1f}%). "
                                        f"Tienes {VENTANA_DECISION_IA_S}s para elegir ciclo [1..{MAX_CICLOS}] o ESC."
                                    )
                        # ==================== /AUTO-PRESELECCIÓN ====================

                        if candidatos and not MODO_REAL_MANUAL:
                            meta_live = resolver_canary_estado(leer_model_meta() or {})
                            embudo_live = EMBUDO_DECISION_STATE if isinstance(EMBUDO_DECISION_STATE, dict) else {}
                            dec_live = str(embudo_live.get("decision_final", EMBUDO_FINAL_WAIT_SOFT))
                            risk_live = str(embudo_live.get("risk_mode", "WAIT_SOFT"))
                            if dec_live in (EMBUDO_FINAL_REAL_MICRO, EMBUDO_FINAL_REAL_NORMAL):
                                agregar_evento(
                                    f"🧭 EMBUDO listo: {dec_live} | risk={risk_live} | gate={embudo_live.get('gate_quality','--')} "
                                    f"| top1={embudo_live.get('top1_bot') or '--'}"
                                )
                            else:
                                candidatos = []

                        if candidatos and not MODO_REAL_MANUAL:
                            ciclo_auto = ciclo_martingala_siguiente()
                            if reset_martingala_por_saldo(ciclo_auto, saldo_val):
                                ciclo_auto = 1
                            emb = EMBUDO_DECISION_STATE if isinstance(EMBUDO_DECISION_STATE, dict) else {}
                            mejor_bot = str(emb.get("top1_bot") or "").strip()
                            mejor = next((c for c in candidatos if str(c[1]) == mejor_bot), None)
                            if mejor is not None:
                                score_top, mejor_bot, prob, p_post, reg_score, ev_n, ev_wr, ev_lb = mejor
                                agregar_evento(f"⚙️ IA AUTO (embudo único): {mejor_bot} p_oper={prob*100:.1f}% risk={emb.get('risk_mode','--')} gate={emb.get('gate_quality','--')}")
                                monto = MARTI_ESCALADO[max(0, min(len(MARTI_ESCALADO)-1, ciclo_auto - 1))]
                                val = obtener_valor_saldo()
                                if val is None or val < monto:
                                    pass
                                else:
                                    estado_bots[mejor_bot]["ia_senal_pendiente"] = True
                                    estado_bots[mejor_bot]["ia_prob_senal"] = prob

                                    # Handoff entre ciclos REAL: si quedó lock residual de otro bot,
                                    # liberarlo antes de emitir la nueva orden para no bloquear rotación.
                                    owner_prev = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else None
                                    if owner_prev and owner_prev != mejor_bot and ciclo_auto > 1:
                                        cerrar_por_fin_de_ciclo(owner_prev, f"Handoff rotación C{ciclo_auto}→{mejor_bot}")

                                    ok_real = emitir_real_autorizado(mejor_bot, ciclo_auto, source="IA_AUTO")
                                    if ok_real:
                                        if estado_real == "SHADOW":
                                            try:
                                                _REAL_SHADOW_MICRO_OPEN_TS.append(float(time.time()))
                                            except Exception:
                                                pass
                                        estado_bots[mejor_bot]["fuente"] = "IA_AUTO"
                                        estado_bots[mejor_bot]["ciclo_actual"] = ciclo_auto
                                        activo_real = REAL_OWNER_LOCK if REAL_OWNER_LOCK in BOT_NAMES else mejor_bot
                                        marti_activa = True
                                    else:
                                        estado_bots[mejor_bot]["ia_senal_pendiente"] = False
                                        estado_bots[mejor_bot]["ia_prob_senal"] = None
                        else:
                            max_prob = max((_prob_ia_operativa_bot(bot, default=0.0) for bot in BOT_NAMES if estado_bots[bot]["ia_ready"]), default=0)
                            if max_prob < umbral_ia_real:
                                pass

                    set_etapa("TICK_04")
                    await refresh_saldo_real()
                    if meta_mostrada and not pausado and not MODAL_ACTIVO:
                        mostrar_advertencia_meta()
                    if not MODAL_ACTIVO:
                        with RENDER_LOCK:
                            mostrar_panel()
            except Exception as e:
                set_etapa("TICK_04", f"Error: {str(e)}")
                agregar_evento(f"⚠️ Error en loop principal: {str(e)}")
                await asyncio.sleep(1)  
            await asyncio.sleep(2)
    except Exception as e:
        set_etapa("STOP", f"Error en main: {str(e)}", anunciar=True)
        agregar_evento(f"⛔ Error en main: {str(e)}")
        _log_exception("Error en main()", e)

if __name__ == "__main__":
    # ============================================
    # MODO LIMPIEZA INICIAL (Opción A datos buenos)
    # ============================================
    MODO_LIMPIEZA_DATASET = False  # ← PONER True SOLO PARA EJECUTAR LA LIMPIEZA UNA VEZ

    if MODO_LIMPIEZA_DATASET:
        print("\n🚿 MODO LIMPIEZA DATASET_INCREMENTAL ACTIVADO")
        print("   - Se borrará dataset_incremental.csv")
        print("   - Se borrarán modelo_ia.json y meta_ia.json")
        print("   - Luego se reconstruirá dataset_incremental.csv")
        print("     usando las últimas 500 filas enriquecidas de cada bot.\n")

        try:
            # 1) Borrar dataset_incremental + modelo + meta
            resetear_incremental_y_modelos(borrar_modelos=True)

            # 2) Volver a llenar dataset_incremental SOLO con datos enriquecidos buenos
            backfill_incremental(ultimas=500)

            print("\n✅ Limpieza + backfill completados correctamente.")
            print("   dataset_incremental.csv ahora contiene solo filas con:")
            print("   volatilidad, es_rebote, hora_bucket y resto de features nuevas.")
        except Exception as e:
            print(f"\n⛔ Error durante limpieza/backfill: {e}")

        input("\nPulsa ENTER para cerrar este modo, luego edita el archivo y pon MODO_LIMPIEZA_DATASET = False.")
        sys.exit(0)

    # ======================
    # MODO NORMAL (loop loop)
    # ======================
    while True:  
        try:
            asyncio.run(main())
        except KeyboardInterrupt:
            print("\n🔴 Programa terminado por el usuario.")
            break
        except Exception as e:
            print(f"⛔ Error crítico: {str(e)}")
            _log_exception("Error crítico en __main__", e)
            time.sleep(5)

# === FIN BLOQUE 13 ===
# === BLOQUE 99 — RESUMEN FINAL DE LO QUE SE LOGRA ===
#
# - Bot maestro 5R6M-1-2-4-8-16 con:
#   * Martingala 1-2-4-8 intacta.
#   * Tokens DEMO/REAL y handshake maestro→bots intactos.
#   * CSV enriquecidos, dataset_incremental.csv, IA XGBoost, reentrenos intactos.
#   * HUD visual con Prob IA, % éxito, saldo, meta, eventos
#   * Audio para GANANCIA/PÉRDIDA, racha, meta, IA 53%, etc.
# - Organización por bloques numerados:
#   ver índice de bloques al inicio del archivo.
#
# Esta organización no cambia la lógica original, solo la hace más mantenible.
# === FIN BLOQUE 99 ===
