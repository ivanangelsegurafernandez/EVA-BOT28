#!/usr/bin/env python3
"""
Monitor de saldo REAL DERIV (PySide6 + PyQtGraph).

Dependencias:
  pip install pandas numpy pyqtgraph PySide6

Lectura de datos (prioridad REAL):
1) saldo_real_live_history.jsonl (ruta compartida)
2) saldo_real_live.json (snapshot maestro)
3) saldo_real_series.csv (fallback real)
4) LOG_SALDOS / *.log / *.txt (observado)
5) registro_enriquecido_fulll*.csv (auxiliar)
"""

from __future__ import annotations

import glob
import csv
import json
import os
import re
import sys
import time
import traceback
from collections import deque
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Dict, List, Optional, Tuple
try:
    from zoneinfo import ZoneInfo
except Exception:
    ZoneInfo = None

try:
    import numpy as np
except Exception as e:
    print(f"[MONITOR][ERROR] Dependencia faltante o inválida: numpy ({e})")
    raise
try:
    import pandas as pd
except Exception as e:
    print(f"[MONITOR][ERROR] Dependencia faltante o inválida: pandas ({e})")
    raise
try:
    import pyqtgraph as pg
except Exception as e:
    print(f"[MONITOR][ERROR] Dependencia faltante o inválida: pyqtgraph ({e})")
    raise
try:
    from PySide6 import QtCore, QtGui, QtWidgets
except Exception as e:
    print(f"[MONITOR][ERROR] Dependencia faltante o inválida: PySide6 ({e})")
    raise

# ------------------------ Config ------------------------
CUENTA_OBJETIVO = "REAL"  # REAL | DEMO | ALL
REFRESH_SEGUNDOS = 5
REFRESH_SEGUNDOS_MINIMIZADO = 15
VENTANA_HORAS = 9
VENTANA_MINUTOS = 60
VENTANA_DIAS = 14
FULLSCREEN_INICIAL = False
LOG_SALDOS = "LOG_SALDOS"
CSV_PATTERN = "registro_enriquecido_fulll*.csv"
SALDO_LIVE_FILE = "saldo_real_live.json"
SALDO_LIVE_HISTORY_FILE = "saldo_real_live_history.jsonl"
SALDO_SERIES_CSV_FILE = "saldo_real_series.csv"
DISPLAY_TIMEZONE = "America/Lima"
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
SALDO_LIVE_SHARED_PATH = os.path.abspath(
    os.getenv("SALDO_LIVE_SHARED_PATH", os.path.join(os.path.expanduser("~"), SALDO_LIVE_FILE))
)
SALDO_LIVE_HISTORY_SHARED_PATH = os.path.abspath(
    os.getenv(
        "SALDO_LIVE_HISTORY_SHARED_PATH",
        os.path.join(os.path.dirname(SALDO_LIVE_SHARED_PATH), SALDO_LIVE_HISTORY_FILE),
    )
)
def resolver_ruta_saldo_series() -> str:
    custom = os.getenv("SALDO_SERIES_CSV_PATH", "").strip()
    if custom:
        return os.path.abspath(os.path.expanduser(custom))
    return os.path.abspath(os.path.join(SCRIPT_DIR, SALDO_SERIES_CSV_FILE))

SALDO_SERIES_CSV_PATH = resolver_ruta_saldo_series()
SALDO_LIVE_PATH = os.getenv("SALDO_LIVE_PATH", "").strip()

MONITOR_VERSION = "v2026.03.31-r1"
MONITOR_BUILD_ID = "MONITOR_SALDO_PRO_REAL_SERIES_GUARD"
MIN_POINTS_FOR_LINE = 2
SHOW_LAST_MARKER = True
SHOW_EXTREME_MARKERS = False
Y_SCALE_MODE = os.getenv("Y_SCALE_MODE", "manual").strip().lower()  # capital | manual | auto
Y_AXIS_MIN_USD = float(os.getenv("Y_AXIS_MIN_USD", "0"))
Y_AXIS_MAX_USD = float(os.getenv("Y_AXIS_MAX_USD", "300"))
Y_AUTO_SPAN_USD = float(os.getenv("Y_AUTO_SPAN_USD", "120"))
CAPITAL_BASE_USD = float(os.getenv("CAPITAL_BASE_USD", "0") or "0")
MIN_X_SPAN_SECONDS = 20.0
OBSERVED_TAIL_BYTES = int(os.getenv("OBSERVED_TAIL_BYTES", str(256 * 1024)))
ESTIMATED_REFRESH_SECONDS = int(os.getenv("ESTIMATED_REFRESH_SECONDS", "30"))
MASTER_LIVE_STALE_SECONDS = int(os.getenv("MASTER_LIVE_STALE_SECONDS", "90"))
MASTER_DELTA_WARN_USD = float(os.getenv("MASTER_DELTA_WARN_USD", "1.0"))
REAL_CANONICAL_SOURCES = {
    "MAESTRO_5R6M",
    "MAESTRO_LIVE",
    "MAESTRO_HISTORY",
    "MAESTRO_HISTORY_DEGRADED",
    "MAESTRO_SERIES_CANONICAL",
}

def _main_window_seconds() -> int:
    """
    Ventana de contexto para MAIN:
    - independiente de DÍAS para evitar panel clon
    - ligada a HORAS para mantener coherencia operativa visible
    """
    try:
        h = int(VENTANA_HORAS)
    except Exception:
        h = 9
    h_ctx = max(24, min(72, h * 3))
    return int(h_ctx * 3600)
def _safe_display_tz():
    if ZoneInfo is None:
        return timezone.utc
    try:
        return ZoneInfo(DISPLAY_TIMEZONE)
    except Exception:
        return timezone.utc


DISPLAY_TZ = _safe_display_tz()



def _now() -> datetime:
    return datetime.now(timezone.utc).astimezone(DISPLAY_TZ)


def _fmt_money(v: Optional[float]) -> str:
    if v is None or (isinstance(v, float) and not np.isfinite(v)):
        return "--"
    return f"{v:,.2f} USD"


def _fmt_local_ts(ts_obj) -> str:
    if ts_obj is None:
        return "--"
    try:
        if isinstance(ts_obj, pd.Timestamp):
            if ts_obj.tzinfo is None:
                ts_obj = ts_obj.tz_localize("UTC")
            return ts_obj.to_pydatetime().astimezone(DISPLAY_TZ).strftime("%Y-%m-%d %H:%M:%S %Z")
        if isinstance(ts_obj, datetime):
            if ts_obj.tzinfo is None:
                ts_obj = ts_obj.replace(tzinfo=timezone.utc)
            return ts_obj.astimezone(DISPLAY_TZ).strftime("%Y-%m-%d %H:%M:%S %Z")
    except Exception:
        return "--"
    return "--"


def _fmt_file_mtime(path_obj: Optional[Path]) -> str:
    if path_obj is None:
        return "--"
    try:
        if not Path(path_obj).exists():
            return "--"
        ts = datetime.fromtimestamp(Path(path_obj).stat().st_mtime, tz=timezone.utc)
        return _fmt_local_ts(ts)
    except Exception:
        return "--"


def _sanitize_series_for_plot(s: pd.DataFrame) -> pd.DataFrame:
    if s is None or s.empty:
        return pd.DataFrame(columns=["timestamp", "equity"])
    d = s.copy()
    d["timestamp"] = pd.to_datetime(d["timestamp"], errors="coerce", utc=True)
    d["equity"] = pd.to_numeric(d["equity"], errors="coerce")
    d = d.dropna(subset=["timestamp", "equity"]).sort_values("timestamp")
    d = d.drop_duplicates(subset=["timestamp"], keep="last")
    return d.reset_index(drop=True)


def _sample_window_series(
    series: pd.DataFrame,
    cutoff: datetime,
    target_points: int,
) -> pd.DataFrame:
    base = _sanitize_series_for_plot(series[series["timestamp"] >= cutoff].copy()) if not series.empty else pd.DataFrame(columns=["timestamp", "equity"])
    tgt = max(12, int(target_points or 0))
    if base.empty or len(base) <= tgt:
        return base
    try:
        df = base.reset_index(drop=True).copy()
        t_sec = (df["timestamp"].astype("int64") // 1_000_000_000).to_numpy(dtype=np.int64)
        n = int(len(df))
        span = int(max(1, t_sec[-1] - t_sec[0]))

        # Fallback por densidad/irregularidad: bucket por índice para evitar aliasing raro.
        use_index_bucket = bool(span <= max(4, n // 2))
        if use_index_bucket:
            bucket_size = max(1, int(np.ceil(n / float(tgt))))
            bucket_id = (np.arange(n, dtype=np.int64) // bucket_size).astype(np.int64)
        else:
            bucket_s = max(1, int(np.ceil(span / float(tgt))))
            bucket_id = ((t_sec - t_sec[0]) // bucket_s).astype(np.int64)

        df["bucket_id"] = bucket_id
        keep_idx = set()
        for _, g in df.groupby("bucket_id", sort=True):
            if g.empty:
                continue
            keep_idx.add(int(g.index[0]))   # first
            keep_idx.add(int(g.index[-1]))  # last
            keep_idx.add(int(g["equity"].idxmin()))  # min
            keep_idx.add(int(g["equity"].idxmax()))  # max
            keep_idx.add(int(g.index[len(g) // 2]))  # punto medio local (reduce aplanado)
        keep_idx.add(0)               # preserva inicio global
        keep_idx.add(len(df) - 1)     # preserva fin global
        sampled = df.loc[sorted(keep_idx), ["timestamp", "equity"]]
        sampled = sampled.drop_duplicates(subset=["timestamp", "equity"], keep="last").sort_values("timestamp")
        sampled = sampled.reset_index(drop=True)

        # Tope de seguridad: evita sobre-compresión irregular cuando buckets son muy densos.
        max_keep = int(max(tgt, tgt * 1.35))
        if len(sampled) > max_keep:
            idx = np.linspace(0, len(sampled) - 1, num=max_keep, dtype=int)
            sampled = sampled.iloc[np.unique(idx)].copy()
            sampled = sampled.reset_index(drop=True)
        return sampled
    except Exception:
        return base


def _safe_float(x, default=np.nan):
    try:
        if x is None:
            return default
        if isinstance(x, str):
            x = x.replace("USD", "").replace("$", "").replace(",", "").strip()
        return float(x)
    except Exception:
        return default


def _is_valid_number(v) -> bool:
    try:
        return v is not None and np.isfinite(float(v))
    except Exception:
        return False


class SmartDateAxis(pg.DateAxisItem):
    def tickStrings(self, values, scale, spacing):
        if not values:
            return []
        finite_vals = [v for v in values if isinstance(v, (int, float, np.floating)) and np.isfinite(v)]
        if not finite_vals:
            return ["" for _ in values]
        span = max(finite_vals) - min(finite_vals)
        out = []
        last_label = None
        for v in values:
            try:
                if not isinstance(v, (int, float, np.floating)) or not np.isfinite(v):
                    out.append("")
                    continue
                # Rango seguro para datetime (aprox. 0001..9999 en segundos epoch)
                if v < -62135596800 or v > 253402300799:
                    out.append("")
                    continue
                dt_utc = datetime.fromtimestamp(float(v), tz=timezone.utc)
                dt_local = dt_utc.astimezone(DISPLAY_TZ)
                if span <= 15 * 60:
                    label = dt_local.strftime("%H:%M:%S")
                elif span <= 6 * 3600:
                    label = dt_local.strftime("%H:%M")
                elif span <= 48 * 3600:
                    label = dt_local.strftime("%d-%m %H:%M")
                else:
                    label = dt_local.strftime("%d-%m")
                if label == last_label:
                    out.append("")
                else:
                    out.append(label)
                    last_label = label
            except Exception:
                out.append("")
        return out


class MoneyAxis(pg.AxisItem):
    def tickStrings(self, values, scale, spacing):
        return [f"{v:,.2f}" for v in values]


@dataclass
class Snapshot:
    source: str
    saldo_actual: Optional[float]
    last_update: Optional[datetime]
    now: datetime
    series_real: pd.DataFrame
    series_main: pd.DataFrame
    series_minutes: pd.DataFrame
    series_hours: pd.DataFrame
    series_days: pd.DataFrame
    series_est: pd.DataFrame
    warnings: List[str]
    view: str


class DataEngine:
    def __init__(self, base_dir: Path):
        self.base_dir = base_dir
        self._cache: Dict[str, Tuple[Tuple, object]] = {}
        self._history_last_seen: Optional[Tuple[str, int, int]] = None
        self._agg_cache_state: Dict[str, object] = {}
        self._est_last_build_ts: Dict[str, float] = {}
        self._est_last_value: Dict[str, pd.DataFrame] = {}
        self._obs_last_build_ts: Dict[str, float] = {}
        self._obs_last_value: Dict[str, pd.DataFrame] = {}
        self._series_last_fingerprint: Optional[Tuple[str, str]] = None
        self._series_lock_warn_ts: float = 0.0
        self._series_repair_sig: Dict[str, Tuple[Optional[int], Optional[int]]] = {}
        self._series_ensure_notice_once: Optional[str] = None
        self._last_series_filter_stats: Dict[str, int] = {"valid": 0, "discarded": 0}

    @staticmethod
    def _normalize_source_label(source: Optional[str]) -> str:
        s = str(source or "").strip().upper()
        if not s:
            return ""
        if s == "FUENTE_SALDO":
            return ""
        return s

    def _is_canonical_real_source(self, source: Optional[str]) -> bool:
        src = self._normalize_source_label(source)
        return bool(src) and src in REAL_CANONICAL_SOURCES

    def _source_rank(self, source: Optional[str]) -> int:
        src = self._normalize_source_label(source)
        if src == "MAESTRO_5R6M":
            return 5
        if src == "MAESTRO_LIVE":
            return 4
        if src == "MAESTRO_HISTORY":
            return 3
        if src == "MAESTRO_HISTORY_DEGRADED":
            return 2
        if src == "MAESTRO_SERIES_CANONICAL":
            return 1
        return 0

    @staticmethod
    def _sig(paths: List[Path]) -> Tuple:
        sig = []
        for p in paths:
            try:
                st = p.stat()
                sig.append((str(p), st.st_mtime_ns, st.st_size))
            except Exception:
                sig.append((str(p), None, None))
        return tuple(sig)

    def _master_live_candidates(self) -> List[Path]:
        cands: List[Path] = [Path(SALDO_LIVE_SHARED_PATH).expanduser(), self.base_dir / SALDO_LIVE_FILE]
        if SALDO_LIVE_PATH:
            custom = Path(SALDO_LIVE_PATH).expanduser()
            cands.append(custom / SALDO_LIVE_FILE if custom.is_dir() else custom)
        return self._sort_candidates_by_freshness(cands)

    def _master_history_candidates(self) -> List[Path]:
        cands: List[Path] = [Path(SALDO_LIVE_HISTORY_SHARED_PATH).expanduser()]
        for p in self._master_live_candidates():
            cands.append(p.parent / SALDO_LIVE_HISTORY_FILE)
        return self._sort_candidates_by_freshness(cands)

    def _master_series_candidates(self) -> List[Path]:
        cands: List[Path] = [Path(SALDO_SERIES_CSV_PATH).expanduser()]
        for p in self._master_live_candidates():
            cands.append(p.parent / SALDO_SERIES_CSV_FILE)
        return self._sort_candidates_by_freshness(cands)

    def _sort_candidates_by_freshness(self, cands: List[Path]) -> List[Path]:
        uniq: List[Path] = []
        seen = set()
        for p in cands:
            k = str(p)
            if k in seen:
                continue
            seen.add(k)
            uniq.append(p)

        def _rank(path: Path) -> Tuple[int, int, int, str]:
            try:
                st = path.stat()
                mtime_ns = int(st.st_mtime_ns)
                exists_rank = 1
            except Exception:
                mtime_ns = -1
                exists_rank = 0
            try:
                base_pref = 1 if path.parent.resolve() == self.base_dir.resolve() else 0
            except Exception:
                base_pref = 0
            return (exists_rank, mtime_ns, base_pref, str(path))

        return sorted(uniq, key=_rank, reverse=True)

    @staticmethod
    def _ts_utc_iso(ts_obj) -> Optional[str]:
        try:
            ts = pd.to_datetime(ts_obj, errors="coerce", utc=True)
            if pd.isna(ts):
                return None
            return ts.strftime("%Y-%m-%dT%H:%M:%S.%fZ")
        except Exception:
            return None

    @staticmethod
    def _normalize_equity_value(value) -> Optional[float]:
        try:
            v = float(value)
            if not np.isfinite(v):
                return None
            return float(v)
        except Exception:
            return None

    def _ensure_series_csv_exists(self, path: Path) -> Optional[str]:
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            if not path.exists():
                with path.open("w", encoding="utf-8", newline="") as fh:
                    fh.write("timestamp,equity,source\n")
                    fh.flush()
                    os.fsync(fh.fileno())
                return f"{SALDO_SERIES_CSV_FILE} creado automáticamente en {path}"
        except Exception as e:
            return f"No se pudo crear {SALDO_SERIES_CSV_FILE} en {path}: {e}"
        return None

    def _read_last_series_row(self, path: Path) -> Optional[Tuple[str, float, str]]:
        try:
            d = self._normalize_saldo_series_csv(path)
            if d.empty:
                return None
            row = d.iloc[-1]
            ts_iso = self._ts_utc_iso(row.get("timestamp"))
            eq = self._normalize_equity_value(row.get("equity"))
            src = self._normalize_source_label(row.get("source")) or "MAESTRO_SERIES_CANONICAL"
            if ts_iso is not None and eq is not None:
                return (ts_iso, eq, src)
        except Exception:
            return None
        return None

    def _repair_series_csv_if_needed(self, path: Path) -> Optional[str]:
        try:
            st = path.stat()
            sig = (int(st.st_mtime_ns), int(st.st_size))
        except Exception:
            sig = (None, None)
        key = str(path)
        if self._series_repair_sig.get(key) == sig:
            return None
        created_msg = self._ensure_series_csv_exists(path)
        if created_msg:
            try:
                st = path.stat()
                self._series_repair_sig[key] = (int(st.st_mtime_ns), int(st.st_size))
            except Exception:
                self._series_repair_sig[key] = (None, None)
            return created_msg
        try:
            if path.stat().st_size == 0:
                with path.open("w", encoding="utf-8", newline="") as fh:
                    fh.write("timestamp,equity,source\n")
                    fh.flush()
                    os.fsync(fh.fileno())
                return f"{SALDO_SERIES_CSV_FILE} estaba vacío; cabecera restaurada en {path}"
            with path.open("r", encoding="utf-8", errors="ignore", newline="") as fh:
                lines = fh.read().splitlines()
            if not lines:
                with path.open("w", encoding="utf-8", newline="") as fh:
                    fh.write("timestamp,equity,source\n")
                    fh.flush()
                    os.fsync(fh.fileno())
                return f"{SALDO_SERIES_CSV_FILE} sin contenido; cabecera restaurada en {path}"
            head = [c.strip().lower() for c in lines[0].split(",")]
            is_basic_header = len(head) >= 3 and head[0] in ("timestamp", "ts_utc") and head[1] == "equity"
            is_extended_header = ("ts_epoch" in head and "ts_iso" in head and "saldo_real" in head and "fuente_saldo" in head)
            valid_header = is_basic_header or is_extended_header
            if valid_header:
                return None
            normalized = self._normalize_saldo_series_csv(path)
            valid_n = int(len(normalized))
            discarded_n = int(self._last_series_filter_stats.get("discarded", 0))
            if normalized.empty:
                return f"{SALDO_SERIES_CSV_FILE} recreado limpio tras corrupción de cabecera/contenido"
            tmp = path.with_suffix(path.suffix + ".repair.tmp")
            bak = path.with_suffix(path.suffix + ".repair.bak")
            try:
                os.replace(path, bak)
            except Exception:
                bak = None
            with tmp.open("w", encoding="utf-8", newline="") as fh:
                fh.write("timestamp,equity,source\n")
                for _, row in normalized.iterrows():
                    ts_iso = self._ts_utc_iso(row.get("timestamp"))
                    eq = self._normalize_equity_value(row.get("equity"))
                    src = self._normalize_source_label(row.get("source")) or "MAESTRO_SERIES_CANONICAL"
                    if ts_iso is None or eq is None:
                        continue
                    fh.write(f"{ts_iso},{eq:.8f},{src}\n")
                fh.flush()
                os.fsync(fh.fileno())
            os.replace(tmp, path)
            try:
                st = path.stat()
                self._series_repair_sig[key] = (int(st.st_mtime_ns), int(st.st_size))
            except Exception:
                self._series_repair_sig[key] = (None, None)
            if bak is not None:
                return (
                    f"Series CSV saneado: {valid_n} filas válidas conservadas / {discarded_n} descartadas "
                    f"(backup: {bak})"
                )
            return f"Series CSV saneado: {valid_n} filas válidas conservadas / {discarded_n} descartadas"
        except Exception as e:
            return f"No se pudo reparar {SALDO_SERIES_CSV_FILE} en {path}: {e}"
        finally:
            try:
                st = path.stat()
                self._series_repair_sig[key] = (int(st.st_mtime_ns), int(st.st_size))
            except Exception:
                self._series_repair_sig[key] = (None, None)

    def _append_series_sample_if_new(self, path: Path, ts, equity, source: str) -> Optional[str]:
        ts_iso = self._ts_utc_iso(ts)
        eq = self._normalize_equity_value(equity)
        if ts_iso is None or eq is None:
            return None
        src = self._normalize_source_label(source)
        if not self._is_canonical_real_source(src):
            return f"Bloqueadas filas source={src or 'VACIO'} para saldo REAL"
        fp = (ts_iso, f"{eq:.8f}")
        if self._series_last_fingerprint == fp:
            return None
        last = self._read_last_series_row(path)
        if last is not None:
            last_ts, last_eq, _ = last
            if last_ts == ts_iso or (last_ts == ts_iso and abs(last_eq - eq) < 1e-9) or (abs(last_eq - eq) < 1e-9 and self._series_last_fingerprint == fp):
                self._series_last_fingerprint = fp
                return None
        lock_path = path.with_suffix(path.suffix + ".monitor.lock")
        wrote = False
        for _ in range(3):
            lock_fd = None
            try:
                lock_fd = os.open(str(lock_path), os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o644)
                with os.fdopen(lock_fd, "w", encoding="utf-8") as lfh:
                    lfh.write(str(os.getpid()))
                lock_fd = None
                if not path.exists():
                    self._ensure_series_csv_exists(path)
                with path.open("a", encoding="utf-8", newline="") as fh:
                    fh.write(f"{ts_iso},{eq:.8f},{src}\n")
                    fh.flush()
                    os.fsync(fh.fileno())
                wrote = True
                break
            except FileExistsError:
                time.sleep(0.06)
            except Exception:
                time.sleep(0.04)
            finally:
                if lock_fd is not None:
                    try:
                        os.close(lock_fd)
                    except Exception:
                        pass
                try:
                    if lock_path.exists():
                        lock_path.unlink()
                except Exception:
                    pass
        if not wrote:
            now_mono = time.monotonic()
            if (now_mono - self._series_lock_warn_ts) > 20.0:
                self._series_lock_warn_ts = now_mono
                return f"No se pudo anexar muestra a {SALDO_SERIES_CSV_FILE} (lock temporal)"
            return None
        self._series_last_fingerprint = fp
        return None

    def _extract_best_real_sample_for_persist(
        self,
        hist: pd.DataFrame,
        master: Optional[Tuple[float, datetime]],
        series_csv: pd.DataFrame,
        saldo_actual: Optional[float],
        last_update,
        source: str,
        observed: pd.DataFrame,
        estimated: Optional[pd.DataFrame] = None,
    ) -> Optional[Tuple[str, float, str]]:
        if master is not None:
            mv, mts = master
            ts_iso = self._ts_utc_iso(mts)
            eq = self._normalize_equity_value(mv)
            if ts_iso and eq is not None:
                return (ts_iso, eq, "MAESTRO_LIVE")
        if not hist.empty:
            row = hist.iloc[-1]
            ts_iso = self._ts_utc_iso(row.get("timestamp"))
            eq = self._normalize_equity_value(row.get("equity"))
            if ts_iso and eq is not None:
                return (ts_iso, eq, "MAESTRO_HISTORY")
        ts_iso = self._ts_utc_iso(last_update)
        eq = self._normalize_equity_value(saldo_actual)
        src = self._normalize_source_label(source)
        if ts_iso and eq is not None and self._is_canonical_real_source(src):
            return (ts_iso, eq, src)
        return None

    def _cached(self, key: str, sig: Tuple):
        old = self._cache.get(key)
        if old and old[0] == sig:
            return old[1]
        return None

    def _store_cache(self, key: str, sig: Tuple, value):
        self._cache[key] = (sig, value)
        return value

    @staticmethod
    def _read_tail_lines(path: Path, max_bytes: int) -> List[str]:
        try:
            with path.open("rb") as fh:
                fh.seek(0, os.SEEK_END)
                size = fh.tell()
                read_from = max(0, size - max(1024, int(max_bytes)))
                fh.seek(read_from, os.SEEK_SET)
                data = fh.read()
            if read_from > 0:
                nl = data.find(b"\n")
                if nl >= 0:
                    data = data[nl + 1 :]
            return data.decode("utf-8", errors="ignore").splitlines()
        except Exception:
            return []

    def _read_master_live(self) -> Tuple[Optional[Tuple[float, datetime]], Optional[str], Optional[Path]]:
        paths = self._master_live_candidates()
        sig = self._sig(paths)
        cached = self._cached("live", sig)
        if cached is not None:
            return cached

        found_any = False
        best_live: Optional[Tuple[float, datetime, Path, int]] = None
        warnings: List[str] = []
        for p in paths:
            if not p.exists():
                continue
            found_any = True
            try:
                obj = json.loads(p.read_text(encoding="utf-8", errors="ignore"))
                v = _safe_float(
                    obj.get("saldo_real", obj.get("equity", obj.get("balance"))),
                    default=np.nan,
                )
                if not np.isfinite(v):
                    warnings.append(f"{SALDO_LIVE_FILE} inválido en {'ruta compartida' if str(p)==SALDO_LIVE_SHARED_PATH else p}")
                    continue
                ts = pd.to_datetime(obj.get("timestamp"), errors="coerce", utc=True)
                if pd.isna(ts):
                    ts = pd.to_datetime(pd.to_numeric(obj.get("ts"), errors="coerce"), unit="s", errors="coerce", utc=True)
                if pd.isna(ts):
                    ts = pd.to_datetime(p.stat().st_mtime, unit="s", utc=True)
                if pd.isna(ts):
                    continue
                cand = (float(v), ts.to_pydatetime(), p, self._path_mtime_ns(p))
                if best_live is None:
                    best_live = cand
                else:
                    _bv, bts, bp, bmt = best_live
                    if (cand[1], cand[3], str(cand[2])) > (bts, bmt, str(bp)):
                        best_live = cand
            except Exception as e:
                warnings.append(f"{SALDO_LIVE_FILE} inválido en {'ruta compartida' if str(p)==SALDO_LIVE_SHARED_PATH else p}: {e}")
        if best_live is not None:
            v, ts, p, _mt = best_live
            return self._store_cache("live", sig, ((float(v), ts), None, p))

        msg = f"{SALDO_LIVE_FILE} no encontrado en ruta compartida: {SALDO_LIVE_SHARED_PATH}"
        if found_any:
            msg = f"saldo real del maestro no disponible ({SALDO_LIVE_FILE})"
        if warnings:
            msg = f"{msg} | {' | '.join(warnings[-3:])}"
        return self._store_cache("live", sig, (None, msg, None))

    def _read_master_history(self) -> Tuple[pd.DataFrame, Optional[str], Optional[Path], Optional[str]]:
        paths = self._master_history_candidates()
        sig = self._sig(paths)
        cached = self._cached("hist", sig)
        if cached is not None:
            return cached

        warnings: List[str] = []
        best_hist: Optional[Tuple[pd.DataFrame, Path, datetime, int]] = None
        for p in paths:
            if not p.exists():
                continue
            try:
                rows = []
                with p.open("r", encoding="utf-8", errors="ignore") as fh:
                    for line in fh:
                        line = line.strip()
                        if not line:
                            continue
                        obj = json.loads(line)
                        v = _safe_float(
                            obj.get("saldo_real", obj.get("equity", obj.get("balance"))),
                            default=np.nan,
                        )
                        if not np.isfinite(v):
                            continue
                        ts = pd.to_datetime(obj.get("timestamp"), errors="coerce", utc=True)
                        if pd.isna(ts):
                            ts = pd.to_datetime(pd.to_numeric(obj.get("ts"), errors="coerce"), unit="s", errors="coerce", utc=True)
                        if pd.isna(ts):
                            ts = pd.to_datetime(p.stat().st_mtime, unit="s", utc=True)
                        if pd.isna(ts):
                            continue
                        rows.append((ts.to_pydatetime(), float(v)))
                if rows:
                    d = pd.DataFrame(rows, columns=["timestamp", "equity"]).sort_values("timestamp")
                    d = d.drop_duplicates(subset=["timestamp", "equity"], keep="last")
                    last_ts = pd.to_datetime(d["timestamp"].iloc[-1], errors="coerce", utc=True)
                    if pd.isna(last_ts):
                        continue
                    cand = (d, p, last_ts.to_pydatetime(), self._path_mtime_ns(p))
                    if best_hist is None:
                        best_hist = cand
                    else:
                        _bd, bp, bts, bmt = best_hist
                        if (cand[2], cand[3], str(cand[1])) > (bts, bmt, str(bp)):
                            best_hist = cand
            except Exception as e:
                warnings.append(f"{SALDO_LIVE_HISTORY_FILE} inválido en {'ruta compartida' if str(p)==SALDO_LIVE_HISTORY_SHARED_PATH else p}: {e}")
        if best_hist is not None:
            d, p, _lts, _mt = best_hist
            growth_msg = self._check_history_growth(p, len(d))
            return self._store_cache("hist", sig, (d, None, p, growth_msg))

        msg = f"Sin histórico real: no se encontró {SALDO_LIVE_HISTORY_FILE} en ruta compartida: {SALDO_LIVE_HISTORY_SHARED_PATH}"
        if warnings:
            msg = f"{msg} | {' | '.join(warnings[-3:])}"
        return self._store_cache(
            "hist",
            sig,
            (pd.DataFrame(columns=["timestamp", "equity"]), msg, None, None),
        )

    def _read_saldo_series_csv(self) -> Tuple[pd.DataFrame, Optional[str], Optional[Path]]:
        paths = self._master_series_candidates()
        sig = self._sig(paths)
        cached = self._cached("series_csv", sig)
        if cached is not None:
            return cached
        warnings: List[str] = []
        found_any = False
        best_series: Optional[Tuple[pd.DataFrame, Path, datetime, int]] = None
        for p in paths:
            if not p.exists():
                continue
            found_any = True
            try:
                repair_msg = self._repair_series_csv_if_needed(p)
                if repair_msg:
                    warnings.append(repair_msg)
                d = self._normalize_saldo_series_csv(p)
                if d.empty:
                    discarded_n = int(self._last_series_filter_stats.get("discarded", 0))
                    if discarded_n > 0:
                        warnings.append(f"REAL filtrado: descartadas {discarded_n} filas degradadas del series_csv")
                    continue
                d = d.sort_values("timestamp").drop_duplicates(subset=["timestamp"], keep="last")
                discarded_n = int(self._last_series_filter_stats.get("discarded", 0))
                if discarded_n > 0:
                    warnings.append(f"REAL filtrado: descartadas {discarded_n} filas degradadas del series_csv")
                last_ts = pd.to_datetime(d["timestamp"].iloc[-1], errors="coerce", utc=True)
                if pd.isna(last_ts):
                    continue
                cand = (d, p, last_ts.to_pydatetime(), self._path_mtime_ns(p))
                if best_series is None:
                    best_series = cand
                else:
                    _bd, bp, bts, bmt = best_series
                    if (cand[2], cand[3], str(cand[1])) > (bts, bmt, str(bp)):
                        best_series = cand
            except Exception as e:
                warnings.append(f"{SALDO_SERIES_CSV_FILE} inválido en {p}: {e}")
        if best_series is not None:
            d, p, _lts, _mt = best_series
            warn_msg = " | ".join(warnings[-3:]) if warnings else None
            return self._store_cache("series_csv", sig, (d, warn_msg, p))
        if not found_any:
            primary = Path(SALDO_SERIES_CSV_PATH).expanduser()
            msg = self._ensure_series_csv_exists(primary)
            if msg:
                warnings.append(msg)
        err = " | ".join(warnings[-3:]) if warnings else None
        return self._store_cache("series_csv", sig, (pd.DataFrame(columns=["timestamp", "equity", "source"]), err, None))

    def _normalize_saldo_series_csv(self, path: Path) -> pd.DataFrame:
        rows: List[Tuple[datetime, float, str]] = []
        discarded = 0
        with path.open("r", encoding="utf-8", errors="ignore", newline="") as fh:
            reader = csv.reader(fh)
            headers: List[str] = []
            for raw in reader:
                if not raw:
                    continue
                row = [str(c).strip() for c in raw]
                if not row:
                    continue
                low0 = row[0].lower()
                if not headers and any(("timestamp" in c.lower() or "ts_iso" in c.lower() or "ts_epoch" in c.lower()) for c in row):
                    headers = [c.strip().lower() for c in row]
                    continue
                if low0 in ("ts_utc", "timestamp", "ts_epoch"):
                    continue
                payload = {}
                if headers and len(headers) >= len(row):
                    payload = {headers[i]: row[i] for i in range(len(row))}
                ts_iso_raw = payload.get("ts_iso") or payload.get("timestamp") or payload.get("ts_utc")
                epoch_raw = payload.get("ts_epoch") or payload.get("epoch")
                saldo_real_raw = payload.get("saldo_real")
                saldo_total_raw = payload.get("saldo_total")
                equity_raw = payload.get("equity")
                source_raw = payload.get("fuente_saldo") or payload.get("source")

                if not payload:
                    if len(row) == 3:
                        ts_iso_raw, c1, c2 = row[0], row[1], row[2]
                        epoch_probe = pd.to_numeric(c1, errors="coerce")
                        if np.isfinite(epoch_probe) and float(epoch_probe) >= 1_000_000_000:
                            epoch_raw = c1
                            equity_raw = c2
                            saldo_real_raw = c2
                            source_raw = "MAESTRO_HISTORY_DEGRADED"
                        else:
                            equity_raw = c1
                            saldo_real_raw = c1
                            source_raw = c2
                    elif len(row) >= 10:
                        epoch_raw = row[0]
                        ts_iso_raw = row[1]
                        saldo_real_raw = row[6] if len(row) > 6 else None
                        saldo_total_raw = row[8] if len(row) > 8 else None
                        source_raw = row[9] if len(row) > 9 else None
                    elif len(row) >= 4:
                        ts_iso_raw, epoch_raw, saldo_real_raw = row[0], row[1], row[2]
                        equity_raw = row[3] if len(row) >= 4 else None
                        source_raw = row[4] if len(row) >= 5 else "MAESTRO_HISTORY_DEGRADED"
                    else:
                        discarded += 1
                        continue

                ts = pd.to_datetime(ts_iso_raw, errors="coerce", utc=True)
                if pd.isna(ts):
                    ts = pd.to_datetime(pd.to_numeric(epoch_raw, errors="coerce"), unit="s", errors="coerce", utc=True)
                if pd.isna(ts):
                    discarded += 1
                    continue
                eq = pd.to_numeric(saldo_real_raw, errors="coerce")
                if not np.isfinite(eq):
                    eq = pd.to_numeric(equity_raw, errors="coerce")
                if not np.isfinite(eq) and CUENTA_OBJETIVO == "REAL":
                    eq = pd.to_numeric(saldo_total_raw, errors="coerce")
                if not np.isfinite(eq):
                    discarded += 1
                    continue
                src = self._normalize_source_label(source_raw) or "MAESTRO_SERIES_CANONICAL"
                if not self._is_canonical_real_source(src):
                    discarded += 1
                    continue
                rows.append((ts.to_pydatetime(), float(eq), src))
        if not rows:
            self._last_series_filter_stats = {"valid": 0, "discarded": discarded}
            return pd.DataFrame(columns=["timestamp", "equity", "source"])
        out = pd.DataFrame(rows, columns=["timestamp", "equity", "source"])
        out["source_rank"] = out["source"].map(self._source_rank).fillna(0).astype(int)
        out = out.sort_values(["timestamp", "source_rank", "equity"], ascending=[True, False, False])
        out = out.drop_duplicates(subset=["timestamp"], keep="first")
        out = out.sort_values("timestamp")
        self._last_series_filter_stats = {"valid": int(len(out)), "discarded": int(discarded)}
        return out.reset_index(drop=True)

    def _check_history_growth(self, path: Path, valid_rows: int) -> Optional[str]:
        try:
            st = path.stat()
            current = (str(path), st.st_size, valid_rows)
            previous = self._history_last_seen
            self._history_last_seen = current
            if previous is None or previous[0] != current[0]:
                return None
            if previous[1] == current[1] and previous[2] == current[2]:
                return (
                    f"Histórico sin crecimiento: {SALDO_LIVE_HISTORY_FILE} no cambió "
                    f"(size={current[1]} bytes, muestras={current[2]})"
                )
        except Exception:
            return None
        return None

    def _parse_observed(self, view: str) -> pd.DataFrame:
        if view == "ALL":
            real = self._parse_observed("REAL")
            demo = self._parse_observed("DEMO")
            if real.empty:
                return demo
            if demo.empty:
                return real
            rr = real.rename(columns={"equity": "real"}).sort_values("timestamp")
            dd = demo.rename(columns={"equity": "demo"}).sort_values("timestamp")
            z = pd.merge_asof(rr, dd, on="timestamp", direction="nearest", tolerance=pd.Timedelta("12h"))
            z["real"] = z["real"].ffill().fillna(0.0)
            z["demo"] = z["demo"].ffill().fillna(0.0)
            z["equity"] = z["real"] + z["demo"]
            return z[["timestamp", "equity"]]

        files = [self.base_dir / LOG_SALDOS]
        files.extend(sorted(self.base_dir.glob("*.log")))
        files.extend(sorted(self.base_dir.glob("*.txt")))
        sig = self._sig(files)
        key = f"obs:{view}"
        cached = self._cached(key, sig)
        if cached is not None:
            return cached
        now_mono = time.monotonic()
        if view in self._obs_last_build_ts and (now_mono - self._obs_last_build_ts[view]) < 2.0:
            return self._obs_last_value.get(view, pd.DataFrame(columns=["timestamp", "equity"]))

        patterns = [
            re.compile(r"SALDO\s+EN\s+CUENTA\s+REAL\s+DERIV\s*:\s*([-\d\.,]+)(?:\s*USD)?", re.IGNORECASE),
            re.compile(r"Saldo\s+cuenta\s+REAL(?:\s*\([^)]*\))?\s*:\s*([-\d\.,]+)(?:\s*USD)?", re.IGNORECASE),
        ] if view == "REAL" else [
            re.compile(r"Saldo\s+cuenta\s+DEMO(?:\s*\([^)]*\))?\s*:\s*([-\d\.,]+)(?:\s*USD)?", re.IGNORECASE)
        ]

        rows: List[Tuple[datetime, float]] = []
        for p in files:
            if not p.exists() or not p.is_file():
                continue
            try:
                lines = self._read_tail_lines(p, OBSERVED_TAIL_BYTES)
            except Exception:
                continue
            base = datetime.fromtimestamp(p.stat().st_mtime, tz=timezone.utc) - timedelta(seconds=len(lines))
            for i, line in enumerate(lines):
                match = None
                for pat in patterns:
                    match = pat.search(line)
                    if match:
                        break
                if not match:
                    continue
                v = _safe_float(match.group(1), default=np.nan)
                if not np.isfinite(v):
                    continue
                ts = pd.to_datetime(line, errors="coerce", utc=True)
                ts = (base + timedelta(seconds=i)) if pd.isna(ts) else ts.to_pydatetime()
                rows.append((ts, float(v)))

        if not rows:
            out = self._store_cache(key, sig, pd.DataFrame(columns=["timestamp", "equity"]))
            self._obs_last_build_ts[view] = now_mono
            self._obs_last_value[view] = out
            return out
        d = pd.DataFrame(rows, columns=["timestamp", "equity"]).sort_values("timestamp")
        d = d.drop_duplicates(subset=["timestamp", "equity"], keep="last")
        out = self._store_cache(key, sig, d)
        self._obs_last_build_ts[view] = now_mono
        self._obs_last_value[view] = out
        return out

    def _build_estimated(self, view: str) -> pd.DataFrame:
        now_mono = time.monotonic()
        if view in self._est_last_build_ts and (now_mono - self._est_last_build_ts[view]) < float(ESTIMATED_REFRESH_SECONDS):
            last = self._est_last_value.get(view)
            if last is not None:
                return last
        files = [Path(p) for p in sorted(glob.glob(str(self.base_dir / CSV_PATTERN)))]
        sig = self._sig(files)
        key = f"est:{view}"
        cached = self._cached(key, sig)
        if cached is not None:
            self._est_last_build_ts[view] = now_mono
            self._est_last_value[view] = cached
            return cached
        if not files:
            out = self._store_cache(key, sig, pd.DataFrame(columns=["timestamp", "equity"]))
            self._est_last_build_ts[view] = now_mono
            self._est_last_value[view] = out
            return out

        dfs = []
        for p in files:
            for enc in ("utf-8", "utf-8-sig", "latin-1", "cp1252"):
                try:
                    dfs.append(pd.read_csv(p, encoding=enc, low_memory=False))
                    break
                except Exception:
                    pass
        if not dfs:
            out = self._store_cache(key, sig, pd.DataFrame(columns=["timestamp", "equity"]))
            self._est_last_build_ts[view] = now_mono
            self._est_last_value[view] = out
            return out

        d = pd.concat(dfs, ignore_index=True)
        if "ganancia_perdida" not in d.columns:
            out = self._store_cache(key, sig, pd.DataFrame(columns=["timestamp", "equity"]))
            self._est_last_build_ts[view] = now_mono
            self._est_last_value[view] = out
            return out
        ts = pd.Series(pd.NaT, index=d.index, dtype="datetime64[ns, UTC]")
        if "fecha" in d.columns:
            ts = ts.fillna(pd.to_datetime(d["fecha"], errors="coerce", utc=True))
        if "ts" in d.columns:
            ts = ts.fillna(pd.to_datetime(d["ts"], errors="coerce", utc=True))
        if "epoch" in d.columns:
            ts = ts.fillna(pd.to_datetime(pd.to_numeric(d["epoch"], errors="coerce"), unit="s", errors="coerce", utc=True))
        d["timestamp"] = ts
        d = d.dropna(subset=["timestamp"]).sort_values("timestamp")
        if "trade_status" in d.columns:
            d = d[d["trade_status"].astype(str).str.upper().str.strip() == "CERRADO"]
        if "cuenta" in d.columns and view in ("REAL", "DEMO"):
            d = d[d["cuenta"].astype(str).str.upper().str.contains(view, na=False)]
        pnl = pd.to_numeric(d["ganancia_perdida"], errors="coerce").fillna(0.0)
        base = 1000.0 if view == "REAL" else (10000.0 if view == "DEMO" else 11000.0)
        d["equity"] = base + pnl.cumsum()
        out = self._store_cache(key, sig, d[["timestamp", "equity"]])
        self._est_last_build_ts[view] = now_mono
        self._est_last_value[view] = out
        return out

    def build_snapshot(self, view: str) -> Snapshot:
        now = _now()
        warnings: List[str] = []
        series_target_path = Path(SALDO_SERIES_CSV_PATH).expanduser()
        if view == "REAL":
            ensure_msg = self._ensure_series_csv_exists(series_target_path)
            if ensure_msg and ensure_msg != self._series_ensure_notice_once:
                warnings.append(ensure_msg)
                self._series_ensure_notice_once = ensure_msg

        master, master_msg, live_path_used = self._read_master_live() if view == "REAL" else (None, None, None)
        hist, hist_msg, hist_path_used, hist_growth_msg = self._read_master_history() if view == "REAL" else (pd.DataFrame(columns=["timestamp", "equity"]), None, None, None)
        series_csv, series_msg, series_path_used = self._read_saldo_series_csv() if view == "REAL" else (pd.DataFrame(columns=["timestamp", "equity"]), None, None)
        real_primary_ok = view == "REAL" and (master is not None or not hist.empty or not series_csv.empty)
        observed = self._parse_observed(view) if view != "REAL" else pd.DataFrame(columns=["timestamp", "equity"])
        estimated = self._build_estimated(view) if view != "REAL" else self._est_last_value.get(view, pd.DataFrame(columns=["timestamp", "equity"]))

        if master_msg and view == "REAL":
            warnings.append(master_msg)
        if hist_msg and view == "REAL":
            warnings.append(hist_msg)

        if view == "REAL":
            warnings.append(f"Monitor {MONITOR_VERSION} · id={MONITOR_BUILD_ID}")
            warnings.append(f"Ruta live usada: {live_path_used if live_path_used else SALDO_LIVE_SHARED_PATH}")
            warnings.append(f"Ruta history usada: {hist_path_used if hist_path_used else SALDO_LIVE_HISTORY_SHARED_PATH}")
            live_exists = bool(live_path_used and Path(live_path_used).exists())
            live_mtime = _fmt_file_mtime(Path(live_path_used) if live_path_used else None)
            live_ts = _fmt_local_ts(master[1]) if master is not None else "--"
            live_saldo = _fmt_money(float(master[0])) if master is not None else "--"
            warnings.append(
                f"Diag live: exists={'yes' if live_exists else 'no'} mtime={live_mtime} "
                f"saldo={live_saldo} ts={live_ts}"
            )
            if series_msg:
                warnings.append(series_msg)
            warnings.append(f"Ruta series usada: {series_path_used if series_path_used else series_target_path}")
            warnings.append(
                f"Estado snapshot: {'OK' if live_path_used and Path(live_path_used).exists() else 'NO ENCONTRADO'} | "
                f"Estado histórico: {'OK' if hist_path_used and Path(hist_path_used).exists() else 'NO ENCONTRADO'}"
            )
            valid_rows = int(len(hist))
            last_hist_ts = _fmt_local_ts(hist["timestamp"].iloc[-1]) if valid_rows else "--"
            warnings.append(
                f"Histórico válido: {valid_rows} muestra(s) | última marca válida: {last_hist_ts}"
            )
            if hist_growth_msg:
                warnings.append(hist_growth_msg)
            if master is not None:
                mv_live, mts_live = master
                live_age_sec = max(0.0, (_now().astimezone(timezone.utc) - mts_live.astimezone(timezone.utc)).total_seconds())
                if live_age_sec > float(MASTER_LIVE_STALE_SECONDS):
                    warnings.append(f"Live stale: {live_age_sec:.0f}s > {MASTER_LIVE_STALE_SECONDS}s")
                if not hist.empty:
                    hts = pd.to_datetime(hist["timestamp"].iloc[-1], errors="coerce", utc=True)
                    if not pd.isna(hts):
                        newer_by = (hts.to_pydatetime() - mts_live.astimezone(timezone.utc)).total_seconds()
                        if newer_by > 2.0:
                            warnings.append(f"Histórico más nuevo que live por {newer_by:.1f}s")
                    hdelta = abs(float(hist["equity"].iloc[-1]) - float(mv_live))
                    if hdelta >= float(MASTER_DELTA_WARN_USD):
                        warnings.append(f"Desfase live↔hist: {hdelta:.2f} USD")
                if not series_csv.empty:
                    sts = pd.to_datetime(series_csv["timestamp"].iloc[-1], errors="coerce", utc=True)
                    if not pd.isna(sts):
                        newer_by = (sts.to_pydatetime() - mts_live.astimezone(timezone.utc)).total_seconds()
                        if newer_by > 2.0:
                            warnings.append(f"Series CSV más nueva que live por {newer_by:.1f}s")
                    sdelta = abs(float(series_csv["equity"].iloc[-1]) - float(mv_live))
                    if sdelta >= float(MASTER_DELTA_WARN_USD):
                        warnings.append(f"Desfase live↔series: {sdelta:.2f} USD")

        source = "SIN_DATOS_REALES"
        saldo_actual: Optional[float] = None
        last_update: Optional[datetime] = None
        real_series = pd.DataFrame(columns=["timestamp", "equity"])

        if view == "REAL":
            frames = []
            if not hist.empty:
                h2 = hist[["timestamp", "equity"]].copy()
                h2["source"] = "MAESTRO_HISTORY"
                frames.append(h2)
            if not series_csv.empty:
                s2 = series_csv[["timestamp", "equity"]].copy()
                s2["source"] = series_csv["source"] if "source" in series_csv.columns else "MAESTRO_SERIES_CANONICAL"
                frames.append(s2)
            if master is not None:
                mv, mts = master
                frames.append(pd.DataFrame([{"timestamp": mts, "equity": mv, "source": "MAESTRO_LIVE"}]))
            if frames:
                real_series = pd.concat(frames, ignore_index=True)
                real_series["timestamp"] = pd.to_datetime(real_series["timestamp"], errors="coerce", utc=True)
                real_series["equity"] = pd.to_numeric(real_series["equity"], errors="coerce")
                real_series = real_series.dropna(subset=["timestamp", "equity"])
                if "source" not in real_series.columns:
                    real_series["source"] = "MAESTRO_SERIES_CANONICAL"
                real_series["source"] = real_series["source"].map(self._normalize_source_label)
                real_series["source_rank"] = real_series["source"].map(self._source_rank).fillna(0).astype(int)
                real_series = real_series.sort_values(["timestamp", "source_rank"], ascending=[True, False]).drop_duplicates(subset=["timestamp"], keep="first")
                real_series = real_series.drop(columns=["source_rank"], errors="ignore")
                real_series = real_series.reset_index(drop=True)

            live_fresh = False
            if master is not None:
                _mv, mts_live = master
                live_age_sec = max(0.0, (_now().astimezone(timezone.utc) - mts_live.astimezone(timezone.utc)).total_seconds())
                live_fresh = live_age_sec <= float(MASTER_LIVE_STALE_SECONDS)

            if master is not None and live_fresh:
                mv, mts = master
                source = "MAESTRO_LIVE"
                saldo_actual = mv
                last_update = mts
                warnings.append("REAL principal = MAESTRO_LIVE")
            else:
                latest_hist = None if hist.empty else hist.iloc[-1]
                latest_series = None if series_csv.empty else series_csv.iloc[-1]
                hts = pd.to_datetime(latest_hist["timestamp"], errors="coerce", utc=True) if latest_hist is not None else pd.NaT
                sts = pd.to_datetime(latest_series["timestamp"], errors="coerce", utc=True) if latest_series is not None else pd.NaT
                if latest_hist is not None and (pd.isna(sts) or (not pd.isna(hts) and hts >= sts)):
                    source = "MAESTRO_HISTORY"
                    saldo_actual = float(latest_hist["equity"])
                    last_update = pd.to_datetime(latest_hist["timestamp"], errors="coerce", utc=True).to_pydatetime()
                    warnings.append("REAL principal = MAESTRO_HISTORY")
                elif latest_series is not None:
                    source = self._normalize_source_label(latest_series.get("source")) or "MAESTRO_SERIES_CANONICAL"
                    saldo_actual = float(latest_series["equity"])
                    last_update = pd.to_datetime(latest_series["timestamp"], errors="coerce", utc=True).to_pydatetime()
                    warnings.append(f"REAL principal = {source}")
                if master is not None and not live_fresh and source != "SIN_DATOS_REALES":
                    warnings.append("Live stale descartado como saldo principal")
            if source == "SIN_DATOS_REALES":
                warnings.append("SIN_DATOS_REALES: no hay fuente canónica de saldo real")
        elif not observed.empty:
            source = "OBSERVADO_FALLBACK"
            saldo_actual = float(observed["equity"].iloc[-1])
            last_update = observed["timestamp"].iloc[-1]
            real_series = observed
            warnings.append("DEGRADED: usando observado por falta de feed maestro")
        else:
            live_real = self._parse_observed("REAL") if view == "REAL" else self._parse_observed(view)
            if not live_real.empty:
                source = "OBSERVADO_FALLBACK"
                saldo_actual = float(live_real["equity"].iloc[-1])
                last_update = live_real["timestamp"].iloc[-1]
                real_series = pd.DataFrame([live_real.iloc[-1]])
                warnings.append("DEGRADED: observado de emergencia")
            else:
                warnings.append("saldo real del maestro no disponible")
        if source == "SIN_DATOS_REALES" and view != "REAL" and not observed.empty:
            source = "OBSERVADO_FALLBACK"
            saldo_actual = float(observed["equity"].iloc[-1])
            last_update = observed["timestamp"].iloc[-1]
            real_series = observed
        if source == "SIN_DATOS_REALES" and view != "REAL" and not estimated.empty:
            source = "ESTIMADO_EMERGENCIA"
            saldo_actual = float(estimated["equity"].iloc[-1])
            last_update = estimated["timestamp"].iloc[-1]
            real_series = estimated[["timestamp", "equity"]].copy()
            warnings.append("Usando estimado en emergencia")
        if view == "REAL":
            warnings.append(f"Fuente real efectiva usada: {source}")
            if source != "MAESTRO_LIVE" and master is not None:
                warnings.append("Diag: live descartado por stale/prioridad temporal")

        real_points = int(len(real_series))
        if real_points == 0:
            warnings.append("Sin datos para graficar: 0 muestras reales válidas")
            warnings.append(f"Sin histórico real: no se encontró {SALDO_LIVE_HISTORY_FILE}")
        elif real_points == 1:
            warnings.append("Histórico insuficiente: solo 1 muestra real válida")
            warnings.append("No se puede trazar línea: se requieren al menos 2 puntos")
        if source == "SIN_DATOS_REALES" and not estimated.empty:
            warnings.append("Estimado CSV disponible solo como auxiliar")
        if view == "REAL":
            append_msg = self._persist_real_if_valid(
                series_target_path=series_target_path,
                hist=hist,
                master=master,
                series_csv=series_csv,
                saldo_actual=saldo_actual,
                last_update=last_update,
                source=source,
                observed=observed,
                estimated=estimated,
            )
            if append_msg:
                warnings.append(append_msg)

        mcut = now - timedelta(minutes=VENTANA_MINUTOS)
        hcut = now - timedelta(hours=VENTANA_HORAS)
        dcut = now - timedelta(days=VENTANA_DIAS)
        main_cut = now - timedelta(seconds=_main_window_seconds())

        smain = _sample_window_series(real_series, main_cut, target_points=900)
        smin = _sample_window_series(real_series, mcut, target_points=420)
        shrs = _sample_window_series(real_series, hcut, target_points=520)
        sday = _sample_window_series(real_series, dcut, target_points=360)
        if not sday.empty and len(sday) < MIN_POINTS_FOR_LINE:
            sday = sday.tail(min(120, len(sday))).copy()
            warnings.append("Panel DÍAS en fallback crudo: histórico diario aún insuficiente")

        return Snapshot(
            source=source,
            saldo_actual=saldo_actual,
            last_update=last_update,
            now=now,
            series_real=real_series,
            series_main=smain,
            series_minutes=smin,
            series_hours=shrs,
            series_days=sday,
            series_est=estimated,
            warnings=warnings,
            view=view,
        )


class DashboardWindow(QtWidgets.QMainWindow):
    def __init__(self, engine: DataEngine):
        super().__init__()
        self.engine = engine
        self.view = CUENTA_OBJETIVO if CUENTA_OBJETIVO in ("REAL", "DEMO", "ALL") else "REAL"
        self.last_good_snapshot: Optional[Snapshot] = None
        self.last_good_saldo: Optional[float] = None
        self.last_good_source: Optional[str] = None
        self.last_good_last_update: Optional[datetime] = None
        self.last_build_ms: float = 0.0
        self.refresh_skipped: int = 0
        self.worker_running: bool = False
        self._refresh_in_progress: bool = False
        self._error_throttle: Dict[str, Tuple[float, int]] = {}
        self._last_plot_series: Dict[str, pd.DataFrame] = {}
        self._build_ms_hist = deque(maxlen=120)
        self._force_autorange_once = True
        self._last_scale_mode = str(Y_SCALE_MODE)
        self.markers_enabled = SHOW_LAST_MARKER
        self._last_warn_compact: str = ""
        self.setWindowTitle(f"Monitor Saldo Real Deriv {MONITOR_VERSION}")
        self.resize(1600, 900)

        cw = QtWidgets.QWidget()
        self.setCentralWidget(cw)
        root = QtWidgets.QVBoxLayout(cw)
        root.setContentsMargins(6, 6, 6, 6)
        root.setSpacing(4)

        header = QtWidgets.QFrame(); header.setObjectName("HeaderCard")
        hl = QtWidgets.QVBoxLayout(header); hl.setContentsMargins(8, 6, 8, 6); hl.setSpacing(4)

        top = QtWidgets.QHBoxLayout(); top.setSpacing(10)
        self.lbl_title = QtWidgets.QLabel(f"SALDO REAL DERIV ACTUAL · {MONITOR_VERSION}"); self.lbl_title.setObjectName("Title")
        self.lbl_source = QtWidgets.QLabel("FUENTE: --"); self.lbl_source.setObjectName("BadgeWarn")
        top.addWidget(self.lbl_title, 1); top.addWidget(self.lbl_source, 0)
        hl.addLayout(top)

        self.lbl_big = QtWidgets.QLabel("--"); self.lbl_big.setObjectName("Big")
        self.lbl_big.setAlignment(QtCore.Qt.AlignCenter); self.lbl_big.setMinimumHeight(74)
        self.lbl_big.setSizePolicy(QtWidgets.QSizePolicy.Expanding, QtWidgets.QSizePolicy.Preferred)
        hl.addWidget(self.lbl_big)

        self.lbl_meta_compact = QtWidgets.QLabel("Estado: --")
        self.lbl_meta_compact.setObjectName("MetaCompact")
        hl.addWidget(self.lbl_meta_compact)

        controls = QtWidgets.QHBoxLayout(); controls.setSpacing(6)
        self.btn_real = QtWidgets.QPushButton("REAL")
        self.btn_demo = QtWidgets.QPushButton("DEMO")
        self.btn_all = QtWidgets.QPushButton("ALL")
        self.btn_reset = QtWidgets.QPushButton("RESET VISTA")
        self.btn_export = QtWidgets.QPushButton("EXPORTAR CSV")
        for b in (self.btn_real, self.btn_demo, self.btn_all, self.btn_reset, self.btn_export):
            b.setObjectName("MetaBox")
            controls.addWidget(b)
        self.cmb_min = QtWidgets.QComboBox(); self.cmb_min.setObjectName("MetaBox")
        self.cmb_min.addItems(["15m", "30m", "60m", "90m", "120m"])
        self.cmb_hour = QtWidgets.QComboBox(); self.cmb_hour.setObjectName("MetaBox")
        self.cmb_hour.addItems(["3h", "6h", "9h", "12h", "24h"])
        self.cmb_day = QtWidgets.QComboBox(); self.cmb_day.setObjectName("MetaBox")
        self.cmb_day.addItems(["7d", "14d", "30d"])
        self._sync_window_combos()
        controls.addWidget(self.cmb_min)
        controls.addWidget(self.cmb_hour)
        controls.addWidget(self.cmb_day)
        controls.addStretch(1)
        hl.addLayout(controls)
        root.addWidget(header)

        self.graphics = pg.GraphicsLayoutWidget(); root.addWidget(self.graphics, 3)
        self.p_main = self.graphics.addPlot(row=0, col=0, colspan=2, axisItems={"bottom": SmartDateAxis("bottom"), "left": MoneyAxis("left")})
        self.p_min = self.graphics.addPlot(row=1, col=0, axisItems={"bottom": SmartDateAxis("bottom"), "left": MoneyAxis("left")})
        self.p_hour = self.graphics.addPlot(row=1, col=1, axisItems={"bottom": SmartDateAxis("bottom"), "left": MoneyAxis("left")})
        self.p_day = self.graphics.addPlot(row=2, col=0, colspan=2, axisItems={"bottom": SmartDateAxis("bottom"), "left": MoneyAxis("left")})
        try:
            self.graphics.ci.layout.setRowStretchFactor(0, 5)
            self.graphics.ci.layout.setRowStretchFactor(1, 3)
            self.graphics.ci.layout.setRowStretchFactor(2, 2)
        except Exception:
            pass

        self._style_plot(self.p_main, "EQUITY CURVE PRINCIPAL · dinero vs tiempo")
        self._style_plot(self.p_min, "MINUTOS · detalle")
        self._style_plot(self.p_hour, "HORAS · comportamiento")
        self._style_plot(self.p_day, "DÍAS · tendencia")

        self.plot_states = {
            "main": self._init_plot_state(self.p_main, "#5df2ff", "#d9fbff", _main_window_seconds()),
            "min": self._init_plot_state(self.p_min, "#3fe9ff", "#c6f7ff", VENTANA_MINUTOS * 60),
            "hour": self._init_plot_state(self.p_hour, "#7aa6ff", "#dae3ff", VENTANA_HORAS * 3600),
            "day": self._init_plot_state(self.p_day, "#7ff0b9", "#dcffe9", VENTANA_DIAS * 86400),
        }

        self.lbl_warn = QtWidgets.QLabel(""); self.lbl_warn.setObjectName("Warn"); root.addWidget(self.lbl_warn)
        self.lbl_stats = QtWidgets.QLabel("STATS VIS: --")
        self.lbl_stats.setObjectName("Warn")
        self.lbl_stats.setMaximumHeight(20)
        root.addWidget(self.lbl_stats)
        self.lbl_help = QtWidgets.QLabel(f"Teclas: [1]REAL [2]DEMO [3]ALL [F]Fullscreen [R]Reset [E]Export [Q]Salir · {MONITOR_VERSION}")
        self.lbl_help.setObjectName("Help"); root.addWidget(self.lbl_help)
        self.lbl_help.setMaximumHeight(14)

        self.setStyleSheet(
            """
            QMainWindow, QWidget { background: #0b0f14; color: #d9e2f2; }
            #HeaderCard { background: #0f1622; border: 1px solid #203047; border-radius: 14px; }
            #Title { font-size: 18px; color: #b9d3ff; font-weight: 780; }
            #Big { font-size: 74px; color: #ecfff3; font-weight: 900; padding: 2px 0 4px 0; }
            #MetaCompact { font-size: 11px; color: #9cb4d9; padding: 0px 2px; }
            #MetaBox { font-size: 12px; color: #bdd6ff; background: #101e31; border: 1px solid #263e5f; border-radius: 8px; padding: 5px 9px; }
            #BadgeMaster { font-size: 13px; color: #041d13; background: #72f8b1; border: 1px solid #9dffd0; border-radius: 13px; padding: 4px 11px; font-weight: 900; }
            #BadgeObserved { font-size: 13px; color: #02222b; background: #67efff; border: 1px solid #8ff6ff; border-radius: 13px; padding: 4px 11px; font-weight: 850; }
            #BadgeLive { font-size: 13px; color: #0b2a1f; background: #9ef7d8; border: 1px solid #c0ffe8; border-radius: 13px; padding: 4px 11px; font-weight: 850; }
            #BadgeNeutral { font-size: 13px; color: #d8e7ff; background: #23364f; border: 1px solid #3d5c81; border-radius: 13px; padding: 4px 11px; font-weight: 800; }
            #BadgeWarn { font-size: 13px; color: #3d2a00; background: #ffd67f; border: 1px solid #ffe09e; border-radius: 13px; padding: 4px 11px; font-weight: 850; }
            #BadgeBad { font-size: 13px; color: #390000; background: #ff9c9c; border: 1px solid #ffb8b8; border-radius: 13px; padding: 4px 11px; font-weight: 850; }
            #Warn { font-size: 9px; color: #ffc374; font-weight: 520; }
            #Help { font-size: 8px; color: #6b84a6; }
            """
        )
        pg.setConfigOptions(antialias=True, background="#0b0f14", foreground="#d9e2f2")

        self.timer = QtCore.QTimer(self)
        self.timer.timeout.connect(self.refresh)
        self.timer.start(int(REFRESH_SEGUNDOS * 1000))

        self.btn_real.clicked.connect(lambda: self._switch_view("REAL"))
        self.btn_demo.clicked.connect(lambda: self._switch_view("DEMO"))
        self.btn_all.clicked.connect(lambda: self._switch_view("ALL"))
        self.btn_reset.clicked.connect(self._reset_view)
        self.btn_export.clicked.connect(self._export_visible_csv)
        self.cmb_min.currentTextChanged.connect(self._on_window_combo_changed)
        self.cmb_hour.currentTextChanged.connect(self._on_window_combo_changed)
        self.cmb_day.currentTextChanged.connect(self._on_window_combo_changed)

        if FULLSCREEN_INICIAL:
            self.showMaximized()
        try:
            self.refresh(force=True)
        except Exception as e:
            self._startup_warning = f"Refresh inicial falló: {e}"
            self.lbl_warn.setText(f"⚠ {self._startup_warning}")
            traceback.print_exc()

    def _style_plot(self, plot: pg.PlotItem, title: str):
        plot.setTitle(f"<span style='color:#cfe2ff;font-size:12pt;font-weight:680'>{title}</span>")
        plot.setLabel("left", "USD")
        plot.showGrid(x=True, y=True, alpha=0.05)
        for ax in (plot.getAxis("left"), plot.getAxis("bottom")):
            ax.setTextPen(pg.mkPen("#b9d0ee")); ax.setPen(pg.mkPen("#35506f"))
        plot.addLegend(offset=(5, 5), labelTextSize="7pt")
        y0, y1, _ = self._resolve_y_range(None)
        plot.setYRange(y0, y1, padding=0.0)
        plot.setLimits(yMin=y0, yMax=y1)

    def _resolve_y_range(self, y: Optional[np.ndarray]) -> Tuple[float, float, str]:
        if Y_SCALE_MODE == "manual":
            ymin = float(min(Y_AXIS_MIN_USD, Y_AXIS_MAX_USD))
            ymax = float(max(Y_AXIS_MIN_USD, Y_AXIS_MAX_USD))
            if ymax - ymin < 0.01:
                ymax = ymin + 1.0
            return ymin, ymax, f"manual · min={ymin:,.2f} max={ymax:,.2f}"
        if Y_SCALE_MODE == "capital":
            if CAPITAL_BASE_USD > 0:
                base = float(CAPITAL_BASE_USD)
            elif y is not None and len(y) > 0:
                base = float(max(0.01, y[-1]))
            else:
                base = 10.0
            data_span = 0.0
            if y is not None and len(y) > 1:
                data_span = float(max(0.0, np.nanmax(y) - np.nanmin(y)))
            band = max(2.0, base * 0.35, data_span * 2.5)
            y0 = max(0.0, base - band * 0.5)
            y1 = y0 + band
            return y0, y1, f"capital · base={base:,.2f} span={band:,.2f}"
        if y is None or len(y) == 0:
            span = float(max(10.0, Y_AUTO_SPAN_USD))
            return 0.0, span, f"auto · span={span:,.2f}"
        ymin_data = float(np.nanmin(y))
        ymax_data = float(np.nanmax(y))
        span = float(max(0.0, ymax_data - ymin_data))
        if span < 1e-9:
            pad = max(0.5, abs(ymin_data) * 0.10)
        else:
            pad = max(0.25, span * 0.08)
        y0 = max(0.0, ymin_data - pad)
        y1 = ymax_data + pad
        if y1 - y0 < 0.5:
            y1 = y0 + 0.5
        return y0, y1, f"auto · data=[{ymin_data:,.2f},{ymax_data:,.2f}]"

    def _init_plot_state(self, plot: pg.PlotItem, color: str, endpoint: str, canonical_window_s: int) -> Dict[str, object]:
        glow = plot.plot([], [], pen=pg.mkPen(color + "55", width=8.0), name=None)
        line = plot.plot([], [], pen=pg.mkPen(color, width=5.2), name="Equity")
        last = plot.plot([], [], pen=None, symbol="o", symbolSize=5, symbolBrush=endpoint, name=None)
        txt = pg.TextItem(text="", color="#9ec2ff", anchor=(0, 1))
        plot.addItem(txt)
        return {"plot": plot, "glow": glow, "line": line, "last": last, "text": txt, "endpoint": endpoint, "canonical_window_s": int(canonical_window_s)}

    def _sync_window_combos(self):
        self.cmb_min.setCurrentText(f"{int(VENTANA_MINUTOS)}m")
        self.cmb_hour.setCurrentText(f"{int(VENTANA_HORAS)}h")
        self.cmb_day.setCurrentText(f"{int(VENTANA_DIAS)}d")

    def _on_window_combo_changed(self, _text: str):
        global VENTANA_MINUTOS, VENTANA_HORAS, VENTANA_DIAS
        try:
            VENTANA_MINUTOS = int(str(self.cmb_min.currentText()).replace("m", "").strip())
            VENTANA_HORAS = int(str(self.cmb_hour.currentText()).replace("h", "").strip())
            VENTANA_DIAS = int(str(self.cmb_day.currentText()).replace("d", "").strip())
        except Exception:
            return
        self.plot_states["min"]["canonical_window_s"] = int(VENTANA_MINUTOS) * 60
        self.plot_states["hour"]["canonical_window_s"] = int(VENTANA_HORAS) * 3600
        self.plot_states["day"]["canonical_window_s"] = int(VENTANA_DIAS) * 86400
        self.plot_states["main"]["canonical_window_s"] = _main_window_seconds()
        self.refresh(force=True)

    def _set_x_range_visible(self, plot: pg.PlotItem, x: np.ndarray, canonical_window_s: int):
        if len(x) == 0:
            return
        xmin = float(np.nanmin(x))
        xmax = float(np.nanmax(x))
        span = max(0.0, xmax - xmin)
        if len(x) == 1:
            pad = max(MIN_X_SPAN_SECONDS, canonical_window_s * 0.02)
            plot.setXRange(xmin - pad, xmax + pad, padding=0.0)
            return
        if span < float(canonical_window_s):
            pad = max(MIN_X_SPAN_SECONDS, span * 0.08, canonical_window_s * 0.01)
            plot.setXRange(xmin - pad, xmax + pad, padding=0.0)
        else:
            plot.setXRange(xmax - float(canonical_window_s), xmax, padding=0.0)

    def _switch_view(self, view: str):
        self.view = view
        self.refresh(force=True)

    def _reset_view(self):
        self.p_main.enableAutoRange(); self.p_min.enableAutoRange(); self.p_hour.enableAutoRange(); self.p_day.enableAutoRange()
        self._force_autorange_once = True
        self.refresh(force=True)

    def _export_visible_csv(self):
        vis = _sanitize_series_for_plot(self._last_plot_series.get("main", pd.DataFrame(columns=["timestamp", "equity"])))
        if vis.empty:
            self.lbl_warn.setText("⚠ Exportación omitida: no hay serie visible")
            return
        now_tag = datetime.now().strftime("%Y%m%d_%H%M%S")
        out_path = self.engine.base_dir / f"monitor_visible_export_{self.view.lower()}_{now_tag}.csv"
        src = (self.last_good_source or "--")
        exp = vis.copy()
        exp["source"] = src
        exp["view"] = self.view
        exp["window_tag"] = "visible_main"
        exp.to_csv(out_path, index=False, columns=["timestamp", "equity", "source", "view", "window_tag"])
        self.lbl_warn.setText(f"⚠ Exportado visible CSV: {out_path}")

    def keyPressEvent(self, ev: QtGui.QKeyEvent):
        k = ev.key()
        if k == QtCore.Qt.Key_1:
            self.view = "REAL"; self.refresh(force=True)
        elif k == QtCore.Qt.Key_2:
            self.view = "DEMO"; self.refresh(force=True)
        elif k == QtCore.Qt.Key_3:
            self.view = "ALL"; self.refresh(force=True)
        elif k == QtCore.Qt.Key_F:
            self.showNormal() if self.isFullScreen() else self.showFullScreen()
        elif k == QtCore.Qt.Key_R:
            self._reset_view()
        elif k == QtCore.Qt.Key_E:
            self._export_visible_csv()
        elif k == QtCore.Qt.Key_Q:
            self.close()
        else:
            super().keyPressEvent(ev)

    def changeEvent(self, ev: QtCore.QEvent):
        if ev.type() == QtCore.QEvent.WindowStateChange:
            interval = REFRESH_SEGUNDOS_MINIMIZADO if self.isMinimized() else REFRESH_SEGUNDOS
            self.timer.setInterval(int(interval * 1000))
        super().changeEvent(ev)

    def _is_snapshot_valid(self, snap: Snapshot) -> bool:
        return (
            _is_valid_number(snap.saldo_actual)
            or (snap.series_real is not None and not snap.series_real.empty)
            or (snap.series_main is not None and not snap.series_main.empty)
        )

    def _update_last_good(self, snap: Snapshot):
        if not self._is_snapshot_valid(snap):
            return
        self.last_good_snapshot = snap
        if _is_valid_number(snap.saldo_actual):
            self.last_good_saldo = float(snap.saldo_actual)
        if snap.source:
            self.last_good_source = snap.source
        if snap.last_update is not None:
            self.last_good_last_update = snap.last_update

    def _throttled_warn(self, key: str, msg: str, cooldown_s: float = 20.0):
        now_mono = time.monotonic()
        prev = self._error_throttle.get(key, (0.0, 0))
        last_ts, count = prev
        count += 1
        self._error_throttle[key] = (now_mono, count)
        if (now_mono - last_ts) >= cooldown_s:
            print(f"[MONITOR][WARN] {msg} (x{count})")
            self._error_throttle[key] = (now_mono, 0)

    def _update_plot_state(self, state: Dict[str, object], s: pd.DataFrame) -> Tuple[str, float, float]:
        plot = state["plot"]
        glow = state["glow"]; line = state["line"]; last = state["last"]; txt = state["text"]
        endpoint = state.get("endpoint", "#9ef7d8")
        s = _sanitize_series_for_plot(s)
        if s.empty:
            glow.setData([], [])
            line.setData([], [])
            last.setData([], [])
            txt.setText("Sin puntos")
            y0, y1, scale_info = self._resolve_y_range(None)
            plot.setYRange(y0, y1, padding=0.0)
            return "sin datos", y0, y1

        x = (s["timestamp"].astype("int64") / 1e9).to_numpy(dtype=float)
        y = s["equity"].to_numpy(dtype=float)

        if len(x) >= MIN_POINTS_FOR_LINE:
            glow.setData(x, y)
            line.setData(x, y)
            txt.setText("")
        else:
            glow.setData([], [])
            line.setData([], [])
            txt.setText("1 punto: esperando más histórico")

        marker_size = 8 if len(x) == 1 else 4
        try:
            last.setSymbolBrush(endpoint)
        except Exception:
            pass
        if SHOW_LAST_MARKER:
            last.setData([x[-1]], [y[-1]], symbolSize=marker_size)
        else:
            last.setData([], [])
        y0, y1, scale_info = self._resolve_y_range(y)
        plot.setYRange(y0, y1, padding=0.0)
        if Y_SCALE_MODE == "manual":
            plot.setLimits(yMin=y0, yMax=y1)
        self._set_x_range_visible(plot, x, int(state["canonical_window_s"]))
        return scale_info, y0, y1

    def refresh(self, force: bool = False):
        if self.isMinimized() and not force:
            self.refresh_skipped += 1
            return
        if self._refresh_in_progress and not force:
            self.refresh_skipped += 1
            return
        self._refresh_in_progress = True
        try:
            if not MONITOR_BUILD_ID or MIN_POINTS_FOR_LINE != 2:
                self.lbl_warn.setText("⚠ Versión desactualizada o incompleta del monitor detectada")
            scale_mode_now = str(Y_SCALE_MODE)
            if scale_mode_now != str(self._last_scale_mode):
                self._last_scale_mode = scale_mode_now
                self._force_autorange_once = True
            build_t0 = time.perf_counter()
            snap = self.engine.build_snapshot(self.view)
            self.last_build_ms = (time.perf_counter() - build_t0) * 1000.0
            self._build_ms_hist.append(self.last_build_ms)
            current_valid = self._is_snapshot_valid(snap)
            self._update_last_good(snap)

            status = "OK"
            if not current_valid and self.last_good_snapshot is not None:
                status = "STALE"
            elif current_valid and self.view == "REAL" and snap.source in ("MAESTRO_HISTORY_DEGRADED", "SERIE_CSV_DEGRADED"):
                status = "DEGRADED"
            elif not current_valid and self.last_good_snapshot is None:
                status = "NO DATA"

            # FAST-PATH UI principal (saldo + badge): nunca debe caer por errores accesorios.
            effective_saldo = snap.saldo_actual if _is_valid_number(snap.saldo_actual) else self.last_good_saldo
            if _is_valid_number(effective_saldo):
                self.lbl_big.setText(_fmt_money(float(effective_saldo)))
            else:
                self.lbl_big.setText("--")
            raw_src = snap.source.upper().strip()
            effective_src = raw_src if current_valid else ((self.last_good_source or raw_src).upper().strip() if self.last_good_source or raw_src else "--")
            self.lbl_source.setText(f"FUENTE: {effective_src} · {status}")
            if status == "NO DATA":
                self.lbl_source.setObjectName("BadgeBad"); self.lbl_big.setStyleSheet("color:#ffb9b9;")
            elif status == "STALE":
                self.lbl_source.setObjectName("BadgeWarn"); self.lbl_big.setStyleSheet("color:#ffe9b8;")
            elif status == "DEGRADED":
                self.lbl_source.setObjectName("BadgeObserved"); self.lbl_big.setStyleSheet("color:#67efff;")
            elif effective_src in ("MAESTRO_LIVE", "MAESTRO_5R6M"):
                self.lbl_source.setObjectName("BadgeMaster"); self.lbl_big.setStyleSheet("color:#72f8b1;")
            elif effective_src in ("MAESTRO_HISTORY_DEGRADED", "SERIE_CSV_DEGRADED"):
                self.lbl_source.setObjectName("BadgeObserved"); self.lbl_big.setStyleSheet("color:#67efff;")
            elif effective_src in ("SIN_DATOS_REALES",):
                self.lbl_source.setObjectName("BadgeBad"); self.lbl_big.setStyleSheet("color:#ffb9b9;")
            else:
                self.lbl_source.setObjectName("BadgeNeutral"); self.lbl_big.setStyleSheet("color:#d8e7ff;")
            self.lbl_source.style().unpolish(self.lbl_source); self.lbl_source.style().polish(self.lbl_source)

            effective_last_update = snap.last_update if snap.last_update else self.last_good_last_update
            last = effective_last_update.astimezone(DISPLAY_TZ).strftime("%H:%M:%S") if effective_last_update else "--"

            main_scale = "--"
            main_y0, main_y1 = 0.0, 0.0
            series_map = {
                "main": snap.series_main,
                "min": snap.series_minutes,
                "hour": snap.series_hours,
                "day": snap.series_days,
            }
            try:
                for key, series in (
                    ("main", series_map["main"]),
                    ("min", series_map["min"]),
                    ("hour", series_map["hour"]),
                    ("day", series_map["day"]),
                ):
                    try:
                        use_series = _sanitize_series_for_plot(series)
                        if use_series.empty and key in self._last_plot_series and not self._last_plot_series[key].empty:
                            use_series = self._last_plot_series[key]
                            if status in ("STALE", "DEGRADED"):
                                snap.warnings.append(f"Mostrando última serie válida en panel {key}")
                        elif not use_series.empty:
                            self._last_plot_series[key] = use_series
                        scale_info, py0, py1 = self._update_plot_state(self.plot_states[key], use_series)
                        if key == "main":
                            main_scale = scale_info
                            main_y0, main_y1 = py0, py1
                    except Exception as plot_err:
                        snap.warnings.append(f"plot {key} con error: {plot_err}")
                        self._throttled_warn(f"plot:{key}", f"Error en gráfico {key}: {plot_err}")
                visible = _sanitize_series_for_plot(series_map["main"])
                if visible.empty and "main" in self._last_plot_series:
                    visible = self._last_plot_series["main"]
                n_visible = int(len(visible))
                if n_visible >= 1:
                    first = float(visible["equity"].iloc[0])
                    last_v = float(visible["equity"].iloc[-1])
                    delta = last_v - first
                    pct = (delta / first * 100.0) if abs(first) > 1e-12 else 0.0
                    compact_delta = f"{delta:+,.2f} USD ({pct:+.2f}%)"
                else:
                    compact_delta = "--"
                if n_visible >= 1:
                    min_v = float(visible["equity"].min())
                    max_v = float(visible["equity"].max())
                    first_v = float(visible["equity"].iloc[0])
                    last_v = float(visible["equity"].iloc[-1])
                    dd = min_v - max_v
                    amp_pct = ((max_v - min_v) / first_v * 100.0) if abs(first_v) > 1e-12 else 0.0
                    self.lbl_stats.setText(
                        f"VIS | first={first_v:,.2f} last={last_v:,.2f} max={max_v:,.2f} min={min_v:,.2f} "
                        f"drawdown={dd:,.2f} rango={max_v-min_v:,.2f} amp={amp_pct:.2f}% pts={n_visible}"
                    )
                else:
                    self.lbl_stats.setText("STATS VIS: --")
                self.lbl_meta_compact.setText(
                    f"{snap.now.strftime('%H:%M:%S %Z')} · última {last} · pts {n_visible} · Δvis {compact_delta}"
                )
            else:
                self.lbl_stats.setText("STATS VIS: --")
            self.lbl_meta_compact.setText(
                f"{snap.now.strftime('%H:%M:%S %Z')} · última {last} · pts {n_visible} · Δvis {compact_delta}"
            )

            last_good_age = "--"
            if self.last_good_last_update is not None:
                age_s = max(0.0, (snap.now - self.last_good_last_update.astimezone(DISPLAY_TZ)).total_seconds())
                last_good_age = f"{age_s:,.1f}s"
            if status == "STALE":
                snap.warnings.insert(0, "Mostrando último saldo válido")
            elif status == "DEGRADED":
                snap.warnings.insert(0, "Modo degradado: fuente principal no disponible, fallback válido activo")
            elif status == "NO DATA":
                snap.warnings.insert(0, "No hay datos válidos desde el arranque")

            if snap.warnings:
                compact = [w.strip()[:96] + ("…" if len(w.strip()) > 96 else "") for w in snap.warnings[:2]]
                compact_msg = "⚠ " + " · ".join(compact)
                if compact_msg != self._last_warn_compact:
                    self.lbl_warn.setText(compact_msg)
                    self._last_warn_compact = compact_msg
                self.lbl_warn.setToolTip(
                    "\n".join(
                        snap.warnings
                        + [
                            f"Estado: {status}",
                            f"Fuente efectiva actual: {effective_src}",
                            f"build ms: {self.last_build_ms:,.2f}",
                            f"build ms avg: {np.mean(self._build_ms_hist):,.2f}" if self._build_ms_hist else "build ms avg: --",
                            f"Escala efectiva: {main_scale}",
                            f"Escala main: {Y_SCALE_MODE} | y=[{main_y0:,.2f}, {main_y1:,.2f}]",
                        ]
                    )
                )
            else:
                self.lbl_warn.setText("")
                self._last_warn_compact = ""
                self.lbl_warn.setToolTip(
                    f"Estado: {status}\n"
                    f"Fuente efectiva actual: {effective_src}\n"
                    f"Fuente último saldo válido: {self.last_good_source or '--'}\n"
                    f"Edad último saldo válido: {last_good_age}\n"
                    f"build ms: {self.last_build_ms:,.2f}\n"
                    f"build ms avg: {np.mean(self._build_ms_hist):,.2f}\n"
                    f"refresh skipped: {self.refresh_skipped}\n"
                    f"worker running: {'yes' if self.worker_running else 'no'}\n"
                    f"filas series_real: {len(_sanitize_series_for_plot(snap.series_real))}\n"
                    f"filas series_main: {len(_sanitize_series_for_plot(snap.series_main))}\n"
                    f"ruta live: {SALDO_LIVE_SHARED_PATH}\n"
                    f"ruta history: {SALDO_LIVE_HISTORY_SHARED_PATH}\n"
                    f"ruta series csv: {SALDO_SERIES_CSV_PATH}\n"
                    f"Escala efectiva: {main_scale}\n"
                    f"Escala main: {Y_SCALE_MODE} | y=[{main_y0:,.2f}, {main_y1:,.2f}]"
                )
            if self._force_autorange_once:
                self._force_autorange_once = False
        except Exception as e:
            self._throttled_warn("refresh", f"Error monitor: {e}")
            if self.last_good_saldo is not None:
                self.lbl_big.setText(_fmt_money(self.last_good_saldo))
            self.lbl_warn.setText(f"⚠ Error monitor (conservando último dato válido): {e}")
        finally:
            self._refresh_in_progress = False


def main():
    print(f"[MONITOR] Monitor Saldo Real Deriv {MONITOR_VERSION} · build={MONITOR_BUILD_ID}")
    try:
        app = QtWidgets.QApplication(sys.argv)
        w = DashboardWindow(DataEngine(Path(__file__).resolve().parent))
        w.show()
        return int(app.exec())
    except Exception:
        print("[MONITOR][ERROR] Falló el arranque del monitor.")
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
