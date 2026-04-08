#!/usr/bin/env python3
"""
Monitor independiente de saldo REAL (5R6M) con DB CSV persistente y gráfica viva.

Prioridad de lectura:
1) Feed compartido del maestro (SALDO_LIVE_SHARED_PATH / HISTORY / SERIES)
2) Feed local consolidado del maestro (en carpeta del repo)
3) Fallback opcional por WebSocket Deriv (solo si 1 y 2 fallan)
"""

from __future__ import annotations

import asyncio
import csv
import json
import os
import re
import shutil
import sys
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from zoneinfo import ZoneInfo

import tkinter as tk
from tkinter import messagebox, ttk

import matplotlib.dates as mdates
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure


# =========================
# Configuración
# =========================
SAMPLE_INTERVAL_SECONDS = float(os.getenv("SALDO_MONITOR_SAMPLE_INTERVAL", "1.0"))
MAX_SECONDS_WITHOUT_CHANGE = float(os.getenv("SALDO_MONITOR_MAX_SAME", "12.0"))
SOURCE_STALE_SECONDS = float(os.getenv("SALDO_MONITOR_SOURCE_STALE", "90.0"))
CSV_WRITE_RETRIES = int(os.getenv("SALDO_MONITOR_WRITE_RETRIES", "8"))
CSV_WRITE_RETRY_SLEEP = float(os.getenv("SALDO_MONITOR_WRITE_RETRY_SLEEP", "0.15"))
LOCK_RETRY_SLEEP = float(os.getenv("SALDO_MONITOR_LOCK_RETRY_SLEEP", "0.10"))
DERIV_WS_URL = os.getenv("DERIV_WS_URL", "wss://ws.derivws.com/websockets/v3?app_id=1089")

SOURCE_SERIES_FILE = "saldo_real_series.csv"  # feed del maestro (solo lectura)
DB_FILENAME = "saldo_monitor_db.csv"  # DB canónica del monitor (lectura/escritura)
LEGACY_DB_FILENAME = "saldo_real_series.csv"  # histórico legacy del monitor
DB_HEADERS = ["ts_epoch", "ts_iso", "saldo", "fuente", "maestro_activo", "observacion"]

SALDO_LIVE_FILE = "saldo_real_live.json"
SALDO_HISTORY_FILE = "saldo_real_live_history.jsonl"

SCRIPT_DIR = Path(__file__).resolve().parent
HOME_DIR = Path.home()
LIMA_TZ = ZoneInfo("America/Lima")


@dataclass
class SaldoSample:
    ts_epoch: float
    ts_iso: str
    saldo: Optional[float]
    fuente: str
    maestro_activo: int
    observacion: str


@dataclass
class DbRepairResult:
    migrated_rows: int = 0
    backups: List[Path] = None
    recreated: bool = False
    loaded_rows: int = 0

    def __post_init__(self):
        if self.backups is None:
            self.backups = []


# =========================
# Utilidades de parsing
# =========================
def _to_float(value) -> Optional[float]:
    try:
        if value is None:
            return None
        val = float(str(value).replace(",", "").strip())
        if val != val:
            return None
        return val
    except Exception:
        return None


def _now_iso() -> str:
    return datetime.now(LIMA_TZ).isoformat()


def _fmt_lima(ts_epoch: float) -> str:
    return datetime.fromtimestamp(ts_epoch, tz=LIMA_TZ).strftime("%Y-%m-%d %H:%M:%S PET")


def _extract_saldo(payload: dict) -> Optional[float]:
    for key in ("saldo_real", "equity", "balance", "saldo"):
        val = _to_float(payload.get(key))
        if val is not None:
            return val
    return None


def _extract_ts_epoch(payload: dict) -> Optional[float]:
    for key in ("ts", "timestamp_epoch", "ts_epoch"):
        val = _to_float(payload.get(key))
        if val is not None:
            return val
    raw = payload.get("timestamp") or payload.get("ts_iso")
    if isinstance(raw, str) and raw.strip():
        try:
            return datetime.fromisoformat(raw.replace("Z", "+00:00")).timestamp()
        except Exception:
            return None
    return None


def _read_last_nonempty_line(path: Path) -> Optional[str]:
    try:
        if not path.exists() or path.stat().st_size <= 0:
            return None
        with path.open("rb") as fh:
            fh.seek(0, os.SEEK_END)
            size = fh.tell()
            start = max(0, size - 32_768)
            fh.seek(start, os.SEEK_SET)
            chunk = fh.read().decode("utf-8", errors="ignore")
        lines = [ln.strip() for ln in chunk.splitlines() if ln.strip()]
        return lines[-1] if lines else None
    except Exception:
        return None


def _is_deriv_token(txt: str) -> bool:
    candidate = (txt or "").strip()
    if not candidate:
        return False
    if re.search(r"token|pegar|aqui|placeholder", candidate, flags=re.IGNORECASE):
        return False
    return re.fullmatch(r"[A-Za-z0-9_-]{8,}", candidate) is not None


def _choose_deriv_token() -> Optional[str]:
    candidates: List[str] = []
    env_token = os.getenv("DERIV_API_TOKEN", "").strip()
    if env_token:
        candidates.append(env_token)

    tokens_usuario = SCRIPT_DIR / "tokens_usuario.txt"
    if tokens_usuario.exists():
        for line in tokens_usuario.read_text(encoding="utf-8", errors="ignore").splitlines():
            txt = line.strip()
            if txt:
                candidates.append(txt)

    token_actual = SCRIPT_DIR / "token_actual.txt"
    if token_actual.exists():
        for line in token_actual.read_text(encoding="utf-8", errors="ignore").splitlines():
            txt = line.strip()
            if txt:
                candidates.append(txt)

    for token in candidates:
        if _is_deriv_token(token):
            return token
    return None


# =========================
# Fuentes de saldo
# =========================
def detector_fuente_saldo(db_path: Optional[Path] = None) -> List[Tuple[str, Path]]:
    """Devuelve candidatos en orden de prioridad (fuente, ruta)."""
    env_live = Path(os.path.expanduser(os.getenv("SALDO_LIVE_SHARED_PATH", str(HOME_DIR / SALDO_LIVE_FILE))))
    env_history = Path(os.path.expanduser(os.getenv("SALDO_LIVE_HISTORY_SHARED_PATH", str(env_live.parent / SALDO_HISTORY_FILE))))
    env_series = Path(os.path.expanduser(os.getenv("SALDO_SERIES_CSV_PATH", str(SCRIPT_DIR / SOURCE_SERIES_FILE))))

    shared = [
        ("shared_live", env_live),
        ("shared_history", env_history),
        ("shared_series", env_series),
    ]

    local = [
        ("local_live", SCRIPT_DIR / SALDO_LIVE_FILE),
        ("local_history", SCRIPT_DIR / SALDO_HISTORY_FILE),
        ("local_series", SCRIPT_DIR / SOURCE_SERIES_FILE),
    ]

    excluded = {str(db_path.resolve())} if db_path is not None else set()
    dedup: List[Tuple[str, Path]] = []
    seen = set()
    for src, p in (shared + local):
        key = str(p.resolve()) if p.exists() else str(p)
        if key in seen or key in excluded:
            continue
        seen.add(key)
        dedup.append((src, p))
    return dedup


async def _leer_saldo_deriv_ws() -> Optional[SaldoSample]:
    token = _choose_deriv_token()
    if not token:
        return None

    try:
        import websockets  # type: ignore
    except Exception:
        return None

    try:
        async with websockets.connect(DERIV_WS_URL, ping_interval=20, ping_timeout=20) as ws:
            await ws.send(json.dumps({"authorize": token}))
            auth_raw = await asyncio.wait_for(ws.recv(), timeout=8)
            auth = json.loads(auth_raw)
            if auth.get("error"):
                return None

            await ws.send(json.dumps({"balance": 1}))
            bal_raw = await asyncio.wait_for(ws.recv(), timeout=8)
            bal = json.loads(bal_raw)
            if bal.get("error"):
                return None
            payload = bal.get("balance", {})
            saldo = _to_float(payload.get("balance"))
            if saldo is None:
                return None
            ts_epoch = time.time()
            return SaldoSample(ts_epoch, _now_iso(), saldo, "fallback_deriv_ws", 0, "ok")
    except Exception:
        return None


def leer_saldo_desde_fuente(db_path: Path) -> Tuple[SaldoSample, Optional[Path]]:
    now = time.time()
    for fuente, path in detector_fuente_saldo(db_path=db_path):
        try:
            if "live" in fuente:
                if not path.exists():
                    continue
                payload = json.loads(path.read_text(encoding="utf-8", errors="ignore"))
                saldo = _extract_saldo(payload)
                if saldo is None:
                    continue
                ts_epoch = _extract_ts_epoch(payload) or now
                obs = "ok" if now - ts_epoch <= SOURCE_STALE_SECONDS else "stale"
                return SaldoSample(ts_epoch, _now_iso(), saldo, fuente, 1, obs), path

            if "history" in fuente:
                line = _read_last_nonempty_line(path)
                if not line:
                    continue
                payload = json.loads(line)
                saldo = _extract_saldo(payload)
                if saldo is None:
                    continue
                ts_epoch = _extract_ts_epoch(payload) or now
                obs = "ok" if now - ts_epoch <= SOURCE_STALE_SECONDS else "stale"
                return SaldoSample(ts_epoch, _now_iso(), saldo, fuente, 1, obs), path

            if "series" in fuente:
                if not path.exists() or path.stat().st_size <= 0:
                    continue
                line = _read_last_nonempty_line(path)
                if not line or "timestamp" in line.lower() or "ts_epoch" in line.lower():
                    continue
                cols = [c.strip() for c in line.split(",")]
                saldo = None
                ts_epoch = now
                if len(cols) >= 2:
                    saldo = _to_float(cols[1])
                    try:
                        ts_epoch = datetime.fromisoformat(cols[0].replace("Z", "+00:00")).timestamp()
                    except Exception:
                        ts_epoch = now
                if saldo is None and len(cols) >= 3:
                    ts_epoch = _to_float(cols[0]) or now
                    saldo = _to_float(cols[2])
                if saldo is None:
                    continue
                obs = "ok" if now - ts_epoch <= SOURCE_STALE_SECONDS else "stale"
                return SaldoSample(ts_epoch, _now_iso(), saldo, fuente, 1, obs), path
        except Exception:
            continue

    ws_sample = asyncio.run(_leer_saldo_deriv_ws())
    if ws_sample is not None:
        return ws_sample, None

    return SaldoSample(now, _now_iso(), None, "sin_fuente", 0, "sin_datos"), None


# =========================
# DB CSV robusta
# =========================
def _backup_file(path: Path) -> Path:
    stamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")
    backup = path.with_suffix(path.suffix + f".{stamp}.bak")
    shutil.copy2(path, backup)
    return backup


def _normalize_monitor_row(row: Dict[str, str]) -> Optional[SaldoSample]:
    ts_epoch = _to_float(row.get("ts_epoch"))
    saldo = _to_float(row.get("saldo"))
    if ts_epoch is None or saldo is None:
        return None
    ts_iso = (row.get("ts_iso") or "").strip() or datetime.fromtimestamp(ts_epoch, tz=LIMA_TZ).isoformat()
    fuente = (row.get("fuente") or "db").strip() or "db"
    maestro_activo = int(_to_float(row.get("maestro_activo")) or 0)
    observacion = (row.get("observacion") or "hist").strip() or "hist"
    return SaldoSample(ts_epoch, ts_iso, saldo, fuente, maestro_activo, observacion)


def _parse_legacy_line(line: str) -> Optional[SaldoSample]:
    ln = (line or "").strip()
    if not ln:
        return None
    low = ln.lower()
    if low.startswith("ts_epoch,") or low.startswith("timestamp,equity"):
        return None

    cols = [c.strip() for c in ln.split(",")]
    if len(cols) >= 6:
        return _normalize_monitor_row(
            {
                "ts_epoch": cols[0],
                "ts_iso": cols[1],
                "saldo": cols[2],
                "fuente": cols[3],
                "maestro_activo": cols[4],
                "observacion": ",".join(cols[5:]),
            }
        )

    if len(cols) >= 2:
        # formato maestro: timestamp,equity,source
        ts_epoch = None
        try:
            ts_epoch = datetime.fromisoformat(cols[0].replace("Z", "+00:00")).timestamp()
        except Exception:
            ts_epoch = _to_float(cols[0])
        saldo = _to_float(cols[1])
        if ts_epoch is None or saldo is None:
            return None
        fuente = cols[2] if len(cols) >= 3 else "legacy_series"
        ts_iso = datetime.fromtimestamp(ts_epoch, tz=LIMA_TZ).isoformat()
        return SaldoSample(ts_epoch, ts_iso, saldo, fuente or "legacy_series", 1, "migrado_legacy")

    return None


def _parse_db_file_any_format(path: Path) -> List[SaldoSample]:
    rescued: List[SaldoSample] = []
    if not path.exists() or path.stat().st_size == 0:
        return rescued

    raw_lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
    for line in raw_lines:
        sample = _parse_legacy_line(line)
        if sample is not None:
            rescued.append(sample)
    return rescued


def reparar_y_migrar_db_saldo(db_path: Path, legacy_candidates: List[Path]) -> DbRepairResult:
    result = DbRepairResult()
    db_path.parent.mkdir(parents=True, exist_ok=True)

    candidates = [db_path] + [p for p in legacy_candidates if p != db_path]
    rescued: List[SaldoSample] = []
    for cand in candidates:
        if cand.exists() and cand.stat().st_size > 0:
            rescued.extend(_parse_db_file_any_format(cand))

    # dedup exacta por ts/saldo/fuente
    dedup: Dict[Tuple[int, int, str], SaldoSample] = {}
    for s in rescued:
        if s.saldo is None:
            continue
        key = (int(round(s.ts_epoch * 1000)), int(round(s.saldo * 100000000)), s.fuente)
        dedup[key] = s

    ordered = sorted(dedup.values(), key=lambda x: x.ts_epoch)

    # respaldos de archivos legacy (incluye db inválida existente)
    for cand in candidates:
        if cand.exists() and cand.stat().st_size > 0:
            backup = _backup_file(cand)
            result.backups.append(backup)

    with db_path.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.writer(fh)
        writer.writerow(DB_HEADERS)
        for s in ordered:
            writer.writerow(
                [
                    f"{s.ts_epoch:.3f}",
                    s.ts_iso,
                    f"{(s.saldo or 0.0):.8f}",
                    s.fuente,
                    str(s.maestro_activo),
                    s.observacion,
                ]
            )
        fh.flush()
        os.fsync(fh.fileno())

    result.migrated_rows = len(ordered)
    result.recreated = True
    return result


def ensure_db_header_or_repair(db_path: Path, legacy_candidates: List[Path]) -> DbRepairResult:
    result = DbRepairResult()
    db_path.parent.mkdir(parents=True, exist_ok=True)

    if not db_path.exists():
        with db_path.open("w", newline="", encoding="utf-8") as fh:
            csv.writer(fh).writerow(DB_HEADERS)
            fh.flush()
            os.fsync(fh.fileno())
        return result

    if db_path.stat().st_size == 0:
        with db_path.open("w", newline="", encoding="utf-8") as fh:
            csv.writer(fh).writerow(DB_HEADERS)
            fh.flush()
            os.fsync(fh.fileno())
        result.recreated = True
        return result

    try:
        with db_path.open("r", newline="", encoding="utf-8", errors="ignore") as fh:
            first = fh.readline().strip().lower()
        expected = ",".join(DB_HEADERS).lower()
        if first != expected:
            migrated = reparar_y_migrar_db_saldo(db_path, legacy_candidates)
            result.migrated_rows = migrated.migrated_rows
            result.backups.extend(migrated.backups)
            result.recreated = migrated.recreated
    except Exception:
        migrated = reparar_y_migrar_db_saldo(db_path, legacy_candidates)
        result.migrated_rows = migrated.migrated_rows
        result.backups.extend(migrated.backups)
        result.recreated = migrated.recreated

    return result


def _acquire_lock(lock_path: Path) -> Optional[int]:
    for _ in range(CSV_WRITE_RETRIES):
        try:
            fd = os.open(str(lock_path), os.O_CREAT | os.O_EXCL | os.O_RDWR)
            os.write(fd, str(os.getpid()).encode("utf-8", errors="ignore"))
            return fd
        except FileExistsError:
            time.sleep(LOCK_RETRY_SLEEP)
        except OSError:
            time.sleep(LOCK_RETRY_SLEEP)
    return None


def _release_lock(lock_path: Path, fd: Optional[int]) -> None:
    try:
        if fd is not None:
            os.close(fd)
    except Exception:
        pass
    try:
        if lock_path.exists():
            lock_path.unlink()
    except Exception:
        pass


def anexar_muestra_csv(db_path: Path, sample: SaldoSample, last_saved: Optional[SaldoSample], lock_path: Path) -> Tuple[bool, str]:
    if sample.saldo is None:
        return False, "sin_saldo"

    should_write = last_saved is None
    if not should_write and last_saved is not None:
        changed = abs(sample.saldo - (last_saved.saldo or sample.saldo)) > 1e-9
        elapsed = sample.ts_epoch - last_saved.ts_epoch >= MAX_SECONDS_WITHOUT_CHANGE
        should_write = changed or elapsed
    if not should_write:
        return False, "sin_cambio"

    if last_saved is not None and last_saved.saldo is not None:
        same_exact = (
            abs(sample.ts_epoch - last_saved.ts_epoch) < 1e-9
            and abs(sample.saldo - last_saved.saldo) < 1e-9
            and sample.fuente == last_saved.fuente
        )
        if same_exact:
            return False, "duplicada_exacta"

    row = [
        f"{sample.ts_epoch:.3f}",
        sample.ts_iso,
        f"{sample.saldo:.8f}",
        sample.fuente,
        str(sample.maestro_activo),
        sample.observacion,
    ]

    for _ in range(CSV_WRITE_RETRIES):
        lock_fd = _acquire_lock(lock_path)
        if lock_fd is None:
            time.sleep(CSV_WRITE_RETRY_SLEEP)
            continue
        try:
            with db_path.open("a", newline="", encoding="utf-8") as fh:
                csv.writer(fh).writerow(row)
                fh.flush()
                os.fsync(fh.fileno())
            return True, "ok"
        except PermissionError:
            time.sleep(CSV_WRITE_RETRY_SLEEP)
        except OSError:
            time.sleep(CSV_WRITE_RETRY_SLEEP)
        finally:
            _release_lock(lock_path, lock_fd)
    return False, "write_failed"


def cargar_historial_csv(db_path: Path) -> List[SaldoSample]:
    out: List[SaldoSample] = []
    if not db_path.exists() or db_path.stat().st_size == 0:
        return out

    try:
        with db_path.open("r", newline="", encoding="utf-8", errors="ignore") as fh:
            reader = csv.reader(fh)
            for row in reader:
                if not row:
                    continue
                low0 = (row[0] or "").strip().lower()
                if low0 in {"ts_epoch", "timestamp"}:
                    continue
                sample = _parse_legacy_line(",".join(row))
                if sample is None or sample.saldo is None:
                    continue
                out.append(sample)
    except Exception:
        return []

    out.sort(key=lambda s: s.ts_epoch)
    return out


class MonitorSaldoApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Monitor saldo vs tiempo (5R6M)")
        self.root.configure(bg="#0b0b0b")
        self.db_path = SCRIPT_DIR / DB_FILENAME
        self.lock_path = SCRIPT_DIR / f"{DB_FILENAME}.lock"
        self.legacy_db_path = SCRIPT_DIR / LEGACY_DB_FILENAME
        self.active_source_path: Optional[Path] = None

        repair = ensure_db_header_or_repair(self.db_path, legacy_candidates=[self.legacy_db_path])
        print(f"[DB SALDO][OK] usando db propia: {self.db_path.name}")
        if repair.migrated_rows > 0:
            print(f"[DB SALDO][MIGRADA] {repair.migrated_rows} filas rescatadas desde archivo legacy")
        if repair.recreated:
            print("[DB SALDO][RECREADA] esquema canónico aplicado")
        for bkp in repair.backups:
            print(f"[DB SALDO][BACKUP] {bkp.name}")

        self.series: List[SaldoSample] = cargar_historial_csv(self.db_path)
        print(f"[DB SALDO][CARGA] filas en DB: {len(self.series)} | db_path={self.db_path}")
        self.last_saved: Optional[SaldoSample] = self.series[-1] if self.series else None
        self.last_valid: Optional[SaldoSample] = self.last_saved
        self.skip_counts = {"sin_cambio": 0, "duplicada_exacta": 0}
        self.last_skip_summary_ts = 0.0
        self.skip_summary_every_s = 20.0
        self.stop_evt = threading.Event()
        self.view_mode = tk.StringVar(value="15m")
        self.last_status = "OK"

        self.scale_mode = tk.StringVar(value="AUTO")
        self.min_y_var = tk.StringVar(value="0")
        self.max_y_var = tk.StringVar(value="100")
        self.manual_min_y = 0.0
        self.manual_max_y = 100.0
        self.last_valid_manual_range: Tuple[float, float] = (self.manual_min_y, self.manual_max_y)

        # === Tema oscuro visual (sin tocar lógica) ===
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure(".", background="#101010", foreground="#f5f5f5")
        style.configure("Dark.TFrame", background="#101010")
        style.configure("DarkPanel.TFrame", background="#151515")
        style.configure("Dark.TLabel", background="#101010", foreground="#f5f5f5")
        style.configure("Muted.TLabel", background="#101010", foreground="#cfcfcf")
        style.configure("Scale.TLabel", background="#101010", foreground="#8ad8ff")
        style.configure("Dark.TRadiobutton", background="#151515", foreground="#f5f5f5")
        style.map(
            "Dark.TRadiobutton",
            background=[("active", "#1b1b1b"), ("selected", "#1b1b1b")],
            foreground=[("disabled", "#777777"), ("active", "#f5f5f5"), ("selected", "#8ad8ff")],
        )
        style.configure("Dark.TButton", background="#222222", foreground="#f5f5f5", borderwidth=1, focusthickness=0)
        style.map("Dark.TButton", background=[("active", "#2f2f2f"), ("pressed", "#1d1d1d")])
        style.configure("Dark.TEntry", fieldbackground="#171717", foreground="#f5f5f5")

        header = ttk.Frame(root, style="Dark.TFrame")
        header.pack(fill="x", padx=8, pady=(8, 2))

        status_band = ttk.Frame(header, style="DarkPanel.TFrame")
        status_band.pack(fill="x", pady=(0, 4))
        self.lbl_status = ttk.Label(status_band, text="Estado: iniciando...", style="Muted.TLabel", anchor="center")
        self.lbl_status.pack(fill="x", padx=10, pady=(6, 4))

        saldo_band = ttk.Frame(header, style="DarkPanel.TFrame")
        saldo_band.pack(fill="x", pady=(0, 6))
        self.lbl_saldo = ttk.Label(
            saldo_band,
            text="--",
            font=("Segoe UI", 120, "bold"),
            style="Dark.TLabel",
            anchor="center",
            justify="center",
        )
        self.lbl_saldo.pack(fill="x", padx=10, pady=(6, 8))

        controls = ttk.Frame(header, style="DarkPanel.TFrame")
        controls.pack(fill="x", padx=0, pady=(0, 4))
        for txt, val in (("5 min", "5m"), ("15 min", "15m"), ("1 hora", "1h"), ("Todo", "all")):
            ttk.Radiobutton(
                controls, text=txt, value=val, variable=self.view_mode, command=self.actualizar_grafica, style="Dark.TRadiobutton"
            ).pack(side="left", padx=4, pady=2)

        scale_controls = ttk.Frame(header, style="DarkPanel.TFrame")
        scale_controls.pack(fill="x", padx=0, pady=(0, 2))
        ttk.Label(scale_controls, text="Escala Y:", style="Dark.TLabel").pack(side="left", padx=(6, 6), pady=2)
        ttk.Radiobutton(scale_controls, text="AUTO", value="AUTO", variable=self.scale_mode, command=self.actualizar_grafica, style="Dark.TRadiobutton").pack(side="left", padx=3, pady=2)
        ttk.Radiobutton(scale_controls, text="MANUAL", value="MANUAL", variable=self.scale_mode, command=self.actualizar_grafica, style="Dark.TRadiobutton").pack(side="left", padx=3, pady=2)
        ttk.Label(scale_controls, text="Min Y", style="Dark.TLabel").pack(side="left", padx=(12, 4), pady=2)
        ttk.Entry(scale_controls, textvariable=self.min_y_var, width=10, style="Dark.TEntry").pack(side="left", padx=2, pady=2)
        ttk.Label(scale_controls, text="Max Y", style="Dark.TLabel").pack(side="left", padx=(8, 4), pady=2)
        ttk.Entry(scale_controls, textvariable=self.max_y_var, width=10, style="Dark.TEntry").pack(side="left", padx=2, pady=2)
        ttk.Button(scale_controls, text="Aplicar escala", command=self.aplicar_escala_manual, style="Dark.TButton").pack(side="left", padx=8, pady=2)
        ttk.Button(scale_controls, text="Reset auto", command=self.reset_auto_scale, style="Dark.TButton").pack(side="left", padx=4, pady=2)

        self.lbl_scale = ttk.Label(header, text="ESCALA: AUTO", style="Scale.TLabel", anchor="center")
        self.lbl_scale.pack(fill="x", padx=10, pady=(0, 4))

        fig = Figure(figsize=(10, 5), dpi=100)
        self.ax = fig.add_subplot(111)
        fig.patch.set_facecolor("#0b0b0b")
        self.ax.set_facecolor("#111111")
        self.ax.set_title("Saldo REAL vs Tiempo", color="#f5f5f5")
        self.ax.set_xlabel("Tiempo (hora Perú)", color="#cfcfcf")
        self.ax.set_ylabel("Dinero / Saldo", color="#cfcfcf")
        self.ax.tick_params(colors="#cfcfcf")
        for sp in self.ax.spines.values():
            sp.set_color("#4a4a4a")
        self.line_main, = self.ax.plot([], [], lw=2.2, color="#7fe8ff", label="Saldo")
        self.line_ma_short, = self.ax.plot([], [], lw=1.4, alpha=0.9, color="#8affb2", label="MM corta")
        self.line_ma_long, = self.ax.plot([], [], lw=1.3, alpha=0.9, color="#f4d35e", label="MM lenta")
        self.marker_last, = self.ax.plot([], [], marker="o", linestyle="", markersize=7, color="#ffffff")
        legend = self.ax.legend(loc="best")
        if legend:
            legend.get_frame().set_facecolor("#1a1a1a")
            legend.get_frame().set_edgecolor("#4a4a4a")
            for t in legend.get_texts():
                t.set_color("#f5f5f5")
        self.ax.grid(True, color="#2f2f2f", alpha=0.6, linewidth=0.8)
        self.ax.xaxis.set_major_formatter(mdates.DateFormatter("%H:%M:%S", tz=LIMA_TZ))
        self.ax.tick_params(axis="x", rotation=18)

        self.canvas = FigureCanvasTkAgg(fig, master=root)
        self.canvas.get_tk_widget().pack(fill="both", expand=True, padx=10, pady=(4, 8))
        self.canvas.mpl_connect("motion_notify_event", self._on_plot_hover)
        self._xs_num: List[float] = []
        self._ys_live: List[float] = []

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        threading.Thread(target=self.loop_muestreo, daemon=True).start()
        self.root.after(500, self.actualizar_grafica)

    def _on_plot_hover(self, event):
        if event.inaxes != self.ax or not self._xs_num or not self._ys_live:
            if self.crosshair_v.get_visible() or self.crosshair_h.get_visible() or self.crosshair_txt.get_visible():
                self.crosshair_v.set_visible(False)
                self.crosshair_h.set_visible(False)
                self.crosshair_txt.set_visible(False)
                self.canvas.draw_idle()
            return
        if event.xdata is None or event.ydata is None:
            return
        idx = min(range(len(self._xs_num)), key=lambda i: abs(self._xs_num[i] - float(event.xdata)))
        x_num = self._xs_num[idx]
        y_val = self._ys_live[idx]
        dt = mdates.num2date(x_num, tz=LIMA_TZ).strftime("%H:%M:%S")
        self.crosshair_v.set_xdata([x_num, x_num])
        self.crosshair_h.set_ydata([y_val, y_val])
        self.crosshair_txt.set_text(f"{dt} | {y_val:,.2f}")
        self.crosshair_v.set_visible(True)
        self.crosshair_h.set_visible(True)
        self.crosshair_txt.set_visible(True)
        self.canvas.draw_idle()

    def _on_close(self):
        self.stop_evt.set()
        self.root.after(200, self.root.destroy)

    def aplicar_escala_manual(self):
        try:
            min_y = float(self.min_y_var.get().strip())
            max_y = float(self.max_y_var.get().strip())
            if max_y <= min_y:
                raise ValueError("Max Y debe ser mayor a Min Y")
            self.manual_min_y = min_y
            self.manual_max_y = max_y
            self.last_valid_manual_range = (min_y, max_y)
            self.scale_mode.set("MANUAL")
            self.lbl_scale.config(text=f"ESCALA: MANUAL {min_y:,.2f}..{max_y:,.2f} USD")
            self.actualizar_grafica()
        except Exception:
            prev_min, prev_max = self.last_valid_manual_range
            self.min_y_var.set(f"{prev_min:g}")
            self.max_y_var.set(f"{prev_max:g}")
            messagebox.showwarning("Escala inválida", "Valores inválidos. Usa Max Y > Min Y.")

    def reset_auto_scale(self):
        self.scale_mode.set("AUTO")
        self.lbl_scale.config(text="ESCALA: AUTO")
        self.actualizar_grafica()

    def _apply_y_scale(self, ys: List[float]):
        if not ys:
            return
        mode = self.scale_mode.get().upper()
        ymin = min(ys)
        ymax = max(ys)

        if mode == "AUTO":
            self.ax.relim()
            self.ax.autoscale_view()
            span = max(ymax - ymin, max(abs(ymax), 1.0) * 0.02, 0.5)
            margin = span * 0.10
            self.ax.set_ylim(ymin - margin, ymax + margin)
            self.lbl_scale.config(text="ESCALA: AUTO")
            return

        min_y, max_y = self.manual_min_y, self.manual_max_y
        if max_y <= min_y:
            min_y, max_y = self.last_valid_manual_range

        orig_min, orig_max = min_y, max_y
        margin = max((ymax - ymin) * 0.10, max(abs(ymax), abs(ymin), 1.0) * 0.05, 0.5)
        expanded = False
        if ymax > max_y:
            max_y = ymax + margin
            expanded = True
        if ymin < min_y:
            min_y = ymin - margin
            expanded = True

        if expanded:
            print(f"[ESCALA] expandida automáticamente: {orig_min:,.2f}..{orig_max:,.2f} -> {min_y:,.2f}..{max_y:,.2f}")
            self.manual_min_y = min_y
            self.manual_max_y = max_y
            self.last_valid_manual_range = (min_y, max_y)
            self.min_y_var.set(f"{min_y:g}")
            self.max_y_var.set(f"{max_y:g}")

        self.ax.set_ylim(min_y, max_y)
        self.lbl_scale.config(text=f"ESCALA: MANUAL {min_y:,.2f}..{max_y:,.2f} USD")

    def _flush_skip_summary(self, force: bool = False):
        now = time.time()
        total = int(self.skip_counts.get("sin_cambio", 0)) + int(self.skip_counts.get("duplicada_exacta", 0))
        if total <= 0:
            return
        if (not force) and (now - float(self.last_skip_summary_ts or 0.0) < float(self.skip_summary_every_s)):
            return
        print(
            f"[DB SALDO][SKIP-RESUMEN] "
            f"sin_cambio={int(self.skip_counts.get('sin_cambio', 0))} "
            f"duplicada_exacta={int(self.skip_counts.get('duplicada_exacta', 0))}"
        )
        self.skip_counts = {"sin_cambio": 0, "duplicada_exacta": 0}
        self.last_skip_summary_ts = now

    def loop_muestreo(self):
        last_log_err = 0.0
        while not self.stop_evt.is_set():
            started = time.time()
            try:
                sample, source_path = leer_saldo_desde_fuente(self.db_path)
                if source_path != self.active_source_path:
                    self.active_source_path = source_path
                    if source_path is not None:
                        print(f"[DB SALDO][SOURCE] leyendo desde {sample.fuente}: {source_path}")
                        if "series" in sample.fuente:
                            print("[DB SALDO][WARN] source_series es solo lectura")

                if sample.saldo is not None:
                    self.last_valid = sample
                wrote, reason = anexar_muestra_csv(self.db_path, sample, self.last_saved, self.lock_path)
                if wrote:
                    self._flush_skip_summary(force=True)
                    self.series.append(sample)
                    self.last_saved = sample
                    print(
                        f"[DB SALDO][WRITE] saldo={float(sample.saldo):,.2f} "
                        f"fuente={sample.fuente} ts={_fmt_lima(sample.ts_epoch)} db={self.db_path.name}"
                    )
                elif reason in {"duplicada_exacta", "sin_cambio"}:
                    self.skip_counts[reason] = int(self.skip_counts.get(reason, 0)) + 1
                    self._flush_skip_summary(force=False)

                status = "OK"
                if sample.observacion == "stale":
                    status = "STALE"
                if sample.fuente.startswith("fallback"):
                    status = "FALLBACK"
                self._update_status_ui(sample, status)
            except Exception as exc:
                now = time.time()
                if now - last_log_err >= 5:
                    print(f"[monitor_saldo_tiempo] error: {exc}")
                    last_log_err = now
            elapsed = time.time() - started
            time.sleep(max(0.05, SAMPLE_INTERVAL_SECONDS - elapsed))

    def _update_status_ui(self, sample: SaldoSample, status: str):
        saldo_txt = "--" if sample.saldo is None else f"{sample.saldo:,.2f}"
        ts = _fmt_lima(sample.ts_epoch)
        source_txt = str(self.active_source_path) if self.active_source_path else "n/a"
        text = (
            f"Estado: {status} | Fuente: {sample.fuente} | "
            f"Último saldo válido: {saldo_txt} | Actualización: {ts} | "
            f"DB: {self.db_path.name} | Source: {source_txt}"
        )

        def apply_text():
            self.last_status = status
            self.lbl_saldo.config(text=saldo_txt)
            if status == "OK":
                self.lbl_saldo.config(foreground="#f5f5f5")
            elif status == "STALE":
                self.lbl_saldo.config(foreground="#f4d35e")
            else:
                self.lbl_saldo.config(foreground="#ff9f7f")
            self.lbl_status.config(text=text)

        self.root.after(0, apply_text)

    def actualizar_grafica(self):
        samples = [s for s in self.series if s.saldo is not None]
        if not samples:
            self.canvas.draw_idle()
            self.root.after(900, self.actualizar_grafica)
            return

        now = time.time()
        mode = self.view_mode.get()
        if mode == "5m":
            low = now - 300
        elif mode == "15m":
            low = now - 900
        elif mode == "1h":
            low = now - 3600
        else:
            low = float("-inf")

        window = [s for s in samples if s.ts_epoch >= low]
        if not window:
            window = samples[-1:]

        xs = [datetime.fromtimestamp(s.ts_epoch, tz=LIMA_TZ) for s in window]
        ys = [float(s.saldo) for s in window if s.saldo is not None]

        def moving_avg(vals: List[float], n: int) -> List[float]:
            out = []
            acc = 0.0
            q: List[float] = []
            for v in vals:
                q.append(v)
                acc += v
                if len(q) > n:
                    acc -= q.pop(0)
                out.append(acc / len(q))
            return out

        ma_short = moving_avg(ys, 5)
        ma_long = moving_avg(ys, 20)

        self.line_main.set_data(xs, ys)
        if bool(self.show_ma_short.get()):
            self.line_ma_short.set_data(xs, ma_short)
            self.line_ma_short.set_visible(True)
        else:
            self.line_ma_short.set_visible(False)
        if bool(self.show_ma_long.get()):
            self.line_ma_long.set_data(xs, ma_long)
            self.line_ma_long.set_visible(True)
        else:
            self.line_ma_long.set_visible(False)
        self.marker_last.set_data([xs[-1]], [ys[-1]])
        self.last_price_line.set_ydata([ys[-1], ys[-1]])
        y_min, y_max = min(ys), max(ys)
        self.range_low_line.set_ydata([y_min, y_min])
        self.range_high_line.set_ydata([y_max, y_max])
        self.last_value_annot.xy = (xs[-1], ys[-1])
        self.last_value_annot.set_text(f"  {ys[-1]:,.2f}  ")
        self._xs_num = mdates.date2num(xs).tolist()
        self._ys_live = list(ys)

        self.ax.relim()
        self.ax.autoscale_view()
        self._apply_y_scale(ys)
        self.ax.set_title(f"Saldo REAL vs Tiempo · vista={mode}")
        self.canvas.draw_idle()
        self.root.after(900, self.actualizar_grafica)


def main():
    root = tk.Tk()
    root.geometry("1100x700")
    app = MonitorSaldoApp(root)
    _ = app
    root.mainloop()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(0)
