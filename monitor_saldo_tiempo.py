#!/usr/bin/env python3
"""
Monitor independiente de saldo REAL (5R6M) con CSV persistente y gráfica viva.

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
import sys
import threading
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import List, Optional, Tuple

import tkinter as tk
from tkinter import ttk

import matplotlib.dates as mdates
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure


# =========================
# Configuración
# =========================
SAMPLE_INTERVAL_SECONDS = float(os.getenv("SALDO_MONITOR_SAMPLE_INTERVAL", "1.0"))
MAX_SECONDS_WITHOUT_CHANGE = float(os.getenv("SALDO_MONITOR_MAX_SAME", "12.0"))
SOURCE_STALE_SECONDS = float(os.getenv("SALDO_MONITOR_SOURCE_STALE", "20.0"))
CSV_WRITE_RETRIES = int(os.getenv("SALDO_MONITOR_WRITE_RETRIES", "8"))
CSV_WRITE_RETRY_SLEEP = float(os.getenv("SALDO_MONITOR_WRITE_RETRY_SLEEP", "0.15"))
DERIV_WS_URL = os.getenv("DERIV_WS_URL", "wss://ws.derivws.com/websockets/v3?app_id=1089")

CSV_FILENAME = "saldo_real_series.csv"
CSV_HEADERS = ["ts_epoch", "ts_iso", "saldo", "fuente", "maestro_activo", "observacion"]

SALDO_LIVE_FILE = "saldo_real_live.json"
SALDO_HISTORY_FILE = "saldo_real_live_history.jsonl"
SALDO_SERIES_FILE = "saldo_real_series.csv"

SCRIPT_DIR = Path(__file__).resolve().parent
HOME_DIR = Path.home()


@dataclass
class SaldoSample:
    ts_epoch: float
    ts_iso: str
    saldo: Optional[float]
    fuente: str
    maestro_activo: int
    observacion: str


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
    return datetime.now(timezone.utc).isoformat()


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


# =========================
# Fuentes de saldo
# =========================
def detector_fuente_saldo() -> List[Tuple[str, Path]]:
    """Devuelve candidatos en orden de prioridad (fuente, ruta)."""
    env_live = Path(os.path.expanduser(os.getenv("SALDO_LIVE_SHARED_PATH", str(HOME_DIR / SALDO_LIVE_FILE))))
    env_history = Path(os.path.expanduser(os.getenv("SALDO_LIVE_HISTORY_SHARED_PATH", str(env_live.parent / SALDO_HISTORY_FILE))))
    env_series = Path(os.path.expanduser(os.getenv("SALDO_SERIES_CSV_PATH", str(SCRIPT_DIR / SALDO_SERIES_FILE))))

    shared = [
        ("shared_live", env_live),
        ("shared_history", env_history),
        ("shared_series", env_series),
    ]

    local = [
        ("local_live", SCRIPT_DIR / SALDO_LIVE_FILE),
        ("local_history", SCRIPT_DIR / SALDO_HISTORY_FILE),
        ("local_series", SCRIPT_DIR / SALDO_SERIES_FILE),
    ]

    dedup: List[Tuple[str, Path]] = []
    seen = set()
    for src, p in (shared + local):
        key = str(p.resolve()) if p.exists() else str(p)
        if key in seen:
            continue
        seen.add(key)
        dedup.append((src, p))
    return dedup


async def _leer_saldo_deriv_ws() -> Optional[SaldoSample]:
    token = None
    token_file = SCRIPT_DIR / "token_actual.txt"
    if token_file.exists():
        for line in token_file.read_text(encoding="utf-8", errors="ignore").splitlines():
            txt = line.strip()
            if txt:
                token = txt
                break
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


def leer_saldo_desde_fuente() -> SaldoSample:
    now = time.time()
    for fuente, path in detector_fuente_saldo():
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
                return SaldoSample(ts_epoch, _now_iso(), saldo, fuente, 1, obs)

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
                return SaldoSample(ts_epoch, _now_iso(), saldo, fuente, 1, obs)

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
                    # formato maestro: timestamp,equity,source
                    saldo = _to_float(cols[1])
                    try:
                        ts_epoch = datetime.fromisoformat(cols[0].replace("Z", "+00:00")).timestamp()
                    except Exception:
                        ts_epoch = now
                if saldo is None and len(cols) >= 3:
                    # formato monitor: ts_epoch,ts_iso,saldo,...
                    ts_epoch = _to_float(cols[0]) or now
                    saldo = _to_float(cols[2])
                if saldo is None:
                    continue
                obs = "ok" if now - ts_epoch <= SOURCE_STALE_SECONDS else "stale"
                return SaldoSample(ts_epoch, _now_iso(), saldo, fuente, 1, obs)
        except Exception:
            continue

    ws_sample = asyncio.run(_leer_saldo_deriv_ws())
    if ws_sample is not None:
        return ws_sample

    return SaldoSample(now, _now_iso(), None, "sin_fuente", 0, "sin_datos")


# =========================
# CSV robusto
# =========================
def _ensure_csv_header(csv_path: Path) -> None:
    csv_path.parent.mkdir(parents=True, exist_ok=True)
    if not csv_path.exists() or csv_path.stat().st_size == 0:
        with csv_path.open("w", newline="", encoding="utf-8") as fh:
            writer = csv.writer(fh)
            writer.writerow(CSV_HEADERS)
            fh.flush()
            os.fsync(fh.fileno())


def anexar_muestra_csv(csv_path: Path, sample: SaldoSample, last_saved: Optional[SaldoSample]) -> bool:
    if sample.saldo is None:
        return False

    should_write = last_saved is None
    if not should_write and last_saved is not None:
        changed = abs(sample.saldo - (last_saved.saldo or sample.saldo)) > 1e-9
        elapsed = sample.ts_epoch - last_saved.ts_epoch >= MAX_SECONDS_WITHOUT_CHANGE
        should_write = changed or elapsed
    if not should_write:
        return False

    _ensure_csv_header(csv_path)
    row = [
        f"{sample.ts_epoch:.3f}",
        sample.ts_iso,
        f"{sample.saldo:.8f}",
        sample.fuente,
        str(sample.maestro_activo),
        sample.observacion,
    ]

    for _ in range(CSV_WRITE_RETRIES):
        try:
            with csv_path.open("a", newline="", encoding="utf-8") as fh:
                csv.writer(fh).writerow(row)
                fh.flush()
                os.fsync(fh.fileno())
            return True
        except PermissionError:
            time.sleep(CSV_WRITE_RETRY_SLEEP)
        except OSError:
            time.sleep(CSV_WRITE_RETRY_SLEEP)
    return False


def cargar_historial_csv(csv_path: Path) -> List[SaldoSample]:
    out: List[SaldoSample] = []
    if not csv_path.exists() or csv_path.stat().st_size == 0:
        return out
    try:
        with csv_path.open("r", newline="", encoding="utf-8", errors="ignore") as fh:
            reader = csv.DictReader(fh)
            for row in reader:
                ts_epoch = _to_float(row.get("ts_epoch"))
                saldo = _to_float(row.get("saldo"))
                if ts_epoch is None or saldo is None:
                    continue
                out.append(
                    SaldoSample(
                        ts_epoch=ts_epoch,
                        ts_iso=row.get("ts_iso", "") or _now_iso(),
                        saldo=saldo,
                        fuente=row.get("fuente", "csv"),
                        maestro_activo=int(_to_float(row.get("maestro_activo")) or 0),
                        observacion=row.get("observacion", "hist"),
                    )
                )
    except Exception:
        return out
    return out


class MonitorSaldoApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Monitor saldo vs tiempo (5R6M)")
        self.csv_path = SCRIPT_DIR / CSV_FILENAME

        self.series: List[SaldoSample] = cargar_historial_csv(self.csv_path)
        self.last_saved: Optional[SaldoSample] = self.series[-1] if self.series else None
        self.last_valid: Optional[SaldoSample] = self.last_saved
        self.stop_evt = threading.Event()
        self.view_mode = tk.StringVar(value="15m")

        self.lbl_saldo = ttk.Label(root, text="--", font=("Segoe UI", 24, "bold"))
        self.lbl_saldo.pack(anchor="w", padx=10, pady=6)

        self.lbl_status = ttk.Label(root, text="Estado: iniciando...")
        self.lbl_status.pack(anchor="w", padx=10)

        controls = ttk.Frame(root)
        controls.pack(fill="x", padx=10, pady=6)
        for txt, val in (("5 min", "5m"), ("15 min", "15m"), ("1 hora", "1h"), ("Todo", "all")):
            ttk.Radiobutton(controls, text=txt, value=val, variable=self.view_mode, command=self.actualizar_grafica).pack(side="left", padx=4)

        fig = Figure(figsize=(10, 5), dpi=100)
        self.ax = fig.add_subplot(111)
        self.ax.set_title("Saldo REAL vs Tiempo")
        self.ax.set_xlabel("Tiempo")
        self.ax.set_ylabel("Dinero / Saldo")
        self.line_main, = self.ax.plot([], [], lw=2, label="Saldo")
        self.line_ma_short, = self.ax.plot([], [], lw=1.2, alpha=0.8, label="MM corta")
        self.line_ma_long, = self.ax.plot([], [], lw=1.2, alpha=0.8, label="MM lenta")
        self.marker_last, = self.ax.plot([], [], marker="o", linestyle="", markersize=6)
        self.ax.legend(loc="best")
        self.ax.grid(True, alpha=0.3)
        self.ax.xaxis.set_major_formatter(mdates.DateFormatter("%H:%M:%S"))

        self.canvas = FigureCanvasTkAgg(fig, master=root)
        self.canvas.get_tk_widget().pack(fill="both", expand=True, padx=10, pady=10)

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        threading.Thread(target=self.loop_muestreo, daemon=True).start()
        self.root.after(500, self.actualizar_grafica)

    def _on_close(self):
        self.stop_evt.set()
        self.root.after(200, self.root.destroy)

    def loop_muestreo(self):
        last_log_err = 0.0
        while not self.stop_evt.is_set():
            started = time.time()
            try:
                sample = leer_saldo_desde_fuente()
                if sample.saldo is not None:
                    self.last_valid = sample
                wrote = anexar_muestra_csv(self.csv_path, sample, self.last_saved)
                if wrote:
                    self.series.append(sample)
                    self.last_saved = sample
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
        ts = datetime.fromtimestamp(sample.ts_epoch, tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
        text = f"Estado: {status} | Fuente: {sample.fuente} | Último saldo válido: {saldo_txt} | Actualización: {ts}"

        def apply_text():
            self.lbl_saldo.config(text=saldo_txt)
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

        xs = [datetime.fromtimestamp(s.ts_epoch, tz=timezone.utc) for s in window]
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
        self.line_ma_short.set_data(xs, ma_short)
        self.line_ma_long.set_data(xs, ma_long)
        self.marker_last.set_data([xs[-1]], [ys[-1]])

        self.ax.relim()
        self.ax.autoscale_view()
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
