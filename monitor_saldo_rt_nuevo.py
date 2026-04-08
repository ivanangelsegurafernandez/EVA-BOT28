#!/usr/bin/env python3
from __future__ import annotations

import csv
import json
import logging
import math
import os
import sys
import time
import uuid
from collections import deque
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Optional

try:
    from PyQt5 import QtCore, QtWidgets
except Exception as exc:
    raise RuntimeError("PyQt5 no está disponible. Instálalo con: pip install PyQt5 matplotlib") from exc

import matplotlib

matplotlib.use("Qt5Agg")
import matplotlib.dates as mdates
from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas
from matplotlib.figure import Figure

# ==============================
# Constantes de configuración
# ==============================
POLL_INTERVAL_MS = 1000
SAVE_MIN_INTERVAL_S = 5.0
FREEZE_THRESHOLD_S = 20.0
LAST_GOOD_LIVE_TTL_S = 15.0
LOG_THROTTLE_S = 8.0

LIVE_JSON_MAX_AGE_S = 20.0
HISTORY_JSONL_MAX_AGE_S = 25.0
SERIES_CSV_MAX_AGE_S = 60.0

CSV_MONITOR_FILE = "saldo_muestras_monitor.csv"
CSV_COLUMNS = [
    "timestamp_iso",
    "timestamp_epoch",
    "saldo_real",
    "delta_abs",
    "delta_pct",
    "fuente",
    "fuente_grafica",
    "estado_feed",
    "latencia_seg",
    "muestra_valida",
    "sesion_id",
    "media_1m",
    "media_5m",
    "media_15m",
    "min_1m",
    "max_1m",
    "pendiente_corta",
    "pendiente_media",
]

LIVE_JSON_NAME = "saldo_real_live.json"
HIST_JSONL_NAME = "saldo_real_live_history.jsonl"
SERIES_CSV_NAME = "saldo_real_series.csv"

SOURCE_LABELS = {
    "live": "JSON_LIVE",
    "history": "JSONL_HISTORY",
    "series": "CSV_SERIES",
    "none": "SIN_FUENTE",
}


@dataclass
class FeedSample:
    saldo_real: Optional[float]
    ts_feed_epoch: Optional[float]
    source_kind: str
    source_path: Optional[Path]
    valid_numeric: bool
    fresh_for_ui: bool
    fresh_for_plot: bool
    note: str


@dataclass
class DiscoverResult:
    ui_sample: Optional[FeedSample]
    plot_sample: Optional[FeedSample]
    live_sample: FeedSample
    history_sample: FeedSample
    series_sample: FeedSample
    ui_status: str


@dataclass
class MonitorSample:
    timestamp_iso: str
    timestamp_epoch: float
    saldo_real: Optional[float]
    delta_abs: Optional[float]
    delta_pct: Optional[float]
    fuente: str
    fuente_grafica: str
    estado_feed: str
    latencia_seg: Optional[float]
    muestra_valida: int
    sesion_id: str
    media_1m: Optional[float]
    media_5m: Optional[float]
    media_15m: Optional[float]
    min_1m: Optional[float]
    max_1m: Optional[float]
    pendiente_corta: Optional[float]
    pendiente_media: Optional[float]


class AtomicAppendCSV:
    def __init__(self, path: Path, columns: list[str]):
        self.path = path
        self.columns = columns
        self.lock_path = path.with_suffix(path.suffix + ".lock")
        self._ensure_header()

    def _ensure_header(self) -> None:
        self.path.parent.mkdir(parents=True, exist_ok=True)
        if self.path.exists() and self.path.stat().st_size > 0:
            return
        self.append_row({col: col for col in self.columns})

    def _acquire_lock(self, timeout: float = 1.8, retry_s: float = 0.05) -> bool:
        start = time.monotonic()
        while time.monotonic() - start <= timeout:
            try:
                fd = os.open(str(self.lock_path), os.O_CREAT | os.O_EXCL | os.O_WRONLY)
                os.write(fd, f"{os.getpid()}|{time.time()}".encode("utf-8"))
                os.close(fd)
                return True
            except FileExistsError:
                time.sleep(retry_s)
            except Exception:
                return False
        return False

    def _release_lock(self) -> None:
        try:
            if self.lock_path.exists():
                self.lock_path.unlink()
        except Exception:
            pass

    def append_row(self, row: dict[str, Any]) -> bool:
        if not self._acquire_lock():
            return False
        try:
            vals = ["" if row.get(c) is None else str(row.get(c)) for c in self.columns]
            line = ",".join(self._escape_csv(v) for v in vals) + "\n"
            with open(self.path, "a", encoding="utf-8", newline="") as f:
                f.write(line)
                f.flush()
                os.fsync(f.fileno())
            return True
        finally:
            self._release_lock()

    @staticmethod
    def _escape_csv(v: str) -> str:
        if any(ch in v for ch in [",", '"', "\n", "\r"]):
            return '"' + v.replace('"', '""') + '"'
        return v


class FeedReader:
    def __init__(self, base_dir: Path):
        home_feed = Path(os.path.expanduser("~")) / "saldo_feed_5r6m"
        self.home_feed = home_feed
        self.base_dir = base_dir

        # Prioridad: feed compartido del maestro primero.
        # Para live, preferimos exclusivamente home_feed salvo ausencia total.
        self.candidates = {
            "live": [home_feed / LIVE_JSON_NAME, base_dir / LIVE_JSON_NAME],
            "history": [home_feed / HIST_JSONL_NAME, base_dir / HIST_JSONL_NAME],
            "series": [home_feed / SERIES_CSV_NAME, base_dir / SERIES_CSV_NAME],
        }
        self.file_offsets: dict[Path, int] = {}

    def discover_best_source(self, now_epoch: float) -> DiscoverResult:
        live = self._read_live_json(now_epoch)
        history = self._read_history_jsonl(now_epoch)
        series = self._read_series_csv(now_epoch)

        # UI: SOLO live fresco o history fresco como respaldo temporal.
        ui_sample: Optional[FeedSample] = None
        status = "SIN LIVE"
        if live.valid_numeric and live.fresh_for_ui:
            ui_sample = live
            status = "LIVE OK"
        elif history.valid_numeric and history.fresh_for_ui:
            ui_sample = history
            status = "HISTORY OK"
        elif live.valid_numeric and (not live.fresh_for_ui):
            status = "LIVE STALE"
        elif history.valid_numeric and (not history.fresh_for_ui):
            status = "HISTORY STALE"

        # Plot: live/history/series (series solo gráfica)
        plot_sample = self._choose_plot_sample(live, history, series)

        return DiscoverResult(
            ui_sample=ui_sample,
            plot_sample=plot_sample,
            live_sample=live,
            history_sample=history,
            series_sample=series,
            ui_status=status,
        )

    def _choose_plot_sample(self, live: FeedSample, history: FeedSample, series: FeedSample) -> Optional[FeedSample]:
        candidates = [s for s in (live, history, series) if s.valid_numeric and s.fresh_for_plot]
        if candidates:
            candidates.sort(key=lambda x: (x.ts_feed_epoch or 0.0), reverse=True)
            return candidates[0]

        candidates = [s for s in (live, history, series) if s.valid_numeric]
        if candidates:
            candidates.sort(key=lambda x: (x.ts_feed_epoch or 0.0), reverse=True)
            return candidates[0]
        return None

    def _find_existing(self, kind: str) -> Optional[Path]:
        for p in self.candidates[kind]:
            if p.exists():
                return p
        return None

    def _read_live_json(self, now_epoch: float) -> FeedSample:
        p = self._find_existing("live")
        if not p:
            return FeedSample(None, None, "live", None, False, False, False, "live no encontrado")

        payload = self._safe_read_json(p)
        if payload is None:
            return FeedSample(None, self._mtime_epoch(p), "live", p, False, False, False, "live corrupto/incompleto")

        saldo = self._extract_balance(payload)
        ts = self._extract_timestamp(payload, p)
        valid = self._is_valid_balance(saldo)
        age = self._age_s(now_epoch, ts)
        fresh_ui = valid and (age is not None) and age <= LIVE_JSON_MAX_AGE_S
        fresh_plot = valid and (age is not None) and age <= SERIES_CSV_MAX_AGE_S

        return FeedSample(saldo if valid else None, ts, "live", p, valid, fresh_ui, fresh_plot, "ok" if valid else "saldo inválido")

    def _read_history_jsonl(self, now_epoch: float) -> FeedSample:
        p = self._find_existing("history")
        if not p:
            return FeedSample(None, None, "history", None, False, False, False, "history no encontrado")

        try:
            if p not in self.file_offsets:
                self.file_offsets[p] = max(0, p.stat().st_size - 8192)
            with open(p, "r", encoding="utf-8", errors="ignore") as f:
                f.seek(self.file_offsets[p], os.SEEK_SET)
                chunk = f.read()
                self.file_offsets[p] = f.tell()
        except Exception:
            chunk = ""

        lines = [ln.strip() for ln in chunk.splitlines() if ln.strip()]
        if not lines:
            lines = self._tail_lines(p, max_lines=10)

        for raw in reversed(lines):
            try:
                obj = json.loads(raw)
            except Exception:
                continue
            saldo = self._extract_balance(obj)
            ts = self._extract_timestamp(obj, p)
            valid = self._is_valid_balance(saldo)
            if not valid:
                continue
            age = self._age_s(now_epoch, ts)
            fresh_ui = (age is not None) and age <= HISTORY_JSONL_MAX_AGE_S
            fresh_plot = (age is not None) and age <= SERIES_CSV_MAX_AGE_S
            return FeedSample(saldo, ts, "history", p, True, fresh_ui, fresh_plot, "ok")

        return FeedSample(None, self._mtime_epoch(p), "history", p, False, False, False, "history sin muestra válida")

    def _read_series_csv(self, now_epoch: float) -> FeedSample:
        p = self._find_existing("series")
        if not p:
            return FeedSample(None, None, "series", None, False, False, False, "series no encontrado")

        lines = self._tail_lines(p, max_lines=12)
        if not lines:
            return FeedSample(None, self._mtime_epoch(p), "series", p, False, False, False, "series vacío")

        reader = csv.reader(lines)
        rows = [r for r in reader if r]
        for row in reversed(rows):
            row_low = [str(x).strip().lower() for x in row]
            if row_low and row_low[0] in ("timestamp", "ts_utc"):
                continue
            ts_raw = row[0] if len(row) > 0 else ""
            saldo_raw = row[1] if len(row) > 1 else None
            saldo = self._coerce_float(saldo_raw)
            valid = self._is_valid_balance(saldo)
            if not valid:
                continue
            ts = self._parse_any_datetime(ts_raw) or self._mtime_epoch(p)
            age = self._age_s(now_epoch, ts)
            fresh_plot = (age is not None) and age <= SERIES_CSV_MAX_AGE_S
            # Prohibido para UI, incluso fresco.
            return FeedSample(saldo, ts, "series", p, True, False, fresh_plot, "series solo gráfica")

        return FeedSample(None, self._mtime_epoch(p), "series", p, False, False, False, "series sin valor válido")

    @staticmethod
    def _tail_lines(path: Path, max_lines: int = 10) -> list[str]:
        try:
            with open(path, "rb") as f:
                f.seek(0, os.SEEK_END)
                size = f.tell()
                seek_pos = max(0, size - 8192)
                f.seek(seek_pos, os.SEEK_SET)
                text = f.read().decode("utf-8", errors="ignore")
            lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
            return lines[-max_lines:]
        except Exception:
            return []

    def _safe_read_json(self, path: Path) -> Optional[dict[str, Any]]:
        for _ in range(2):
            try:
                txt = path.read_text(encoding="utf-8", errors="ignore").strip()
                if not txt:
                    return None
                return json.loads(txt)
            except Exception:
                time.sleep(0.02)
        return None

    @staticmethod
    def _extract_balance(payload: dict[str, Any]) -> Optional[float]:
        for k in ("saldo_real", "equity", "balance"):
            if k in payload:
                val = FeedReader._coerce_float(payload.get(k))
                if val is not None:
                    return val
        bal = payload.get("balance")
        if isinstance(bal, dict):
            return FeedReader._coerce_float(bal.get("balance", bal.get("equity")))
        return None

    def _extract_timestamp(self, payload: dict[str, Any], path: Optional[Path]) -> Optional[float]:
        for k in ("ts", "timestamp_epoch", "timestamp"):
            if k in payload:
                v = payload.get(k)
                if isinstance(v, (int, float)):
                    return float(v)
                parsed = self._parse_any_datetime(v)
                if parsed is not None:
                    return parsed
        return self._mtime_epoch(path)

    @staticmethod
    def _parse_any_datetime(v: Any) -> Optional[float]:
        if v is None:
            return None
        if isinstance(v, (int, float)):
            try:
                val = float(v)
                if val > 1e12:
                    val /= 1000.0
                return val
            except Exception:
                return None
        s = str(v).strip()
        if not s:
            return None
        s = s.replace("Z", "+00:00")
        try:
            return datetime.fromisoformat(s).timestamp()
        except Exception:
            pass
        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y/%m/%d %H:%M:%S"):
            try:
                return datetime.strptime(s, fmt).replace(tzinfo=timezone.utc).timestamp()
            except Exception:
                continue
        return None

    @staticmethod
    def _coerce_float(x: Any) -> Optional[float]:
        try:
            if x is None:
                return None
            v = float(str(x).strip())
            return v if math.isfinite(v) else None
        except Exception:
            return None

    @staticmethod
    def _is_valid_balance(v: Optional[float]) -> bool:
        return v is not None and math.isfinite(v)

    @staticmethod
    def _mtime_epoch(path: Optional[Path]) -> Optional[float]:
        try:
            if path and path.exists():
                return path.stat().st_mtime
        except Exception:
            return None
        return None

    @staticmethod
    def _age_s(now_epoch: float, ts_epoch: Optional[float]) -> Optional[float]:
        if ts_epoch is None:
            return None
        age = now_epoch - ts_epoch
        if age < 0:
            return 0.0
        return age


class MonitorSaldoWindow(QtWidgets.QMainWindow):
    def __init__(self, base_dir: Path):
        super().__init__()
        self.base_dir = base_dir
        self.session_id = datetime.now().strftime("%Y%m%d_%H%M%S") + "_" + uuid.uuid4().hex[:8]
        self.reader = FeedReader(base_dir)
        self.csv_writer = AtomicAppendCSV(base_dir / CSV_MONITOR_FILE, CSV_COLUMNS)

        self.samples: list[MonitorSample] = []
        self.ui_series = deque(maxlen=24 * 60 * 60)
        self.plot_series = deque(maxlen=24 * 60 * 60)

        self.last_saved_epoch: Optional[float] = None
        self.last_saved_balance: Optional[float] = None
        self.last_feed_change_epoch: Optional[float] = None
        self.last_good_ui_sample: Optional[FeedSample] = None
        self.last_good_ui_seen_epoch: Optional[float] = None
        self.last_log: dict[str, float] = {}

        self._build_ui()
        self._setup_timers()

    def _build_ui(self) -> None:
        self.setWindowTitle("Monitor Saldo RT 5R6M - Nuevo")
        self.resize(1520, 920)

        central = QtWidgets.QWidget()
        self.setCentralWidget(central)
        root = QtWidgets.QVBoxLayout(central)

        top_grid = QtWidgets.QGridLayout()
        root.addLayout(top_grid)

        self.lbl_saldo = QtWidgets.QLabel("--")
        self.lbl_saldo.setStyleSheet("font-size: 40px; font-weight: 700; color: #0B7D3E;")

        self.lbl_estado = QtWidgets.QLabel("Estado feed: INICIANDO")
        self.lbl_src_ui = QtWidgets.QLabel("Fuente saldo actual: --")
        self.lbl_src_plot = QtWidgets.QLabel("Fuente gráficas: --")
        self.lbl_hora = QtWidgets.QLabel("Hora local: --")
        self.lbl_muestras = QtWidgets.QLabel("Muestras: 0")
        self.lbl_ultima = QtWidgets.QLabel("Última actualización feed: --")
        self.lbl_delta = QtWidgets.QLabel("Δ abs: -- | Δ %: --")
        self.lbl_ind = QtWidgets.QLabel("Indicadores: --")
        self.lbl_stale = QtWidgets.QLabel("Segundos sin cambio: --")

        top_grid.addWidget(QtWidgets.QLabel("Saldo actual"), 0, 0)
        top_grid.addWidget(self.lbl_saldo, 1, 0, 1, 2)
        top_grid.addWidget(self.lbl_estado, 0, 2)
        top_grid.addWidget(self.lbl_src_ui, 0, 3)
        top_grid.addWidget(self.lbl_src_plot, 1, 2)
        top_grid.addWidget(self.lbl_hora, 1, 3)
        top_grid.addWidget(self.lbl_muestras, 2, 2)
        top_grid.addWidget(self.lbl_ultima, 2, 3)
        top_grid.addWidget(self.lbl_delta, 3, 2)
        top_grid.addWidget(self.lbl_stale, 3, 3)
        top_grid.addWidget(self.lbl_ind, 4, 2, 1, 2)

        self.figure = Figure(figsize=(13, 8), constrained_layout=True)
        self.canvas = FigureCanvas(self.figure)
        root.addWidget(self.canvas)

        self.ax_minute = self.figure.add_subplot(311)
        self.ax_hour = self.figure.add_subplot(312)
        self.ax_full = self.figure.add_subplot(313)

        for ax, title in [
            (self.ax_minute, "Gráfica minuto a minuto (últimos 15 min)"),
            (self.ax_hour, "Gráfica hora a hora (últimas 24 h)"),
            (self.ax_full, "Gráfica general de toda la sesión"),
        ]:
            ax.set_title(title)
            ax.set_ylabel("Saldo")
            ax.grid(True, alpha=0.25)
            ax.xaxis.set_major_formatter(mdates.DateFormatter("%H:%M:%S"))

        self.ax_full.set_xlabel("Tiempo")

    def _setup_timers(self) -> None:
        self.timer = QtCore.QTimer(self)
        self.timer.timeout.connect(self._tick)
        self.timer.start(POLL_INTERVAL_MS)

    def _tick(self) -> None:
        now = time.time()
        result = self.reader.discover_best_source(now)

        self._log_source_health(result)

        ui_sample = result.ui_sample
        plot_sample = result.plot_sample

        # Conservación corta del último live/history bueno para UI.
        ui_used: Optional[FeedSample] = ui_sample
        ui_status = result.ui_status
        if ui_used and ui_used.valid_numeric:
            self.last_good_ui_sample = ui_used
            self.last_good_ui_seen_epoch = now
        else:
            ttl_ok = (
                self.last_good_ui_sample is not None
                and self.last_good_ui_seen_epoch is not None
                and (now - self.last_good_ui_seen_epoch) <= LAST_GOOD_LIVE_TTL_S
            )
            if ttl_ok:
                ui_used = self.last_good_ui_sample
                ui_status = "STALE TTL"
            else:
                ui_used = None
                if result.ui_status in ("LIVE STALE", "HISTORY STALE"):
                    ui_status = "STALE"
                else:
                    ui_status = "SIN LIVE"
                self._log_throttled(
                    "ui_blocked",
                    "SALDO UI BLOQUEADO POR FALTA DE LIVE/HISTORY FRESCO",
                    logging.WARNING,
                )

        if plot_sample and plot_sample.valid_numeric and plot_sample.saldo_real is not None:
            self._append_plot_point(now, plot_sample)

        current_balance = ui_used.saldo_real if ui_used and ui_used.valid_numeric else None
        feed_ts = ui_used.ts_feed_epoch if ui_used else None

        valid_ui = current_balance is not None
        if valid_ui:
            if self.last_saved_balance is None or abs(current_balance - self.last_saved_balance) > 1e-12:
                self.last_feed_change_epoch = now

        metrics = self._calculate_metrics_for_value(current_balance, now)
        should_save = self._should_save(valid_ui, current_balance, now)

        fuente_ui = self._format_source(ui_used)
        fuente_plot = self._format_source(plot_sample)
        lat = (now - feed_ts) if feed_ts else None

        sample = MonitorSample(
            timestamp_iso=datetime.now(timezone.utc).isoformat(),
            timestamp_epoch=now,
            saldo_real=current_balance,
            delta_abs=metrics["delta_abs"],
            delta_pct=metrics["delta_pct"],
            fuente=fuente_ui,
            fuente_grafica=fuente_plot,
            estado_feed=ui_status,
            latencia_seg=lat,
            muestra_valida=1 if valid_ui else 0,
            sesion_id=self.session_id,
            media_1m=metrics["media_1m"],
            media_5m=metrics["media_5m"],
            media_15m=metrics["media_15m"],
            min_1m=metrics["min_1m"],
            max_1m=metrics["max_1m"],
            pendiente_corta=metrics["pendiente_corta"],
            pendiente_media=metrics["pendiente_media"],
        )

        if should_save:
            ok = self.csv_writer.append_row(sample.__dict__)
            if ok:
                self.samples.append(sample)
                self.ui_series.append(sample)
                self.last_saved_epoch = now
                if valid_ui:
                    self.last_saved_balance = current_balance
            else:
                self._log_throttled("csv_write", "No se pudo escribir muestra (lock ocupado)", logging.WARNING)

        self._refresh_panel(sample, ui_used, plot_sample, now)
        self._refresh_plots()

    def _append_plot_point(self, now: float, feed_sample: FeedSample) -> None:
        ms = MonitorSample(
            timestamp_iso=datetime.now(timezone.utc).isoformat(),
            timestamp_epoch=now,
            saldo_real=feed_sample.saldo_real,
            delta_abs=None,
            delta_pct=None,
            fuente="",
            fuente_grafica=self._format_source(feed_sample),
            estado_feed="PLOT",
            latencia_seg=None,
            muestra_valida=1 if feed_sample.saldo_real is not None else 0,
            sesion_id=self.session_id,
            media_1m=None,
            media_5m=None,
            media_15m=None,
            min_1m=None,
            max_1m=None,
            pendiente_corta=None,
            pendiente_media=None,
        )
        if not self.plot_series:
            self.plot_series.append(ms)
            return
        last = self.plot_series[-1]
        if (
            last.saldo_real is not None
            and ms.saldo_real is not None
            and abs(last.saldo_real - ms.saldo_real) <= 1e-12
            and (now - last.timestamp_epoch) < 1.0
        ):
            return
        self.plot_series.append(ms)

    @staticmethod
    def _format_source(sample: Optional[FeedSample]) -> str:
        if not sample:
            return "SIN_FUENTE"
        src = SOURCE_LABELS.get(sample.source_kind, sample.source_kind.upper())
        if sample.source_path:
            return f"{src}:{sample.source_path.name}"
        return src

    def _log_source_health(self, result: DiscoverResult) -> None:
        if result.live_sample.valid_numeric and result.live_sample.fresh_for_ui:
            self._log_throttled("live_ok", "LIVE OK", logging.INFO)
        elif result.live_sample.valid_numeric:
            self._log_throttled("live_stale", "LIVE STALE", logging.WARNING)

        if result.history_sample.valid_numeric and result.history_sample.fresh_for_ui:
            self._log_throttled("hist_ok", "HISTORY OK", logging.INFO)
        elif result.history_sample.valid_numeric:
            self._log_throttled("hist_stale", "HISTORY STALE", logging.WARNING)

        if result.series_sample.valid_numeric:
            self._log_throttled("series_plot", "SERIES SOLO GRAFICA", logging.INFO)

    def _should_save(self, valid: bool, value: Optional[float], now: float) -> bool:
        if self.last_saved_epoch is None:
            return True

        elapsed = now - self.last_saved_epoch
        changed = False
        if valid and (self.last_saved_balance is None or value is None):
            changed = True
        elif valid and value is not None and self.last_saved_balance is not None:
            changed = abs(value - self.last_saved_balance) > 1e-12

        if changed:
            return True
        if elapsed >= SAVE_MIN_INTERVAL_S:
            return True
        return False

    def _calculate_metrics_for_value(self, current_balance: Optional[float], now_epoch: float) -> dict[str, Optional[float]]:
        valid_samples = [s for s in self.ui_series if s.muestra_valida == 1 and s.saldo_real is not None]
        prev = valid_samples[-1].saldo_real if valid_samples else None

        delta_abs = None
        delta_pct = None
        if current_balance is not None and prev is not None:
            delta_abs = current_balance - prev
            if abs(prev) > 1e-12:
                delta_pct = (delta_abs / prev) * 100.0

        def window_vals(seconds: int) -> list[float]:
            low = now_epoch - seconds
            return [float(s.saldo_real) for s in valid_samples if s.timestamp_epoch >= low and s.saldo_real is not None]

        vals_1m = window_vals(60)
        vals_5m = window_vals(300)
        vals_15m = window_vals(900)

        media_1m = (sum(vals_1m) / len(vals_1m)) if vals_1m else None
        media_5m = (sum(vals_5m) / len(vals_5m)) if vals_5m else None
        media_15m = (sum(vals_15m) / len(vals_15m)) if vals_15m else None
        min_1m = min(vals_1m) if vals_1m else None
        max_1m = max(vals_1m) if vals_1m else None

        pendiente_corta = self._calc_slope(valid_samples, seconds=120)
        pendiente_media = self._calc_slope(valid_samples, seconds=600)

        return {
            "delta_abs": delta_abs,
            "delta_pct": delta_pct,
            "media_1m": media_1m,
            "media_5m": media_5m,
            "media_15m": media_15m,
            "min_1m": min_1m,
            "max_1m": max_1m,
            "pendiente_corta": pendiente_corta,
            "pendiente_media": pendiente_media,
        }

    @staticmethod
    def _calc_slope(samples: list[MonitorSample], seconds: int) -> Optional[float]:
        if not samples:
            return None
        now = samples[-1].timestamp_epoch
        window = [s for s in samples if s.timestamp_epoch >= now - seconds and s.saldo_real is not None]
        if len(window) < 2:
            return None

        x0 = window[0].timestamp_epoch
        xs = [s.timestamp_epoch - x0 for s in window]
        ys = [float(s.saldo_real) for s in window]
        n = len(xs)
        sx, sy = sum(xs), sum(ys)
        sxx = sum(x * x for x in xs)
        sxy = sum(x * y for x, y in zip(xs, ys))
        denom = n * sxx - sx * sx
        if abs(denom) < 1e-12:
            return None
        return (n * sxy - sx * sy) / denom

    def _detect_feed_state(self, now: float, sample: MonitorSample) -> str:
        if sample.estado_feed in ("SIN LIVE", "STALE"):
            return sample.estado_feed
        if sample.muestra_valida == 0:
            return "SIN LIVE"
        if self.last_feed_change_epoch is None:
            return "ACTIVO"
        if now - self.last_feed_change_epoch > FREEZE_THRESHOLD_S:
            return "CONGELADO"
        if sample.fuente.startswith("JSONL_HISTORY"):
            return "FALLBACK"
        return "ACTIVO"

    def _refresh_panel(self, sample: MonitorSample, ui_feed: Optional[FeedSample], plot_feed: Optional[FeedSample], now: float) -> None:
        estado = self._detect_feed_state(now, sample)
        saldo_txt = "--" if sample.saldo_real is None else f"{sample.saldo_real:,.2f}"
        self.lbl_saldo.setText(saldo_txt)

        color = "#0B7D3E"
        if estado in ("FALLBACK", "STALE TTL"):
            color = "#B8860B"
        elif estado in ("SIN LIVE", "STALE", "CONGELADO"):
            color = "#C0392B"

        self.lbl_estado.setText(f"Estado feed: {estado}")
        self.lbl_estado.setStyleSheet(f"font-size: 14px; font-weight: 700; color: {color};")

        self.lbl_src_ui.setText(f"Fuente saldo actual: {sample.fuente}")
        self.lbl_src_plot.setText(f"Fuente gráficas: {sample.fuente_grafica}")
        self.lbl_hora.setText(f"Hora local: {datetime.now().astimezone().strftime('%Y-%m-%d %H:%M:%S')}")
        self.lbl_muestras.setText(f"Muestras guardadas: {len(self.samples)}")
        self.lbl_ultima.setText(f"Última actualización feed: {self._fmt_ts(ui_feed.ts_feed_epoch if ui_feed else None)}")

        d_abs = "--" if sample.delta_abs is None else f"{sample.delta_abs:+.2f}"
        d_pct = "--" if sample.delta_pct is None else f"{sample.delta_pct:+.4f}%"
        self.lbl_delta.setText(f"Δ abs: {d_abs} | Δ %: {d_pct} | Latencia: {self._fmt_float(sample.latencia_seg, 2)} s")

        sec_no_change = "--"
        if self.last_feed_change_epoch is not None:
            sec_no_change = f"{max(0, int(now - self.last_feed_change_epoch))}"
        self.lbl_stale.setText(f"Segundos sin cambio real: {sec_no_change}")

        rango = None
        if sample.min_1m is not None and sample.max_1m is not None:
            rango = sample.max_1m - sample.min_1m

        self.lbl_ind.setText(
            "Indicadores: "
            f"MA1m={self._fmt_float(sample.media_1m, 2)} | "
            f"MA5m={self._fmt_float(sample.media_5m, 2)} | "
            f"Min1m={self._fmt_float(sample.min_1m, 2)} | "
            f"Max1m={self._fmt_float(sample.max_1m, 2)} | "
            f"Rango1m={self._fmt_float(rango, 2)} | "
            f"PendC={self._fmt_float(sample.pendiente_corta, 4)}"
        )

        if estado == "CONGELADO":
            self._log_throttled("freeze", "Feed congelado (>20s sin cambios). Continúa en modo vigilancia.", logging.WARNING)

    def _refresh_plots(self) -> None:
        valid = [s for s in self.plot_series if s.muestra_valida == 1 and s.saldo_real is not None]
        if not valid:
            self.canvas.draw_idle()
            return

        t = [datetime.fromtimestamp(s.timestamp_epoch, tz=timezone.utc) for s in valid]
        y = [float(s.saldo_real) for s in valid]

        now = valid[-1].timestamp_epoch
        t_min, y_min = self._select_window(valid, now - 900)
        t_hour, y_hour = self._select_window(valid, now - 24 * 3600)

        for ax in (self.ax_minute, self.ax_hour, self.ax_full):
            ax.clear()
            ax.grid(True, alpha=0.25)
            ax.xaxis.set_major_formatter(mdates.DateFormatter("%H:%M:%S"))

        self.ax_minute.plot(t_min, y_min, color="#1f77b4", linewidth=1.8, label="Saldo")
        self._plot_moving_average(self.ax_minute, t_min, y_min, 12, "MA corta")
        if t_min:
            self.ax_minute.scatter([t_min[-1]], [y_min[-1]], color="#d62728", s=25, zorder=3, label="Último")
        self.ax_minute.set_title("Gráfica minuto a minuto (últimos 15 min)")
        self.ax_minute.legend(loc="upper left")

        self.ax_hour.plot(t_hour, y_hour, color="#2ca02c", linewidth=1.8, label="Saldo")
        self._plot_moving_average(self.ax_hour, t_hour, y_hour, 30, "MA media")
        if t_hour:
            self.ax_hour.scatter([t_hour[-1]], [y_hour[-1]], color="#d62728", s=25, zorder=3)
        self.ax_hour.set_title("Gráfica hora a hora (últimas 24 h)")
        self.ax_hour.legend(loc="upper left")

        self.ax_full.plot(t, y, color="#9467bd", linewidth=1.8, label="Saldo sesión")
        if t:
            self.ax_full.scatter([t[-1]], [y[-1]], color="#d62728", s=25, zorder=3)
        self.ax_full.set_title("Gráfica general de toda la sesión")
        self.ax_full.set_xlabel("Tiempo")
        self.ax_full.legend(loc="upper left")

        self.canvas.draw_idle()

    @staticmethod
    def _select_window(samples: list[MonitorSample], low_epoch: float) -> tuple[list[datetime], list[float]]:
        win = [s for s in samples if s.timestamp_epoch >= low_epoch and s.saldo_real is not None]
        return (
            [datetime.fromtimestamp(s.timestamp_epoch, tz=timezone.utc) for s in win],
            [float(s.saldo_real) for s in win],
        )

    @staticmethod
    def _plot_moving_average(ax, tvals: list[datetime], yvals: list[float], window: int, label: str) -> None:
        if len(yvals) < 2:
            return
        ma = []
        for i in range(len(yvals)):
            lo = max(0, i - window + 1)
            chunk = yvals[lo : i + 1]
            ma.append(sum(chunk) / len(chunk))
        ax.plot(tvals, ma, linestyle="--", linewidth=1.2, alpha=0.85, label=label)

    def _log_throttled(self, key: str, msg: str, level: int = logging.INFO) -> None:
        now = time.monotonic()
        prev = self.last_log.get(key)
        if prev is not None and (now - prev) < LOG_THROTTLE_S:
            return
        self.last_log[key] = now
        logging.log(level, msg)

    @staticmethod
    def _fmt_ts(ts: Optional[float]) -> str:
        if ts is None:
            return "--"
        try:
            return datetime.fromtimestamp(ts).astimezone().strftime("%Y-%m-%d %H:%M:%S")
        except Exception:
            return "--"

    @staticmethod
    def _fmt_float(v: Optional[float], d: int) -> str:
        if v is None:
            return "--"
        return f"{v:.{d}f}"


def configure_logging() -> None:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s | %(levelname)s | %(message)s",
        datefmt="%H:%M:%S",
    )


def main() -> int:
    configure_logging()
    base_dir = Path(__file__).resolve().parent
    app = QtWidgets.QApplication(sys.argv)
    app.setStyle("Fusion")
    win = MonitorSaldoWindow(base_dir)
    win.show()
    return app.exec_()


if __name__ == "__main__":
    sys.exit(main())
