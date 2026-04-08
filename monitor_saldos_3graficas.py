#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import csv
import os
import shutil
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import numpy as np
import pandas as pd

from PyQt5 import QtCore, QtGui, QtWidgets
import pyqtgraph as pg


# =========================
# Configuración
# =========================
CSV_FILENAME = "saldo_real_series.csv"
SAMPLE_INTERVAL_SECONDS = float(os.getenv("SALDOS_SAMPLE_INTERVAL_SECONDS", "10"))
UI_REFRESH_MS = int(os.getenv("SALDOS_UI_REFRESH_MS", "1200"))
CSV_READ_MAX_ROWS = int(os.getenv("SALDOS_CSV_READ_MAX_ROWS", "300000"))
WRITE_LOCK_RETRIES = int(os.getenv("SALDOS_WRITE_LOCK_RETRIES", "4"))
WRITE_LOCK_SLEEP = float(os.getenv("SALDOS_WRITE_LOCK_SLEEP", "0.05"))
SOURCE_STALE_SECONDS = float(os.getenv("SALDOS_SOURCE_STALE_SECONDS", "90"))

HEADER = [
    "ts_epoch",
    "ts_iso",
    "fecha",
    "hora",
    "minuto_bucket",
    "hora_bucket",
    "saldo_real",
    "saldo_demo",
    "saldo_total",
    "fuente_saldo",
    "delta_real",
    "delta_demo",
    "delta_total",
]


@dataclass
class SaldoSnapshot:
    ts_epoch: float
    ts_iso: str
    saldo_real: Optional[float]
    saldo_demo: Optional[float]
    saldo_total: Optional[float]
    fuente_saldo: str
    estado_fuente: str


# =========================
# Utilidades de tiempo / formato
# =========================
def _now_epoch() -> float:
    return float(time.time())


def _iso_utc(epoch: float) -> str:
    return datetime.fromtimestamp(epoch, tz=timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def _to_bucket_minute(epoch: float) -> str:
    return datetime.fromtimestamp(epoch, tz=timezone.utc).strftime("%Y-%m-%d %H:%M")


def _to_bucket_hour(epoch: float) -> str:
    return datetime.fromtimestamp(epoch, tz=timezone.utc).strftime("%Y-%m-%d %H:00")


def _safe_float(v) -> Optional[float]:
    try:
        out = float(v)
        if not np.isfinite(out):
            return None
        return out
    except Exception:
        return None


def _money(v: Optional[float]) -> str:
    if v is None:
        return "--"
    return f"{float(v):,.2f}"


# =========================
# Rutas / bootstrap
# =========================
def fijar_directorio_script() -> Path:
    script_dir = Path(__file__).resolve().parent
    os.chdir(script_dir)
    return script_dir


def _feed_candidates(script_dir: Path) -> Dict[str, List[Path]]:
    home = Path.home()
    return {
        "real_live": [
            script_dir / "saldo_real_live.json",
            home / "saldo_real_live.json",
        ],
        "real_history": [
            script_dir / "saldo_real_live_history.jsonl",
            home / "saldo_real_live_history.jsonl",
        ],
        "demo_live": [
            script_dir / "saldo_demo_live.json",
            home / "saldo_demo_live.json",
        ],
    }


def asegurar_csv_saldos(csv_path: Path) -> Tuple[bool, str]:
    try:
        csv_path.parent.mkdir(parents=True, exist_ok=True)
        if not csv_path.exists() or csv_path.stat().st_size == 0:
            with csv_path.open("w", encoding="utf-8", newline="") as fh:
                writer = csv.writer(fh)
                writer.writerow(HEADER)
                fh.flush()
                os.fsync(fh.fileno())
            return True, f"CSV creado: {csv_path.name}"

        with csv_path.open("r", encoding="utf-8", errors="ignore", newline="") as fh:
            first = fh.readline().strip()
        if first.lower() != ",".join(HEADER).lower():
            backup = csv_path.with_suffix(".csv.bak_header")
            shutil.copy2(csv_path, backup)
            repaired_rows: List[List[str]] = []
            with csv_path.open("r", encoding="utf-8", errors="ignore", newline="") as fh:
                reader = csv.reader(fh)
                for row in reader:
                    if not row:
                        continue
                    if row[0].strip().lower() in ("ts_epoch", "timestamp"):
                        continue
                    repaired_rows.append(row)
            with csv_path.open("w", encoding="utf-8", newline="") as fh:
                writer = csv.writer(fh)
                writer.writerow(HEADER)
                for row in repaired_rows:
                    writer.writerow(row)
                fh.flush()
                os.fsync(fh.fileno())
            return True, f"CSV reparado (header) con backup: {backup.name}"
        return True, "CSV OK"
    except Exception as e:
        return False, f"Error asegurando CSV: {e}"


# =========================
# Lectura de fuentes de saldo
# =========================
def normalizar_saldo(value) -> Optional[float]:
    return _safe_float(value)


def _read_json(path: Path) -> Optional[dict]:
    if not path.exists():
        return None
    try:
        return pd.read_json(path, typ="series").to_dict()
    except Exception:
        try:
            import json
            return json.loads(path.read_text(encoding="utf-8", errors="ignore"))
        except Exception:
            return None


def _best_live(paths: List[Path]) -> Tuple[Optional[float], Optional[float], Optional[Path]]:
    best: Optional[Tuple[float, float, int, Path]] = None
    for p in paths:
        obj = _read_json(p)
        if not obj:
            continue
        real = normalizar_saldo(obj.get("saldo_real", obj.get("equity", obj.get("balance"))))
        if real is None:
            continue
        ts = pd.to_datetime(obj.get("timestamp"), errors="coerce", utc=True)
        if pd.isna(ts):
            ts = pd.to_datetime(pd.to_numeric(obj.get("ts"), errors="coerce"), unit="s", errors="coerce", utc=True)
        if pd.isna(ts):
            try:
                ts = pd.to_datetime(p.stat().st_mtime, unit="s", utc=True)
            except Exception:
                continue
        epoch = float(ts.timestamp())
        try:
            mtime_ns = int(p.stat().st_mtime_ns)
        except Exception:
            mtime_ns = 0
        cand = (epoch, float(real), mtime_ns, p)
        if best is None or (cand[0], cand[2], str(cand[3])) > (best[0], best[2], str(best[3])):
            best = cand
    if best is None:
        return None, None, None
    return best[1], best[0], best[3]


def _best_history_last(paths: List[Path]) -> Tuple[Optional[float], Optional[float], Optional[Path]]:
    best: Optional[Tuple[float, float, int, Path]] = None
    for p in paths:
        if not p.exists():
            continue
        try:
            import json
            rows = []
            with p.open("r", encoding="utf-8", errors="ignore") as fh:
                for line in fh:
                    line = line.strip()
                    if not line:
                        continue
                    obj = json.loads(line)
                    val = normalizar_saldo(obj.get("saldo_real", obj.get("equity", obj.get("balance"))))
                    if val is None:
                        continue
                    ts = pd.to_datetime(obj.get("timestamp"), errors="coerce", utc=True)
                    if pd.isna(ts):
                        ts = pd.to_datetime(pd.to_numeric(obj.get("ts"), errors="coerce"), unit="s", errors="coerce", utc=True)
                    if pd.isna(ts):
                        continue
                    rows.append((float(ts.timestamp()), float(val)))
            if not rows:
                continue
            rows.sort(key=lambda x: x[0])
            last_epoch, last_val = rows[-1]
            try:
                mtime_ns = int(p.stat().st_mtime_ns)
            except Exception:
                mtime_ns = 0
            cand = (last_epoch, last_val, mtime_ns, p)
            if best is None or (cand[0], cand[2], str(cand[3])) > (best[0], best[2], str(best[3])):
                best = cand
        except Exception:
            continue
    if best is None:
        return None, None, None
    return best[1], best[0], best[3]


def leer_fuente_saldos(script_dir: Path, last_real: Optional[float], last_demo: Optional[float]) -> SaldoSnapshot:
    cands = _feed_candidates(script_dir)

    real_live, real_live_ts, p_live = _best_live(cands["real_live"])
    real_hist, real_hist_ts, p_hist = _best_history_last(cands["real_history"])

    now_epoch = _now_epoch()
    fuente = "SIN_DATOS_REALES"
    estado = "NO DATA"
    saldo_real = None

    if real_live is not None and real_live_ts is not None:
        age = max(0.0, now_epoch - real_live_ts)
        if age <= SOURCE_STALE_SECONDS:
            saldo_real = real_live
            fuente = "MAESTRO_LIVE"
            estado = "OK"
        else:
            # live stale, degradar por frescura real
            if real_hist is not None and real_hist_ts is not None and real_hist_ts >= real_live_ts:
                saldo_real = real_hist
                fuente = "MAESTRO_HISTORY_DEGRADED"
                estado = "DEGRADED"
            else:
                saldo_real = real_live
                fuente = "MAESTRO_HISTORY_DEGRADED"
                estado = "DEGRADED"
    elif real_hist is not None:
        saldo_real = real_hist
        fuente = "MAESTRO_HISTORY_DEGRADED"
        estado = "DEGRADED"

    # saldo demo (si existe archivo demo_live, úsalo; si no, conserva último válido)
    demo_val: Optional[float] = None
    demo_ts: Optional[float] = None
    p_demo: Optional[Path] = None
    demo_val, demo_ts, p_demo = _best_live(cands["demo_live"])
    saldo_demo = demo_val if demo_val is not None else last_demo

    if saldo_real is None:
        saldo_real = last_real
        if saldo_real is None:
            fuente = "SIN_DATOS_REALES"
            estado = "NO DATA"
        else:
            fuente = "SIN_DATOS_REALES"
            estado = "STALE"

    saldo_total = None
    if saldo_real is not None or saldo_demo is not None:
        saldo_total = float((saldo_real or 0.0) + (saldo_demo or 0.0))

    ts_epoch = now_epoch
    return SaldoSnapshot(
        ts_epoch=ts_epoch,
        ts_iso=_iso_utc(ts_epoch),
        saldo_real=saldo_real,
        saldo_demo=saldo_demo,
        saldo_total=saldo_total,
        fuente_saldo=fuente,
        estado_fuente=estado,
    )


# =========================
# Escritura CSV robusta
# =========================
def _read_last_row(csv_path: Path) -> Optional[dict]:
    if not csv_path.exists() or csv_path.stat().st_size <= 0:
        return None
    try:
        with csv_path.open("rb") as fh:
            fh.seek(0, os.SEEK_END)
            size = fh.tell()
            fh.seek(max(0, size - 65536), os.SEEK_SET)
            data = fh.read().decode("utf-8", errors="ignore").splitlines()
        for line in reversed(data):
            if not line.strip() or line.lower().startswith("ts_epoch"):
                continue
            parts = [p.strip() for p in line.split(",")]
            if len(parts) < len(HEADER):
                continue
            return dict(zip(HEADER, parts[: len(HEADER)]))
    except Exception:
        return None
    return None


def append_saldo_csv(csv_path: Path, snap: SaldoSnapshot, force_sample: bool = False) -> Tuple[bool, str]:
    ok, msg = asegurar_csv_saldos(csv_path)
    if not ok:
        return False, msg

    last = _read_last_row(csv_path)
    last_real = normalizar_saldo(last.get("saldo_real")) if last else None
    last_demo = normalizar_saldo(last.get("saldo_demo")) if last else None
    last_total = normalizar_saldo(last.get("saldo_total")) if last else None

    changed = False
    if last is None:
        changed = True
    else:
        if snap.saldo_real is not None and (last_real is None or abs(snap.saldo_real - last_real) > 1e-9):
            changed = True
        if snap.saldo_demo is not None and (last_demo is None or abs(snap.saldo_demo - last_demo) > 1e-9):
            changed = True
        if snap.saldo_total is not None and (last_total is None or abs(snap.saldo_total - last_total) > 1e-9):
            changed = True

    if not changed and not force_sample:
        return True, "Sin cambios, no se anexa fila"

    d_real = None if snap.saldo_real is None or last_real is None else (snap.saldo_real - last_real)
    d_demo = None if snap.saldo_demo is None or last_demo is None else (snap.saldo_demo - last_demo)
    d_total = None if snap.saldo_total is None or last_total is None else (snap.saldo_total - last_total)

    dt = datetime.fromtimestamp(snap.ts_epoch, tz=timezone.utc)
    row = [
        f"{snap.ts_epoch:.6f}",
        snap.ts_iso,
        dt.strftime("%Y-%m-%d"),
        dt.strftime("%H:%M:%S"),
        _to_bucket_minute(snap.ts_epoch),
        _to_bucket_hour(snap.ts_epoch),
        "" if snap.saldo_real is None else f"{snap.saldo_real:.8f}",
        "" if snap.saldo_demo is None else f"{snap.saldo_demo:.8f}",
        "" if snap.saldo_total is None else f"{snap.saldo_total:.8f}",
        snap.fuente_saldo,
        "" if d_real is None else f"{d_real:.8f}",
        "" if d_demo is None else f"{d_demo:.8f}",
        "" if d_total is None else f"{d_total:.8f}",
    ]

    lock_path = csv_path.with_suffix(".csv.lock")
    for _ in range(WRITE_LOCK_RETRIES):
        fd = None
        try:
            fd = os.open(str(lock_path), os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o644)
            with os.fdopen(fd, "w", encoding="utf-8") as lfh:
                lfh.write(str(os.getpid()))
            fd = None

            with csv_path.open("a", encoding="utf-8", newline="") as fh:
                writer = csv.writer(fh)
                writer.writerow(row)
                fh.flush()
                os.fsync(fh.fileno())
            return True, "Fila anexada"
        except FileExistsError:
            time.sleep(WRITE_LOCK_SLEEP)
        except Exception as e:
            return False, f"Error append CSV: {e}"
        finally:
            if fd is not None:
                try:
                    os.close(fd)
                except Exception:
                    pass
            try:
                if lock_path.exists():
                    lock_path.unlink()
            except Exception:
                pass
    return False, "CSV ocupado temporalmente"


# =========================
# Carga CSV y agregación
# =========================
def cargar_csv_saldos(csv_path: Path, max_rows: int = CSV_READ_MAX_ROWS) -> pd.DataFrame:
    if not csv_path.exists() or csv_path.stat().st_size <= 0:
        return pd.DataFrame(columns=HEADER)

    try:
        df = pd.read_csv(csv_path, encoding="utf-8", low_memory=False)
    except Exception:
        try:
            df = pd.read_csv(csv_path, encoding="latin-1", low_memory=False)
        except Exception:
            # fallback conservador
            rows = []
            with csv_path.open("r", encoding="utf-8", errors="ignore", newline="") as fh:
                reader = csv.reader(fh)
                for i, row in enumerate(reader):
                    if i == 0:
                        continue
                    if not row:
                        continue
                    if len(row) < len(HEADER):
                        row = row + [""] * (len(HEADER) - len(row))
                    rows.append(row[: len(HEADER)])
            df = pd.DataFrame(rows, columns=HEADER)

    for col in HEADER:
        if col not in df.columns:
            df[col] = ""

    df = df[HEADER].copy()
    df["ts_epoch"] = pd.to_numeric(df["ts_epoch"], errors="coerce")
    for col in ("saldo_real", "saldo_demo", "saldo_total", "delta_real", "delta_demo", "delta_total"):
        df[col] = pd.to_numeric(df[col], errors="coerce")

    df = df.replace([np.inf, -np.inf], np.nan)
    df = df.dropna(subset=["ts_epoch"])
    df = df.sort_values("ts_epoch")
    df = df.drop_duplicates(subset=["ts_epoch", "saldo_real", "saldo_demo", "saldo_total"], keep="last")

    if len(df) > max_rows:
        df = df.tail(max_rows).copy()

    df.reset_index(drop=True, inplace=True)
    return df


def agrupar_por_minuto(df: pd.DataFrame) -> pd.DataFrame:
    if df.empty:
        return pd.DataFrame(columns=["ts_epoch", "saldo_total", "saldo_real", "saldo_demo"])
    d = df.copy()
    d["bucket"] = d["minuto_bucket"].astype(str)
    g = d.groupby("bucket", dropna=False).agg(
        ts_epoch=("ts_epoch", "max"),
        saldo_total=("saldo_total", "last"),
        saldo_real=("saldo_real", "last"),
        saldo_demo=("saldo_demo", "last"),
    )
    g = g.sort_values("ts_epoch").reset_index(drop=True)
    return g


def agrupar_por_hora(df: pd.DataFrame) -> pd.DataFrame:
    if df.empty:
        return pd.DataFrame(columns=["ts_epoch", "saldo_total", "saldo_real", "saldo_demo"])
    d = df.copy()
    d["bucket"] = d["hora_bucket"].astype(str)
    g = d.groupby("bucket", dropna=False).agg(
        ts_epoch=("ts_epoch", "max"),
        saldo_total=("saldo_total", "last"),
        saldo_real=("saldo_real", "last"),
        saldo_demo=("saldo_demo", "last"),
    )
    g = g.sort_values("ts_epoch").reset_index(drop=True)
    return g


# =========================
# UI / gráficas
# =========================
class TimeAxis(pg.AxisItem):
    def tickStrings(self, values, scale, spacing):
        if not values:
            return []
        out = []
        span = (max(values) - min(values)) if len(values) > 1 else 0
        for v in values:
            try:
                dt = datetime.fromtimestamp(float(v), tz=timezone.utc)
                if span <= 2 * 3600:
                    out.append(dt.strftime("%H:%M:%S"))
                elif span <= 3 * 86400:
                    out.append(dt.strftime("%d-%m %H:%M"))
                else:
                    out.append(dt.strftime("%Y-%m-%d"))
            except Exception:
                out.append("")
        return out


class MonitorSaldosWindow(QtWidgets.QMainWindow):
    def __init__(self, script_dir: Path):
        super().__init__()
        self.script_dir = script_dir
        self.csv_path = script_dir / CSV_FILENAME

        self._last_csv_sig: Optional[Tuple[int, int]] = None
        self._df_cache = pd.DataFrame(columns=HEADER)
        self._last_write_epoch = 0.0
        self._last_real: Optional[float] = None
        self._last_demo: Optional[float] = None

        self.setWindowTitle("Monitor Saldos · 3 Gráficas")
        self.resize(1680, 960)
        self._build_ui()
        self._apply_style()

        ok, msg = asegurar_csv_saldos(self.csv_path)
        self.lbl_csv_status.setText(f"CSV: {'OK' if ok else 'ERROR'} · {msg}")

        self.timer = QtCore.QTimer(self)
        self.timer.timeout.connect(self.timer_refresh)
        self.timer.start(UI_REFRESH_MS)

        self.timer_refresh(force_reload=True)

    def _build_ui(self):
        cw = QtWidgets.QWidget()
        self.setCentralWidget(cw)
        root = QtWidgets.QVBoxLayout(cw)
        root.setContentsMargins(8, 8, 8, 8)
        root.setSpacing(6)

        top = QtWidgets.QFrame()
        top_l = QtWidgets.QGridLayout(top)
        top_l.setContentsMargins(8, 6, 8, 6)
        top_l.setHorizontalSpacing(12)
        top_l.setVerticalSpacing(4)

        self.lbl_real = QtWidgets.QLabel("REAL: --")
        self.lbl_demo = QtWidgets.QLabel("DEMO: --")
        self.lbl_total = QtWidgets.QLabel("TOTAL: --")
        self.lbl_update = QtWidgets.QLabel("Última actualización: --")
        self.lbl_source = QtWidgets.QLabel("Fuente: --")
        self.lbl_rows = QtWidgets.QLabel("Filas CSV: 0")
        self.lbl_csv_status = QtWidgets.QLabel("CSV: --")
        self.lbl_write = QtWidgets.QLabel("Escritura: --")

        labels = [self.lbl_real, self.lbl_demo, self.lbl_total, self.lbl_update, self.lbl_source, self.lbl_rows, self.lbl_csv_status, self.lbl_write]
        for lb in labels:
            lb.setObjectName("Info")
            lb.setTextInteractionFlags(QtCore.Qt.TextSelectableByMouse)

        top_l.addWidget(self.lbl_real, 0, 0)
        top_l.addWidget(self.lbl_demo, 0, 1)
        top_l.addWidget(self.lbl_total, 0, 2)
        top_l.addWidget(self.lbl_update, 1, 0)
        top_l.addWidget(self.lbl_source, 1, 1)
        top_l.addWidget(self.lbl_rows, 1, 2)
        top_l.addWidget(self.lbl_csv_status, 2, 0, 1, 2)
        top_l.addWidget(self.lbl_write, 2, 2)

        controls = QtWidgets.QHBoxLayout()
        self.btn_reload = QtWidgets.QPushButton("Recargar CSV")
        self.btn_clear_view = QtWidgets.QPushButton("Limpiar vista")
        self.btn_export = QtWidgets.QPushButton("Exportar copia CSV")
        self.cb_range = QtWidgets.QComboBox()
        self.cb_range.addItems(["1H", "6H", "24H", "7D", "TODO"])
        self.cb_range.setCurrentText("24H")
        self.chk_autoscale = QtWidgets.QCheckBox("Autoescala")
        self.chk_autoscale.setChecked(True)

        self.btn_reload.clicked.connect(lambda: self.timer_refresh(force_reload=True))
        self.btn_clear_view.clicked.connect(self._clear_view_only)
        self.btn_export.clicked.connect(self._export_copy_csv)
        self.cb_range.currentTextChanged.connect(lambda _v: self.actualizar_panel_y_graficas(force_plot=True))
        self.chk_autoscale.stateChanged.connect(lambda _v: self.actualizar_panel_y_graficas(force_plot=True))

        controls.addWidget(self.btn_reload)
        controls.addWidget(self.btn_clear_view)
        controls.addWidget(self.btn_export)
        controls.addSpacing(12)
        controls.addWidget(QtWidgets.QLabel("Rango:"))
        controls.addWidget(self.cb_range)
        controls.addSpacing(8)
        controls.addWidget(self.chk_autoscale)
        controls.addStretch(1)

        self.plot_min = pg.PlotWidget(axisItems={"bottom": TimeAxis(orientation="bottom")})
        self.plot_hour = pg.PlotWidget(axisItems={"bottom": TimeAxis(orientation="bottom")})
        self.plot_all = pg.PlotWidget(axisItems={"bottom": TimeAxis(orientation="bottom")})

        self.plot_min.setTitle("Dinero por minuto")
        self.plot_hour.setTitle("Dinero por hora")
        self.plot_all.setTitle("Dinero vs tiempo general")

        for p in (self.plot_min, self.plot_hour, self.plot_all):
            p.showGrid(x=True, y=True, alpha=0.18)
            p.addLegend()
            p.setLabel("left", "Dinero")
            p.setLabel("bottom", "Tiempo")

        self.curve_min_total = self.plot_min.plot(name="TOTAL", pen=pg.mkPen("#7ef6b2", width=2.8))
        self.curve_min_real = self.plot_min.plot(name="REAL", pen=pg.mkPen("#58b6ff", width=2.2))
        self.curve_min_demo = self.plot_min.plot(name="DEMO", pen=pg.mkPen("#ffc46b", width=2.2))

        self.curve_hour_total = self.plot_hour.plot(name="TOTAL", pen=pg.mkPen("#7ef6b2", width=2.8))
        self.curve_hour_real = self.plot_hour.plot(name="REAL", pen=pg.mkPen("#58b6ff", width=2.2))
        self.curve_hour_demo = self.plot_hour.plot(name="DEMO", pen=pg.mkPen("#ffc46b", width=2.2))

        self.curve_all_total = self.plot_all.plot(name="TOTAL", pen=pg.mkPen("#7ef6b2", width=3.0))
        self.curve_all_real = self.plot_all.plot(name="REAL", pen=pg.mkPen("#58b6ff", width=2.3))
        self.curve_all_demo = self.plot_all.plot(name="DEMO", pen=pg.mkPen("#ffc46b", width=2.3))

        splitter = QtWidgets.QSplitter(QtCore.Qt.Vertical)
        top_panel = QtWidgets.QWidget()
        top_layout = QtWidgets.QVBoxLayout(top_panel)
        top_layout.setContentsMargins(0, 0, 0, 0)
        top_layout.addWidget(self.plot_min)

        mid_panel = QtWidgets.QWidget()
        mid_layout = QtWidgets.QVBoxLayout(mid_panel)
        mid_layout.setContentsMargins(0, 0, 0, 0)
        mid_layout.addWidget(self.plot_hour)

        bot_panel = QtWidgets.QWidget()
        bot_layout = QtWidgets.QVBoxLayout(bot_panel)
        bot_layout.setContentsMargins(0, 0, 0, 0)
        bot_layout.addWidget(self.plot_all)

        splitter.addWidget(top_panel)
        splitter.addWidget(mid_panel)
        splitter.addWidget(bot_panel)
        splitter.setSizes([300, 300, 360])

        root.addWidget(top)
        root.addLayout(controls)
        root.addWidget(splitter, 1)

    def _apply_style(self):
        self.setStyleSheet(
            """
            QMainWindow, QWidget { background: #0d1623; color: #dce8ff; }
            QFrame { border: 1px solid #2f4668; border-radius: 10px; background: #111f30; }
            QLabel#Info { font-size: 13px; font-weight: 600; }
            QPushButton { background: #1d3552; border: 1px solid #365b85; border-radius: 8px; padding: 6px 10px; }
            QPushButton:hover { background: #254369; }
            QComboBox { background: #1b3048; border: 1px solid #345574; border-radius: 8px; padding: 4px 8px; }
            QCheckBox { font-size: 13px; }
            """
        )
        pg.setConfigOptions(antialias=True, background="#0f1a2b", foreground="#dce8ff")

    def _clear_view_only(self):
        empty_x = np.array([], dtype=float)
        empty_y = np.array([], dtype=float)
        for curve in (
            self.curve_min_total,
            self.curve_min_real,
            self.curve_min_demo,
            self.curve_hour_total,
            self.curve_hour_real,
            self.curve_hour_demo,
            self.curve_all_total,
            self.curve_all_real,
            self.curve_all_demo,
        ):
            curve.setData(empty_x, empty_y)

    def _export_copy_csv(self):
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        out = self.script_dir / f"saldo_real_series_export_{ts}.csv"
        try:
            shutil.copy2(self.csv_path, out)
            self.lbl_csv_status.setText(f"CSV: exportado en {out.name}")
        except Exception as e:
            self.lbl_csv_status.setText(f"CSV export error: {e}")

    def _csv_changed(self) -> bool:
        try:
            st = self.csv_path.stat()
            sig = (int(st.st_mtime_ns), int(st.st_size))
        except Exception:
            sig = (-1, -1)
        if sig != self._last_csv_sig:
            self._last_csv_sig = sig
            return True
        return False

    def timer_refresh(self, force_reload: bool = False):
        snap = leer_fuente_saldos(self.script_dir, self._last_real, self._last_demo)
        self._last_real = snap.saldo_real
        self._last_demo = snap.saldo_demo

        now = _now_epoch()
        force_sample = (now - self._last_write_epoch) >= SAMPLE_INTERVAL_SECONDS
        wrote_ok, wrote_msg = append_saldo_csv(self.csv_path, snap, force_sample=force_sample)
        if wrote_ok and ("anexada" in wrote_msg.lower() or force_sample):
            self._last_write_epoch = now

        self.lbl_write.setText(f"Escritura: {'OK' if wrote_ok else 'WARN'} · {wrote_msg}")
        if wrote_ok:
            self.lbl_write.setStyleSheet("color:#7ef6b2;")
        else:
            self.lbl_write.setStyleSheet("color:#ffc46b;")

        self.actualizar_panel_y_graficas(force_reload=force_reload)

        self.lbl_real.setText(f"REAL: {_money(snap.saldo_real)}")
        self.lbl_demo.setText(f"DEMO: {_money(snap.saldo_demo)}")
        self.lbl_total.setText(f"TOTAL: {_money(snap.saldo_total)}")
        self.lbl_update.setText(f"Última actualización: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        self.lbl_source.setText(f"Fuente: {snap.fuente_saldo} · Estado: {snap.estado_fuente}")

    def _apply_range(self, df: pd.DataFrame) -> pd.DataFrame:
        if df.empty:
            return df
        mode = self.cb_range.currentText().strip().upper()
        if mode == "TODO":
            return df
        cut_secs = {
            "1H": 3600,
            "6H": 6 * 3600,
            "24H": 24 * 3600,
            "7D": 7 * 86400,
        }.get(mode)
        if cut_secs is None:
            return df
        now = _now_epoch()
        return df[df["ts_epoch"] >= (now - cut_secs)].copy()

    def _set_curve(self, curve, x: np.ndarray, y: np.ndarray):
        if x.size == 0 or y.size == 0:
            curve.setData(np.array([], dtype=float), np.array([], dtype=float))
        else:
            curve.setData(x, y)

    def actualizar_panel_y_graficas(self, force_reload: bool = False, force_plot: bool = False):
        if force_reload or self._csv_changed():
            self._df_cache = cargar_csv_saldos(self.csv_path)

        df = self._df_cache
        self.lbl_rows.setText(f"Filas CSV: {len(df)}")

        if df.empty:
            if force_plot:
                self._clear_view_only()
            return

        df = self._apply_range(df)
        if df.empty:
            self._clear_view_only()
            return

        dmin = agrupar_por_minuto(df)
        dhr = agrupar_por_hora(df)

        x_min = dmin["ts_epoch"].to_numpy(dtype=float)
        x_hr = dhr["ts_epoch"].to_numpy(dtype=float)
        x_all = df["ts_epoch"].to_numpy(dtype=float)

        self._set_curve(self.curve_min_total, x_min, dmin["saldo_total"].to_numpy(dtype=float))
        self._set_curve(self.curve_min_real, x_min, dmin["saldo_real"].to_numpy(dtype=float))
        self._set_curve(self.curve_min_demo, x_min, dmin["saldo_demo"].to_numpy(dtype=float))

        self._set_curve(self.curve_hour_total, x_hr, dhr["saldo_total"].to_numpy(dtype=float))
        self._set_curve(self.curve_hour_real, x_hr, dhr["saldo_real"].to_numpy(dtype=float))
        self._set_curve(self.curve_hour_demo, x_hr, dhr["saldo_demo"].to_numpy(dtype=float))

        self._set_curve(self.curve_all_total, x_all, df["saldo_total"].to_numpy(dtype=float))
        self._set_curve(self.curve_all_real, x_all, df["saldo_real"].to_numpy(dtype=float))
        self._set_curve(self.curve_all_demo, x_all, df["saldo_demo"].to_numpy(dtype=float))

        if self.chk_autoscale.isChecked():
            for p in (self.plot_min, self.plot_hour, self.plot_all):
                p.enableAutoRange(x=True, y=True)
        else:
            for p in (self.plot_min, self.plot_hour, self.plot_all):
                p.disableAutoRange()


# =========================
# Main
# =========================
def main():
    script_dir = fijar_directorio_script()
    app = QtWidgets.QApplication(sys.argv)
    app.setApplicationName("Monitor Saldos 3 Gráficas")

    win = MonitorSaldosWindow(script_dir)
    win.show()

    sys.exit(app.exec_())


if __name__ == "__main__":
    main()
