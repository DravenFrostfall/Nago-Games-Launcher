#!/usr/bin/env python3
"""
NAGO Launcher — A Linux game launcher with SteamGridDB support,
native Linux game support, and Windows game support via Proton.
"""

import sys
import os
import gc
import signal
import platform
import datetime
import functools
import sqlite3
import json
import subprocess
import shutil
import hashlib
import re
import shlex
import tarfile
import time
import socket
import threading
import io
import collections
from pathlib import Path

# ── Lazy imports (heavy, not needed at startup) ────────────────────────────────
def _requests():
    import requests as _r
    return _r

def _pil_image():
    from PIL import Image as _img
    return _img

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QGridLayout, QLabel, QPushButton, QLineEdit, QTextEdit, QScrollArea,
    QFrame, QFileDialog, QDialog, QComboBox, QMessageBox,
    QStackedWidget, QSizePolicy, QMenu,
    QGraphicsOpacityEffect, QTabWidget, QSlider, QStyledItemDelegate,
    QSystemTrayIcon, QButtonGroup, QRadioButton
)
from PyQt6.QtCore import (
    Qt, QThread, pyqtSignal, QTimer, QPoint, QEvent, QMimeData, QRect, QRectF, QSize, QObject,
    QPropertyAnimation, QEasingCurve
)
from PyQt6.QtGui import (
    QImage,
    QPixmap, QFont, QFontMetrics, QColor, QPainter, QPainterPath,
    QBrush, QPen, QPalette, QIcon, QAction,
    QCursor, QMouseEvent, QDrag, QLinearGradient
)
from PyQt6.QtWidgets import QStyle, QProxyStyle
try:
    from PyQt6.QtSvg import QSvgRenderer
    _QSvgRenderer_available = True
except ImportError:
    _QSvgRenderer_available = False

# ── Early crash guard ──────────────────────────────────────────────────────────
# Installed at module level so it catches NameErrors / slot exceptions even
# before main() runs.  Python 3.14 + PyQt6/SIP 13.x will SEGV if a live
# traceback frame holds a Qt wrapper reference during interpreter shutdown.
# This hook prints the exception then immediately wipes all frame references
# so SIP's cleanup_qobject never sees a dangling pointer.
def _safe_excepthook(exc_type, exc_val, exc_tb):
    import traceback as _tb
    try:
        _tb.print_exception(exc_type, exc_val, exc_tb)
    except Exception:
        pass
    # Write crash log to ~/.local/share/nago-launcher/logs/crash.log
    # before scrubbing the traceback chain — this ensures the full trace
    # is preserved even when NAGO is launched via .desktop (no terminal).
    try:
        import datetime as _dt
        # Self-contained XDG resolution: this hook can fire during import, before
        # the module-level XDG_DATA constant exists, so we compute it inline.
        _xdg = os.environ.get("XDG_DATA_HOME") or str(Path.home() / ".local" / "share")
        _logs_dir = Path(_xdg) / "nago-launcher" / "logs"
        _logs_dir.mkdir(parents=True, exist_ok=True)
        _crash_path = _logs_dir / "crash.log"
        with open(_crash_path, "a", encoding="utf-8") as _f:
            _f.write(f"\n{'=' * 64}\n")
            _f.write(f"CRASH  {_fmt_stamp(_dt.datetime.now())}\n")
            _f.write(f"{'=' * 64}\n")
            _tb.print_exception(exc_type, exc_val, exc_tb, file=_f)
            _f.write(f"{'=' * 64}\n")
    except Exception:
        pass
    finally:
        try:
            exc_val.args = ()
        except Exception:
            pass
        # Walk the entire exception chain and clear __traceback__ on each link
        # so no frame objects survive to hold Qt wrapper refs.
        _ex = exc_val
        while _ex is not None:
            try:
                _ex.__traceback__ = None
            except Exception:
                pass
            _next = getattr(_ex, "__context__", None) or getattr(_ex, "__cause__", None)
            if _next is _ex:
                break
            _ex = _next
        del exc_tb, exc_val, exc_type
sys.excepthook = _safe_excepthook


# ── Constants ──────────────────────────────────────────────────────────────────
APP_NAME = "NAGO"
VERSION  = "1.0.0"
BUILD    = "27-06-2026 00:35"

# Locale-safe date helpers — always English month abbreviations regardless of system locale.
_MONTH_ABBR = ("Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec")

def _fmt_stamp(dt) -> str:
    """Return 'DD-Mon-YYYY HH:MM:SS' e.g. '04-Jun-2026 18:23:45'."""
    return f"{dt.day:02d}-{_MONTH_ABBR[dt.month-1]}-{dt.year} {dt.hour:02d}:{dt.minute:02d}:{dt.second:02d}"

def _fmt_stamp_short(dt) -> str:
    """Return 'DD-Mon-YYYY HH:MM' e.g. '04-Jun-2026 18:23'."""
    return f"{dt.day:02d}-{_MONTH_ABBR[dt.month-1]}-{dt.year} {dt.hour:02d}:{dt.minute:02d}"

def _fmt_date(dt) -> str:
    """Return 'DD-Mon-YYYY' e.g. '04-Jun-2026'."""
    return f"{dt.day:02d}-{_MONTH_ABBR[dt.month-1]}-{dt.year}"


# Honor $XDG_DATA_HOME (XDG Base Directory spec) so users who relocate their
# data dir don't end up with a second library in the wrong place. Falls back to
# the spec's default (~/.local/share) when the variable is unset — the common case.
XDG_DATA       = Path(os.environ.get("XDG_DATA_HOME") or (Path.home() / ".local" / "share"))
NAGO_HOME      = XDG_DATA / "nago-launcher"
DB_PATH        = NAGO_HOME / "games.db"
CFG_PATH       = NAGO_HOME / "config.json"
ART_PATH       = NAGO_HOME / "covers"
PREFIXES_PATH  = NAGO_HOME / "prefixes"
TOOLS_HOME        = NAGO_HOME / "tools"
WINETRICKS_BIN    = TOOLS_HOME / "winetricks"
WINETRICKS_URL    = "https://raw.githubusercontent.com/Winetricks/winetricks/master/src/winetricks"
UMU_HOME       = TOOLS_HOME / "umu"
UMU_BIN        = UMU_HOME / "umu-run"
UMU_DB_CSV     = UMU_HOME / "umu-database.csv"
# Ludusavi save-backup tool — fully self-contained inside NAGO's tools dir.
# The binary lives in LUDUSAVI_HOME; every NAGO call passes --config LUDUSAVI_CONFIG_DIR
# so Ludusavi reads/writes its config + manifest there and never touches ~/.config/ludusavi.
LUDUSAVI_HOME       = TOOLS_HOME / "ludusavi"
LUDUSAVI_BIN        = LUDUSAVI_HOME / "ludusavi"
LUDUSAVI_CONFIG_DIR     = LUDUSAVI_HOME / "config"      # --config target dir
LUDUSAVI_BACKUPS        = LUDUSAVI_HOME / "backups"     # default backup destination
LUDUSAVI_MANUAL_BACKUPS = LUDUSAVI_BACKUPS              # manual: same root, no --path needed
LUDUSAVI_AUTO_BACKUPS   = LUDUSAVI_BACKUPS / "_auto"    # auto: _auto/ prefix sorts to top

# Selector value meaning "let umu use its UMU-Proton default (no PROTONPATH set)".
# Distinct from "" so the launch-path `or` fallthrough can't swallow an intentional
# UMU-Proton choice — see ProtonComboBox._fill_combo for the full rationale.
UMU_DEFAULT_SENTINEL = "__umu_default__"


def proton_supports_winetricks(proton_value: str) -> bool:
    """Whether a Proton selection works with umu's `winetricks` verb.

    umu's winetricks integration requires a Proton that bundles protonfixes —
    UMU-Proton, GE-Proton, Proton-CachyOS, Proton-EM, etc. Plain Valve Proton
    (Proton Experimental / Proton 9.0 / Hotfix, installed by Steam) does NOT, and
    `umu-run winetricks` against it fails or hangs.

    We discriminate by PATH, not name: Steam installs official Proton under
    steamapps/common, while every winetricks-capable build lives in
    compatibilitytools.d, umu's own dir, a system path, or a manual location.
    This avoids a name allowlist that would go stale as new community builds appear.

    Auto options (UMU-Proton sentinel, GE-Proton codename) are capable by definition.
    Anything not clearly Valve-in-steamapps/common is treated as capable, so a custom
    or unknown build is never wrongly blocked — the only hard 'no' is detected Valve
    official Proton, which is the case that actually breaks.
    """
    val = (proton_value or "").strip()
    if val in ("", UMU_DEFAULT_SENTINEL, "GE-Proton"):
        return True  # auto-managed UMU/GE — always capable
    # Normalise to path parts and look for a steamapps/common segment pair.
    try:
        parts = [p.lower() for p in Path(val).parts]
    except Exception:
        return True  # unparseable → don't block
    for i in range(len(parts) - 1):
        if parts[i] == "steamapps" and parts[i + 1] == "common":
            return False  # Valve official Proton install location
    return True


# ── Asset resolver ────────────────────────────────────────────────────────────
def _nago_asset(*parts: str) -> Path:
    """Resolve a NAGO asset path robustly for both installed and portable use.

    Search order:
      1. Next to the script file (portable / dev run from any directory)
      2. NAGO_HOME (~/.local/share/nago-launcher) — installed location

    Returns the first path that exists, or the script-relative path as a
    last resort so callers always get a Path back (and can report it missing).
    """
    script_path = Path(__file__).parent.joinpath(*parts)
    if script_path.exists():
        return script_path
    home_path = NAGO_HOME.joinpath(*parts)
    if home_path.exists():
        return home_path
    return script_path  # not found — return script-relative for error messages


# Phosphor icon font — bundled alongside nago-launcher.py
# MIT License © 2023 Phosphor Icons — see https://github.com/phosphor-icons/core
_PHOSPHOR_TTF = _nago_asset("icons", "Phosphor.ttf")
LOGO_PATH     = _nago_asset("icons", "nago-logo.png")
_PHOSPHOR_FONT_ID = -1   # QFontDatabase id, populated in _load_phosphor_font()

# Codepoints for every icon used in NAGO (Phosphor Regular v2.1.2)
PH = {
    # ── Navigation / UI ───────────────────────────────────────────────────────
    "house":                    0x0E2C2,
    "gear":                     0x0E270,
    "magnifying-glass":         0x0E30C,
    "sliders":                  0x0E432,
    "list":                     0x0E2F0,
    "app-window":               0x0E5DA,
    "dots-three-vertical":      0x0E208,
    # ── Files / Data ──────────────────────────────────────────────────────────
    "file-archive":             0x0EB2A,
    "folder":                   0x0E24A,
    "folder-open":              0x0E256,
    "folder-minus":             0x0E254,   # replaces folder-x (removed in v2.1)
    "floppy-disk":              0x0E248,
    "image":                    0x0E2CA,
    "article":                  0x0E0A8,
    "scroll":                   0x0EB7A,
    "database":                 0x0E1DE,
    "stack":                    0x0E466,
    "copy":                     0x0E1CA,
    # ── Editing ───────────────────────────────────────────────────────────────
    "pencil-simple":            0x0E3B4,
    "note-pencil":              0x0E34C,
    "paint-brush":              0x0E6F0,
    "eraser":                   0x0E21E,
    "tag":                      0x0E478,
    "tag-chevron":              0x0E672,
    # ── Actions ───────────────────────────────────────────────────────────────
    "plus":                     0x0E3D4,
    "plus-circle":              0x0E3D6,
    "x":                        0x0E4F6,
    "x-circle":                 0x0E4F8,
    "check":                    0x0E182,
    "check-circle":             0x0E184,
    "trash":                    0x0E4A6,
    "trash-simple":             0x0E4A8,
    "download":                 0x0E20A,
    "download-simple":          0x0E20C,
    "upload-simple":            0x0E4C0,
    "arrow-down":               0x0E03E,
    "arrow-up":                 0x0E08E,
    "arrow-left":               0x0E058,
    "arrows-clockwise":         0x0E094,
    "arrows-counter-clockwise": 0x0E096,
    "scan":                     0x0EBB6,
    "atom":                     0x0E5E4,
    # ── Media / Playback ──────────────────────────────────────────────────────
    "play":                     0x0E3D0,
    "play-circle":              0x0E3D2,
    "sparkle":                  0x0E6A2,
    # ── Status / Info ─────────────────────────────────────────────────────────
    "warning":                  0x0E4E0,
    "info":                     0x0E2CE,
    "clock":                    0x0E19A,
    "circle-notch":             0x0EB44,
    "eye":                      0x0E220,
    "eye-slash":                0x0E224,
    # ── System / Dev ──────────────────────────────────────────────────────────
    "terminal":                 0x0E47E,
    "wrench":                   0x0E5D4,
    "flask":                    0x0E79E,
    "joystick":                 0x0EA5E,
    # ── Logos ─────────────────────────────────────────────────────────────────
    "game-controller":          0x0E26E,
    "linux-logo":               0x0EB02,
    "steam-logo":               0x0EAD4,
}


# ── NAGO styled message box ────────────────────────────────────────────────────
class _NAGODialog(QDialog):
    """Base class for all NAGO dialogs — adds a painted drop shadow and dragging."""
    _SHADOW = 12

    def __init__(self, parent=None):
        super().__init__(parent)
        self._drag_pos = None

    def exec(self):
        """Run the modal loop, then schedule self-destruction.

        Dialogs are created with a Qt parent (the main window), so once the
        Python reference drops they'd otherwise linger as C++ children of the
        main window forever — accumulating across a session and progressively
        slowing event/style propagation through the growing tree.

        We schedule deleteLater() via a zero-delay timer rather than calling it
        inline so that the caller's synchronous post-exec reads (result_data,
        result_label(), selected_ids(), etc.) still see a live object — those
        run before the event loop gets a chance to process the deletion.
        """
        result = super().exec()
        QTimer.singleShot(0, self.deleteLater)
        return result

    @staticmethod
    def _is_interactive(widget) -> bool:
        # Base Qt types are available at import time.
        # NAGOComboBox / NAGOCheckBox are defined later in the module, so we resolve
        # them lazily via globals() to avoid a forward-reference at class-definition time.
        _g = globals()
        _nago_types = tuple(
            _g[n] for n in ("NAGOComboBox", "NAGOCheckBox") if n in _g
        )
        return isinstance(widget, (QPushButton, QLineEdit, QComboBox, QSlider, QScrollArea)
                          + _nago_types)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            child = self.childAt(event.position().toPoint())
            # Walk up the tree — if any ancestor up to the dialog is interactive, don't drag
            widget = child
            interactive = False
            while widget and widget is not self:
                if self._is_interactive(widget):
                    interactive = True
                    break
                widget = widget.parent()
            if not interactive:
                handle = self.windowHandle()
                if handle is not None:
                    handle.startSystemMove()
                    event.accept()
                    return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        self._drag_pos = None
        super().mouseReleaseEvent(event)

    def paintEvent(self, event):
        s = self._SHADOW
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setPen(Qt.PenStyle.NoPen)
        inner = QRectF(self.rect()).adjusted(s, s, -s, -s)
        # Clip to margin area only so shadow never overlaps dialogRoot
        clip = QPainterPath()
        clip.addRect(QRectF(self.rect()))
        cut = QPainterPath()
        cut.addRoundedRect(inner, 12, 12)
        painter.setClipPath(clip.subtracted(cut))
        # Rings: i=1 is closest to dialogRoot (darkest), i=s is outermost (lightest)
        for i in range(1, s + 1):
            alpha = int(25 * (1 - i / s) ** 1.5)
            sr = inner.adjusted(-i, -i, i, i)
            painter.setBrush(QColor(0, 0, 0, alpha))
            painter.drawRoundedRect(sr, 12 + i * 0.5, 12 + i * 0.5)
        painter.end()


class NAGOMessageBox(_NAGODialog):
    """Styled replacement for QMessageBox — matches NAGO's dark theme."""

    # Icon characters from Phosphor font — loaded after font init
    _ICONS = {
        "warning":  ("warning",       "#f59e0b"),
        "critical": ("warning-circle", "#ef4444"),
        "info":     ("info",           "#7b84f0"),
        "question": ("question",       "#7b84f0"),
    }

    def __init__(self, kind: str, title: str, message: str, parent=None,
                 buttons=("OK",), default_button="OK"):
        super().__init__(parent)
        self._result = default_button
        self.setWindowFlags(Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setMinimumWidth(360 + self._SHADOW * 2)
        self.setMaximumWidth(520 + self._SHADOW * 2)

        outer = QVBoxLayout(self)
        outer.setContentsMargins(self._SHADOW, self._SHADOW, self._SHADOW, self._SHADOW)

        root = QFrame()
        root.setObjectName("dialogRoot")
        outer.addWidget(root)

        vbox = QVBoxLayout(root)
        vbox.setContentsMargins(24, 20, 24, 20)
        vbox.setSpacing(16)

        # ── Title bar ──────────────────────────────────────────────────────
        title_row = QHBoxLayout()
        title_row.setSpacing(10)
        icon_name, icon_color = self._ICONS.get(kind, self._ICONS["info"])
        icon_lbl = ph_label(icon_name, 20, icon_color)
        title_lbl = QLabel(title)
        title_lbl.setObjectName("msgBoxTitle")
        title_row.addWidget(icon_lbl)
        title_row.addWidget(title_lbl)
        title_row.addStretch()
        vbox.addLayout(title_row)

        # ── Message ────────────────────────────────────────────────────────
        msg_lbl = QLabel(message)
        msg_lbl.setWordWrap(True)
        msg_lbl.setObjectName("msgBoxMessage")
        msg_lbl.setTextInteractionFlags(Qt.TextInteractionFlag.TextSelectableByMouse)
        vbox.addWidget(msg_lbl)

        # ── Buttons ────────────────────────────────────────────────────────
        btn_row = QHBoxLayout()
        btn_row.setSpacing(8)
        btn_row.addStretch()
        for label in buttons:
            btn = QPushButton(label)
            if label == default_button:
                btn.setObjectName("primary")
                btn.setDefault(True)
            else:
                btn.setObjectName("secondary")
            btn.clicked.connect(lambda checked, l=label: self._on_click(l))
            btn_row.addWidget(btn)
        vbox.addLayout(btn_row)

    def _on_click(self, label: str):
        self._result = label
        self.accept()

    def result_label(self) -> str:
        return self._result

    # ── Static convenience methods — drop-in replacements for QMessageBox ──

    @staticmethod
    def restore_playtime(parent, game_name: str, exe_filename: str,
                         playtime_minutes: int, last_played: str) -> bool:
        """Returns True if user chose Restore, False if Skip."""
        hours = playtime_minutes // 60
        mins  = playtime_minutes % 60
        pt_str = f"{hours} h" if hours else f"{mins} min"
        lp_str = f", last played {last_played}" if last_played else ""
        msg = (f"We found a previous playtime record for\n\n"
               f"{game_name}\n\n"
               f"using  {exe_filename}  —  {pt_str} played{lp_str}.")
        dlg = NAGOMessageBox("info", "Restore playtime?", msg, parent,
                             buttons=("Skip", "Restore"), default_button="Restore")
        dlg.exec()
        return dlg.result_label() == "Restore"

    @staticmethod
    def warning(parent, title: str, message: str) -> None:
        dlg = NAGOMessageBox("warning", title, message, parent)
        dlg.exec()

    @staticmethod
    def critical(parent, title: str, message: str) -> None:
        dlg = NAGOMessageBox("critical", title, message, parent)
        dlg.exec()

    @staticmethod
    def information(parent, title: str, message: str) -> None:
        dlg = NAGOMessageBox("info", title, message, parent)
        dlg.exec()

    @staticmethod
    def question(parent, title: str, message: str,
                 buttons=None, default_button=None) -> "QMessageBox.StandardButton":
        """Returns QMessageBox.StandardButton.Yes or .No for drop-in compatibility."""
        dlg = NAGOMessageBox("question", title, message, parent,
                             buttons=("Yes", "No"), default_button="No")
        dlg.exec()
        if dlg.result_label() == "Yes":
            return QMessageBox.StandardButton.Yes
        return QMessageBox.StandardButton.No


def _current_theme() -> str:
    """Return 'light' or 'dark' from the running app's nagoTheme property.
    Safe to call from paintEvent — never raises."""
    app = QApplication.instance()
    if app is None:
        return "dark"
    return (app.property("nagoTheme") or "dark")


def _t(dark: str, light: str) -> str:
    """Return dark or light inline style value based on current theme.
    Use for setStyleSheet() calls that can't be expressed as QSS object names."""
    return light if _current_theme() == "light" else dark


class NAGOStyle(QProxyStyle):
    """
    QProxyStyle subclass that draws QCheckBox indicators using the Phosphor
    check icon instead of the platform default or a pre-generated PNG file.
    Everything else delegates to the base Fusion style unchanged.
    """

    _check_px: "QPixmap | None" = None  # cached at class level

    @classmethod
    def _checkmark(cls) -> "QPixmap":
        """Return the cached checkmark pixmap, rendering it on first call."""
        if cls._check_px is not None:
            return cls._check_px
        _load_phosphor_font()
        family = _ph_family()
        if not family:
            return QPixmap()  # null — don't cache, allow retry
        # Render directly to QPixmap — skip QIcon to avoid size registration issues
        size = 16
        canvas = size * 4
        px = QPixmap(canvas, canvas)
        px.fill(Qt.GlobalColor.transparent)
        p = QPainter(px)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        font = QFont(family)
        font.setPixelSize(canvas)
        p.setFont(font)
        p.setPen(QColor("#ffffff"))
        p.drawText(px.rect(), Qt.AlignmentFlag.AlignCenter, chr(PH["check"]))
        p.end()
        cls._check_px = px.scaled(
            size, size,
            Qt.AspectRatioMode.KeepAspectRatio,
            Qt.TransformationMode.SmoothTransformation
        )
        return cls._check_px

    def drawPrimitive(self, element, option, painter, widget=None):
        if element == QStyle.PrimitiveElement.PE_IndicatorCheckBox:
            rect = option.rect
            state = option.state

            checked      = bool(state & QStyle.StateFlag.State_On)
            hovered      = bool(state & QStyle.StateFlag.State_MouseOver)
            enabled      = bool(state & QStyle.StateFlag.State_Enabled)
            indeterminate = bool(state & QStyle.StateFlag.State_NoChange)

            # ── Background & border ───────────────────────────────────────
            painter.save()
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)

            if not enabled:
                _theme = _current_theme()
                bg     = QColor("#f0f0f4") if _theme == "light" else QColor("#2a2a30")
                border = QColor("#d4d4d8") if _theme == "light" else QColor("#3d3d42")
            elif checked or indeterminate:
                app    = QApplication.instance()
                accent = (app.property("nagoAccent") or "#6366f1") if app else "#6366f1"
                bg     = QColor(accent).lighter(115) if hovered else QColor(accent)
                border = bg
            elif hovered:
                _theme  = _current_theme()
                app     = QApplication.instance()
                accent2 = (app.property("nagoAccent2") or "#818cf8") if app else "#818cf8"
                bg      = QColor("#e8e8ec") if _theme == "light" else QColor("#3d3d42")
                border  = QColor(accent2)
            else:
                _theme = _current_theme()
                bg     = QColor("#ffffff") if _theme == "light" else QColor("#2d2d32")
                border = QColor("#c4c4cf") if _theme == "light" else QColor("#505058")

            painter.setPen(QPen(border, 1.5))
            painter.setBrush(QBrush(bg))
            painter.drawRoundedRect(rect.adjusted(1, 1, -1, -1), 5, 5)

            # ── Checkmark glyph ───────────────────────────────────────────
            if checked or indeterminate:
                px = self._checkmark()
                if not px.isNull():
                    cx = rect.x() + (rect.width()  - px.width())  // 2
                    cy = rect.y() + (rect.height() - px.height()) // 2
                    painter.drawPixmap(cx, cy, px)

            painter.restore()
            return

        super().drawPrimitive(element, option, painter, widget)

    def styleHint(self, hint, option=None, widget=None, returnData=None):
        if hint == QStyle.StyleHint.SH_ToolTip_WakeUpDelay:
            return 400
        return super().styleHint(hint, option, widget, returnData)


class NAGOCheckBox(QWidget):
    """
    Custom checkbox that draws itself entirely via paintEvent.
    KDE (and any other DE) cannot override paintEvent, so this works
    identically on every Linux desktop environment.
    Emits stateChanged(bool) and supports isChecked() / setChecked().
    """

    stateChanged = pyqtSignal(bool)
    toggled      = pyqtSignal(bool)  # alias — same semantics as QCheckBox.toggled

    def __init__(self, label: str = "", parent=None):
        super().__init__(parent)
        self._checked = False
        self._hovered = False
        self._label   = label
        self._box     = 18          # indicator size px
        self._spacing = 6           # gap between box and label
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self.setMouseTracking(True)
        self._update_size()

    # ── public API (drop-in for QCheckBox) ───────────────────────────────────
    def isChecked(self) -> bool:
        return self._checked

    def setChecked(self, value: bool):
        if self._checked != value:
            self._checked = value
            self.stateChanged.emit(self._checked)
            self.toggled.emit(self._checked)
            self.update()

    def toggle(self):
        self.setChecked(not self._checked)

    def text(self) -> str:
        return self._label

    def setText(self, text: str):
        self._label = text
        self._update_size()
        self.update()

    # ── sizing ────────────────────────────────────────────────────────────────
    def _update_size(self):
        hint = self.sizeHint()
        self.setMinimumSize(hint)
        self.setSizePolicy(QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Fixed)

    def sizeHint(self):
        fm = self.fontMetrics()
        w = self._box + self._spacing + fm.horizontalAdvance(self._label) + 4
        h = max(self._box, fm.height()) + 8
        return QSize(w, h)

    # ── events ────────────────────────────────────────────────────────────────
    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self.toggle()

    def enterEvent(self, event):
        self._hovered = True
        self.update()

    def leaveEvent(self, event):
        self._hovered = False
        self.update()

    def changeEvent(self, event):
        super().changeEvent(event)
        self._update_size()
        self.update()

    # ── painting ──────────────────────────────────────────────────────────────
    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)

        app = QApplication.instance()
        accent = (app.property("nagoAccent") or "#6366f1") if app else "#6366f1"
        accent2 = (app.property("nagoAccent2") or "#818cf8") if app else "#818cf8"

        h = self.height()
        box_y = (h - self._box) // 2
        box_rect = QRectF(1, box_y, self._box - 2, self._box - 2)

        # Background & border
        if not self.isEnabled():
            _theme = _current_theme()
            bg     = QColor("#1e1e22") if _theme == "dark" else QColor("#f0f0f4")
            border = QColor("#2a2a2f") if _theme == "dark" else QColor("#d4d4d8")
        elif self._checked:
            bg     = QColor(accent2) if self._hovered else QColor(accent)
            border = bg
        elif self._hovered:
            _theme = _current_theme()
            bg     = QColor("#e8e8ec") if _theme == "light" else QColor("#3d3d42")
            border = QColor(accent2)
        else:
            _theme = _current_theme()
            bg     = QColor("#ffffff") if _theme == "light" else QColor("#2d2d32")
            border = QColor("#c4c4cf") if _theme == "light" else QColor("#505058")

        p.setPen(QPen(border, 1.5))
        p.setBrush(QBrush(bg))
        p.drawRoundedRect(box_rect, 3, 3)

        # Checkmark
        if self._checked:
            ck_color = QColor("#71717a") if not self.isEnabled() else QColor("#ffffff")
            pen = QPen(ck_color, 2.0)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
            p.setPen(pen)
            # Scale checkmark points to box size
            s = self._box - 2
            ox, oy = 1, box_y
            p.drawLine(
                QPoint(int(ox + s * 0.18), int(oy + s * 0.52)),
                QPoint(int(ox + s * 0.40), int(oy + s * 0.76))
            )
            p.drawLine(
                QPoint(int(ox + s * 0.40), int(oy + s * 0.76)),
                QPoint(int(ox + s * 0.82), int(oy + s * 0.24))
            )

        # Label
        if self._label:
            lx = self._box + self._spacing
            _theme = _current_theme()
            if not self.isEnabled():
                color = QColor("#a1a1aa") if _theme == "light" else QColor("#71717a")
            else:
                color = QColor("#18181b") if _theme == "light" else QColor("#e4e4e7")
            p.setPen(color)
            p.setFont(self.font())
            p.drawText(lx, 0, self.width() - lx, h,
                       Qt.AlignmentFlag.AlignVCenter | Qt.AlignmentFlag.AlignLeft,
                       self._label)

        p.end()


def _load_phosphor_font():
    """Load the Phosphor TTF into Qt's font database. Safe to call multiple times."""
    global _PHOSPHOR_FONT_ID
    if _PHOSPHOR_FONT_ID != -1:
        return                          # already loaded
    if not _PHOSPHOR_TTF.exists():
        return                          # font file missing
    if QApplication.instance() is None:
        return                          # QApplication not yet created
    from PyQt6.QtGui import QFontDatabase
    _PHOSPHOR_FONT_ID = QFontDatabase.addApplicationFont(str(_PHOSPHOR_TTF))
    if _PHOSPHOR_FONT_ID == -1:
        print(f"[NAGO] Warning: failed to load Phosphor font from {_PHOSPHOR_TTF}",
              file=sys.stderr)


def _ph_family() -> str:
    """Return the loaded Phosphor font family name, or empty string."""
    from PyQt6.QtGui import QFontDatabase
    if _PHOSPHOR_FONT_ID != -1:
        families = QFontDatabase.applicationFontFamilies(_PHOSPHOR_FONT_ID)
        if families:
            return families[0]
    return ""


@functools.lru_cache(maxsize=256)
def ph_icon(name: str, size: int = 16, color: str = "#a1a1aa") -> QIcon:
    """
    Render a Phosphor icon glyph into a QIcon by painting it onto a QPixmap.
    Lazy-loads the font on first call so call order doesn't matter.
    Result is cached — same name/size/color returns the same QIcon instance.
    """
    _load_phosphor_font()          # no-op if already loaded
    family = _ph_family()
    canvas = size * 3              # render at 3x for crisp edges, scale down
    px = QPixmap(canvas, canvas)
    px.fill(Qt.GlobalColor.transparent)
    if not family:
        return QIcon(px)
    painter = QPainter(px)
    painter.setRenderHint(QPainter.RenderHint.TextAntialiasing)
    painter.setRenderHint(QPainter.RenderHint.Antialiasing)
    font = QFont(family)
    font.setPixelSize(canvas)
    painter.setFont(font)
    painter.setPen(QColor(color))
    painter.drawText(QRect(0, 0, canvas, canvas),
                     Qt.AlignmentFlag.AlignCenter,
                     chr(PH.get(name, 0x0020)))
    painter.end()
    px = px.scaled(size, size,
                   Qt.AspectRatioMode.KeepAspectRatio,
                   Qt.TransformationMode.SmoothTransformation)
    icon = QIcon(px)
    # Render a dimmer copy of the glyph and register it as the Disabled-mode
    # pixmap. These are icon-only buttons (no text), so QSS `color` can't reach
    # them — Qt's auto-generated disabled icon is too faint on a dark surface.
    # Giving QIcon an explicit Disabled pixmap makes Qt swap to it automatically
    # whenever the button is disabled, with no per-button code.
    dim = QPixmap(canvas, canvas)
    dim.fill(Qt.GlobalColor.transparent)
    dpainter = QPainter(dim)
    dpainter.setRenderHint(QPainter.RenderHint.TextAntialiasing)
    dpainter.setRenderHint(QPainter.RenderHint.Antialiasing)
    dpainter.setFont(font)
    dim_color = QColor(color)
    dim_color.setAlpha(70)         # ~27% opacity — clearly reads as "off"
    dpainter.setPen(dim_color)
    dpainter.drawText(QRect(0, 0, canvas, canvas),
                      Qt.AlignmentFlag.AlignCenter,
                      chr(PH.get(name, 0x0020)))
    dpainter.end()
    dim = dim.scaled(size, size,
                     Qt.AspectRatioMode.KeepAspectRatio,
                     Qt.TransformationMode.SmoothTransformation)
    icon.addPixmap(dim, QIcon.Mode.Disabled)
    return icon


def ph_label(name: str, size: int = 16, color: str = "#a1a1aa") -> QLabel:
    """
    Return a QLabel showing a single Phosphor icon glyph as a pixmap.
    Safe against stylesheet font-family overrides.
    ph_icon() is cached so the pixmap is only rendered once per name/size/color.
    """
    lbl = QLabel()
    lbl.setPixmap(ph_icon(name, size, color).pixmap(size, size))
    lbl.setFixedSize(size + 4, size + 4)
    lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
    lbl.setObjectName("phIcon")
    return lbl


@functools.lru_cache(maxsize=32)
def store_icon(name: str, size: int = 16, color: str = "#ffffff") -> QIcon:
    """
    Load a store SVG icon from the NAGO icons directory and render it as a
    monochrome QIcon at the requested size and color.

    `name` is the SVG filename without extension, e.g. "steam", "lutris".
    Falls back to an empty QIcon silently if the file is missing or
    PyQt6.QtSvg is unavailable — the button still shows its text label.

    Color is applied by painting the SVG path onto a solid-color mask so
    all pixels become the requested color regardless of the SVG's own fill.
    This matches how ph_icon() works — theme-driven monochrome rendering.
    """
    if not _QSvgRenderer_available:
        return QIcon()
    svg_path = _nago_asset("icons", f"{name}.svg")
    if not svg_path.is_file():
        return QIcon()
    try:
        renderer = QSvgRenderer(str(svg_path))
        canvas = size * 3  # render at 3x for crisp edges, scale down
        # Preserve the SVG's own aspect ratio — render into a centered
        # square region so non-square viewBoxes don't skew.
        vp = renderer.viewBoxF()
        if vp.width() > 0 and vp.height() > 0:
            aspect = vp.width() / vp.height()
        else:
            aspect = 1.0
        if aspect >= 1.0:
            rw = float(canvas)
            rh = canvas / aspect
        else:
            rw = canvas * aspect
            rh = float(canvas)
        rx = (canvas - rw) / 2.0
        ry = (canvas - rh) / 2.0
        # Render SVG into a pixmap with transparency
        raw = QPixmap(canvas, canvas)
        raw.fill(Qt.GlobalColor.transparent)
        painter = QPainter(raw)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        renderer.render(painter, QRectF(rx, ry, rw, rh))
        painter.end()
        # Convert to monochrome: use the SVG alpha channel as a mask,
        # paint every opaque pixel in the requested color.
        result = QPixmap(canvas, canvas)
        result.fill(Qt.GlobalColor.transparent)
        painter = QPainter(result)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.drawPixmap(0, 0, raw)
        painter.setCompositionMode(
            QPainter.CompositionMode.CompositionMode_SourceIn
        )
        painter.fillRect(result.rect(), QColor(color))
        painter.end()
        result = result.scaled(
            size, size,
            Qt.AspectRatioMode.KeepAspectRatio,
            Qt.TransformationMode.SmoothTransformation,
        )
        return QIcon(result)
    except Exception:
        return QIcon()


@functools.lru_cache(maxsize=64)
def _spinner_icon(angle: int, size: int = 22, color: str = "#a1a1aa") -> QIcon:
    """Render the circle-notch glyph rotated by `angle` degrees.
    Cached per (angle, size, color) — only 12 distinct angles at 30° steps,
    so the cache stays tiny and each frame is rendered at most once."""
    _load_phosphor_font()
    family = _ph_family()
    canvas = size * 3
    px = QPixmap(canvas, canvas)
    px.fill(Qt.GlobalColor.transparent)
    if family:
        painter = QPainter(px)
        painter.setRenderHint(QPainter.RenderHint.TextAntialiasing)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.translate(canvas / 2, canvas / 2)
        painter.rotate(angle)
        painter.translate(-canvas / 2, -canvas / 2)
        font = QFont(family)
        font.setPixelSize(canvas)
        painter.setFont(font)
        painter.setPen(QColor(color))
        painter.drawText(QRect(0, 0, canvas, canvas),
                         Qt.AlignmentFlag.AlignCenter,
                         chr(PH["circle-notch"]))
        painter.end()
    px = px.scaled(size, size,
                   Qt.AspectRatioMode.KeepAspectRatio,
                   Qt.TransformationMode.SmoothTransformation)
    return QIcon(px)


class _ButtonSpinner:
    """Animates a rotating circle-notch icon on a QPushButton while a task runs.
    Restores the button's original icon when stopped. Safe to start/stop repeatedly.

    Usage:
        spin = _ButtonSpinner(my_button)
        spin.start()          # button shows a real spinning icon
        ... background work ...
        spin.stop()           # original icon restored
    """
    def __init__(self, button, size: int = 22, color: str = "#a1a1aa"):
        self._btn   = button
        self._size  = size
        self._color = color
        self._angle = 0
        self._orig_icon = None
        self._timer = QTimer(button)
        self._timer.setInterval(80)   # ~12.5 fps — smooth enough, cheap
        self._timer.timeout.connect(self._tick)

    def start(self):
        if self._timer.isActive():
            return
        self._orig_icon = self._btn.icon()
        self._angle = 0
        self._timer.start()
        self._tick()

    def _tick(self):
        self._angle = (self._angle + 30) % 360
        try:
            self._btn.setIcon(_spinner_icon(self._angle, self._size, self._color))
        except RuntimeError:
            self._timer.stop()   # button was destroyed mid-spin

    def stop(self):
        self._timer.stop()
        if self._orig_icon is not None:
            try:
                self._btn.setIcon(self._orig_icon)
            except RuntimeError:
                pass
            self._orig_icon = None


CARD_W = 185
COVER_H = CARD_W * 3 // 2   # true 2:3 ratio, no clipping ever
CARD_H = COVER_H              # no strip — name lives inside cover over gradient
CARD_RADIUS  = round(CARD_W * 0.0667)  # ~12px at 175px; scales with card width
COVER_RADIUS = CARD_RADIUS - 2          # inner edge; offset by the 2px card border

# ── umu-launcher integration ───────────────────────────────────────────────────
UMU_STORES = ["none", "egs", "amazon", "battlenet", "ea", "humble",
              "itchio", "ubisoft", "zoomplatform",
              "gog", "steam"]  # gog/steam auto-set, not shown in dropdown

def find_umu_run() -> str:
    """
    Locate the umu-run binary. NAGO always prefers its own bundled copy.
    Falls back to PATH only if the user has explicitly installed one elsewhere
    (and NAGO doesn't have its own yet).
    """
    if UMU_BIN.exists():
        return str(UMU_BIN)
    # PATH fallback for users who already have one installed
    hit = shutil.which("umu-run")
    if hit:
        return hit
    return ""

def umu_install_kind() -> str:
    """
    Returns:
      'managed' if NAGO's own bundled umu-run is installed
      'system'  if some other umu-run is on PATH
      ''        if neither is found
    """
    if UMU_BIN.exists():
        return "managed"
    if shutil.which("umu-run"):
        return "system"
    return ""

def _invalidate_umu_version_cache():
    global _umu_version_cache
    _umu_version_cache = None

def _invalidate_winetricks_version_cache():
    global _winetricks_version_cache
    _winetricks_version_cache = None

def _invalidate_ludusavi_version_cache():
    global _ludusavi_version_cache
    _ludusavi_version_cache = None

def _invalidate_tool_caches():
    """Invalidate all tool version caches at once.
    Call this whenever a tool path changes so every cache is cleared from one site."""
    _invalidate_umu_version_cache()
    _invalidate_winetricks_version_cache()
    _invalidate_ludusavi_version_cache()

def get_umu_version() -> str:
    """
    Get a printable version/identifier for the active umu-launcher install.
    For NAGO-managed installs, reads the cached tag from config.json.
    Falls back to running `umu-run --version` for system installs.
    Also migrates any leftover version.txt file from earlier builds.
    Result is module-level cached — call _invalidate_umu_version_cache() after
    install/update to force a fresh read on the next call.
    """
    global _umu_version_cache
    if _umu_version_cache is not None:
        return _umu_version_cache

    if UMU_BIN.exists():
        cfg = load_config()
        tag = (cfg.get("umu_version") or "").strip()
        if tag:
            _umu_version_cache = tag
            return _umu_version_cache

        # Migrate from the old version.txt sidecar if it still exists
        version_file = UMU_HOME / "version.txt"
        if version_file.exists():
            try:
                tag = version_file.read_text().strip()
                if tag:
                    cfg["umu_version"] = tag
                    save_config(cfg)
                    version_file.unlink(missing_ok=True)
                    _umu_version_cache = tag
                    return _umu_version_cache
            except Exception as e:
                _NAGOLog.session(f"[warn] get_umu_version: failed to read version.txt: {e}")
        _umu_version_cache = "installed"
        return _umu_version_cache

    # System install: version resolved asynchronously via UmuVersionSubprocessWorker.
    # Return a placeholder here — _refresh_umu_status() will update the label
    # once the worker emits its result.
    binary = shutil.which("umu-run")
    if not binary:
        _umu_version_cache = ""
        return _umu_version_cache

    # Don't block — caller should use UmuVersionSubprocessWorker for system installs.
    # Return empty string as sentinel; worker will call _invalidate_umu_version_cache()
    # and emit the real version when done.
    return ""

def _set_pdeathsig_sigterm():
    """
    preexec_fn for subprocess.Popen — makes the child process receive SIGTERM
    automatically when this process (NAGO) dies unexpectedly.
    Linux-only. Safe no-op if prctl is unavailable.
    Only applied to NAGO-managed tools (upscaler), never to the game itself.
    """
    try:
        import ctypes
        import signal as _signal
        PR_SET_PDEATHSIG = 1
        ctypes.CDLL("libc.so.6").prctl(PR_SET_PDEATHSIG, _signal.SIGTERM)
    except Exception:
        pass


def slugify(name: str, fallback: str = "game", max_len: int = 100) -> str:
    """
    Turn an arbitrary game name into a filesystem-safe slug.
    'Kingdom Come: Deliverance II' → 'Kingdom_Come_Deliverance_II'
    Capped at max_len characters to keep filenames sane.
    """
    if not name:
        return fallback
    cleaned = "".join(c if c.isalnum() or c in " -_" else "" for c in name)
    cleaned = "_".join(cleaned.split())
    cleaned = cleaned.strip("_-")
    return (cleaned or fallback)[:max_len]

def get_prefixes_root() -> Path:
    """Return the directory where game prefixes live. Honors `prefixes_path` in config."""
    cfg = load_config()
    custom = (cfg.get("prefixes_path") or "").strip()
    if custom:
        # Expand ~ and environment variables for portability
        return Path(os.path.expandvars(os.path.expanduser(custom)))
    return PREFIXES_PATH

def get_game_prefix(game_id: int, game_name: str = "") -> Path:
    """
    Return the WINEPREFIX path for a given game id, creating it if needed.
    Naming is '<GameName>_<id>', e.g. 'Hogwarts_Legacy_3'.
    """
    root = get_prefixes_root()
    slug = slugify(game_name) if game_name else "game"
    pfx = root / f"{slug}_{game_id}"
    pfx.mkdir(parents=True, exist_ok=True)
    return pfx


def _gamescope_resolution() -> tuple[int, int, int]:
    """
    Return (width, height, refresh) of the PRIMARY connected output for
    gamescope -W/-H/-r. Without -r, gamescope caps the nested session at 60Hz
    regardless of the real panel rate, so the rate must be read and passed.

    Routes through _hdr_tool_choice() so KDE uses kscreen-doctor and GNOME uses
    gdctl. The KDE branch parses `Output:` blocks with priority + active mode;
    the GNOME branch parses `gdctl show` and looks for the [current] mode
    marker. Falls back to (1920, 1080, 60) and logs a warning if detection
    fails. Refresh falls back to 60 if a mode is found but its rate isn't.
    """
    _use_ksd, _use_gdct = _hdr_tool_choice()
    try:
        if _use_ksd:
            _r = subprocess.run(
                ["kscreen-doctor", "-o"],
                capture_output=True, text=True, timeout=3,
                env={**os.environ, "NO_COLOR": "1"},
            )
            _raw = re.sub(r"\x1b\[[0-9;]*m", "", _r.stdout)
            # (priority, width, height, refresh) per enabled+connected output
            _candidates: list[tuple[int, int, int, int]] = []
            for _blk in re.split(r"(?=\bOutput:\s*\d+\b)", _raw):
                _blk = _blk.strip()
                if not _blk:
                    continue
                if "enabled" not in _blk.lower() or "connected" not in _blk.lower():
                    continue
                # Priority — kscreen-doctor uses 1 for primary, 2+ for others
                _pm = re.search(r"priority\s+(\d+)", _blk, re.IGNORECASE)
                _prio = int(_pm.group(1)) if _pm else 99
                _rate = 60
                _w = _h = None
                # Active mode: each mode token is "id:WxHx@rate" with the
                # current-mode flag ('*', optionally with preferred '!')
                # attached DIRECTLY to that token, e.g. "2:2560x1440@144.00*!".
                # All modes for an output share one "Modes:" line, often
                # grouped by resolution with multiple rates each — searching
                # loosely for "any '*' later in the line" (the old approach)
                # locks onto the FIRST WxH@rate token (typically the lowest
                # rate at native res) and is satisfied by an asterisk that
                # actually belongs to a later, different token. Tying the
                # flag to its own token fixes that.
                for _mm in re.finditer(r"(\d{3,5})x(\d{3,5})@([\d.]+)([!*]{0,2})", _blk):
                    if "*" in _mm.group(4):
                        _w, _h = int(_mm.group(1)), int(_mm.group(2))
                        _rate = round(float(_mm.group(3))) or 60
                        break
                if _w is None:
                    # Alternate: "size=WxH" on a line containing * — older/
                    # different kscreen-doctor output form, no rate to read.
                    _m = re.search(r"\*[^\n]*size=(\d{3,5})x(\d{3,5})", _blk)
                    if not _m:
                        _m = re.search(r"size=(\d{3,5})x(\d{3,5})[^\n]*\*", _blk)
                    if _m:
                        _w, _h = int(_m.group(1)), int(_m.group(2))
                if _w is not None:
                    _candidates.append((_prio, _w, _h, _rate))
            if _candidates:
                _candidates.sort()  # lowest priority first = primary
                return _candidates[0][1], _candidates[0][2], _candidates[0][3]
        elif _use_gdct:
            # gdctl show: each monitor block lists modes, the active one
            # marked with [current] (and usually also [preferred]). We don't
            # have a reliable cross-version "primary" marker, so the first
            # monitor's current mode wins — matches gdctl's display ordering.
            _r = subprocess.run(["gdctl", "show"],
                                capture_output=True, text=True, timeout=3)
            for _line in _r.stdout.splitlines():
                if "[current" not in _line.lower():
                    continue
                _m = re.search(r"(\d{3,5})x(\d{3,5})", _line)
                if _m:
                    _rm = re.search(r"(\d{3,5})x(\d{3,5})@?\s*([\d.]+)", _line)
                    _rate = round(float(_rm.group(3))) if _rm and _rm.group(3) else 60
                    return int(_m.group(1)), int(_m.group(2)), (_rate or 60)
    except Exception:
        pass
    try:
        _NAGOLog.launch("[warn] gamescope resolution detection failed — falling back to 1920x1080@60")
    except Exception:
        pass
    return 1920, 1080, 60


def _hdr_tool_choice() -> tuple[bool, bool]:
    """Decide which HDR control tool to use based on desktop and PATH.

    Returns (use_ksd, use_gdct). Exactly one (or neither) is True.
    KDE/Plasma  → kscreen-doctor
    GNOME/Unity → gdctl
    Other DEs   → whichever tool is installed (kscreen-doctor preferred)
    """
    desktop  = os.environ.get("XDG_CURRENT_DESKTOP", "").lower()
    is_kde   = "kde" in desktop or "plasma" in desktop
    is_gnome = "gnome" in desktop or "unity" in desktop
    has_ksd  = bool(shutil.which("kscreen-doctor"))
    has_gdct = bool(shutil.which("gdctl"))

    use_ksd  = (is_kde and has_ksd) or (not is_kde and not is_gnome and has_ksd)
    use_gdct = (is_gnome and has_gdct) or (not is_kde and not is_gnome and not has_ksd and has_gdct)
    return use_ksd, use_gdct


def _hdr_capable_connectors() -> list[str]:
    """Return list of HDR-capable output connector names (e.g. 'DP-1', 'HDMI-A-1').

    Shared by _hdr_commands (used at launch time) and _hdr_scan_monitors
    (used in the dialog tooltip) so both paths agree on what's HDR-capable.

    Returns [] if no detection tool is available or no HDR-capable outputs
    were found.
    """
    use_ksd, use_gdct = _hdr_tool_choice()
    if not use_ksd and not use_gdct:
        return []

    connectors: list[str] = []
    try:
        if use_ksd:
            _r = subprocess.run(["kscreen-doctor", "-o"],
                                capture_output=True, text=True, timeout=3,
                                env={**os.environ, "NO_COLOR": "1"})
            _raw = re.sub(r"\x1b\[[0-9;]*m", "", _r.stdout)
            for _blk in re.split(r"(?=\bOutput:\s*\d+\b)", _raw):
                _blk = _blk.strip()
                _m = re.match(r"Output:\s*\d+\s+(\S+)", _blk)
                if not _m or re.match(r"^[0-9a-f]{8}-", _m.group(1)):
                    continue
                _hdr_m = re.search(r"HDR:\s*(enabled|disabled|incapable)", _blk, re.IGNORECASE)
                if _hdr_m and _hdr_m.group(1).lower() != "incapable":
                    connectors.append(_m.group(1))
        elif use_gdct:
            # gdctl 48+ groups output by "Monitor <conn>" blocks. The exact
            # capability marker format isn't stable across gdctl versions, so
            # try several positive signals in order before falling back to a
            # permissive "mentions HDR without explicit negation" check. Any
            # remaining false positives are made harmless by the per-command
            # `|| true` in _hdr_commands.
            _r = subprocess.run(["gdctl", "show"],
                                capture_output=True, text=True, timeout=3)
            _current: str | None = None
            _block_lines: list[str] = []
            _all_blocks: list[tuple[str, str]] = []
            for _line in _r.stdout.splitlines():
                _m = re.search(r"Monitor\s+(\S+)", _line)
                if _m:
                    if _current is not None:
                        _all_blocks.append((_current, "\n".join(_block_lines)))
                    _current = _m.group(1)
                    _block_lines = [_line]
                else:
                    _block_lines.append(_line)
            if _current is not None:
                _all_blocks.append((_current, "\n".join(_block_lines)))
            for _con, _txt in _all_blocks:
                # 1. Explicit "HDR: <state>" marker (most reliable)
                if re.search(r"HDR\s*:\s*(supported|capable|yes|true|enabled|disabled)",
                             _txt, re.IGNORECASE):
                    connectors.append(_con)
                    continue
                # 2. Mentions bt2100 colorspace (HDR colour space)
                if re.search(r"bt\.?2100", _txt, re.IGNORECASE):
                    connectors.append(_con)
                    continue
                # 3. Permissive fallback — HDR keyword without explicit negation
                _l = _txt.lower()
                if "hdr" in _l and "not supported" not in _l and "incapable" not in _l:
                    connectors.append(_con)
    except Exception:
        pass
    return connectors


def _hdr_commands(monitor: str = "*", connectors: list[str] | None = None) -> tuple[str, str]:
    """
    Return (pre_cmd, post_cmd) to enable/disable HDR on all HDR-capable monitors.

    The `monitor` parameter is legacy and ignored — connectors are always
    auto-detected via _hdr_capable_connectors(). The DB column hdr_monitor
    still exists but is always "*" in new saves.

    `connectors` lets a caller pass in a pre-computed list to avoid the
    subprocess call inside _hdr_capable_connectors(). Used by _launch_game to
    avoid scanning the displays three times per HDR-enabled launch (pre-cmd
    build, post-cmd build, launch log).

    Commands within the returned strings are separated by `;` (not `&&`) so
    a failure on one monitor doesn't abort the rest. The gdctl path appends
    `|| true` per command to tolerate non-HDR monitors that slip through.

    KDE Plasma  → kscreen-doctor
    GNOME 48+   → gdctl
    Other DEs   → whichever tool is installed
    Missing tool → ("", "") — caller silently skips HDR
    """
    use_ksd, use_gdct = _hdr_tool_choice()
    if not use_ksd and not use_gdct:
        return "", ""

    if connectors is None:
        connectors = _hdr_capable_connectors()
    if not connectors:
        return "", ""

    pre_parts:  list[str] = []
    post_parts: list[str] = []
    for _con in connectors:
        if use_ksd:
            # kscreen-doctor: hdr.enable; wcg.enable. `;` so wcg still runs if hdr
            # already enabled (returns non-zero). Same idea for the post path.
            pre_parts.append(f"kscreen-doctor output.{_con}.hdr.enable ; "
                             f"kscreen-doctor output.{_con}.wcg.enable")
            post_parts.append(f"kscreen-doctor output.{_con}.hdr.disable ; "
                              f"kscreen-doctor output.{_con}.wcg.disable")
        else:
            # gdctl: `|| true` so non-HDR monitors (incorrectly slipped through
            # capability detection) don't break the whole chain.
            pre_parts.append(f"gdctl pref --monitor {_con} --color-mode bt2100 || true")
            post_parts.append(f"gdctl pref --monitor {_con} --color-mode default || true")

    return " ; ".join(pre_parts), " ; ".join(post_parts)


# Cached result of probing whether the installed gamescope supports --hdr-enabled.
# gamescope added the flag in v3.13; older builds error out with "unrecognised
# option" and refuse to start. None = not probed yet; True/False = result.
_GAMESCOPE_HDR_SUPPORT_CACHE: bool | None = None


def _gamescope_supports_hdr() -> bool:
    """Return True if the installed gamescope accepts --hdr-enabled.

    Probes once via `gamescope --help` and caches the result. Returns False if
    gamescope isn't installed, the probe fails, or the flag isn't in the help
    output. Cheap to call at every launch after the first.
    """
    global _GAMESCOPE_HDR_SUPPORT_CACHE
    if _GAMESCOPE_HDR_SUPPORT_CACHE is not None:
        return _GAMESCOPE_HDR_SUPPORT_CACHE
    if not shutil.which("gamescope"):
        _GAMESCOPE_HDR_SUPPORT_CACHE = False
        return False
    try:
        _r = subprocess.run(["gamescope", "--help"],
                            capture_output=True, text=True, timeout=3)
        # gamescope prints help to stderr on some versions, stdout on others.
        _haystack = (_r.stdout or "") + (_r.stderr or "")
        _GAMESCOPE_HDR_SUPPORT_CACHE = "--hdr-enabled" in _haystack
    except Exception:
        _GAMESCOPE_HDR_SUPPORT_CACHE = False
    return _GAMESCOPE_HDR_SUPPORT_CACHE


class _NAGOThread(QThread):
    """Common base for every background QThread in NAGO.

    Exists for two reasons, both driven by a recurring fatal-abort crash:
    Qt calls qFatal() (which aborts the whole process) if a QThread C++ object
    is destroyed while the thread is still running. NAGO hit this repeatedly
    when a dialog that owned a worker was closed mid-request — the worker's
    only Python reference died with the dialog, Python GC'd it while it was
    still running, and Qt aborted. Surgical per-dialog fixes kept missing
    sibling cases, so the guard lives here instead, once, for all workers.

    (1) Lifecycle logging. Every worker logs start / finish / orphan-park to
        the Session log (and stderr, so it survives an abort in the terminal
        even though the in-memory buffer dies with the process). The class
        name is in every line — the thing the stripped C++ crash stacks could
        never tell us, which is why blind diagnosis kept failing.

    (2) A class-level keepalive + a stop_safely() helper. If a worker is still
        running when its owner wants to go away, stop_safely() disconnects it,
        asks it to quit, waits briefly, and — if it won't stop in time —
        parks it in a class-level set so it outlives the owner and finishes
        detached, rather than being destroyed mid-run (which is the abort).
        Disconnect-first makes the detached finish harmless.

    Subclasses override run() exactly as before. They get logging for free.
    To also get crash-proof teardown, owners call worker.stop_safely() on
    close instead of bare deleteLater()/letting the reference drop.
    """

    # Every worker that is currently running holds a reference here, added in
    # start() and removed on finished. This is the safety net: a running worker
    # is always referenced by this set, so it can never be garbage-collected
    # mid-run even if its owner is destroyed — which is the condition that
    # aborts the process. Class-level / module-lifetime on purpose.
    _running: set = set()
    _log_lifecycle: bool = True  # set False on bulk workers to suppress start/finish noise

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        # Log start/finish from signals rather than wrapping run(), so it works
        # no matter how the subclass starts itself (start() vs a helper method).
        self.started.connect(self._log_started)
        self.finished.connect(self._log_finished)

    def _cls(self) -> str:
        return type(self).__name__

    def _log_started(self):
        if not self.__class__._log_lifecycle:
            return
        try:
            _NAGOLog.session(f"[thread] {self._cls()} started")
        except Exception:
            pass

    def _log_finished(self):
        if not self.__class__._log_lifecycle:
            return
        try:
            _NAGOLog.session(f"[thread] {self._cls()} finished")
        except Exception:
            pass

    def start(self, *args, **kwargs):
        """The actual global guard — register this worker as running so it can
        never be garbage-collected mid-run.

        The crash is always the same shape: a worker is start()ed, its owner
        (a dialog, a page) keeps the only reference, and when that owner is
        destroyed while the worker is still running, Python collects the
        worker's wrapper and Qt's ~QThread aborts the process. Dozens of call
        sites use `worker.finished.connect(worker.deleteLater)` + `start()`,
        and every one is a latent instance of this. Guarding each teardown site
        by hand kept missing siblings.

        Instead: the moment ANY worker starts, it adds itself to a module-level
        registry and stays there until it actually finishes. While running it
        is therefore always referenced by the registry, independent of whatever
        the owner does — so the owner dying can no longer leave a running thread
        with a zero refcount. On finished, it removes itself and is collected
        normally. This needs no cooperation from call sites, touches nothing
        about how workers do their work, and cannot itself crash (it only
        adds/removes from a set at start and finish). It is the global fix the
        per-site teardowns were only approximating."""
        try:
            _NAGOThread._running.add(self)
            # Remove from the registry once the thread genuinely finishes.
            # Connect via a bound helper, not deleteLater, so the reference is
            # released exactly when the thread is done — not before.
            self.finished.connect(self._unregister)
        except Exception:
            pass
        super().start(*args, **kwargs)

    def _unregister(self):
        try:
            _NAGOThread._running.discard(self)
        except Exception:
            pass

    def stop_safely(self, grace_ms: int = 1500):
        """Disconnect, ask to quit, wait briefly; if still running, park so it
        outlives the caller and can never be destroyed mid-run. Safe to call
        from a UI thread (the wait is short and capped). Idempotent.

        Note: with the start()-time registry above, a worker is already safe
        from mid-run GC without this being called — but stop_safely() is still
        the right thing to call on an owner's close, because it actively asks
        the worker to stop and disconnects its signals so stale results don't
        fire into a half-torn-down owner. The two work together: stop_safely()
        is the polite shutdown, the registry is the safety net under it."""
        try:
            self.disconnect()
        except Exception:
            pass
        # disconnect() above also dropped the finished→_unregister link, so make
        # sure the registry still releases this worker when it eventually ends.
        try:
            self.finished.connect(self._unregister)
        except Exception:
            pass
        try:
            if not self.isRunning():
                self.deleteLater()
                return
            self.quit()
            if self.wait(grace_ms):
                self.deleteLater()
                return
            try:
                _NAGOLog.session(
                    f"[thread] {self._cls()} still running at teardown — parked "
                    f"(outlives owner, finishes detached)"
                )
            except Exception:
                pass
            # Registry already holds it; nothing more needed to keep it alive.
        except Exception:
            pass

class _HDRScanWorker(_NAGOThread):
    """One-shot worker that scans HDR-capable monitors off the GUI thread.

    Wraps `_hdr_capable_connectors` + EDID model-name resolution. Emits a list
    of "DP-1 — Monitor Model" formatted strings when done. Always parentless —
    parenting a QThread to a dialog causes Qt to destroy the worker before
    accept/reject teardown runs, which segfaults if the worker is still active.

    Callers must keep a reference to the worker until it finishes (use the
    class-level _keepalive set) and tolerate the dialog being destroyed while
    the worker is mid-run (the slot uses try/except RuntimeError on the widget).
    """
    result_ready = pyqtSignal(list)

    # Class-level keepalive set so the GC doesn't collect a parentless worker
    # while it's running. Workers remove themselves on finished.
    _keepalive: set = set()

    def run(self):
        out: list[str] = []
        try:
            for _con in _hdr_capable_connectors():
                _model = self._edid_model(_con)
                out.append(f"{_con}{(' — ' + _model) if _model else ''}")
        except Exception:
            pass
        self.result_ready.emit(out)

    @staticmethod
    def _edid_model(connector: str) -> str:
        drm = Path("/sys/class/drm")
        try:
            for entry in drm.iterdir():
                if re.search(rf"-{re.escape(connector)}$", entry.name):
                    data = (entry / "edid").read_bytes()
                    for i in range(4):
                        offset = 54 + i * 18
                        block = data[offset:offset + 18]
                        if len(block) >= 18 and block[3] == 0xFC:
                            return block[5:18].decode("ascii", errors="replace").strip().rstrip("\n").strip()
        except Exception:
            pass
        return ""


# Shared constants for umu GitHub release fetching — used by both
# UmuInstallWorker and UmuLatestVersionWorker so neither duplicates them.
_UMU_RELEASES_API = "https://api.github.com/repos/Open-Wine-Components/umu-launcher/releases"
_UMU_ZIPAPP_RE    = re.compile(r"^umu-launcher-.+-zipapp\.tar(\.gz|\.xz)?$")


class UmuInstallWorker(_NAGOThread):
    """
    Downloads the prebuilt umu-run zipapp from upstream GitHub releases.
    The asset is a small tar archive named umu-launcher-<ver>-zipapp.tar
    that contains a single file 'umu-run' (a self-contained Python zipapp).
    """
    progress    = pyqtSignal(str)   # status text
    finished_ok = pyqtSignal(str)   # version on success
    failed      = pyqtSignal(str)   # error message

    def run(self):
        try:
            self.progress.emit("Querying releases…")
            r = _requests().get(
                _UMU_RELEASES_API,
                headers={"Accept": "application/vnd.github+json"},
                params={"per_page": 30},
                timeout=15,
            )
            r.raise_for_status()
            releases = r.json()
            if not isinstance(releases, list) or not releases:
                self.failed.emit("No releases returned from GitHub.")
                return

            # Walk newest-first looking for the zipapp tarball
            asset_url    = None
            asset_digest = None         # GitHub's "sha256:abc…" format if available
            tag          = None
            zipapp_re    = _UMU_ZIPAPP_RE

            for rel in releases:
                if rel.get("draft") or rel.get("prerelease"):
                    continue
                for a in rel.get("assets", []):
                    name = a.get("name", "")
                    if zipapp_re.match(name) or name == "umu-run":
                        asset_url    = a.get("browser_download_url")
                        asset_digest = a.get("digest", "")  # may be empty
                        tag          = rel.get("tag_name", "unknown")
                        break
                if asset_url:
                    break

            if not asset_url:
                self.failed.emit(
                    "No release contains a downloadable umu-run zipapp.\n\n"
                    "The upstream distribution format may have changed again. "
                    "You can install umu-launcher via your distro's package manager instead."
                )
                return

            # Skip download if the installed version already matches latest.
            if UMU_BIN.exists() and tag:
                current = (load_config().get("umu_version") or "").strip()
                if current.lstrip("v") == tag.lstrip("v"):
                    self.progress.emit("Already up to date.")
                    self.finished_ok.emit(tag)
                    return

            UMU_HOME.mkdir(parents=True, exist_ok=True)
            tmp_path = UMU_HOME / "umu-download.tmp"

            # Download
            asset_name = asset_url.rsplit("/", 1)[-1]
            self.progress.emit(f"Downloading {asset_name} ({tag})…")
            with _requests().get(asset_url, stream=True, timeout=120) as resp:
                resp.raise_for_status()
                total = int(resp.headers.get("content-length", 0))
                done  = 0
                with open(tmp_path, "wb") as f:
                    for chunk in resp.iter_content(chunk_size=64 * 1024):
                        if not chunk:
                            continue
                        f.write(chunk)
                        done += len(chunk)
                        if total:
                            pct = (done * 100) // total
                            self.progress.emit(f"Downloading {asset_name} ({tag})… {pct}%")

            # Verify checksum if GitHub returned one (e.g. "sha256:138ce4b…")
            if asset_digest and ":" in asset_digest:
                self.progress.emit("Verifying checksum…")
                algo, expected = asset_digest.split(":", 1)
                expected = expected.strip().lower()
                if algo.lower() in ("sha256", "sha512", "sha1"):
                    h = hashlib.new(algo.lower())
                    with open(tmp_path, "rb") as f:
                        for chunk in iter(lambda: f.read(64 * 1024), b""):
                            h.update(chunk)
                    actual = h.hexdigest()
                    if expected and expected != actual:
                        tmp_path.unlink(missing_ok=True)
                        self.failed.emit(
                            "Checksum mismatch — the download may be corrupted.\n"
                            f"Expected ({algo}): {expected[:32]}…\nActual:   {actual[:32]}…"
                        )
                        return

            # If the asset is a raw umu-run zipapp, just move it. Otherwise extract from the tar.
            if asset_name == "umu-run":
                if UMU_BIN.exists():
                    UMU_BIN.unlink()
                tmp_path.rename(UMU_BIN)
            else:
                self.progress.emit("Extracting umu-run…")
                # Determine open mode from extension
                if asset_name.endswith(".tar.gz"):
                    mode = "r:gz"
                elif asset_name.endswith(".tar.xz"):
                    mode = "r:xz"
                else:
                    mode = "r:"
                with tarfile.open(tmp_path, mode) as tf:
                    # Find any member whose basename is 'umu-run'
                    target_member = None
                    for m in tf.getmembers():
                        if m.isfile() and Path(m.name).name == "umu-run":
                            target_member = m
                            break
                    if target_member is None:
                        tmp_path.unlink(missing_ok=True)
                        self.failed.emit(
                            f"Archive {asset_name} did not contain a 'umu-run' file."
                        )
                        return
                    extracted_io = tf.extractfile(target_member)
                    if extracted_io is None:
                        tmp_path.unlink(missing_ok=True)
                        self.failed.emit("Could not read umu-run from the archive.")
                        return
                    if UMU_BIN.exists():
                        UMU_BIN.unlink()
                    with open(UMU_BIN, "wb") as out:
                        shutil.copyfileobj(extracted_io, out)
                tmp_path.unlink(missing_ok=True)

            UMU_BIN.chmod(0o755)
            cfg = load_config()
            cfg["umu_version"] = tag
            save_config(cfg)
            self.finished_ok.emit(tag)
        except Exception as e:
            self.failed.emit(str(e))


class UmuLatestVersionWorker(_NAGOThread):
    """Quickly fetches the latest available umu release tag from GitHub."""
    got_version = pyqtSignal(str)  # tag string, or '' on failure

    def run(self):
        try:
            r = _requests().get(
                _UMU_RELEASES_API,
                headers={"Accept": "application/vnd.github+json"},
                params={"per_page": 10},
                timeout=10,
            )
            r.raise_for_status()
            releases = r.json() or []
            zipapp_re = _UMU_ZIPAPP_RE
            for rel in releases:
                if rel.get("draft") or rel.get("prerelease"):
                    continue
                for a in rel.get("assets", []):
                    name = a.get("name", "")
                    if zipapp_re.match(name) or name == "umu-run":
                        self.got_version.emit(rel.get("tag_name", ""))
                        return
            self.got_version.emit("")
        except Exception as e:
            _NAGOLog.session(f"[warn] UmuLatestVersionWorker: {e}")
            self.got_version.emit("")


class UmuDatabaseDownloadWorker(_NAGOThread):
    """Downloads umu-database.csv from upstream into UMU_DB_CSV."""
    finished_ok = pyqtSignal()
    failed      = pyqtSignal(str)

    URL = "https://raw.githubusercontent.com/Open-Wine-Components/umu-database/main/umu-database.csv"

    def run(self):
        try:
            UMU_HOME.mkdir(parents=True, exist_ok=True)
            r = _requests().get(self.URL, timeout=20)
            r.raise_for_status()
            tmp = UMU_DB_CSV.with_suffix(".csv.tmp")
            tmp.write_bytes(r.content)
            tmp.replace(UMU_DB_CSV)
            self.finished_ok.emit()
        except Exception as e:
            self.failed.emit(str(e))


class UmuVersionSubprocessWorker(_NAGOThread):
    """Runs `umu-run --version` in a background thread for system installs.
    Emits got_version(str) with the version string, or 'installed' on failure."""
    got_version = pyqtSignal(str)

    def run(self):
        binary = shutil.which("umu-run")
        if not binary:
            self.got_version.emit("")
            return
        try:
            out = subprocess.run([binary, "--version"],
                                 capture_output=True, text=True, timeout=5)
            text = (out.stdout + out.stderr).strip()
            for line in text.splitlines():
                line = line.strip()
                if not line or line.lower().startswith(("usage", "error")):
                    continue
                self.got_version.emit(line)
                return
        except Exception as e:
            _NAGOLog.session(f"[warn] UmuVersionSubprocessWorker: umu-run --version failed: {e}")
        self.got_version.emit("installed")


class SteamPlaytimeWorker(_NAGOThread):
    """Fetch Steam bulk playtime in a background thread.
    Emits done(dict) where dict is {str(appid): int(minutes)}.
    Emits nothing on failure — caller treats missing key as 0."""
    done = pyqtSignal(dict)

    def __init__(self, api_key: str):
        super().__init__()
        self._api_key = api_key

    def run(self):
        result = steam_bulk_playtime_fetch(self._api_key)
        self.done.emit(result)


class UmuDatabase:
    """
    Loads and searches the umu-database.csv mapping of (title, store) → UMU_ID.
    The CSV is cached at UMU_DB_CSV; call ensure() to download/refresh it.
    """
    _entries: list[dict] = []   # [{title, store, codename, umu_id}]
    _loaded_path: Path = None

    @classmethod
    def needs_download(cls, max_age_days: int = 7) -> bool:
        if not UMU_DB_CSV.exists():
            return True
        try:
            age = time.time() - UMU_DB_CSV.stat().st_mtime
            return age > max_age_days * 86400
        except Exception:
            return True

    @classmethod
    def load(cls) -> list[dict]:
        """Load entries from the cached CSV, parsing once and caching the result."""
        if cls._entries and cls._loaded_path == UMU_DB_CSV:
            return cls._entries
        cls._entries = []
        if not UMU_DB_CSV.exists():
            return cls._entries
        try:
            import csv
            with open(UMU_DB_CSV, newline="", encoding="utf-8") as f:
                reader = csv.DictReader(f)
                for row in reader:
                    title = (row.get("TITLE") or "").strip()
                    if not title:
                        continue
                    cls._entries.append({
                        "title":    title,
                        "store":    (row.get("STORE")    or "").strip().lower(),
                        "codename": (row.get("CODENAME") or "").strip(),
                        "umu_id":   (row.get("UMU_ID")   or "").strip(),
                    })
            cls._loaded_path = UMU_DB_CSV
        except Exception as e:
            print(f"[umu-db] failed to load CSV: {e}")
        return cls._entries

    @classmethod
    def search(cls, query: str, limit: int = 50) -> list[dict]:
        """Case-insensitive substring search over title."""
        q = query.strip().lower()
        if not q:
            return []
        entries = cls.load()
        matches = [e for e in entries if q in e["title"].lower()]
        # Stable sort: exact matches first, then prefix matches, then substring
        def rank(e):
            t = e["title"].lower()
            if t == q:        return 0
            if t.startswith(q): return 1
            return 2
        matches.sort(key=lambda e: (rank(e), e["title"].lower()))
        return matches[:limit]

    @classmethod
    def title_for_id(cls, umu_id: str) -> str:
        """Reverse lookup: return the title for a given UMU_ID, '' if unknown.
        Used to label a stored/matched gameid in the UI without storing the title."""
        uid = (umu_id or "").strip()
        if not uid:
            return ""
        for e in cls.load():
            if e["umu_id"] == uid:
                return e["title"]
        return ""


def _filesystem_share_root(path_str: str) -> str:
    """
    Find the host mount boundary a path lives on, for exposing it to umu's
    Steam Linux Runtime sandbox (pressure-vessel) via STEAM_COMPAT_LIBRARY_PATHS.

    umu runs Proton inside the same container Steam itself uses. That
    container exposes the user's entire $HOME by default, but only a
    subset of everything else on the host — a second game library on a
    separate drive/mount (e.g. /mnt/Games, /media/SomeDrive, a NAS mount)
    is invisible to the sandboxed process even though `if exist` checks
    against $HOME work fine. Files there can read as silently "missing" to
    anything running inside the sandbox.

    Paths already under $HOME return "" (nothing extra needed — already
    exposed). For anything else, this walks up from the given path to the
    nearest actual mount point (os.path.ismount) and returns that boundary.
    No specific location is ever assumed or hardcoded — this works for any
    library path on any system, derived fresh from whatever's actually
    being launched.
    """
    if not path_str:
        return ""
    try:
        p = Path(path_str)
        try:
            p = p.resolve()
        except Exception:
            pass
        try:
            home = Path.home()
            if p == home or home in p.parents:
                return ""
        except Exception:
            pass
        cur = p if p.is_dir() else p.parent
        while not cur.exists() and cur != cur.parent:
            cur = cur.parent
        while cur != cur.parent and not os.path.ismount(cur):
            cur = cur.parent
        return str(cur)
    except Exception:
        return ""


def build_umu_env(base_env: dict, *, wineprefix: str, proton_path: str = "",
                  game_id: str = "", store: str = "",
                  extra_share_paths: "list[str] | None" = None) -> dict:
    """Populate environment variables for umu-run. Modifies a copy of base_env.

    extra_share_paths: host paths actually being launched/touched this run
    (typically the game's or tool's exe_path) that may live outside $HOME.
    See _filesystem_share_root for why this matters — without it, umu's
    sandbox can silently fail to see files on a second drive/mount even
    though they're really there.
    """
    env = dict(base_env)
    env["WINEPREFIX"] = wineprefix
    # PROTONPATH: empty / "umu" / "UMU-Proton" / the umu-default sentinel → set nothing,
    #   so umu uses (and auto-downloads) its UMU-Proton stable default;
    # "GE-Proton" → umu auto-downloads the latest GE-Proton; otherwise a full path.
    if proton_path and proton_path not in (UMU_DEFAULT_SENTINEL, "umu", "UMU-Proton"):
        env["PROTONPATH"] = proton_path
    if game_id:
        env["GAMEID"] = game_id
    if store:
        env["STORE"] = store

    # ── Sandbox filesystem exposure (dynamic — no hardcoded paths) ───────
    share_roots = set()
    for _p in [wineprefix, *(extra_share_paths or [])]:
        _root = _filesystem_share_root(_p)
        if _root:
            share_roots.add(_root)
    if share_roots:
        existing = (base_env.get("STEAM_COMPAT_LIBRARY_PATHS") or "").strip()
        existing_parts = [seg for seg in existing.split(":") if seg]
        combined = list(dict.fromkeys(existing_parts + sorted(share_roots)))
        env["STEAM_COMPAT_LIBRARY_PATHS"] = ":".join(combined)

    return env

# ── Winetricks integration ─────────────────────────────────────────────────────
def find_winetricks() -> str:
    """Locate winetricks. Prefers NAGO's managed copy, falls back to system."""
    if WINETRICKS_BIN.exists():
        return str(WINETRICKS_BIN)
    hit = shutil.which("winetricks")
    return hit or ""

def winetricks_install_kind() -> str:
    """Return 'managed', 'system', or '' (not found)."""
    if WINETRICKS_BIN.exists():
        return "managed"
    if shutil.which("winetricks"):
        return "system"
    return ""

def get_winetricks_version() -> str:
    """
    Return a printable version string for the active winetricks install.
    Winetricks encodes its version as YYYYMMDD in the script itself.
    Cached at module level; call _invalidate_winetricks_version_cache() after install/update.
    """
    global _winetricks_version_cache
    if _winetricks_version_cache is not None:
        return _winetricks_version_cache
    binary = find_winetricks()
    if not binary:
        _winetricks_version_cache = ""
        return ""
    try:
        # winetricks stores its version as: WINETRICKS_VERSION=YYYYMMDD[-next]
        # It's near the top of the file so we only read the first 4 KB.
        with open(binary, "r", errors="ignore") as f:
            head = f.read(4096)
        for line in head.splitlines():
            if line.startswith("WINETRICKS_VERSION="):
                ver = line.split("=", 1)[1].strip().strip('"').strip("'")
                _winetricks_version_cache = ver
                return ver
    except Exception as e:
        _NAGOLog.session(f"[warn] get_winetricks_version: {e}")
    _winetricks_version_cache = "installed"
    return _winetricks_version_cache


class WinetricksInstallWorker(_NAGOThread):
    """Downloads the latest winetricks script from upstream into TOOLS_HOME.

    Uses ETag-based conditional requests to skip the download when the server
    copy hasn't changed since the last install. The ETag is stored in config.json
    under 'winetricks_etag' after each successful download.
    """
    progress    = pyqtSignal(str)
    finished_ok = pyqtSignal(str)   # emits version string on success
    failed      = pyqtSignal(str)

    def run(self):
        try:
            self.progress.emit("Checking winetricks…")
            TOOLS_HOME.mkdir(parents=True, exist_ok=True)

            cfg = load_config()
            stored_etag = (cfg.get("winetricks_etag") or "").strip()

            # Send If-None-Match so GitHub can respond with 304 if unchanged.
            headers = {}
            if stored_etag and WINETRICKS_BIN.exists():
                headers["If-None-Match"] = stored_etag

            resp = _requests().get(WINETRICKS_URL, headers=headers, timeout=30)

            if resp.status_code == 304:
                # Server confirms nothing changed — already up to date.
                self.progress.emit("Already up to date.")
                version = get_winetricks_version() or "installed"
                self.finished_ok.emit(version)
                return

            resp.raise_for_status()
            data = resp.content

            # Parse version from downloaded content before writing.
            version = "installed"
            try:
                for line in resp.text.splitlines()[:60]:
                    if line.startswith("WINETRICKS_VERSION="):
                        version = line.split("=", 1)[1].strip().strip('"').strip("'")
                        break
            except Exception as e:
                _NAGOLog.session(f"[warn] WinetricksInstallWorker: failed to parse version from response: {e}")

            tmp = WINETRICKS_BIN.with_suffix(".tmp")
            tmp.write_bytes(data)
            tmp.chmod(0o755)
            if WINETRICKS_BIN.exists():
                WINETRICKS_BIN.unlink()
            tmp.rename(WINETRICKS_BIN)

            # Persist the new ETag so the next update check can skip the download.
            new_etag = resp.headers.get("etag", "").strip()
            if new_etag:
                cfg = load_config()
                cfg["winetricks_etag"] = new_etag
                save_config(cfg)

            _invalidate_winetricks_version_cache()
            self.finished_ok.emit(version)
        except Exception as e:
            self.failed.emit(str(e))


# ── Ludusavi integration ────────────────────────────────────────────────────────
def find_ludusavi() -> str:
    """Locate the ludusavi binary. Prefers NAGO's managed copy, falls back to system."""
    if LUDUSAVI_BIN.exists():
        return str(LUDUSAVI_BIN)
    hit = shutil.which("ludusavi")
    return hit or ""

def ludusavi_install_kind() -> str:
    """'managed' if NAGO's own copy is installed, 'system' if one is on PATH, '' if neither."""
    if LUDUSAVI_BIN.exists():
        return "managed"
    if shutil.which("ludusavi"):
        return "system"
    return ""

def get_ludusavi_version() -> str:
    """
    Return a printable version string for the active ludusavi install.
    For NAGO-managed installs, reads the cached GitHub tag from config.json (no
    process spawn). Falls back to running `ludusavi --version` for system installs.
    Cached at module level; call _invalidate_ludusavi_version_cache() after install/update.
    """
    global _ludusavi_version_cache
    if _ludusavi_version_cache is not None:
        return _ludusavi_version_cache
    if LUDUSAVI_BIN.exists():
        tag = (load_config().get("ludusavi_version") or "").strip()
        if tag:
            _ludusavi_version_cache = tag
            return _ludusavi_version_cache
        # Managed but no cached tag (older install) — read it off the binary.
        ver = _ludusavi_version_from_binary(str(LUDUSAVI_BIN))
        _ludusavi_version_cache = ver or "installed"
        return _ludusavi_version_cache
    # System install on PATH
    sys_bin = shutil.which("ludusavi")
    if sys_bin:
        ver = _ludusavi_version_from_binary(sys_bin)
        _ludusavi_version_cache = ver or "installed"
        return _ludusavi_version_cache
    _ludusavi_version_cache = ""
    return _ludusavi_version_cache

def _ludusavi_version_from_binary(binary: str) -> str:
    """Run `ludusavi --version` and parse the version (e.g. 'ludusavi 0.31.0' -> 'v0.31.0')."""
    try:
        out = subprocess.run(
            [binary, "--version"], capture_output=True, text=True, timeout=8
        ).stdout.strip()
        # Output is like "ludusavi 0.31.0"; normalize to a leading-v tag for display parity.
        parts = out.split()
        if parts:
            ver = parts[-1]
            return ver if ver.startswith("v") else f"v{ver}"
    except Exception as e:
        _NAGOLog.session(f"[warn] _ludusavi_version_from_binary: {e}")
    return ""


_LUDUSAVI_RELEASES_API = "https://api.github.com/repos/mtkennerly/ludusavi/releases"
# Standalone Linux build, e.g. ludusavi-v0.31.0-linux.tar.gz (a single 'ludusavi' binary)
_LUDUSAVI_LINUX_RE     = re.compile(r"^ludusavi-v.+-linux\.tar\.gz$")


class LudusaviInstallWorker(_NAGOThread):
    """
    Downloads the prebuilt standalone Linux ludusavi binary from GitHub releases.
    The asset is ludusavi-v<ver>-linux.tar.gz containing a single 'ludusavi' binary.
    Version check happens here (only fired by the Install/Update button), never on
    Settings open.
    """
    progress    = pyqtSignal(str)   # status text
    finished_ok = pyqtSignal(str)   # version tag on success
    failed      = pyqtSignal(str)   # error message

    def run(self):
        try:
            self.progress.emit("Querying releases…")
            r = _requests().get(
                _LUDUSAVI_RELEASES_API,
                headers={"Accept": "application/vnd.github+json"},
                params={"per_page": 15},
                timeout=15,
            )
            r.raise_for_status()
            releases = r.json()
            if not isinstance(releases, list) or not releases:
                self.failed.emit("No releases returned from GitHub.")
                return

            asset_url    = None
            asset_digest = None
            tag          = None
            for rel in releases:
                if rel.get("draft") or rel.get("prerelease"):
                    continue
                for a in rel.get("assets", []):
                    if _LUDUSAVI_LINUX_RE.match(a.get("name", "")):
                        asset_url    = a.get("browser_download_url")
                        asset_digest = a.get("digest", "")
                        tag          = rel.get("tag_name", "unknown")
                        break
                if asset_url:
                    break

            if not asset_url:
                self.failed.emit(
                    "No release contains a downloadable Linux ludusavi build.\n\n"
                    "The upstream distribution format may have changed. You can "
                    "install ludusavi via your distro's package manager instead."
                )
                return

            # Skip download if the installed version already matches latest.
            if LUDUSAVI_BIN.exists() and tag:
                current = (load_config().get("ludusavi_version") or "").strip()
                if current.lstrip("v") == tag.lstrip("v"):
                    self.progress.emit("Already up to date.")
                    self.finished_ok.emit(tag)
                    return

            LUDUSAVI_HOME.mkdir(parents=True, exist_ok=True)
            tmp_path = LUDUSAVI_HOME / "ludusavi-download.tmp"
            asset_name = asset_url.rsplit("/", 1)[-1]
            self.progress.emit(f"Downloading ({tag})…")
            with _requests().get(asset_url, stream=True, timeout=120) as resp:
                resp.raise_for_status()
                total = int(resp.headers.get("content-length", 0))
                done  = 0
                with open(tmp_path, "wb") as f:
                    for chunk in resp.iter_content(chunk_size=64 * 1024):
                        if not chunk:
                            continue
                        f.write(chunk)
                        done += len(chunk)
                        if total:
                            pct = (done * 100) // total
                            self.progress.emit(f"Downloading ({tag})… {pct}%")

            # Verify checksum if GitHub returned one (e.g. "sha256:abc…")
            if asset_digest and ":" in asset_digest:
                self.progress.emit("Verifying…")
                algo, expected = asset_digest.split(":", 1)
                expected = expected.strip().lower()
                if algo.lower() in ("sha256", "sha512", "sha1"):
                    h = hashlib.new(algo.lower())
                    with open(tmp_path, "rb") as f:
                        for chunk in iter(lambda: f.read(64 * 1024), b""):
                            h.update(chunk)
                    actual = h.hexdigest()
                    if expected and expected != actual:
                        tmp_path.unlink(missing_ok=True)
                        self.failed.emit(
                            "Checksum mismatch — the download may be corrupted.\n"
                            f"Expected ({algo}): {expected[:32]}…\nActual:   {actual[:32]}…"
                        )
                        return

            # Extract the 'ludusavi' binary from the tar.gz
            self.progress.emit("Extracting…")
            with tarfile.open(tmp_path, "r:gz") as tf:
                target_member = None
                for m in tf.getmembers():
                    if m.isfile() and Path(m.name).name == "ludusavi":
                        target_member = m
                        break
                if target_member is None:
                    tmp_path.unlink(missing_ok=True)
                    self.failed.emit(
                        f"Archive {asset_name} did not contain a 'ludusavi' binary."
                    )
                    return
                extracted_io = tf.extractfile(target_member)
                if extracted_io is None:
                    tmp_path.unlink(missing_ok=True)
                    self.failed.emit("Could not read ludusavi from the archive.")
                    return
                if LUDUSAVI_BIN.exists():
                    LUDUSAVI_BIN.unlink()
                with open(LUDUSAVI_BIN, "wb") as out:
                    shutil.copyfileobj(extracted_io, out)
            tmp_path.unlink(missing_ok=True)

            LUDUSAVI_BIN.chmod(0o755)
            cfg = load_config()
            cfg["ludusavi_version"] = tag
            save_config(cfg)
            _invalidate_ludusavi_version_cache()
            self.finished_ok.emit(tag)
        except Exception as e:
            self.failed.emit(str(e))


class LudusaviManifestUpdateWorker(_NAGOThread):
    """
    Refresh the ludusavi primary manifest (manifest.yaml — the game-save
    database, ~19,000 entries from PCGamingWiki). Separate from the binary
    update: the binary is the program, the manifest is its data, and they
    update on entirely different cadences and sources.

    Runs `ludusavi manifest update`. Uses the bare binary + config (NOT
    _ludusavi_base_cmd, whose --no-manifest-update would suppress the update).
    We read only the exit code, so no --api/JSON is needed (and --api is a
    global flag that must precede the subcommand, not follow it).
    Ludusavi throttles the actual download to once per 24h internally and uses
    an ETag conditional request, so repeat clicks won't re-download — within
    the window it reports success without fetching, which is the desired no-op.
    """
    progress    = pyqtSignal(str)
    finished_ok = pyqtSignal(str)   # short status, e.g. "Updated"
    failed      = pyqtSignal(str)

    def run(self):
        try:
            bin_path = LUDUSAVI_BIN if LUDUSAVI_BIN.exists() else None
            if bin_path is None:
                sys_bin = shutil.which("ludusavi")
                if not sys_bin:
                    self.failed.emit("Ludusavi is not installed.")
                    return
                bin_path = sys_bin
            self.progress.emit("Updating…")
            cmd = [
                str(bin_path), "--config", str(LUDUSAVI_CONFIG_DIR),
                "manifest", "update",
            ]
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            # Exit code 0 means the manifest is current (whether or not a
            # download occurred — ludusavi's ETag check + 24h throttle decide).
            if proc.returncode == 0:
                self.finished_ok.emit("Updated")
                return
            out = (proc.stdout or "").strip()
            err = (proc.stderr or "").strip() or out or f"exit code {proc.returncode}"
            self.failed.emit(err)
        except subprocess.TimeoutExpired:
            self.failed.emit("Manifest update timed out.")
        except Exception as e:
            self.failed.emit(str(e))
#
# Architecture
# ============
# Every backup/restore goes through two sequential phases:
#
#   Phase 1 — FIND (LudusaviFindWorker)
#     Resolves the game to a canonical Ludusavi manifest title. Resolution order
#     exactly mirrors ludusavi's own precedence:
#       Steam ID  →  GOG ID  →  Lutris ID  →  exact name  →  normalized/fuzzy
#     Shortcut: if `ludusavi_title` is cached in the DB, find + verify are
#     skipped entirely (stored-title shortcut). The shortcut self-heals: a
#     preview runs first to confirm the title still resolves saves; if it
#     doesn't, the cache is cleared and the full resolution runs again.
#     For RenPy games not in the manifest, the NAGO game title is used directly
#     as the customGames key — no manifest resolution needed.
#
#   Phase 2 — BACKUP or RESTORE (LudusaviBackupWorker / LudusaviRestoreWorker)
#     Writes a per-game config.yaml (roots appropriate to the game type), then
#     runs `backup --api --force <title>` or `restore --api --force <title>`.
#     The title comes from Phase 1 or from the DB shortcut.
#
# Root strategy by game type
# ==========================
#   steam   → store=steam pointing at each library that holds the appid
#              + the main Steam install (for userdata/cloud saves).  Deduped.
#              Ludusavi handles Proton compatdata + registry itself.
#
#   proton  → store=otherWine  pointing at <prefix>  (or <prefix>/pfx if that
#              sub-dir exists — Proton-managed prefix layout).
#             + store=uplay    pointing at Ubisoft Game Launcher dir inside
#              drive_c, when present (resolves <ubisoftconnect> placeholder).
#             + store=other    pointing at the library parent (install_dir.parent)
#              so that <base> saves outside the prefix are found.
#
#   gog     → store=otherWine  pointing at <prefix> / <prefix>/pfx (same as above).
#             + store=other    pointing at the library parent (install_dir.parent)
#              covers <base> saves for all GOG games regardless of GOG ID.
#              Note: store=gog is NOT used — it requires GOG Galaxy running and
#              makes false store assumptions; store=other is more reliable.
#
#   native  → no root needed for manifest games (ludusavi scans ~/ / XDG dirs).
#              For RenPy games, a customGames entry is written to config.yaml
#              with glob paths pointing at ~/.renpy/<SaveDir>/ so saves are
#              backed up even when the game is not in the community manifest.
#
# The DB column `ludusavi_title` caches the resolved manifest title. It is the
# backbone of the stored-title shortcut in LudusaviFindWorker: when set, find +
# verify are skipped (after one self-heal preview confirms it still resolves
# saves). Written by the manual picker (trilogy disambiguation) and auto-cached
# after a clean single-title backup. Self-healing: cleared automatically if it
# ever stops resolving saves.
#
def _ludusavi_steam_root() -> str:
    """Return the main Steam install dir (contains steamapps + userdata), or ''.

    These are the canonical Linux locations of the Steam *client* install — the
    native package (~/.steam/steam), the XDG data dir (~/.local/share/Steam),
    Flatpak, and Snap. This is the one irreducible discovery floor: libraryfolders.vdf
    lives under the client install, and there's no API on Linux that reports where
    the client is, so we probe the known homes. Everything past this is data-driven.
    """
    candidates = [
        Path.home() / ".steam" / "steam",
        XDG_DATA / "Steam",
        Path.home() / ".var" / "app" / "com.valvesoftware.Steam" / "data" / "Steam",
        Path.home() / "snap" / "steam" / "common" / ".local" / "share" / "Steam",
        Path.home() / "snap" / "steam" / "common" / ".steam" / "steam",
    ]
    for c in candidates:
        if (c / "steamapps").exists():
            return str(c)
    return ""


def _parse_steam_libraryfolders(steam_root: str) -> list:
    """Parse <steam_root>/steamapps/libraryfolders.vdf into a list of
    (library_path, set_of_appids).

    Hand-written VDF reader — no dependency. Handles the modern numbered-block
    format (each library is an object with "path" and an "apps" sub-block) and the
    legacy flat format (each numbered key maps directly to a path string, no apps).
    For the legacy format the appid set is empty, which is fine: callers fall back
    to checking each library on disk when no appid mapping is available.

    The format is a brace-delimited key/value tree, e.g.:
        "libraryfolders"
        {
            "0" { "path" "/home/u/.local/share/Steam"  "apps" { "8930" "123" } }
            "1" { "path" "/mnt/Games/SteamLibrary"      "apps" { "570"  "456" } }
        }
    """
    if not steam_root:
        return []
    vdf = Path(steam_root) / "steamapps" / "libraryfolders.vdf"
    try:
        text = vdf.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return []

    # Tokenize into quoted strings and braces. VDF strings are double-quoted; braces
    # are bare. This is enough for libraryfolders.vdf, which has no escaped quotes in
    # practice on Linux paths.
    tokens = re.findall(r'"((?:[^"\\]|\\.)*)"|(\{)|(\})', text)
    # Each match is a 3-tuple: (string, '{', '}') with two empty. Flatten to a stream.
    stream = []
    for s, ob, cb in tokens:
        if ob:
            stream.append(("{", None))
        elif cb:
            stream.append(("}", None))
        else:
            stream.append(("str", s.replace('\\\\', '\\')))

    libs = []  # list of (path, set(appids))

    # Walk the stream. We only care about library blocks: a "str" key (numeric)
    # followed by "{", inside which we find a "path" str and optionally an "apps"
    # block whose contents are appid/size string pairs.
    i = 0
    n = len(stream)

    def _read_block(idx):
        """Given idx pointing just after a '{', return (path, appids, next_idx)."""
        path = ""
        appids = set()
        depth = 1
        j = idx
        while j < n and depth > 0:
            tok, val = stream[j]
            if tok == "{":
                depth += 1
                j += 1
                continue
            if tok == "}":
                depth -= 1
                j += 1
                continue
            # tok == "str"
            if depth == 1 and val == "path" and j + 1 < n and stream[j + 1][0] == "str":
                path = stream[j + 1][1]
                j += 2
                continue
            if depth == 1 and val == "apps" and j + 1 < n and stream[j + 1][0] == "{":
                # Read appid keys inside the apps sub-block.
                k = j + 2
                adepth = 1
                expect_key = True  # within apps, tokens alternate key, value, key...
                while k < n and adepth > 0:
                    atok, aval = stream[k]
                    if atok == "{":
                        adepth += 1
                    elif atok == "}":
                        adepth -= 1
                    elif atok == "str" and adepth == 1:
                        # Pairs are "appid" "size". Only the key (every other token,
                        # starting with the first) is an appid; skip the size value.
                        if expect_key:
                            appids.add(aval)
                        expect_key = not expect_key
                    k += 1
                j = k
                continue
            j += 1
        return path, appids, j

    # Find the top-level "libraryfolders" block, then iterate its numbered children.
    while i < n:
        tok, val = stream[i]
        if tok == "str" and val == "libraryfolders" and i + 1 < n and stream[i + 1][0] == "{":
            i += 2
            depth = 1
            while i < n and depth > 0:
                tok, val = stream[i]
                if tok == "}":
                    depth -= 1
                    i += 1
                    continue
                if tok == "{":
                    depth += 1
                    i += 1
                    continue
                # Numbered library key at depth 1.
                if depth == 1 and tok == "str":
                    if i + 1 < n and stream[i + 1][0] == "{":
                        path, appids, nxt = _read_block(i + 2)
                        if path:
                            libs.append((path, appids))
                        i = nxt
                        continue
                    elif i + 1 < n and stream[i + 1][0] == "str":
                        # Legacy flat format: "0" "/path/to/library"
                        libs.append((stream[i + 1][1], set()))
                        i += 2
                        continue
                i += 1
            break
        i += 1

    return libs


def _ludusavi_steam_roots_for_appid(appid: str) -> list:
    """Return a list of {store: steam, path: ...} roots for a Steam game.

    Resolves the game's *actual* library (which may live on any drive / custom
    location) by reading libraryfolders.vdf and matching the appid, then emits:
      1. that library's root (holds steamapps/compatdata/<appid> — Proton prefix), and
      2. the main Steam install root (holds userdata — Steam Cloud / local saves),
    deduped. Both are needed because compatdata follows the game to its library
    while userdata stays in the main install.

    Falls back gracefully: if the main root can't be found, returns []. If the appid
    can't be matched in any library (uninstalled, or legacy vdf with no apps map),
    returns just the main root so behaviour is no worse than before.
    """
    main = _ludusavi_steam_root()
    if not main:
        return []

    appid = (appid or "").strip()
    libs = _parse_steam_libraryfolders(main)

    paths = []  # ordered, de-duplicated
    def _add(p):
        rp = str(Path(p))
        if rp and rp not in paths:
            paths.append(rp)

    # 1. The library that actually contains this appid.
    if appid:
        for lib_path, appids in libs:
            if appid in appids:
                _add(lib_path)
                break
        else:
            # No appid match via the apps map (legacy vdf, or appids absent). Probe
            # each library on disk for the compatdata/appmanifest as a fallback.
            if appid:
                for lib_path, _ in libs:
                    lp = Path(lib_path)
                    if (lp / "steamapps" / f"appmanifest_{appid}.acf").exists() or \
                       (lp / "steamapps" / "compatdata" / appid).exists():
                        _add(lib_path)
                        break

    # 2. The main install (userdata lives here regardless of where the game installs).
    _add(main)

    return [{"store": "steam", "path": p} for p in paths]


def _find_ubisoft_launcher(drive_c: Path) -> str:
    """
    Return the in-prefix 'Ubisoft Game Launcher' dir if Ubisoft Connect is installed
    inside this prefix, else ''. Games like AC Odyssey run through Connect, which
    stores saves under <launcher>/savegames/<userid>/<gameid>/. Ludusavi can only
    resolve the manifest's <ubisoftconnect> placeholder when it's given a uplay root
    pointed here — a bare otherWine root leaves that placeholder unresolved.
    """
    for prog in ("Program Files (x86)", "Program Files"):
        cand = drive_c / prog / "Ubisoft" / "Ubisoft Game Launcher"
        try:
            if cand.is_dir():
                return str(cand)
        except Exception:
            continue
    # Fallback: Connect installed to a custom location. Walk drive_c to a bounded
    # depth and return the first 'Ubisoft Game Launcher' dir found. Depth-capped at
    # 4 so we never crawl an entire prefix (deep game trees would be slow). Only
    # reached when the two standard paths miss, and only for proton games — so this
    # rarely fires and costs nothing in the common case.
    try:
        base_depth = len(drive_c.parts)
        for cur_root, dirs, _files in os.walk(drive_c):
            if (len(Path(cur_root).parts) - base_depth) >= 4:
                dirs[:] = []  # stop descending past depth 4
                continue
            if "Ubisoft Game Launcher" in dirs:
                return str(Path(cur_root) / "Ubisoft Game Launcher")
    except Exception:
        pass
    return ""


def _find_renpy_save_dir_candidates(game: dict) -> list[str]:
    """
    Scan ~/.renpy/ for folders that match this RenPy game's save directory.

    Match logic: split each folder name on the last '-' to isolate the
    save_directory part (e.g. 'SecretsandPromises' from
    'SecretsandPromises-1750058512'). Compare that left part
    case-insensitively against:
      1. Stripped stem(s) of any .sh file(s) in the game directory  (priority)
      2. Stripped NAGO game title                                    (fallback)

    Returns a list of matching folder names (not full paths). Caller decides
    what to do with 0, 1, or multiple results.
    """
    renpy_root = Path.home() / ".renpy"
    if not renpy_root.exists():
        return []

    exe   = (game.get("exe_path") or "").strip()
    title = (game.get("name") or "").strip()

    # Build ordered list of stripped candidates: .sh name(s) first, title last.
    strip_cands: list[str] = []
    if exe:
        game_dir = Path(exe).parent
        try:
            for sh in game_dir.glob("*.sh"):
                s = re.sub(r"[^A-Za-z0-9]", "", sh.stem).lower()
                if s and s not in strip_cands:
                    strip_cands.append(s)
        except Exception:
            pass
    if title:
        s = re.sub(r"[^A-Za-z0-9]", "", title).lower()
        if s and s not in strip_cands:
            strip_cands.append(s)

    if not strip_cands:
        return []

    matches: list[str] = []
    try:
        for folder in renpy_root.iterdir():
            if not folder.is_dir():
                continue
            fname = folder.name
            if "-" not in fname:
                continue
            left = fname.rsplit("-", 1)[0].lower()
            if any(left == c for c in strip_cands):
                if fname not in matches:
                    matches.append(fname)
    except Exception:
        pass
    return matches


def _detect_renpy(exe_path: str) -> bool:
    """Return True if the game appears to be a RenPy game.
    Detection: presence of a 'renpy/' subfolder at or near the game root."""
    if not exe_path:
        return False
    try:
        game_dir = Path(exe_path).parent
        for _ in range(3):
            if (game_dir / "renpy").is_dir():
                return True
            parent = game_dir.parent
            if parent == game_dir:
                break
            game_dir = parent
    except Exception:
        pass
    return False


def _renpy_game_root(exe_path: str) -> Path | None:
    """Return the directory that contains the 'renpy/' subfolder, or None."""
    try:
        game_dir = Path(exe_path).parent
        for _ in range(3):
            if (game_dir / "renpy").is_dir():
                return game_dir
            parent = game_dir.parent
            if parent == game_dir:
                break
            game_dir = parent
    except Exception:
        pass
    return None


def _renpy_save_globs(game: dict) -> list[str]:
    """
    Return ludusavi file glob paths covering all RenPy save locations.

    Each save directory gets two globs: one for root-level files (/*) and
    one for subdirectories (/**). Ludusavi's ** does not match files directly
    in the target directory, so both are required for a complete backup.

    Native game type (~/.renpy/ is the canonical location; game/saves/ is a
    read-only mirror managed by RenPy and does not need separate backup):
      - ~/.renpy/<SaveDir>/*    (root-level save files)
      - ~/.renpy/<SaveDir>/**   (subdirectory saves, e.g. sync/)

    <SaveDir> is resolved in priority order:
      1. stored renpy_save_dir from DB (exact, set after first scan/backup)
      2. scan result from _find_renpy_save_dir_candidates (exact if 1 match)
      3. glob fallback <StrippedTitle>* if no match yet

    Wine game type (proton / gog):
      - <prefix>/drive_c/users/*/AppData/Roaming/RenPy/<StrippedTitle>*/*
      - <prefix>/drive_c/users/*/AppData/Roaming/RenPy/<StrippedTitle>*/**
    """
    gt    = (game.get("game_type") or "").strip()
    exe   = (game.get("exe_path") or "").strip()
    title = (game.get("name") or "").strip()
    if not exe or not title:
        return []

    # Strip to alphanumeric — RenPy save dirs drop spaces/punctuation.
    stripped = re.sub(r"[^A-Za-z0-9]", "", title)
    if not stripped:
        return []

    home_str = str(Path.home())
    globs: list[str] = []

    if gt == "native":
        stored_dir = (game.get("renpy_save_dir") or "").strip()
        if stored_dir:
            # Exact path known — use it directly.
            globs.append(f"{home_str}/.renpy/{stored_dir}/*")
            globs.append(f"{home_str}/.renpy/{stored_dir}/**")
        else:
            candidates = _find_renpy_save_dir_candidates(game)
            if len(candidates) == 1:
                globs.append(f"{home_str}/.renpy/{candidates[0]}/*")
                globs.append(f"{home_str}/.renpy/{candidates[0]}/**")
            else:
                # 0 = not launched yet; >1 = ambiguous — use glob fallback.
                globs.append(f"{home_str}/.renpy/{stripped}*/*")
                globs.append(f"{home_str}/.renpy/{stripped}*/**")

    elif gt in ("proton", "gog"):
        override = (game.get("prefix_path") or "").strip()
        if override and Path(override).exists():
            base = Path(override)
        else:
            gid = game.get("id")
            if not gid:
                return []
            base = get_prefixes_root() / f"{slugify(game.get('name', '')) or 'game'}_{gid}"
        pfx = base / "pfx"
        target = pfx if (pfx / "drive_c").exists() else base
        drive_c = target / "drive_c"
        globs.append(f"{drive_c}/users/*/AppData/Roaming/RenPy/{stripped}*/**")

    return globs


def ludusavi_roots_for_game(game: dict) -> list[dict]:
    """
    Per game-type, return the Ludusavi root(s) to scan.

      • proton / gog : store=otherWine  on the Wine prefix (folder containing
                       drive_c). Covers in-prefix saves.
                       store=other      on the library parent (exe_path.parent).
                       Covers install-folder saves. store=other fires no store-
                       specific manifest conditions, so it works regardless of
                       whether the game is GOG, Steam-manifest, or unlabelled.
                       The sibling false-positive problem (e.g. trilogy games)
                       is handled by the ambiguous picker: when multiple titles
                       pass verification, the user picks once and the confirmed
                       title is stored in DB, bypassing find on all subsequent
                       backups.
                       store=uplay      added for proton games when Ubisoft
                       Connect is found in drive_c.
      • steam        : store=steam roots — ludusavi handles Proton natively.
      • native       : no root needed — ludusavi scans standard XDG/home paths.
    """
    gt = (game.get("game_type") or "").strip()
    if gt in ("proton", "gog"):
        # ── Wine prefix root ───────────────────────────────────────────────
        # Build the prefix path without calling get_game_prefix() — that
        # function creates the directory as a side-effect, which would leave
        # empty prefix folders for games that have never been launched.
        override = (game.get("prefix_path") or "").strip()
        if override and Path(override).exists():
            base = Path(override)
        else:
            gid = game.get("id")
            if not gid:
                return []
            base = get_prefixes_root() / f"{slugify(game.get('name', '')) or 'game'}_{gid}"
        pfx = base / "pfx"
        target = pfx if (pfx / "drive_c").exists() else base
        roots = [{"store": "otherWine", "path": str(target)}]

        # ── Ubisoft Connect (proton only) ──────────────────────────────────
        if gt == "proton":
            ubi = _find_ubisoft_launcher(Path(target) / "drive_c")
            if ubi:
                roots.append({"store": "uplay", "path": ubi})

        # ── Library root (store=other) ─────────────────────────────────────
        # store=other on the library parent covers install-folder saves.
        # Unlike store=gog, it fires no store-specific manifest conditions,
        # so it works for all game types without false store assumptions.
        # Prefer install_dir from DB (user-confirmed ground truth); fall back to
        # _find_install_dir heuristic only when the DB value is absent.
        db_install_dir = (game.get("install_dir") or "").strip()
        exe = (game.get("exe_path") or "").strip()
        try:
            if db_install_dir and Path(db_install_dir).is_dir():
                install_dir = db_install_dir
            elif exe:
                install_dir = _find_install_dir(exe)
            else:
                install_dir = ""
            if install_dir:
                library = str(Path(install_dir).parent)
                if library and library not in {r["path"] for r in roots}:
                    roots.append({"store": "other", "path": library})
        except Exception:
            pass

        return roots

    if gt == "steam":
        appid = (game.get("exe_path") or "").strip()
        return _ludusavi_steam_roots_for_appid(appid)

    # native — no root needed
    return []


def _find_install_dir(exe_path: str) -> str:
    """
    Return the game's install directory as a string, or '' on failure.

    Walks up from the exe looking for a GOG (goggame-*.info) or Epic
    (.egstore/*.mancpn) breadcrumb file — both stores always place theirs at
    the true install root, regardless of how deep the exe itself is nested
    (e.g. <install>/bin/x64/release/game.exe). Checked unconditionally, not
    gated on the game's stored type — the breadcrumb file is the ground
    truth; a stored type tag is just a cached guess at it, and can be
    "proton" for a GOG/Epic install found via raw Browse rather than
    imported through a dedicated flow (see _scan_exe_for_store).

    Falls back to exe_path.parent (the exe's immediate folder) when no
    breadcrumb is found, which is the install root for the vast majority of
    layouts anyway.
    """
    if not exe_path:
        return ""
    current = Path(exe_path).parent
    # Walk up to 6 levels looking for either breadcrumb.
    for _ in range(6):
        if not current.is_dir():
            break
        if any(current.glob("goggame-*.info")):
            return str(current)
        egstore = current / ".egstore"
        if egstore.is_dir() and any(egstore.glob("*.mancpn")):
            return str(current)
        if current.parent == current:
            break
        current = current.parent

    # Fallback: use _game_scan_root structural strip (strips known binary
    # subdirs like bin/win64/windows/x64) for a more accurate install root.
    # Falls back to exe.parent if _game_scan_root returns None.
    _scan = _game_scan_root(exe_path)
    return str(_scan) if _scan is not None else str(Path(exe_path).parent)


def _game_scan_root(exe_path: str) -> "Path | None":
    """
    Resolve the game's true install root from an exe path, config-free.

    Two-pass approach:

    Pass 1 — breadcrumb search (walks upward unconditionally, up to 6 levels).
      Looks for a GOG (goggame-*.info) or Epic (.egstore/*.mancpn) breadcrumb at
      each level.  These files live in the actual game root regardless of how the
      exe is nested, so this handles arbitrary subfolder names like
      Bin/Win64MasterMasterGogPGO/ that would not be in any static name set.
      Returns immediately when a breadcrumb is found.

    Pass 2 — structural strip (only if no breadcrumb was found).
      Walks up from exe parent stripping well-known binary-subdir names
      (Binaries/Win64/bin/x64/...) until a non-bin-subdir directory is reached.
      A flat layout (exe at root) stops on the first step.

    Bounded to 6 levels; never crosses a mount boundary or the filesystem root.
    """
    if not exe_path:
        return None

    start = Path(exe_path).parent
    if not start.is_dir():
        return start

    # Pass 1: walk upward looking for a store breadcrumb.
    cur = start
    for _ in range(6):
        if any(cur.glob("goggame-*.info")):
            return cur
        _eg = cur / ".egstore"
        if _eg.is_dir() and any(_eg.glob("*.mancpn")):
            return cur
        parent = cur.parent
        if parent == cur or os.path.ismount(str(cur)):
            break
        cur = parent

    # Pass 2: no breadcrumb -- strip known binary-subdir names.
    _BIN_SUBDIRS = {"binaries", "bin", "win64", "win32", "win", "windows",
                    "x64", "x86", "x86_64", "amd64", "release", "shipping",
                    "retail", "redist"}
    cur = start
    for _ in range(6):
        parent = cur.parent
        if parent == cur or os.path.ismount(str(cur)):
            return cur
        if cur.name.lower() in _BIN_SUBDIRS:
            cur = parent
            continue
        return cur
    return cur


def _detect_upscaler_dlls(exe_path: str, install_dir: str = "") -> tuple:
    """
    Scan the game's install tree for upscaler DLLs (FSR, DLSS, XeSS).

    If install_dir is provided and is a valid directory it is used directly as
    the scan root (preferred — comes straight from the DB, no guessing needed).
    Otherwise roots at _game_scan_root(exe) structurally.

    Does ONE depth-bounded os.walk (depth <= 6) over the tree, checking every
    filename against the DLL name sets below.  Breaks early once every category
    is maxed.

    Returns (parts: list[str], highlight: bool).
    parts holds one entry per detected technology; join with ' | ' for display.
    highlight is True for FSR 4 (native) or FSR 3.1 (PROTON_FSR4_UPGRADE target).
    """
    if install_dir and Path(install_dir).is_dir():
        root = Path(install_dir)
    else:
        root = _game_scan_root(exe_path)
    if root is None or not root.is_dir():
        return [], False

    # SDK 2.x (FSR4 era): loader + per-effect DLLs.  On RDNA4 these run FSR4;
    # older hardware falls back to FSR3.1.5.  Both `_dx12`-suffixed (SDK 2.0)
    # and plain (SDK 2.1+/2.2) variants ship in the wild.
    _FSR4  = {
        "amd_fidelityfx_loader.dll",
        "amd_fidelityfx_loader_dx12.dll",
        "amd_fidelityfx_upscaler.dll",
        "amd_fidelityfx_upscaler_dx12.dll",
        "amd_fidelityfx_framegeneration.dll",
        "amd_fidelityfx_framegeneration_dx12.dll",
        "amd_fidelityfx_denoiser.dll",       # ray regeneration
        "amd_fidelityfx_radiancecache.dll",  # radiance caching (preview)
        "amdxcffx64.dll",                    # OptiScaler FSR4 GPU-caps DLL
    }
    # SDK 1.x (FSR3.1 era): monolithic DLL — target for PROTON_FSR4_UPGRADE.
    _FSR31 = {
        "amd_fidelityfx_dx12.dll",
        "amd_fidelityfx_vk.dll",
        "ffx_frameinterpolation_x64.dll",
    }
    _FSR30 = {"ffx_fsr3upscaler_x64.dll", "ffx_fsr3_x64.dll"}
    _FSR2  = {
        "ffx_fsr2_api_x64.dll",
        "ffx_fsr2_api_dx12_x64.dll",
        "ffx_fsr2_api_vk_x64.dll",
        "amd_fsr2_api_x64.dll",
    }
    _DLSS  = {"nvngx_dlss.dll", "nvngx_dlssg.dll", "nvngx_dlssd.dll"}
    # XeSS 1.x: libxess.dll only.
    # XeSS 2.x/3.x adds libxell.dll (XeLL) and libxess_fg.dll (frame gen).
    # Pre-1.2 games shipped igxess.dll / XeFX.dll / XeFX_Loader.dll (rare).
    _XESS  = {
        "libxess.dll",
        "libxell.dll",
        "libxess_fg.dll",
        "igxess.dll",
        "xefx.dll",
        "xefx_loader.dll",
    }

    fsr_rank = 0          # 40=FSR4, 31=FSR3.1, 30=FSR3.0, 2=FSR2, 0=none
    dlss_found = False
    xess_found = False

    _MAX_DEPTH = 6
    root_str = os.path.normpath(str(root))
    base_depth = root_str.count(os.sep)

    for dirpath, dirnames, filenames in os.walk(root_str):
        if dirpath.count(os.sep) - base_depth >= _MAX_DEPTH:
            dirnames[:] = []   # prune anything deeper
        for _fn in filenames:
            nl = _fn.lower()
            if   nl in _FSR4:  fsr_rank = max(fsr_rank, 40)
            elif nl in _FSR31: fsr_rank = max(fsr_rank, 31)
            elif nl in _FSR30: fsr_rank = max(fsr_rank, 30)
            elif nl in _FSR2:  fsr_rank = max(fsr_rank, 2)
            elif nl in _DLSS:  dlss_found = True
            elif nl in _XESS:  xess_found = True
        # Stop early once every category is at its max possible state.
        if fsr_rank == 40 and dlss_found and xess_found:
            break

    parts: list = []
    if   fsr_rank == 40: parts.append("FSR 4")
    elif fsr_rank == 31: parts.append("FSR 3.1 — upgrade supported")
    elif fsr_rank == 30: parts.append("FSR 3.0")
    elif fsr_rank == 2:  parts.append("FSR 2.x")
    if dlss_found: parts.append("DLSS")
    if xess_found: parts.append("XeSS")

    return parts, fsr_rank in (40, 31)


def _renpy_store_save_dir(game_id: int, folder_name: str) -> None:
    """Persist the resolved ~/.renpy/ folder name for a RenPy game."""
    try:
        con = db_con()
        con.execute("UPDATE games SET renpy_save_dir=? WHERE id=?",
                    (folder_name, game_id))
        con.commit()
        con.close()
        _NAGOLog.session(
            f"[renpy] stored save dir '{folder_name}' for game {game_id}"
        )
    except Exception as e:
        _NAGOLog.session(f"[renpy] failed to store save dir for game {game_id}: {e}")

def _write_auto_backup_db(gid: int, title: str, summary: dict) -> None:
    """Write auto-backup result to the games DB row (last_backup, summary, title)."""
    import datetime as _dt
    try:
        stamp    = _fmt_stamp_short(_dt.datetime.now())
        n_files  = summary.get("fileCount", 0)
        total_mb = summary.get("totalBytes", 0) / (1024 * 1024)
        _summary = f"{n_files} file(s) ({total_mb:.1f} MB)"
        con = db_con()
        con.execute(
            "UPDATE games SET last_auto_backup=?, auto_backup_summary=?, ludusavi_title=? WHERE id=?",
            (stamp, _summary, title, gid)
        )
        con.commit()
        con.close()
    except Exception as e:
        _NAGOLog.session(f"[auto-backup] DB write failed for game {gid}: {e}")


def _write_ludusavi_config(roots: list[dict], game: dict | None = None):
    """
    Write a minimal config.yaml into LUDUSAVI_CONFIG_DIR so every NAGO ludusavi
    call is fully self-contained (never touches ~/.config/ludusavi). Hand-written
    YAML — no PyYAML dependency. Always writes:
      - roots:   list of store roots for the game (empty list for native)
      - backup:  path → LUDUSAVI_BACKUPS
      - restore: path → LUDUSAVI_BACKUPS

    If game is provided and is a RenPy title (detected by 'renpy/' subfolder),
    also writes a customGames section with glob paths covering the game's save
    directory. This allows ludusavi to back up saves for games not in the
    community manifest, and supplements manifest entries that don't resolve the
    correct save paths for RenPy games.
    """
    LUDUSAVI_CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    LUDUSAVI_BACKUPS.mkdir(parents=True, exist_ok=True)

    def _q(s: str) -> str:
        # Double-quote and escape for YAML. Linux paths have no backslashes, but be safe.
        return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'

    lines = ["roots:"]
    if roots:
        for r in roots:
            lines.append(f"  - path: {_q(r['path'])}")
            lines.append(f"    store: {r['store']}")
    else:
        lines.append("  []")
    lines.append("backup:")
    lines.append(f"  path: {_q(LUDUSAVI_BACKUPS)}")
    lines.append("restore:")
    lines.append(f"  path: {_q(LUDUSAVI_BACKUPS)}")

    # ── RenPy custom save paths ───────────────────────────────────────────────
    # Only written when the game is detected as RenPy AND we have glob paths.
    # The customGames entry tells ludusavi exactly where saves live without any
    # community manifest entry required. Harmless if globs match nothing.
    if game:
        exe   = (game.get("exe_path") or "").strip()
        title = (game.get("name") or "").strip()
        if title and exe and _detect_renpy(exe):
            custom_globs = _renpy_save_globs(game)
            if custom_globs:
                lines.append("customGames:")
                lines.append(f"  - name: {_q(title)}")
                lines.append("    files:")
                for g in custom_globs:
                    lines.append(f"      - {_q(g)}")
                _NAGOLog.session(
                    f"[ludusavi] RenPy detected for '{title}', "
                    f"wrote {len(custom_globs)} custom glob(s)"
                )

    _NAGOLog.session(
        f"[ludusavi][config] game={game.get('name') if game else '?'}  "
        f"type={game.get('game_type') if game else '?'}  "
        f"roots={len(roots)}  "
        f"customGames={'yes' if (game and _detect_renpy((game.get('exe_path') or '').strip()) and _renpy_save_globs(game)) else 'no'}"
    )
    for r in roots:
        _NAGOLog.session(f"[ludusavi][config]   root store={r['store']} path={r['path']}")
    (LUDUSAVI_CONFIG_DIR / "config.yaml").write_text("\n".join(lines) + "\n", encoding="utf-8")


def _ludusavi_sanitize_title(title: str) -> str:
    """Mirror ludusavi's backup-folder naming: invalid filename characters are
    replaced with '_'. Used only as a first guess for the backup folder — the
    result is always verified against the filesystem (with a scan fallback), so
    an imperfect match here is self-correcting."""
    invalid = '\\/:*?"<>|\0'
    name = "".join("_" if c in invalid else c for c in title)
    return name.rstrip(" .")   # ludusavi trims trailing spaces/dots


def _resolve_backup_location(resolved_title: str, allow_scan_fallback: bool = True) -> str:
    """Return the absolute path to the ludusavi backup folder for resolved_title,
    or '' if none can be confirmed. Meant to be called right after a successful
    backup, when the folder is guaranteed to exist on disk. A folder only counts
    if it contains a mapping.yaml (ludusavi's own marker for a real backup).

    Strategy: try the sanitized-name guess first; if that misses (rare
    ludusavi-renamed-<hash> case) and allow_scan_fallback is set, fall back to
    the most-recently-written backup folder. The fallback is only safe right
    after a backup (the newest folder is ours); for backfilling a legacy row it
    must be off, or we could mis-attribute another game's folder."""
    try:
        if not resolved_title or not LUDUSAVI_BACKUPS.exists():
            return ""
        guess = LUDUSAVI_BACKUPS / _ludusavi_sanitize_title(resolved_title)
        if (guess / "mapping.yaml").exists():
            return str(guess)
        if not allow_scan_fallback:
            return ""
        candidates = [
            d for d in LUDUSAVI_BACKUPS.iterdir()
            if d.is_dir() and (d / "mapping.yaml").exists()
        ]
        if candidates:
            newest = max(candidates, key=lambda d: d.stat().st_mtime)
            return str(newest)
    except Exception as e:
        _NAGOLog.session(f"[warn] _resolve_backup_location: {e}")
    return ""


def _backup_location_exists(location: str) -> bool:
    """True if the stored backup location still holds a real ludusavi backup.
    A bare folder without mapping.yaml does not count (ludusavi ignores it on
    restore), so neither do we."""
    if not location:
        return False
    try:
        return (Path(location) / "mapping.yaml").exists()
    except Exception:
        return False


def _db_load_game(game_id) -> dict:
    """Re-read a game row from the DB by id. Returns a fresh dict, or empty dict on failure.
    Used by backup/restore workers to get the latest exe_path regardless of UI state."""
    if not game_id:
        return {}
    try:
        con = db_con()
        cols = [d[0] for d in con.execute("SELECT * FROM games LIMIT 0").description]
        row  = con.execute("SELECT * FROM games WHERE id=?", (game_id,)).fetchone()
        con.close()
        if row:
            return dict(zip(cols, row))
    except Exception as e:
        _NAGOLog.session(f"[warn][ludusavi] _db_load_game({game_id}): {e}")
    return {}


# Marker comment written as the first line of every .ludusavi.yaml NAGO creates.
# Ludusavi's YAML parser ignores comment lines, so this is invisible to it but
# lets NAGO tell its own files apart from developer- or user-supplied manifests.
# We only ever overwrite or delete files carrying this marker.
_NAGO_MANIFEST_MARKER = "# nago-launcher-managed"


def _is_nago_manifest(path: Path) -> bool:
    """True if the .ludusavi.yaml at path was written by NAGO (carries our
    marker comment). False for missing files or foreign (dev/user) manifests."""
    try:
        with open(path, "r", encoding="utf-8") as f:
            head = f.read(256)
        return _NAGO_MANIFEST_MARKER in head
    except Exception:
        return False


def _sweep_orphan_manifest(install_dir: str):
    """Delete a NAGO-marked .ludusavi.yaml left behind by a crashed prior run,
    BEFORE gathering candidates, so a stale orphan can't influence find. Never
    touches a foreign (non-NAGO) manifest."""
    if not install_dir:
        return
    try:
        target = Path(install_dir) / ".ludusavi.yaml"
        if target.exists() and _is_nago_manifest(target):
            target.unlink(missing_ok=True)
            _NAGOLog.session(f"[ludusavi] swept orphan NAGO manifest: {target}")
    except Exception as e:
        _NAGOLog.session(f"[warn][ludusavi] orphan sweep failed: {e}")


def _write_secondary_manifest(install_dir: str, title, folder_name: str) -> Path | None:
    """
    Write a .ludusavi.yaml secondary manifest into the game's install dir.

    Ludusavi auto-detects this file at <base>/.ludusavi.yaml and merges it onto
    the primary manifest BY TITLE KEY. For each title, we declare that its
    installDir is <folder_name> — overriding whatever installDir the primary
    manifest specifies. This lets <base> (= <root>/<installDir>) resolve to the
    actual on-disk folder even when it's been renamed, so the primary entry's
    real save paths resolve against the renamed folder.

    CRITICAL: each title MUST be the canonical manifest title (e.g. the value
    returned by `find`), NOT the folder name. Keying on the folder name creates
    a brand-new, save-less entry that merges with nothing and resolves nothing.

    `title` may be a single string or a list of strings (e.g. base game +
    special edition that share a folder). All listed titles get the same
    installDir override.

    Foreign-manifest safety: if a .ludusavi.yaml already exists and was NOT
    written by NAGO (no marker), it's developer- or user-supplied — we leave it
    untouched, write nothing, and return None so the caller won't delete it.
    Ludusavi uses the existing one. (A bundled manifest sits inside the folder
    and already resolves <base> for its own titles, so the rename is moot there;
    the limitation is only if NAGO backs up under a different title than the
    bundled manifest declares.)

    Returns the Path NAGO wrote (carrying the marker), or None if writing was
    skipped (foreign file present) or failed.
    """
    titles = [title] if isinstance(title, str) else list(title or [])
    titles = [t for t in titles if t]
    if not install_dir or not titles or not folder_name:
        return None
    target = Path(install_dir) / ".ludusavi.yaml"
    # Respect a foreign manifest: present and not ours → don't touch it.
    if target.exists() and not _is_nago_manifest(target):
        _NAGOLog.session(
            f"[ludusavi] existing non-NAGO .ludusavi.yaml at {target} — using as-is"
        )
        return None
    try:
        # Single-quoted YAML strings avoid issues with colons/special chars.
        def _yml_str(s: str) -> str:
            # Double-quote and escape for YAML safety.
            return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'
        blocks = [f"{_NAGO_MANIFEST_MARKER} v{VERSION} ({BUILD})\n"]
        for t in titles:
            blocks.append(
                f"{_yml_str(t)}:\n"
                f"  installDir:\n"
                f"    {_yml_str(folder_name)}: {{}}\n"
            )
        target.write_text("".join(blocks), encoding="utf-8")
        return target
    except Exception as e:
        _NAGOLog.session(f"[warn][ludusavi] secondary manifest write failed: {e}")
        return None


def _remove_secondary_manifest(path: Path | None):
    """Safely remove a NAGO-written secondary manifest. Re-checks the marker at
    delete time and refuses to unlink anything that isn't ours — guards against
    a foreign manifest having appeared at the path after we wrote."""
    if path is None:
        return
    try:
        if path.exists() and not _is_nago_manifest(path):
            _NAGOLog.session(
                f"[ludusavi] refusing to delete non-NAGO manifest at {path}"
            )
            return
        path.unlink(missing_ok=True)
    except Exception as e:
        _NAGOLog.session(f"[warn][ludusavi] secondary manifest removal failed: {e}")


def _ludusavi_manifest_exists() -> bool:
    """True if the primary manifest (manifest.yaml) has been downloaded into our
    private config dir. Ludusavi stores manifest.yaml alongside config.yaml."""
    try:
        return (LUDUSAVI_CONFIG_DIR / "manifest.yaml").is_file()
    except Exception:
        return False


def _ludusavi_base_cmd() -> list:
    """
    Common prefix for every ludusavi call: the binary + our private config dir.

    Manifest-update policy (the find/verify/backup hot path can spawn ludusavi
    3-6 times per operation, and every spawn would otherwise pay an implicit
    manifest-staleness check — a file stat plus, on the 24h boundary, a network
    round-trip mid-backup):

      • Manifest already on disk → --no-manifest-update. Skip the implicit check
        entirely. The manifest is refreshed explicitly via the "Update Database"
        button in Settings, not on every spawn.
      • No manifest yet (first run) → --try-manifest-update. Bootstrap it so
        commands don't fail for lack of data, while a transient network error
        doesn't abort the operation.

    --no-manifest-update would itself fail if no manifest existed, which is why
    the bootstrap branch is required rather than always passing --no-...
    """
    base = [str(LUDUSAVI_BIN), "--config", str(LUDUSAVI_CONFIG_DIR)]
    if _ludusavi_manifest_exists():
        base.append("--no-manifest-update")
    else:
        base.append("--try-manifest-update")
    return base


def _run_ludusavi_json(args: list, timeout: int = 300) -> tuple[dict, str]:
    """
    Run a ludusavi --api command and parse its JSON stdout.
    Returns (parsed_dict, error_str). error_str is '' on success. On a non-zero exit
    with no JSON (e.g. find with no matches), parsed_dict is {} and error_str carries
    the human-readable stderr.
    """
    try:
        proc = subprocess.run(
            _ludusavi_base_cmd() + args,
            capture_output=True, text=True, timeout=timeout,
        )
        out = (proc.stdout or "").strip()
        if out:
            try:
                return json.loads(out), ""
            except Exception:
                # Some error conditions print non-JSON; fall through to stderr.
                pass
        err = (proc.stderr or "").strip() or f"ludusavi exited with code {proc.returncode}"
        return {}, err
    except subprocess.TimeoutExpired:
        return {}, "ludusavi timed out."
    except Exception as e:
        return {}, str(e)


class LudusaviFindWorker(_NAGOThread):
    """
    Resolve a NAGO game to one or more BACKABLE Ludusavi manifest titles.

    The key insight (learned from Metro Exodus): a single GOG ID can map to
    multiple manifest entries (e.g. "Metro Exodus" and "Metro Exodus Enhanced
    Edition"), and only some of them have an `installDir` that lets ludusavi
    resolve <base>. The GOG-ID lookup alone stops at the first match, which may
    be the entry that CAN'T back up. So we:

      1. Gather ALL candidate titles for the game:
           - Steam: --steam-id (+ name, with --multiple)
           - GOG:   --multiple --gog-id <id> "<name>"  (surfaces every entry
                    sharing the ID, not just the first)
           - else:  exact name, then --normalized, then --fuzzy
      2. Verify each candidate by running `backup --preview` and keeping only
         those that actually resolve save files.
      3. Emit the verified set. Multiple survivors → back them all up (each
         lands in its own title-keyed folder under the backups dir).

    Signals:
      resolved(list)   — one or more verified-backable titles; proceed to backup
      candidates(list) — titles exist in the manifest but NONE resolved files;
                         let the user pick / confirm manually
      failed(str)      — nothing matched in the manifest at all
    """
    resolved   = pyqtSignal(list)       # list[str] of backable titles
    candidates = pyqtSignal(list)       # list[str] of manifest titles, unverified
    failed     = pyqtSignal(str)

    def __init__(self, game: dict, parent=None):
        super().__init__(parent)
        self._game = dict(game)
        # Set True only when this run resolved a SINGLE title unambiguously
        # (one candidate survived verify). The backup handler reads this after
        # a successful backup to decide whether to cache the title to the DB so
        # future backups can use the stored-title shortcut. Never set for the
        # ambiguous/multi-title path — those go through the manual picker, which
        # does its own (authoritative) caching.
        self.autocacheable = False

    def run(self):
        try:
            gt   = (self._game.get("game_type") or "").strip()
            name = (self._game.get("name") or "").strip()

            # If a title was previously confirmed for this game, skip find
            # entirely and go straight to backup — the stored-title shortcut.
            # Written either by the manual picker (trilogy disambiguation) or
            # auto-cached after a clean single-title backup.
            #
            # Self-heal: the shortcut is only safe while the stored title still
            # resolves saves. A folder rename or manifest change can make it
            # stale. So before trusting it, do ONE cheap preview; if it resolves
            # nothing, drop the shortcut and fall through to a full find. Cost:
            # one wasted preview on the rare stale case. Benefit: the shortcut
            # can never silently back up against a dead title.
            stored_title = (self._game.get("ludusavi_title") or "").strip()
            if stored_title:
                roots = ludusavi_roots_for_game(self._game)
                _write_ludusavi_config(roots, game=self._game)
                # Self-heal: verify stored title WITHOUT a secondary manifest, and
                # scope-check the returned file paths against THIS game's territory.
                #
                # Problem: the shared library root (store: other, library parent)
                # covers all siblings. A wrong sibling title resolves saves via the
                # primary manifest — its installDir exists in the library — so a
                # plain _title_has_saves() always returns True for any sibling.
                #
                # Fix: inspect WHERE the saves are. A sibling title finds saves in
                # a different install folder. Checking that at least one found path
                # is under this game's own install dir or prefix correctly rejects
                # sibling titles → self-heal invalidates → full find re-runs.
                _sh_install = ""
                _sh_exe = (self._game.get("exe_path") or "").strip()
                if _sh_exe and gt in ("gog", "proton"):
                    _sh_install = _find_install_dir(_sh_exe)
                _sh_prefix = next(
                    (r["path"] for r in roots if r["store"] == "otherWine"), ""
                )
                _NAGOLog.session(
                    f"[ludusavi][find] self-heal check: title='{stored_title}'"
                    f"  install={_sh_install!r}  prefix={_sh_prefix!r}"
                )
                _still_valid = self._title_saves_in_territory(
                    stored_title, _sh_install, _sh_prefix
                )
                if _still_valid:
                    _NAGOLog.session(f"[ludusavi][find] stored title still valid: '{stored_title}'")
                    self.resolved.emit([stored_title])
                    return
                _NAGOLog.session(
                    f"[ludusavi][find] stored title '{stored_title}' failed territory check — "
                    "invalidating and re-finding"
                )
                self._invalidate_stored_title()
                # fall through to full find below

            # ── Resolve install dir / folder name (used by both gather + verify)
            exe = (self._game.get("exe_path") or "").strip()
            _install_dir = ""
            _folder_name = ""
            if exe and gt in ("gog", "proton"):
                _install_dir = _find_install_dir(exe)
                _folder_name = Path(_install_dir).name if _install_dir else ""
                # Clear any NAGO-marked manifest a crashed prior run left behind,
                # before gather, so a stale orphan can't influence find. Foreign
                # (dev/user) manifests are never touched.
                _sweep_orphan_manifest(_install_dir)

            # ── Gather candidates WITHOUT a secondary manifest ─────────────────
            # No manifest is active here, so the folder-name search steps match
            # only genuine primary-manifest titles (a real title that happens to
            # equal the folder name) — never a self-referential entry we planted.
            # For a randomly-renamed folder those steps correctly find nothing,
            # and resolution comes from the ID / NAGO-name steps.
            candidates = self._gather_candidates(gt, name, _folder_name)
            if not candidates:
                # ── RenPy fallback ────────────────────────────────────────
                # Game not in manifest but has a RenPy customGames entry in
                # config.yaml — use the NAGO title directly as the key.
                _rp_exe = (self._game.get("exe_path") or "").strip()
                if name and _rp_exe and _detect_renpy(_rp_exe):
                    _rp_cands = _find_renpy_save_dir_candidates(self._game)
                    if len(_rp_cands) > 1:
                        # Ambiguous — can't resolve without UI; treat as failed.
                        pass
                    else:
                        # Auto-store single candidate so future runs skip the scan.
                        if len(_rp_cands) == 1:
                            gid = self._game.get("id")
                            if gid and not (self._game.get("renpy_save_dir") or "").strip():
                                _renpy_store_save_dir(gid, _rp_cands[0])
                                self._game = dict(self._game, renpy_save_dir=_rp_cands[0])
                        if _renpy_save_globs(self._game):
                            _NAGOLog.session(
                                f"[ludusavi][find] no manifest entry for '{name}' "
                                "but RenPy detected — using NAGO title as customGames key"
                            )
                            self.autocacheable = True
                            self.resolved.emit([name])
                            return
                self.failed.emit(
                    f'No Ludusavi manifest entry found for "{name or "this game"}".\n\n'
                    'You can enter the exact PCGamingWiki title manually.'
                )
                return

            # ── Verify with a secondary manifest keyed on the RESOLVED titles ──
            # Map every candidate title → actual folder name as installDir. Now a
            # `backup --preview <title>` resolves <base> to the real (possibly
            # renamed) folder and the primary entry's save paths resolve against
            # it. Whichever candidates have real saves in this folder survive.
            # Siblings sharing a folder both survive → ambiguous picker (unchanged
            # trilogy behaviour). Removed in the finally block.
            roots = ludusavi_roots_for_game(self._game)
            _write_ludusavi_config(roots, game=self._game)
            _secondary: Path | None = None
            if _install_dir and _folder_name:
                _secondary = _write_secondary_manifest(
                    _install_dir, candidates, _folder_name
                )
            try:
                backable = []
                for title in candidates:
                    if self._title_has_saves(title):
                        backable.append(title)
            finally:
                _remove_secondary_manifest(_secondary)

            if len(backable) == 1:
                # Exactly one title resolved saves — unambiguous. Safe to cache
                # to the DB after a successful backup so the next backup uses the
                # stored-title shortcut (self-healing if it later goes stale).
                self.autocacheable = True
                self.resolved.emit(backable)
            elif len(backable) > 1:
                # Multiple titles resolved saves (e.g. trilogy siblings sharing
                # a save folder). Can't auto-pick safely — let the user choose.
                # The picker will store the confirmed title so this only happens
                # once per game.
                _NAGOLog.session(f"[ludusavi][find] ambiguous: {backable} — sending to picker")
                self.candidates.emit(backable)
            else:
                # No title resolved files.
                # ── RenPy fallback ────────────────────────────────────
                # Manifest found candidates but none resolved saves via
                # standard paths. If this is a RenPy game with known save
                # globs, use the NAGO title as the customGames key instead.
                _rp_exe2 = (self._game.get("exe_path") or "").strip()
                if name and _rp_exe2 and _detect_renpy(_rp_exe2) and _renpy_save_globs(self._game):
                    _NAGOLog.session(
                        f"[ludusavi][find] manifest candidates didn't resolve for '{name}' "
                        "but RenPy detected — using NAGO title as customGames key"
                    )
                    self.autocacheable = True
                    self.resolved.emit([name])
                else:
                    self.candidates.emit(candidates)
        except Exception as e:
            self.failed.emit(str(e))

    def _gather_candidates(self, gt: str, name: str, folder_name: str = "") -> list:
        """Collect all plausible manifest titles for this game, in priority order,
        de-duplicated. Runs with NO secondary manifest active, so every match is
        against the genuine primary manifest.

        Search order (curated signal first, random-folder signal last):
          1. Steam/GOG ID lookup (strongest — near-unambiguous)
          2. Exact match on NAGO name (curated, trustworthy)
          3. Normalized match on NAGO name
          4. Exact match on folder name (only hits when the folder equals a real
             title; for a randomly-renamed folder this correctly finds nothing)
          5. Normalized match on folder name
          6. Fuzzy on NAGO name (broadest, last resort — fuzzy only on the
             curated name; a random folder name has no signal to fuzzy-match)

        Each step short-circuits: the first non-empty result wins. The name block
        precedes the folder block so a renamed folder can't short-circuit on a
        self-match before the curated name is tried.
        """
        out = []
        _tag = f"[ludusavi][find][{name!r}]"

        def _add(titles):
            for t in titles:
                if t and t not in out:
                    out.append(t)


        # 1. Store ID lookup
        if gt == "steam":
            appid = (self._game.get("exe_path") or "").strip()
            if appid:
                args = ["--multiple", "--steam-id", appid]
                if name:
                    args.append(name)
                data, _ = self._find(args)
                _add(self._extract_titles(data))
                if out:
                            return out
    
        if gt == "gog":
            gog_id = resolve_gog_id(self._game)
            if gog_id:
                args = ["--multiple", "--gog-id", gog_id]
                if name:
                    args.append(name)
                data, _ = self._find(args)
                _add(self._extract_titles(data))
                if out:
                            return out
    
        # 2. Exact match on NAGO name
        if name:
            data, _ = self._find([name])
            _add(self._extract_titles(data))
            if out:
                    return out

            # 3. Normalized on NAGO name
            data, _ = self._find(["--multiple", "--normalized", name])
            _add(self._extract_titles(data))
            if out:
                    return out

        # 4. Exact match on folder name
        if folder_name:
            data, _ = self._find([folder_name])
            _add(self._extract_titles(data))
            if out:
                    return out

            # 5. Normalized match on folder name
            data, _ = self._find(["--multiple", "--normalized", folder_name])
            _add(self._extract_titles(data))
            if out:
                    return out

        if not name:
            return out

        # 6. Fuzzy on NAGO name — last resort. No score threshold: the old 0.90
        # threshold had a broken fallback (return-all when nothing passed it),
        # causing inconsistent behaviour. Instead we cap at top 15 by score,
        # which is the real protection against verifying 70+ candidates.
        data, _ = self._find(["--multiple", "--fuzzy", name])
        fuzzy_titles = self._extract_titles_fuzzy(data)
        _NAGOLog.session(
            f"{_tag} step 6 (fuzzy): {len(fuzzy_titles)} candidate(s): {fuzzy_titles}"
        )
        _add(fuzzy_titles)
        return out

    def _invalidate_stored_title(self):
        """Clear the cached ludusavi_title for this game in the DB. Called when
        the stored-title shortcut's self-heal preview resolves no saves, so the
        next backup re-finds from scratch instead of trusting a dead title."""
        gid = self._game.get("id")
        if not gid:
            return
        try:
            con = db_con()
            con.execute("UPDATE games SET ludusavi_title='' WHERE id=?", (gid,))
            con.commit()
            con.close()
        except Exception as e:
            _NAGOLog.session(f"[warn][ludusavi] _invalidate_stored_title: {e}")
        # Also clear it from the in-memory game copy so nothing downstream
        # in this same run re-reads the stale value.
        self._game["ludusavi_title"] = ""

    def _title_has_saves(self, title: str) -> bool:
        """Run a backup preview for one title; True if it resolves ≥1 file.

        This method itself injects no manifest — but the caller writes a
        secondary manifest (keyed on the resolved candidate titles, with the
        actual folder as installDir) and keeps it active across the verify loop,
        so `<base>` resolves to the real on-disk folder even when renamed. If
        sibling titles genuinely share a folder, more than one will pass here;
        that ambiguity is resolved by the manual picker, not suppressed.
        """
        data, _ = _run_ludusavi_json(
            ["backup", "--api", "--preview", title], timeout=120
        )
        if not isinstance(data, dict):
            return False
        games = data.get("games", {}) or {}
        for entry in games.values():
            if isinstance(entry, dict) and (entry.get("files") or {}):
                return True
        return False

    def _title_saves_in_territory(self, title: str,
                                    install_dir: str, prefix_dir: str) -> bool:
        """Like _title_has_saves but also verifies that the found save files
        actually live inside THIS game's territory (install folder or prefix).

        Used for self-heal validation only. A sibling title will find saves
        via the shared library root, but the files will be in a different
        install folder — failing the territory check triggers invalidation.

        Falls back to plain existence check when no territory is known
        (native / steam games, or install_dir not resolved).
        """
        data, _ = _run_ludusavi_json(
            ["backup", "--api", "--preview", title], timeout=120
        )
        if not isinstance(data, dict):
            return False
        games = data.get("games", {}) or {}
        all_paths = []
        for entry in games.values():
            if isinstance(entry, dict):
                all_paths.extend((entry.get("files") or {}).keys())
        if not all_paths:
            # Preview returned nothing — likely because the prefix doesn't exist
            # yet (game never launched) so the otherWine root is missing and
            # ludusavi can't resolve in-prefix saves. If install_dir exists we
            # can't rule the title invalid, so treat as unverifiable → True.
            if install_dir and Path(install_dir).is_dir():
                return True
            return False
        # Build the territory list from what we know about this game.
        territories = []
        if install_dir:
            try:
                territories.append(Path(install_dir).resolve())
            except Exception:
                pass
        if prefix_dir:
            try:
                territories.append(Path(prefix_dir).resolve())
            except Exception:
                pass
        if not territories:
            # No territory info — fall back to plain existence check.
            return True
        # At least one save path must be inside one of our territories.
        for raw_path in all_paths:
            try:
                p = Path(raw_path).resolve()
                if any(p.is_relative_to(t) for t in territories):
                    return True
            except Exception:
                continue
        return False

    def _find(self, extra: list) -> tuple[dict, str]:
        return _run_ludusavi_json(["find", "--api"] + extra, timeout=60)

    @staticmethod
    def _extract_titles(data: dict) -> list:
        """
        Extract game title strings from a ludusavi --api JSON response.

        The `find --api` response wraps results under a "games" key, mirroring
        backup/restore output. We also handle the edge case where the payload IS
        itself a title→object map (older ludusavi builds without the wrapper).
        """
        if not isinstance(data, dict):
            return []
        games = data.get("games")
        if isinstance(games, dict):
            return list(games.keys())
        if isinstance(games, list):
            out = []
            for g in games:
                if isinstance(g, dict):
                    t = g.get("name") or g.get("title")
                    if t:
                        out.append(t)
            return out
        # Fallback: top-level dict that looks like title→object (no "games" wrapper).
        _skip = {"overall", "errors", "cloudConflict", "cloudSyncFailed"}
        if data and all(isinstance(v, dict) for k, v in data.items() if k not in _skip):
            return [k for k in data.keys() if k not in _skip]
        return []

    @staticmethod
    def _extract_titles_fuzzy(data: dict) -> list:
        """Return fuzzy-search titles sorted by score descending, capped at 15.

        No score threshold -- the old 0.90 threshold had a broken fallback that
        returned ALL results when nothing passed, making it worse than useless.
        Capping at 15 is the real guard against verifying 70+ candidates.

        Falls back to unsorted full list when no score data present (older
        ludusavi builds that don't emit a 'score' field).
        """
        if not isinstance(data, dict):
            return []
        games = data.get("games")
        if not isinstance(games, dict):
            return []
        scored = [(title, entry.get("score"))
                  for title, entry in games.items()
                  if isinstance(entry, dict)]
        # If ludusavi returned score data, sort by it and cap at 15.
        if any(s is not None for _, s in scored):
            scored_known = [(t, s if s is not None else 0.0) for t, s in scored]
            scored_known.sort(key=lambda x: x[1], reverse=True)
            return [t for t, _ in scored_known[:15]]
        # No score data -- return all (older ludusavi build).
        return [t for t, _ in scored]


class LudusaviBackupWorker(_NAGOThread):
    """
    Back up one game's saves.

    Steps:
      1. Build the root list for this game type and write config.yaml.
      2. Run `backup --api --force <title>`.
      3. Parse the JSON response and emit done(summary) or failed(msg).

    The `title` passed in MUST come from LudusaviFindWorker — never from a
    DB cache. The result-key lookup scans ALL keys in the games dict rather
    than matching self._title literally, so aliases resolved by ludusavi
    (e.g. "Civ V" → "Sid Meier's Civilization V") still produce a valid count.
    """
    progress = pyqtSignal(str)
    done     = pyqtSignal(dict)
    failed   = pyqtSignal(str)

    def __init__(self, game: dict, title: str, backup_root: str = "", parent=None):
        super().__init__(parent)
        self._game  = dict(game)
        self._title       = title
        self._backup_root = backup_root

    @staticmethod
    def _count_preview_files(data: dict) -> int:
        """Return total file count from a backup --preview --api response."""
        games = (data.get("games") or {}) if isinstance(data, dict) else {}
        return sum(
            len((entry.get("files") or {}))
            for entry in games.values()
            if isinstance(entry, dict)
        )

    def run(self):
        try:
            self.progress.emit("Preparing…")
            _nago_name = (self._game.get("name") or "").strip()
            _gt        = (self._game.get("game_type") or "").strip()
            _exe       = (self._game.get("exe_path") or "").strip()

            roots = ludusavi_roots_for_game(self._game)
            _write_ludusavi_config(roots, game=self._game)

            # ── Phase 1: preview with normal roots ────────────────────────────
            self.progress.emit("Checking saves…")
            preview, _ = _run_ludusavi_json(
                ["backup", "--api", "--preview", self._title], timeout=120
            )
            _prev_games = list((preview.get("games") or {}).keys()) if isinstance(preview, dict) else []
            secondary_manifest: Path | None = None

            # ── Secondary manifest (unconditional) ────────────────────────────
            gt  = _gt
            exe = _exe
            if exe and gt in ("gog", "proton"):
                install_dir = _find_install_dir(exe)
                folder_name = Path(install_dir).name if install_dir else ""
                if install_dir and folder_name:
                    secondary_manifest = _write_secondary_manifest(
                        install_dir, self._title, folder_name
                    )


            # ── Phase 3: real backup ───────────────────────────────────────────
            self.progress.emit("Backing up…")
            try:
                data, err = _run_ludusavi_json(
                    ["backup", "--api", "--force"]
                    + (["--path", self._backup_root] if self._backup_root else [])
                    + [self._title], timeout=600
                )
            finally:
                _remove_secondary_manifest(secondary_manifest)

            if not data:
                _NAGOLog.session(f"[ludusavi][backup] FAILED: {err!r}")
                self.failed.emit(err or "Backup produced no output.")
                return
            overall = data.get("overall", {}) or {}
            games   = data.get("games",   {}) or {}

            # Count files across ALL matched game entries (handles alias resolution).
            total_files = sum(
                len((entry.get("files") or {}))
                for entry in games.values()
                if isinstance(entry, dict)
            )
            summary = {
                "processedGames": overall.get("processedGames", 0),
                "totalBytes":     overall.get("totalBytes", 0),
                "fileCount":      total_files,
                "anyFailed":      bool((data.get("errors") or {}).get("someGamesFailed", False)),
                "resolvedTitle":  self._title,
            }
            self.done.emit(summary)
        except Exception as e:
            _NAGOLog.session(f"[ludusavi][backup] EXCEPTION: {e}")
            self.failed.emit(str(e))


class LudusaviRestoreWorker(_NAGOThread):
    """
    Restore one game's saves.

    Steps:
      1. Build the root list for this game type and write config.yaml.
      2. Run `restore --api --force <title>`.
      3. Parse the JSON response and emit done(summary) or failed(msg).

    Same alias-safe result parsing as LudusaviBackupWorker.
    """
    progress = pyqtSignal(str)
    done     = pyqtSignal(dict)
    failed   = pyqtSignal(str)

    def __init__(self, game: dict, title: str, restore_root: str = "", parent=None):
        super().__init__(parent)
        self._game  = dict(game)
        self._title        = title
        self._restore_root = restore_root

    def run(self):
        try:
            self.progress.emit("Preparing…")
            roots = ludusavi_roots_for_game(self._game)
            _write_ludusavi_config(roots, game=self._game)

            # ── Phase 1: preview with normal roots ────────────────────────────
            # Restore doesn't have a --preview mode that's useful for file count,
            # so we use a backup --preview to probe whether saves resolve at all.
            self.progress.emit("Checking saves…")
            preview, _ = _run_ludusavi_json(
                ["backup", "--api", "--preview", self._title], timeout=120
            )
            secondary_manifest: Path | None = None

            if LudusaviBackupWorker._count_preview_files(preview) == 0:
                # ── Phase 2: fallback — inject .ludusavi.yaml into install dir ─
                gt  = (self._game.get("game_type") or "").strip()
                exe = (self._game.get("exe_path") or "").strip()
                if exe and gt in ("gog", "proton"):
                    install_dir  = _find_install_dir(exe)
                    folder_name  = Path(install_dir).name if install_dir else ""
                    if install_dir and folder_name:
                        self.progress.emit("Retrying with folder hint…")
                        secondary_manifest = _write_secondary_manifest(
                            install_dir, self._title, folder_name
                        )
                        if secondary_manifest:
                            retry, _ = _run_ludusavi_json(
                                ["backup", "--api", "--preview", self._title], timeout=120
                            )
                            if LudusaviBackupWorker._count_preview_files(retry) == 0:
                                _remove_secondary_manifest(secondary_manifest)
                                secondary_manifest = None

            # ── Phase 3: real restore ──────────────────────────────────────────
            self.progress.emit("Restoring…")
            try:
                data, err = _run_ludusavi_json(
                    ["restore", "--api", "--force"]
                    + (["--path", self._restore_root] if self._restore_root else [])
                    + [self._title], timeout=600
                )
            finally:
                _remove_secondary_manifest(secondary_manifest)

            if not data:
                self.failed.emit(err or "Restore produced no output.")
                return
            overall = data.get("overall", {}) or {}
            games   = data.get("games",   {}) or {}
            total_files = sum(
                len((entry.get("files") or {}))
                for entry in games.values()
                if isinstance(entry, dict)
            )
            summary = {
                "processedGames": overall.get("processedGames", 0),
                "totalBytes":     overall.get("totalBytes", 0),
                "fileCount":      total_files,
                "anyFailed":      bool((data.get("errors") or {}).get("someGamesFailed", False)),
            }
            self.done.emit(summary)
        except Exception as e:
            self.failed.emit(str(e))


class WinetricksPresetWorker(_NAGOThread):
    """Runs a set of winetricks verbs silently in a background thread."""
    finished_ok = pyqtSignal(str)   # emits the verbs string on success
    failed      = pyqtSignal(str)   # emits error message on failure

    def __init__(self, umu_bin: str, wt_bin: str, verb_list: list, env: dict, parent=None):
        super().__init__(parent)
        self._umu_bin   = umu_bin
        self._wt_bin    = wt_bin
        self._verb_list = verb_list
        self._env       = env

    def run(self):
        try:
            _NAGOLog.winetricks("=" * 64)
            _winetricks_bridge.line_ready.emit("=" * 64)
            _NAGOLog.winetricks(f"WINETRICKS  verbs: {' '.join(self._verb_list)}")
            _winetricks_bridge.line_ready.emit(f"WINETRICKS  verbs: {' '.join(self._verb_list)}")
            _NAGOLog.winetricks("-" * 64)
            _winetricks_bridge.line_ready.emit("-" * 64)
            proc = subprocess.Popen(
                [self._umu_bin, self._wt_bin, "-q"] + self._verb_list,
                env=self._env,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
            )
            for line in proc.stdout:
                stripped = line.rstrip()
                _NAGOLog.winetricks(stripped)
                _winetricks_bridge.line_ready.emit(stripped)
            proc.wait(timeout=300)
            _NAGOLog.winetricks("-" * 64)
            _winetricks_bridge.line_ready.emit("-" * 64)
            _NAGOLog.winetricks(f"EXIT CODE  {proc.returncode}")
            _winetricks_bridge.line_ready.emit(f"EXIT CODE  {proc.returncode}")
            if proc.returncode == 0:
                self.finished_ok.emit(" ".join(self._verb_list))
            else:
                self.failed.emit(
                    f"winetricks exited with code {proc.returncode}.\n"
                    f"Verbs: {' '.join(self._verb_list)}"
                )
        except subprocess.TimeoutExpired:
            _NAGOLog.winetricks("ERROR  timed out after 5 minutes")
            _winetricks_bridge.line_ready.emit("ERROR  timed out after 5 minutes")
            self.failed.emit("winetricks timed out after 5 minutes.")
        except Exception as e:
            _NAGOLog.winetricks(f"ERROR  {e}")
            _winetricks_bridge.line_ready.emit(f"ERROR  {e}")
            self.failed.emit(str(e))


# ── Proton Scanner ─────────────────────────────────────────────────────────────
def find_proton_installations() -> list[dict]:
    """
    Scan common locations for Proton installations.
    Returns a list of dicts: {label, path}  where path is the 'proton' executable.
    Result is cached at module level after the first call — Proton installs don't
    change during a session. Call _invalidate_proton_cache() to force a rescan.
    """
    global _proton_installations_cache
    if _proton_installations_cache is not None:
        return _proton_installations_cache
    found = []
    seen  = set()

    def _add(label: str, proton_exe: Path):
        key = str(proton_exe.resolve())
        if key not in seen and proton_exe.exists():
            seen.add(key)
            found.append({"label": label, "path": key})

    # ── Steam library roots ────────────────────────────────────────────────────
    steam_roots = [
        Path.home() / ".steam" / "steam",
        XDG_DATA / "Steam",
        Path("/usr/share/steam"),
    ]
    # Also parse libraryfolders.vdf for extra Steam library locations
    for root in list(steam_roots):
        vdf = root / "steamapps" / "libraryfolders.vdf"
        if vdf.exists():
            try:
                text = vdf.read_text(errors="ignore")
                for line in text.splitlines():
                    line = line.strip()
                    if '"path"' in line.lower():
                        parts = line.split('"')
                        if len(parts) >= 4:
                            extra = Path(parts[3])
                            if extra not in steam_roots:
                                steam_roots.append(extra)
            except Exception as e:
                _NAGOLog.session(f"[warn] find_proton_installations: failed to parse libraryfolders.vdf at {vdf}: {e}")

    for root in steam_roots:
        steamapps = root / "steamapps" / "common"
        if not steamapps.exists():
            continue
        for entry in sorted(steamapps.iterdir()):
            if not entry.is_dir():
                continue
            name_lower = entry.name.lower()
            if "proton" not in name_lower:
                continue
            proton_exe = entry / "proton"
            _add(entry.name, proton_exe)

    # ── Flatpak Steam ──────────────────────────────────────────────────────────
    flatpak_steam = Path.home() / ".var" / "app" / "com.valvesoftware.Steam" / \
                    "data" / "Steam" / "steamapps" / "common"
    if flatpak_steam.exists():
        for entry in sorted(flatpak_steam.iterdir()):
            if entry.is_dir() and "proton" in entry.name.lower():
                proton_exe = entry / "proton"
                _add(f"{entry.name} (Flatpak)", proton_exe)

    # ── Proton-GE installed via ProtonUp-Qt or manually ────────────────────────
    ge_locations = [
        Path.home() / ".steam" / "root" / "compatibilitytools.d",
        XDG_DATA / "Steam" / "compatibilitytools.d",
        Path.home() / ".var" / "app" / "com.valvesoftware.Steam" /
            "data" / "Steam" / "compatibilitytools.d",
        Path("/usr/share/steam/compatibilitytools.d"),
        Path("/usr/local/share/steam/compatibilitytools.d"),
    ]
    for loc in ge_locations:
        if not loc.exists():
            continue
        is_system = str(loc).startswith("/usr") or str(loc).startswith("/usr/local")
        for entry in sorted(loc.iterdir()):
            if not entry.is_dir():
                continue
            proton_exe = entry / "proton"
            suffix = " (System)" if is_system else " (GE)"
            _add(f"{entry.name}{suffix}", proton_exe)

    # ── System-installed Proton (distro packages) ──────────────────────────────
    system_paths = [
        Path("/usr/bin/proton"),
        Path("/usr/local/bin/proton"),
    ]
    for p in system_paths:
        _add(f"System Proton ({p})", p)

    # ── Non-Steam manual installs ──────────────────────────────────────────────
    manual_roots = [
        XDG_DATA / "proton",
        Path.home() / ".proton",
        Path("/opt/proton"),
        Path("/opt/GE-Proton"),
        Path("/opt/Proton"),
    ]
    for loc in manual_roots:
        if not loc.exists():
            continue
        # loc itself might be a Proton root (contains 'proton' script)
        proton_exe = loc / "proton"
        if proton_exe.exists():
            _add(loc.name, proton_exe)
        else:
            # or a directory containing multiple Proton versions
            try:
                for entry in sorted(loc.iterdir()):
                    if entry.is_dir():
                        _add(entry.name, entry / "proton")
            except Exception:
                pass

    # ── proton on $PATH (any package manager / custom install) ────────────────
    _proton_on_path = shutil.which("proton")
    if _proton_on_path:
        _add(f"System Proton (PATH)", Path(_proton_on_path))

    _proton_installations_cache = found
    return found


def _invalidate_proton_cache():
    """Force find_proton_installations() to rescan on next call."""
    global _proton_installations_cache
    _proton_installations_cache = None


# ── Steam library scanner ─────────────────────────────────────────────────────
def _resolve_game_folder(game: dict) -> str:
    """Return the on-disk game folder path for any game type, or '' if unresolvable.

    Native / Proton / GOG: exe_path.parent.
    Steam: scan Steam libraries for appmanifest_<appid>.acf and read installdir,
           returning <library>/steamapps/common/<installdir>.
    """
    gt  = (game.get("game_type") or "").strip()
    exe = (game.get("exe_path") or "").strip()

    if gt in ("native", "proton", "gog"):
        if exe:
            p = Path(exe).parent
            if p.exists():
                return str(p)
        return ""

    if gt == "steam":
        appid = exe  # exe_path stores the appid for Steam-type games
        if not appid:
            return ""
        installdir_re = re.compile(r'^\s*"installdir"\s+"(.+)"\s*$')
        for lib in find_steam_libraries():
            manifest = lib / "steamapps" / f"appmanifest_{appid}.acf"
            if not manifest.exists():
                continue
            try:
                for line in manifest.read_text(errors="ignore").splitlines():
                    m = installdir_re.match(line)
                    if m:
                        folder = lib / "steamapps" / "common" / m.group(1)
                        if folder.exists():
                            return str(folder)
            except Exception as e:
                _NAGOLog.session(f"[warn] _resolve_game_folder: failed to parse {manifest.name}: {e}")
        return ""

    return ""


def find_steam_libraries() -> list[Path]:
    """
    Return all Steam library root paths on the system.
    Each library contains a steamapps/ folder with appmanifest_*.acf files.
    Result is cached at module level — Steam library locations don't change
    during a session.
    """
    global _steam_libraries_cache
    if _steam_libraries_cache is not None:
        return _steam_libraries_cache

    libraries: list[Path] = []
    seen: set[str] = set()

    def _add(p: Path):
        try:
            resolved = p.resolve()
        except Exception:
            resolved = p
        key = str(resolved)
        if key not in seen and (p / "steamapps").exists():
            seen.add(key)
            libraries.append(p)

    # Standard Steam roots
    candidates = [
        Path.home() / ".steam" / "steam",
        XDG_DATA / "Steam",
        Path.home() / ".var" / "app" / "com.valvesoftware.Steam" / "data" / "Steam",
        Path("/usr/share/steam"),
    ]
    for c in candidates:
        _add(c)

    # Read libraryfolders.vdf for any extra library locations
    for root in list(libraries):
        vdf = root / "steamapps" / "libraryfolders.vdf"
        if not vdf.exists():
            continue
        try:
            text = vdf.read_text(errors="ignore")
            for line in text.splitlines():
                line = line.strip()
                # Format: "path"  "/path/to/library"
                if line.lower().startswith('"path"'):
                    parts = line.split('"')
                    if len(parts) >= 4:
                        extra = Path(parts[3])
                        _add(extra)
        except Exception as e:
            _NAGOLog.session(f"[warn] find_steam_libraries: failed to parse libraryfolders.vdf at {vdf}: {e}")

    _steam_libraries_cache = libraries
    return libraries


def get_running_steam_appids() -> set[str]:
    """Return the set of non-tool, non-zero SteamAppId values found in /proc.

    Steam launches involve multiple wrapper processes (reaper, pressure-vessel,
    SLR, Proton), each with its own SteamAppId in environ. A single-value
    "first match wins" return is unreliable because /proc iteration order
    isn't stable and the first match might be a runtime, not the game.

    Returning a set lets callers do membership tests against the appids they
    actually care about — robust to unknown runtimes and concurrent Steam
    games. The _STEAM_TOOL_APPIDS filter is best-effort: any unknown runtime
    that slips through just adds noise to the set, which the membership check
    naturally ignores."""
    proc_root = Path("/proc")
    found: set[str] = set()
    try:
        pids = [p for p in proc_root.iterdir() if p.name.isdigit()]
    except Exception:
        return found
    for pid_dir in pids:
        try:
            raw = (pid_dir / "environ").read_bytes()
            for var in raw.split(b"\x00"):
                if var.startswith(b"SteamAppId="):
                    appid = var[len(b"SteamAppId="):].decode("utf-8", errors="ignore").strip()
                    if appid and appid != "0" and appid not in _STEAM_TOOL_APPIDS:
                        found.add(appid)
                    break  # one SteamAppId per process — stop scanning this environ
        except (PermissionError, FileNotFoundError, ProcessLookupError):
            continue
        except Exception:
            continue
    return found


def _kill_steam_appid_processes(appid: str) -> int:
    """Force-kill every process whose environ carries SteamAppId=<appid>.

    Same detection signal as get_running_steam_appids() — reaper,
    pressure-vessel, Proton, and the wine/game processes underneath all
    carry the same SteamAppId, so this catches the whole launch tree in
    one pass. Unlike get_running_steam_appids(), this does NOT filter out
    tool/runtime appids — for a kill we want everything in that tree dead,
    not just the "real" game.

    Steam itself isn't told about this; it will notice the process tree
    died the next time it polls, the same way it already has to recover
    from any ordinary crash. Returns the number of processes killed."""
    proc_root = Path("/proc")
    killed = 0
    try:
        pids = [p for p in proc_root.iterdir() if p.name.isdigit()]
    except Exception:
        return killed
    target = f"SteamAppId={appid}".encode()
    for pid_dir in pids:
        try:
            raw = (pid_dir / "environ").read_bytes()
            if target in raw.split(b"\x00"):
                os.kill(int(pid_dir.name), signal.SIGKILL)
                killed += 1
        except (PermissionError, FileNotFoundError, ProcessLookupError):
            continue
        except Exception:
            continue
    return killed


def _kill_wineprefix_processes(pfx: str) -> int:
    """Force-kill every process whose environ carries WINEPREFIX=<pfx>.

    Hard backstop for _kill_wineserver_for_prefix() — wineserver -k asks its
    clients to terminate via its own internal protocol, which real-world
    reports describe as "fairly clean" but not guaranteed (stragglers like
    winedevice.exe are a documented case that survives it and only responds
    to a direct SIGKILL). Same /proc-scan-and-SIGKILL pattern already used
    for Steam — don't trust wineserver's cooperation, verify and finish the
    job directly. Returns the number of processes killed."""
    if not pfx:
        return 0
    proc_root = Path("/proc")
    killed = 0
    try:
        pids = [p for p in proc_root.iterdir() if p.name.isdigit()]
    except Exception:
        return killed
    target = f"WINEPREFIX={pfx}".encode()
    for pid_dir in pids:
        try:
            raw = (pid_dir / "environ").read_bytes()
            if target in raw.split(b"\x00"):
                os.kill(int(pid_dir.name), signal.SIGKILL)
                killed += 1
        except (PermissionError, FileNotFoundError, ProcessLookupError):
            continue
        except Exception:
            continue
    return killed


def _kill_wineserver_for_prefix(pfx: str, log_fn=None):
    """Shut down wineserver for a specific WINEPREFIX, then directly SIGKILL
    anything left over.

    wineserver -k asks its clients to terminate via its own internal
    protocol — that's a polite request, not a guarantee. So this always
    follows up with _kill_wineprefix_processes(), a direct /proc scan and
    SIGKILL of anything still tagged to this prefix, regardless of whether
    wineserver -k succeeded, timed out, or wineserver wasn't even installed.
    That follow-up sweep is the actual guarantee; wineserver -k is just the
    first, gentler attempt that lets well-behaved clients clean up first.

    log_fn: optional callable(str) for the backstop sweep's kill count.
    Takes a callback rather than calling _NAGOLog directly because this
    function is shared between two different log buffers depending on
    caller — the main game's Force Terminate logs to the launch buffer,
    Run-in-Prefix's Stop button logs to the prefix-run buffer — and this
    function has no way to know which context it's running in."""
    if pfx:
        wineserver_bin = shutil.which("wineserver")
        if wineserver_bin:
            try:
                subprocess.run(
                    [wineserver_bin, "-k"],
                    env={**os.environ, "WINEPREFIX": pfx},
                    timeout=5,
                )
            except Exception:
                pass
    _killed = _kill_wineprefix_processes(pfx)
    if log_fn:
        log_fn(f"wineserver backstop sweep  killed={_killed} straggler process(es)")


def _kill_wineserver_for_prefix_async(pfx: str, log_fn=None):
    """Fire-and-forget version of _kill_wineserver_for_prefix() for UI-thread
    call sites. The synchronous version's subprocess.run() has a 5-second
    timeout — fine from a background worker, but called directly from a Qt
    slot (no QThread involved) it would freeze the whole UI for up to 5
    seconds if wineserver is slow to respond. Runs on a daemon thread instead
    so Force Terminate / Run-in-Prefix Stop never block the window."""
    threading.Thread(target=_kill_wineserver_for_prefix, args=(pfx, log_fn), daemon=True).start()


def _prefix_run_log_header(game_name: str, exe_path: str, pfx: str,
                            proton_arg: str, umu_bin: str, raw_env: str = "",
                            share_paths: str = "") -> None:
    """Write a start banner to the shared Run-in-Prefix log. That log is one
    buffer (_NAGOLog._prefix_lines) fed by _prefix_run_bridge — both the
    dialog's embedded 'Run in Prefix' tab and the global Logs page tab
    watch the same stream, so a run triggered from either GameDialog's
    button or the game card's right-click menu shows up in both places
    live. Multiple runs across different games can interleave in that
    stream, so every run is bracketed with a named banner to keep it
    readable."""
    ts = _fmt_stamp(datetime.datetime.now())
    lines = [
        "=" * 64,
        f"RUN IN PREFIX — {game_name}",
        f"  started : {ts}",
        f"  exe     : {exe_path}",
        f"  prefix  : {pfx}",
        f"  proton  : {proton_arg}",
        f"  umu     : {umu_bin}",
    ]
    if raw_env:
        lines.append(f"  env vars: {raw_env}")
    if share_paths:
        lines.append(f"  share   : {share_paths}  (outside $HOME, exposed to sandbox)")
    lines.append("=" * 64)
    for line in lines:
        _NAGOLog.prefix_run(line)
        _prefix_run_bridge.line_ready.emit(line)


def _prefix_run_log_footer(game_name: str, status: str) -> None:
    """Write the matching end banner for _prefix_run_log_header(). status is
    a short human string: 'finished ok', 'failed: <err>', or
    'force-terminated'."""
    ts = _fmt_stamp(datetime.datetime.now())
    lines = [
        "-" * 64,
        f"END OF RUN — {game_name}  ({status})",
        f"  finished: {ts}",
        "-" * 64,
        "",
    ]
    for line in lines:
        _NAGOLog.prefix_run(line)
        _prefix_run_bridge.line_ready.emit(line)


def _primary_scale_factor() -> float:
    """Return the desktop's real scale factor for the primary output (e.g.
    1.25), reading each DE's native source. Covers KDE and GNOME with a Qt
    fallback for everything else.

    Qt's QScreen.devicePixelRatio() rounds fractional scales to the nearest
    integer (1.25 → 2.0), so it can't be trusted for fractional scaling. The
    per-DE tools below report the true fractional value instead. Each layer
    degrades to the next if its tool is missing or its parse fails, so any
    system still gets *something* rather than crashing.

    Returns 1.0 if nothing can be determined."""
    desktop  = os.environ.get("XDG_CURRENT_DESKTOP", "").lower()
    is_kde   = "kde" in desktop or "plasma" in desktop
    is_gnome = "gnome" in desktop or "unity" in desktop

    # ── KDE / Plasma → kscreen-doctor (verified) ──────────────────────────────
    if (is_kde or (not is_gnome)) and shutil.which("kscreen-doctor"):
        try:
            _r = subprocess.run(
                ["kscreen-doctor", "-o"],
                capture_output=True, text=True, timeout=3,
                env={**os.environ, "NO_COLOR": "1"},
            )
            _raw = re.sub(r"\x1b\[[0-9;]*m", "", _r.stdout)
            # (priority, scale) per enabled+connected output
            _cands: list[tuple[int, float]] = []
            for _blk in re.split(r"(?=\bOutput:\s*\d+\b)", _raw):
                _blk = _blk.strip()
                if not _blk:
                    continue
                if "enabled" not in _blk.lower() or "connected" not in _blk.lower():
                    continue
                _pm = re.search(r"priority\s+(\d+)", _blk, re.IGNORECASE)
                _prio = int(_pm.group(1)) if _pm else 99
                _sm = re.search(r"Scale:\s*([\d.]+)", _blk, re.IGNORECASE)
                if _sm:
                    _cands.append((_prio, float(_sm.group(1))))
            if _cands:
                _cands.sort()  # lowest priority = primary
                _scale = _cands[0][1]
                if _scale > 0:
                    return _scale
        except Exception:
            pass

    # ── GNOME → gsettings text-scaling-factor (UNVERIFIED on real hardware) ────
    # text-scaling-factor is the universal GNOME knob, present on every GNOME
    # install, and reports the true fractional value (1.25, 1.5...). It drives
    # UI element size. The 125%-slider display scale lives in a harder-to-read
    # experimental dconf key; this is the clean readable one. Written from the
    # documented gsettings schema, not tested on a live GNOME box.
    if is_gnome and shutil.which("gsettings"):
        try:
            _r = subprocess.run(
                ["gsettings", "get", "org.gnome.desktop.interface",
                 "text-scaling-factor"],
                capture_output=True, text=True, timeout=3,
            )
            _m = re.search(r"([\d.]+)", _r.stdout)
            if _m:
                _scale = float(_m.group(1))
                if _scale > 0:
                    return _scale
        except Exception:
            pass

    # ── Fallback: Qt's fractional dpr (last resort) ───────────────────────────
    screen = QApplication.primaryScreen()
    if screen:
        try:
            _dpr = screen.devicePixelRatioF()
            if _dpr > 0:
                return _dpr
        except Exception:
            pass
    return 1.0


def _installer_dpi() -> int:
    """Return the Wine LogPixels value for the installer's screen DPI.

    Wine's baseline DPI is 96. Scale it by the desktop's real scale factor
    (_primary_scale_factor — kscreen-doctor on KDE, gsettings on GNOME, Qt
    fallback elsewhere) so the installer matches what the user actually set
    their desktop to. e.g. 125% → 96 × 1.25 = 120.

    Multi-monitor caveat: Wine stores one DPI per prefix, but monitors can
    have different scales. This uses the primary monitor's scale and accepts
    a secondary monitor may not match — unavoidable with a single registry
    value. Always returns a usable int; never raises."""
    return int(round(96 * _primary_scale_factor()))


def _set_prefix_dpi(umu_bin: str, env: dict, dpi: int) -> bool:
    """Write LogPixels=<dpi> into the prefix via umu/Proton's Wine. Wine reads
    DPI from TWO registry locations and both must be set for the change to take
    effect: HKCU\\Control Panel\\Desktop (the primary, drives UI scaling) and
    HKCU\\Software\\Wine\\Fonts (font rendering). Returns True if both writes
    succeed. Quick synchronous calls — reg writes are near-instant."""
    keys = (
        r"HKEY_CURRENT_USER\Control Panel\Desktop",
        r"HKEY_CURRENT_USER\Software\Wine\Fonts",
    )
    ok = True
    for key in keys:
        try:
            result = subprocess.run(
                [umu_bin, "reg", "add", key,
                 "/v", "LogPixels", "/t", "REG_DWORD",
                 "/d", str(dpi), "/f"],
                env=env,
                capture_output=True,
                timeout=30,
            )
            ok = ok and (result.returncode == 0)
        except Exception:
            ok = False
    return ok


def _restore_prefix_dpi(umu_bin: str, env: dict) -> None:
    """Delete LogPixels from both registry locations set by _set_prefix_dpi,
    restoring Wine's default 96 DPI. Best-effort — errors swallowed."""
    keys = (
        r"HKEY_CURRENT_USER\Control Panel\Desktop",
        r"HKEY_CURRENT_USER\Software\Wine\Fonts",
    )
    for key in keys:
        try:
            subprocess.run(
                [umu_bin, "reg", "delete", key,
                 "/v", "LogPixels", "/f"],
                env=env,
                capture_output=True,
                timeout=30,
            )
        except Exception:
            pass


class _RunInPrefixWorker(_NAGOThread):
    """Runs an arbitrary .exe/.msi/.bat/.cmd inside a Wine prefix via umu.
    Shared engine for GameDialog's Run in Prefix button and the game card's
    right-click 'Run File in Prefix' menu item — one class, two entry
    points, so the two never drift apart in behavior."""
    finished_ok = pyqtSignal()
    failed      = pyqtSignal(str)
    cancelled   = pyqtSignal()

    def __init__(self, umu_bin, exe_path, env, cwd):
        super().__init__()
        self._umu_bin   = umu_bin
        self._exe_path  = exe_path
        self._env       = env
        self._cwd       = cwd
        self._proc      = None
        self._cancelled = False

    def terminate_now(self):
        """Force-kill the running process group + this prefix's
        wineserver. Called from the UI thread (a button click or menu
        action), so only touches OS-level process state directly — no Qt
        objects — and fires the wineserver kill on a background thread
        rather than blocking on it, since that call has a 5-second timeout
        that would otherwise freeze the window. Same two-part kill as the
        main game's Force Terminate: wineserver deliberately detaches from
        the process group, so killpg() alone can't be trusted to take it
        down."""
        self._cancelled = True
        if self._proc is not None:
            try:
                os.killpg(os.getpgid(self._proc.pid), signal.SIGKILL)
            except Exception:
                try:
                    self._proc.kill()
                except Exception:
                    pass
        # log_fn routes to the prefix-run buffer specifically, not launch —
        # this worker has no concept of the main launch log, and the
        # buffer/bridge pair here matches what _prefix_run_log_header()
        # already does for every other line in this stream. No game-name
        # baking needed (unlike Force Terminate's case): this buffer only
        # clears on an explicit manual Clear click, never automatically on
        # a new run, so the line lands nested under the banner already
        # printed for this run when it started.
        def _log_fn(msg):
            _NAGOLog.prefix_run(msg)
            _prefix_run_bridge.line_ready.emit(msg)
        _kill_wineserver_for_prefix_async(self._env.get("WINEPREFIX", ""), log_fn=_log_fn)

    def run(self):
        try:
            suffix = Path(self._exe_path).suffix.lower()
            if suffix == ".msi":
                # MSI installers must go through msiexec, not direct exec
                cmd = [self._umu_bin, "msiexec", "/i", self._exe_path]
                _interactive = False
            elif suffix in (".bat", ".cmd"):
                # Batch files: hand the raw path to umu and let Proton's
                # launcher invoke it (via Windows `start`), which spawns a
                # real interactive cmd console. Do NOT use `cmd.exe /c` —
                # /c runs non-interactively and exits, which starves
                # interactive scripts (choice/pause/set /p) of input and
                # makes menu installers fall straight through to their exit
                # branch. This restores the pre-cmd.exe behaviour that
                # worked.
                cmd = [self._umu_bin, self._exe_path]
                _interactive = True
            else:
                cmd = [self._umu_bin, self._exe_path]
                _interactive = False

            if _interactive:
                # Interactive batch installers (choice/pause/set /p) need a
                # real console. Piping stdout/stderr suppresses Wine's cmd
                # window and starves choice of keyboard input, which makes
                # such scripts fall straight through to their exit branch.
                # So for .bat/.cmd we DON'T pipe — Wine renders its own
                # interactive cmd console. Trade-off: output isn't streamed
                # into the in-app Run-in-Prefix log for this case.
                _NAGOLog.prefix_run("[interactive batch — running in Wine's cmd console]")
                _prefix_run_bridge.line_ready.emit(
                    "[interactive batch — running in Wine's cmd console]")
                proc = subprocess.Popen(
                    cmd,
                    env=self._env,
                    cwd=self._cwd,
                    start_new_session=True,
                )
                self._proc = proc
                proc.wait()
                self.cancelled.emit() if self._cancelled else self.finished_ok.emit()
                return

            proc = subprocess.Popen(
                cmd,
                env=self._env,
                cwd=self._cwd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                errors="replace",
                start_new_session=True,
            )
            self._proc = proc
            for line in proc.stdout:
                stripped = line.rstrip()
                _NAGOLog.prefix_run(stripped)
                _prefix_run_bridge.line_ready.emit(stripped)
            proc.wait()
            self.cancelled.emit() if self._cancelled else self.finished_ok.emit()
        except Exception as e:
            if self._cancelled:
                self.cancelled.emit()
            else:
                self.failed.emit(str(e))


def _fire_steam_exit_post_cmd_async(post_exit_cmd: str, identifier: str = ""):
    """Fire the user's post-exit command plus an unconditional HDR-disable
    for a Steam game that just exited (normal exit OR Force Terminate —
    both route through the same poll-loop cleanup that calls this).

    NAGO never enables HDR for Steam games and never exposes an HDR toggle
    for them in the UI (see the pre-cmd exclusion at launch), so there's no
    per-game "did NAGO turn HDR on" state to check. Steam may flip HDR on
    its own when the game goes fullscreen, with zero visibility to NAGO —
    so on exit, just disable HDR on every HDR-capable connector
    unconditionally, the same harmless-when-already-off pattern already
    proven in production for native/Proton games.

    Computed here, fresh, on a background thread, rather than baked into a
    static string at launch time, for two reasons: (1) _hdr_commands()
    does a real subprocess call (kscreen-doctor/gdctl) with up to a 3s
    timeout — running it inline on the poll-loop/UI thread risks the same
    kind of freeze the wineserver kill had before that was moved to a
    thread too. (2) Computing it at launch instead would start the
    background check the moment Launch is clicked — if the Steam game
    exited unusually fast, cleanup could fire before that check finished.
    Starting the check only once the game has already exited removes that
    race entirely, and costs nothing on the launch path itself.

    identifier: the Steam appid, baked into every log line. This fires
    async on every single Steam exit with zero per-game state to check
    against — without an identifier in the line, the log can't say which
    game it was for, only that it happened to whatever Steam game last
    exited. Logs unconditionally now, including the case where there's
    nothing to fire (no user cmd, no HDR-capable connector) — that used
    to be a silent early-return with no log line at all, which looked
    identical to this never having run."""
    _tag = f"[steam-exit appid={identifier}]" if identifier else "[steam-exit]"
    def _work():
        _, hdr_post = _hdr_commands()
        cmd = post_exit_cmd
        if hdr_post:
            cmd = f"{cmd} ; {hdr_post}" if cmd else hdr_post
        if not cmd:
            _NAGOLog.launch(f"{_tag} nothing to fire (no post-exit cmd, no HDR-capable connector)")
            return
        try:
            subprocess.Popen(cmd, shell=True,
                              stdout=subprocess.DEVNULL,
                              stderr=subprocess.DEVNULL)
            _hdr_note = "  (includes HDR-disable)" if hdr_post else ""
            _NAGOLog.launch(f"{_tag} post-exit cmd started: {cmd}{_hdr_note}")
        except Exception as e:
            _NAGOLog.launch(f"{_tag} [error] post-exit command failed: {e}  cmd={cmd}")
    threading.Thread(target=_work, daemon=True).start()


# Known Steam tool/runtime appids — built once at module level, never per-call.
_STEAM_TOOL_APPIDS: frozenset[str] = frozenset({
    "228980",   # Steamworks Common Redistributables
    "1391110",  # Steam Linux Runtime 2.0 (soldier)
    "1628350",  # Steam Linux Runtime 3.0 (sniper)
    "1070560",  # Steam Linux Runtime 1.0 (scout)
    "1493710",  # Proton Experimental
    "961940",   # Proton 4.2
    "858280",   # Proton 3.7-8
    "930400",   # Proton 3.16-9
    "996510",   # Proton 4.11
    "1054830",  # Proton 5.0
    "1113280",  # Proton 5.13
    "1245040",  # Proton 6.3
    "1420170",  # Proton 7.0
    "1887720",  # Proton 8.0
    "2348590",  # Proton 9.0
    "2805730",  # Proton 10.0
    "1391050",  # Steamworks SDK Redist
    "250820",   # SteamVR
    "323910",   # Steam Audio
    "375360",   # Steam Music Player
})


def _is_steam_tool_or_runtime(name: str, appid: str) -> bool:
    """Return True if a Steam appmanifest looks like a tool/runtime/redistributable rather than a game."""
    if appid in _STEAM_TOOL_APPIDS:
        return True
    # Name-based filters for anything we don't have an appid for
    name_lower = name.lower().strip()
    name_patterns = [
        "steamworks",
        "steam linux runtime",   # catches all version suffixes (1.0/2.0/3.0/4.0/scout/soldier/sniper…)
        "steam runtime",
        "steamvr",
        "steam audio",
        "proton ",       # "Proton 8.0", "Proton Experimental", "Proton Hotfix" etc.
        "proton-",       # "Proton-GE", "Proton-tkg"
        "proton easyanticheat",
        "proton battleye",
    ]
    for p in name_patterns:
        if name_lower.startswith(p):
            return True
    if name_lower == "proton":
        return True
    # Dedicated servers — almost never what the user wants to launch from a launcher
    if "dedicated server" in name_lower:
        return True
    return False


def find_steam_games() -> list[dict]:
    """
    Scan all detected Steam libraries for installed games.
    Returns list of {appid, name, library} dicts, sorted by name.
    """
    games: list[dict] = []
    seen_appids: set[str] = set()

    name_re   = re.compile(r'^\s*"name"\s+"(.+)"\s*$')
    appid_re  = re.compile(r'^\s*"appid"\s+"(\d+)"\s*$')

    for lib in find_steam_libraries():
        steamapps = lib / "steamapps"
        if not steamapps.exists():
            continue
        for manifest in sorted(steamapps.glob("appmanifest_*.acf")):
            try:
                text = manifest.read_text(errors="ignore")
                appid = None
                name  = None
                for line in text.splitlines():
                    if appid is None:
                        m = appid_re.match(line)
                        if m:
                            appid = m.group(1)
                            continue
                    if name is None:
                        m = name_re.match(line)
                        if m:
                            name = m.group(1)
                    if appid and name:
                        break
                if not appid or not name:
                    continue
                if appid in seen_appids:
                    continue
                if _is_steam_tool_or_runtime(name, appid):
                    continue
                seen_appids.add(appid)
                games.append({
                    "appid":   appid,
                    "name":    name,
                    "library": str(lib),
                })
            except Exception as e:
                _NAGOLog.session(f"[warn] find_steam_games: failed to parse {manifest.name}: {e}")
                continue

    games.sort(key=lambda g: g["name"].lower())
    return games


# ── Exe classifier: installer vs game heuristics ─────────────────────────────

def _classify_exe(path: str) -> str:
    """
    Classify a Windows executable as 'installer', 'game', or 'unknown'.

    Used by the Add Game dialog when the user browses a file in Proton Install
    mode — if we're confident it's a game, we silently flip to Browse mode.
    If it's a confirmed installer, we stay in Install mode.  Unknown = no-op.

    Priority order (intentional — the exe itself beats folder context):

    Pass 1 — Binary string scan on the selected exe (first 512 KB):
      Installer signals: b'Inno Setup', b'Nullsoft Install', b'InstallShield',
                         b'WixBurn', b'WiX Toolset', b'Setup Factory',
                         b'NSIS Error', b'InstallAware'
      → returns 'installer' immediately on first match.
      Game engine signals: b'UnityPlayer', b'Unreal Engine', b'GameAssembly',
                           b'steam_api', b'FMOD Studio', b'Wwise', b'RenPy',
                           b'RPG Maker', b'Kirikiri'
      → returns 'game' immediately on first match.

      Installer strings run first — if an installer bundles game assets and
      both signals are present, the installer wins. This handles the case
      where a setup.exe sits in the same folder as already-installed game
      files from a previous install.

    Pass 2 — Sibling file scan (no file read, just os.listdir):
      Only reached if Pass 1 found no installer strings.
      Game signals: store DLLs, known engine DLLs, store breadcrumb files,
                    game archive extensions.
      → returns 'game' on first match.

    Returns 'unknown' if neither pass fires.
    """
    try:
        p = Path(path)
        if not p.is_file():
            return "unknown"

        # ── Pass 1: binary string scan on the exe itself (first 512 KB) ──
        _INSTALLER_SIGS = [
            b"Inno Setup",
            b"Nullsoft Install",
            b"InstallShield",
            b"WixBurn",
            b"WiX Toolset",
            b"Setup Factory",
            b"NSIS Error",
            b"InstallAware",
        ]
        _GAME_SIGS = [
            b"UnityPlayer",
            b"Unreal Engine",
            b"GameAssembly",
            b"steam_api",
            b"FMOD Studio",
            b"Wwise",
            b"RenPy",
            b"RPG Maker",
            b"Kirikiri",
        ]
        try:
            with open(path, "rb") as fh:
                blob = fh.read(524288)  # 512 KB
            for sig in _INSTALLER_SIGS:
                if sig in blob:
                    return "installer"
            for sig in _GAME_SIGS:
                if sig in blob:
                    return "game"
        except OSError:
            pass

        # ── Pass 2: sibling files in the same directory ───────────────────
        _GAME_DLLS = {
            "steam_api.dll", "steam_api64.dll",
            "unityplayer.dll", "gameassembly.dll",
            "d3d11.dll", "d3d12.dll", "opengl32.dll", "vulkan-1.dll",
            "xinput1_3.dll", "xinput1_4.dll", "xinput9_1_0.dll",
            "dsound.dll", "dinput8.dll",
            "galaxy64.dll", "galaxy.dll",                # GOG Galaxy DRM
            "uplay_r1.dll", "uplay_r164.dll",            # Ubisoft Connect
            "uplay_r1_loader.dll", "uplay_r1_loader64.dll",
        }
        _GAME_EXTS = {".pak", ".uasset", ".xp3", ".npa", ".ypf"}
        try:
            siblings = {f.lower() for f in os.listdir(p.parent)}
            if siblings & _GAME_DLLS:
                return "game"
            # GOG breadcrumb files: goggame-<id>.info or goggame-<id>.id
            if any(s.startswith("goggame-") for s in siblings):
                return "game"
            # Epic Games Store: .egstore folder present
            if ".egstore" in siblings:
                return "game"
            # Game archive extensions
            for sib in siblings:
                if any(sib.endswith(ext) for ext in _GAME_EXTS):
                    return "game"
            # xinput variants not already in the set
            if any(s.startswith("xinput") and s.endswith(".dll") for s in siblings):
                return "game"
        except OSError:
            pass

        return "unknown"

    except Exception:
        return "unknown"


# ── GOG library scanners (Heroic + Lutris) ────────────────────────────────────

def scan_install_dir_for_store(exe_path: str) -> dict:
    """
    Given a path to a game executable, walk up the directory tree looking for
    store breadcrumb files.  Checks the exe's directory plus up to 3 levels
    above it (4 directories total), then stops.  Returns a dict:
        { "store": "gog"|"egs"|"", "name": "<title or ''>" }

    GOG:  leaves goggame-<id>.info  — JSON with "gameId" and "gameName"
    Epic: leaves .egstore/<hash>.mancpn — JSON with "DisplayName"
    Everything else: returns empty store + empty name.
    """
    if not exe_path:
        return {"store": "", "name": "", "store_id": ""}

    current = Path(exe_path).parent
    for _ in range(4):  # exe dir + 3 levels up
        if not current.is_dir():
            break

        # ── GOG: goggame-<id>.info ────────────────────────────────────────
        for info_file in current.glob("goggame-*.info"):
            try:
                data = json.loads(info_file.read_text(errors="ignore"))
                game_id   = str(data.get("gameId") or "").strip()
                game_name = (data.get("gameName") or "").strip()
                if not game_name and game_id:
                    game_name = _resolve_gog_title(game_id)
                if game_name or game_id:
                    return {"store": "gog", "name": game_name, "store_id": game_id}
            except Exception as e:
                _NAGOLog.session(f"[warn] scan_install_dir_for_store: failed to parse {info_file.name}: {e}")
                continue
        egstore = current / ".egstore"
        if egstore.is_dir():
            for mancpn in egstore.glob("*.mancpn"):
                try:
                    data = json.loads(mancpn.read_text(errors="ignore"))
                    name = (data.get("DisplayName") or "").strip()
                    return {"store": "egs", "name": name, "store_id": ""}
                except Exception as e:
                    _NAGOLog.session(f"[warn] scan_install_dir_for_store: failed to parse {mancpn.name}: {e}")
                    continue
        if current.parent == current:
            break  # filesystem root
        current = current.parent

    return {"store": "", "name": "", "store_id": ""}


def steam_appid_from_exe_path(exe_path: str) -> str:
    """Given a path to an exe inside a Steam library, return the owning Steam
    appid, or '' if the path is not under a recognized steamapps/common install.

    Mechanics: Steam leaves no breadcrumb in the game's own folder. Instead we
    locate the 'steamapps/common/<installdir>' segment in the path, take the
    <installdir> folder name, then scan that library's appmanifest_*.acf files
    for the one whose 'installdir' value matches. The matching manifest's
    filename (appmanifest_<appid>.acf) yields the appid.

    Returns '' when the path isn't under steamapps/common, or when no manifest
    in that library claims the install folder — e.g. a pirated/manually-dropped
    game that isn't in the user's real Steam library. Callers treat '' as
    'not a legit Steam game' and fall back to Proton.
    """
    if not exe_path:
        return ""
    try:
        parts = Path(exe_path).parts
    except Exception:
        return ""
    # Find the 'steamapps' / 'common' adjacent pair, case-insensitively.
    lower = [p.lower() for p in parts]
    common_idx = -1
    for i in range(len(lower) - 1):
        if lower[i] == "steamapps" and lower[i + 1] == "common":
            common_idx = i + 1
            break
    if common_idx < 0 or common_idx + 1 >= len(parts):
        return ""  # not under steamapps/common, or nothing after 'common'

    install_folder = parts[common_idx + 1]          # the dir right under common/
    # Library root = everything up to and including 'steamapps'.
    steamapps_dir = Path(*parts[: common_idx])      # .../steamapps
    if not steamapps_dir.is_dir():
        return ""

    installdir_re = re.compile(r'^\s*"installdir"\s+"(.+)"\s*$')
    appid_re      = re.compile(r"appmanifest_(\d+)\.acf$")
    for manifest in sorted(steamapps_dir.glob("appmanifest_*.acf")):
        try:
            for line in manifest.read_text(errors="ignore").splitlines():
                m = installdir_re.match(line)
                if m and m.group(1).strip().lower() == install_folder.lower():
                    am = appid_re.search(manifest.name)
                    if am:
                        return am.group(1)
                    break
        except Exception as e:
            _NAGOLog.session(
                f"[warn] steam_appid_from_exe_path: failed to parse {manifest.name}: {e}"
            )
            continue
    return ""


def resolve_gog_id(game: dict) -> str:
    """Return the effective GOG ID for a game, preferring a LIVE scan of the current
    exe path over the stored value.

    The backup/restore buttons live inside the Edit window, so we can't rely on a
    save-close-reopen cycle to refresh a stored ID — and a stored ID can go stale if
    the install moved. So we re-read goggame-<id>.info from the live exe path at the
    moment it's needed; only if that scan finds nothing do we fall back to the value
    persisted in the DB (which is itself just a cached scan from the last save).

    Returns '' for non-GOG games or when no ID can be determined (callers then fall
    back to name matching, which is the safe degradation).
    """
    if (game.get("game_type") or "").strip() != "gog":
        return ""
    exe = (game.get("exe_path") or "").strip()
    if exe:
        try:
            live = scan_install_dir_for_store(exe).get("store_id", "")
            if live:
                return live
        except Exception:
            pass
    return (game.get("gog_id") or "").strip()


def _heroic_library_paths() -> list[Path]:
    """Return candidate Heroic config directories (native + Flatpak)."""
    return [
        Path.home() / ".config" / "heroic",
        Path.home() / ".var" / "app" / "com.heroicgameslauncher.hgl" / "config" / "heroic",
    ]


def _heroic_wine_prefix(app_name: str, is_flatpak: bool) -> str:
    """Return the default Wine prefix path Heroic uses for a GOG game."""
    if is_flatpak:
        base = Path.home() / ".var" / "app" / "com.heroicgameslauncher.hgl" / "data" / "heroic"
    else:
        base = XDG_DATA / "heroic"
    return str(base / "prefixes" / "default" / app_name)


def _is_steam_installed() -> bool:
    """Cheap presence check for the Add-flow Import-source picker — reuses
    find_steam_libraries()'s cached result rather than a fresh scan."""
    return bool(find_steam_libraries())


def _is_heroic_installed() -> bool:
    """Cheap presence check for the Add-flow Import-source picker."""
    return any(p.exists() for p in _heroic_library_paths())


def _is_lutris_installed() -> bool:
    """Cheap presence check for the Add-flow Import-source picker."""
    return any(p.exists() for p in _lutris_library_paths())


# Cache file for GOG product ID → title lookups so we only hit the API once per ID.
_GOG_TITLE_CACHE_PATH = NAGO_HOME / "gog_title_cache.json"
_gog_title_cache: dict[str, str] | None = None  # None = not loaded yet
_proton_installations_cache: list[dict] | None = None  # None = not scanned yet
_steam_libraries_cache: list | None = None              # None = not scanned yet
_umu_version_cache: str | None = None                   # None = not yet resolved
_winetricks_version_cache: str | None = None            # None = not yet resolved
_ludusavi_version_cache: str | None = None              # None = not yet resolved
_config_cache: dict | None = None                       # None = not yet loaded


def _load_gog_title_cache() -> dict[str, str]:
    global _gog_title_cache
    if _gog_title_cache is not None:
        return _gog_title_cache
    try:
        _gog_title_cache = json.loads(_GOG_TITLE_CACHE_PATH.read_text())
    except Exception:
        _gog_title_cache = {}
    return _gog_title_cache


def _save_gog_title_cache():
    try:
        _GOG_TITLE_CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
        _GOG_TITLE_CACHE_PATH.write_text(json.dumps(_gog_title_cache or {}))
    except Exception as e:
        _NAGOLog.session(f"[warn] _save_gog_title_cache: {e}")


def _resolve_gog_title(app_name: str) -> str:
    """
    Resolve a GOG numeric product ID to a human title.
    Order: in-memory cache → disk cache → GOG public API (no auth required).
    Result is cached to disk so subsequent launches are instant.
    Returns empty string on failure so callers can skip the entry.
    """
    cache = _load_gog_title_cache()
    if app_name in cache:
        return cache[app_name]

    # Only attempt network lookup for purely numeric IDs — non-numeric app_names
    # are real slugs and should have been found via library.json already.
    if not app_name.isdigit():
        return ""

    try:
        url = f"https://api.gog.com/products/{app_name}?expand=description"
        r = _requests().get(url, timeout=6)
        if r.status_code == 200:
            data = r.json()
            title = (data.get("title") or "").strip()
            if title:
                cache[app_name] = title
                _save_gog_title_cache()
                return title
    except Exception as e:
        _NAGOLog.session(f"[warn] _resolve_gog_title({app_name}): {e}")
    return ""


def find_gog_games_heroic() -> list[dict]:
    """
    Scan Heroic Games Launcher for installed GOG games.
    Returns list of dicts with keys: name, exe_path, wine_prefix, source.

    Heroic stores its library in:
      <heroic_config>/gog_store/library.json   — full account library
      <heroic_config>/gog_store/installed.json — installed subset (has exe paths)

    We join on appName: only return games that are in installed.json,
    using library.json for the display title.
    """
    results: list[dict] = []
    seen: set[str] = set()

    for heroic_cfg in _heroic_library_paths():
        if not heroic_cfg.exists():
            continue
        is_flatpak = "flatpak" in str(heroic_cfg).lower() or ".var" in str(heroic_cfg)

        installed_path = heroic_cfg / "gog_store" / "installed.json"
        library_path   = heroic_cfg / "gog_store" / "library.json"

        if not installed_path.exists():
            continue

        # Build title map from library.json if available.
        # Heroic has changed this format across versions:
        #   v3.x:  { "games": [ { "app_name": "...", "title": "..." }, ... ] }
        #   v2.x:  [ { "app_name": "...", "title": "..." }, ... ]  (plain list)
        #   some:  { "<app_name>": { "title": "..." }, ... }  (object keyed by id)
        title_map: dict[str, str] = {}
        if library_path.exists():
            try:
                lib_data = json.loads(library_path.read_text(errors="ignore"))
                if isinstance(lib_data, list):
                    games_list = lib_data
                elif isinstance(lib_data, dict):
                    # Try "games" array first
                    if "games" in lib_data and isinstance(lib_data["games"], list):
                        games_list = lib_data["games"]
                    else:
                        # Flat object keyed by app_name — values are game dicts
                        games_list = list(lib_data.values())
                else:
                    games_list = []
                for entry in games_list:
                    if not isinstance(entry, dict):
                        continue
                    app_name = (entry.get("app_name") or entry.get("appName") or "").strip()
                    title    = (entry.get("title") or entry.get("name") or "").strip()
                    if app_name and title:
                        title_map[app_name] = title
            except Exception as e:
                _NAGOLog.session(f"[warn] find_gog_games_heroic: failed to parse library.json at {library_path}: {e}")

        try:
            inst_data = json.loads(installed_path.read_text(errors="ignore"))
            # installed.json is either {"installed": [...]} or a plain list
            entries = inst_data.get("installed", inst_data if isinstance(inst_data, list) else [])
            for entry in entries:
                if not isinstance(entry, dict):
                    continue
                # Heroic uses "appName" or "app_name"
                app_name = entry.get("appName") or entry.get("app_name") or ""
                if not app_name or app_name in seen:
                    continue

                # Only GOG games (runner field may be "gog" or missing for GOG store)
                runner = (entry.get("runner") or "").lower()
                if runner and runner != "gog":
                    continue

                install_path = entry.get("install_path") or entry.get("installPath") or ""
                exe_rel      = entry.get("executable") or entry.get("exe") or ""
                if not install_path:
                    continue

                exe_abs = ""
                if exe_rel:
                    exe_abs = str(Path(install_path) / exe_rel.lstrip("/"))
                else:
                    # Try to find the main .exe in the install dir
                    install_dir = Path(install_path)
                    exes = list(install_dir.glob("*.exe"))
                    if exes:
                        exe_abs = str(exes[0])

                # Title resolution priority:
                # 1. library.json title_map (most reliable, full GOG title)
                # 2. "title" field directly in installed.json entry (Heroic 2.x+)
                # 3. "name" field in installed.json entry
                # 4. GOG public API lookup by numeric product ID (cached to disk)
                # 5. Skip — no usable title found anywhere
                title = (
                    title_map.get(app_name)
                    or (entry.get("title") or "").strip()
                    or (entry.get("name") or "").strip()
                    or _resolve_gog_title(app_name)
                )
                if not title:
                    continue  # nothing worked — skip silently

                seen.add(app_name)
                results.append({
                    "name":         title,
                    "exe_path":     exe_abs or install_path,
                    "install_path": install_path,
                    "wine_prefix":  _heroic_wine_prefix(app_name, is_flatpak),
                    "source":       "Heroic (Flatpak)" if is_flatpak else "Heroic",
                    "app_name":     app_name,
                })
        except Exception as e:
            _NAGOLog.session(f"[warn] find_gog_games_heroic: failed to parse installed.json at {installed_path}: {e}")
            continue

    results.sort(key=lambda g: g["name"].lower())
    return results


def _lutris_library_paths() -> list[Path]:
    """Return candidate Lutris data directories (native + Flatpak)."""
    return [
        XDG_DATA / "lutris",
        Path.home() / ".var" / "app" / "net.lutris.Lutris" / "data" / "lutris",
    ]


def find_gog_games_lutris() -> list[dict]:
    """
    Scan Lutris for installed GOG games.
    Lutris stores per-game YAML files under:
      ~/.local/share/lutris/games/<slug>.yml
    and a SQLite DB at:
      ~/.local/share/lutris/pga.db  (games table: id, name, slug, runner, directory, exe)

    We prefer the SQLite DB (more reliable), fall back to YAML glob.
    Both native and Flatpak paths are checked.
    """
    results: list[dict] = []
    seen: set[str] = set()

    lutris_data_roots = _lutris_library_paths()

    for lutris_root in lutris_data_roots:
        if not lutris_root.exists():
            continue

        pga_db = lutris_root / "pga.db"
        if pga_db.exists():
            try:
                con = sqlite3.connect(str(pga_db))
                con.row_factory = sqlite3.Row
                # 'exe' column was removed in newer Lutris versions — check before selecting
                pragma = con.execute("PRAGMA table_info(games)").fetchall()
                col_names = {row[1] for row in pragma}
                exe_col = "exe" if "exe" in col_names else "NULL as exe"
                cur = con.execute(f"""
                    SELECT name, slug, runner, directory, {exe_col}, configpath
                    FROM games
                    WHERE runner IN ('wine', 'dosbox', 'scummvm', 'winesteam')
                       OR configpath LIKE '%gog%'
                       OR directory LIKE '%GOG%'
                       OR directory LIKE '%gog%'
                    ORDER BY name COLLATE NOCASE
                """)
                rows = cur.fetchall()
                con.close()
                for row in rows:
                    name = row["name"] or ""
                    slug = row["slug"] or ""
                    key  = slug or name
                    if not name or key in seen:
                        continue
                    directory = row["directory"] or ""
                    exe       = row["exe"] or ""
                    exe_abs   = str(Path(directory) / exe) if directory and exe else directory
                    seen.add(key)
                    results.append({
                        "name":        name,
                        "exe_path":    exe_abs or directory,
                        "install_dir": directory,
                        "wine_prefix": "",   # Lutris manages its own prefix; user can set in NAGO
                        "source":      "Lutris",
                        "app_name":    slug,
                    })
            except Exception as e:
                _NAGOLog.session(f"[warn] find_gog_games_lutris: failed to query pga.db at {pga_db}: {e}")
            continue  # Don't also glob YAMLs if DB worked

        # Fallback: parse YAML files (Lutris < 0.5.9 or no DB)
        games_dir = lutris_root / "games"
        if not games_dir.exists():
            continue
        for yml_path in sorted(games_dir.glob("*.yml")):
            try:
                text = yml_path.read_text(errors="ignore")
                # Minimal YAML key extraction without a full YAML parser
                name      = ""
                exe_path  = ""
                directory = ""
                for line in text.splitlines():
                    line = line.strip()
                    if line.startswith("name:") and not name:
                        name = line.split(":", 1)[1].strip().strip('"\'')
                    elif line.startswith("exe:") and not exe_path:
                        exe_path = line.split(":", 1)[1].strip().strip('"\'')
                    elif line.startswith("game_path:") or (line.startswith("working_dir:") and not directory):
                        directory = line.split(":", 1)[1].strip().strip('"\'')
                if not name:
                    continue
                key = yml_path.stem
                if key in seen:
                    continue
                seen.add(key)
                exe_abs = str(Path(directory) / exe_path) if directory and exe_path else exe_path or directory
                results.append({
                    "name":        name,
                    "exe_path":    exe_abs,
                    "install_dir": directory,
                    "wine_prefix": "",
                    "source":      "Lutris",
                    "app_name":    key,
                })
            except Exception as e:
                _NAGOLog.session(f"[warn] find_gog_games_lutris: failed to parse {yml_path.name}: {e}")
                continue

    results.sort(key=lambda g: g["name"].lower())
    return results


def find_all_gog_games() -> list[dict]:
    """Merge Heroic + Lutris results, deduplicating by name (case-insensitive)."""
    seen_names: set[str] = set()
    combined: list[dict] = []
    for game in find_gog_games_heroic() + find_gog_games_lutris():
        key = game["name"].lower()
        if key not in seen_names:
            seen_names.add(key)
            combined.append(game)
    combined.sort(key=lambda g: g["name"].lower())
    return combined


# ── Stylesheet ─────────────────────────────────────────────────────────────────
# Palette — midpoint between original (#0d0d0f base) and lifted (#26262a base):
#   bg       #1e1e22  sidebar  #2a2a30  surface  #2d2d32
#   surface2 #3d3d42  border   #424248  border2  #505058
#   text     #f4f4f5  text2    #a1a1aa  text3    #7e7e88
#   accent   #6366f1  accent2  #818cf8
# Fonts: all bumped +1px vs previous version


# Accent color palette — main color + lighter variant used for text/borders.
# Order matches the swatch order in SettingsPage.
ACCENT_COLORS = {
    "#4f46e5": "#818cf8",   # indigo   (default)
    "#1d4ed8": "#60a5fa",   # blue
    "#0284c7": "#38bdf8",   # sky
    "#0f766e": "#2dd4bf",   # teal
    "#16a34a": "#4ade80",   # green
    "#65a30d": "#a3e635",   # lime
    "#ca8a04": "#facc15",   # yellow
    "#ea580c": "#fb923c",   # orange
    "#dc2626": "#f87171",   # red
    "#db2777": "#f472b6",   # pink
    "#7c3aed": "#a78bfa",   # violet
    "#c026d3": "#e879f9",   # fuchsia
}
DEFAULT_ACCENT  = "#4f46e5"
DEFAULT_ACCENT2 = "#818cf8"


# ── Theme token palettes ───────────────────────────────────────────────────────
# Every __T_*__ placeholder in nago-launcher.qss maps to one of these dicts.
# Token substitution happens in _apply_stylesheet BEFORE accent tokens so that
# a light-mode token value of "__ACCENT__" expands correctly in the second pass.
#
# Semantic groupings:
#   BG / SIDEBAR_BG / SURFACE / SURFACE2 / SURFACE_HOVER / TOPBAR_BG / DIALOG_BG /
#   SECTION_BG / CARD_BG / CARD_HOVER / ENV_HDR_BG — backgrounds
#   BORDER / BORDER2 / BORDER3 / BORDER_H — borders by weight/context
#   TEXT … TEXT8 / TEXT_DISABLED / PLACEHOLDER / MUTED / EMPTY — text
#   HOVER / HOVER2 / SEG_HOVER / WINBTN_PRESS / SURFACE_CHK — interactive states
#   SCROLLBAR / SEPARATOR / COMBO_BG / COMBO_BORDER / SEC_CHK_BORDER — misc
#   BTN_HOVER_OVERLAY — rgba overlay (white in dark, black in light)
#   LOG_BG / LOG_TEXT / LOG_BORDER / TOOLTIP_BG — log viewer & tooltip
DARK_TOKENS: dict[str, str] = {
    # Backgrounds
    "__T_BG__":              "#1d1d20",
    "__T_SIDEBAR_BG__":      "#2a2a30",
    "__T_SURFACE__":         "#2d2d32",
    "__T_SURFACE2__":        "#1b1b1c",
    "__T_SURFACE_HOVER__":   "#353539",
    "__T_SURFACE_CHK__":     "__ACCENT_BG__",  # expands in 2nd pass
    "__T_TOPBAR_BG__":       "#1e1e22",
    "__T_DIALOG_BG__":       "#1d1d20",
    "__T_SECTION_BG__":      "#222227",
    "__T_CARD_BG__":         "#2a2a30",
    "__T_CARD_HOVER__":      "#32323a",
    "__T_ENV_HDR_BG__":      "#1a1a1e",
    "__T_COMBO_BG__":        "#141417",
    # Borders
    "__T_BORDER__":          "#3d3d43",
    "__T_BORDER2__":         "#333338",
    "__T_BORDER3__":         "#353539",
    "__T_BORDER_H__":        "#444448",
    "__T_COMBO_BORDER__":    "#5a5a66",
    "__T_SEC_CHK_BORDER__":  "__ACCENT__",  # expands in 2nd pass — matches light theme
    "__T_ENV_ROW_BDR__":     "#222227",
    # Text
    "__T_TEXT__":            "#f4f4f5",
    "__T_TEXT2__":           "#d4d4d8",
    "__T_TEXT3__":           "#a1a1aa",
    "__T_TEXT4__":           "#7e7e88",
    "__T_TEXT5__":           "#636370",
    "__T_TEXT6__":           "#505058",
    "__T_TEXT7__":           "#c4c4cf",
    "__T_TEXT8__":           "#909098",
    "__T_TEXT_DISABLED__":   "#3d3d44",
    "__T_PILL_FG__":         "#4ade80",
    "__T_PILL_BG__":         "#274438",
    "__T_PILL_WARN_FG__":    "#fbbf24",
    "__T_PILL_WARN_BG__":    "#3b2e0a",
    "__T_PILL_ERR_FG__":     "#f87171",
    "__T_PILL_ERR_BG__":     "#3b1c1c",
    "__T_PILL_PEND_FG__":    "#7e7e88",
    "__T_PILL_PEND_BG__":    "#2d2d32",
    "__T_PLACEHOLDER__":     "#3f3f46",
    "__T_MUTED__":           "#52525b",
    "__T_EMPTY__":           "#424248",
    # Interactive
    "__T_HOVER__":           "#424248",
    "__T_HOVER2__":          "#2d2d32",
    "__T_SEG_HOVER__":       "#383840",
    "__T_WINBTN_PRESS__":    "#2a2a2e",
    "__T_BTN_HOVER_OVERLAY__": "rgba(255,255,255,0.04)",
    # Misc
    "__T_SCROLLBAR__":       "#3a3a40",
    "__T_SEPARATOR__":       "#3a3a42",
    # Log & tooltip
    "__T_LOG_BG__":          "#111114",
    "__T_LOG_TEXT__":        "#c4c4cf",
    "__T_LOG_BORDER__":      "#333338",
    "__T_TOOLTIP_BG__":      "#2a2a30",
    # Danger button states
    "__T_DANGER_HOVER__":    "#3f1a1a",
    "__T_DANGER_PRESS__":    "#2a0f0f",
    "__T_ENVDEL_PRESS__":    "#1a0a0a",
    # New semantic tokens
    "__T_STAT_BG__":         "#1b1b1c",
    "__T_CAT_BADGE_FG__":    "#cbd5e1",
    "__T_CAT_BADGE_BG__":    "#1e293b",
    "__T_SEG_BG__":          "#1d1d20",
    "__T_STEAM_WARN_BG__":   "#2a2a3a",
    "__T_STEAM_WARN_BORDER__": "#4c4c6a",
}

LIGHT_TOKENS: dict[str, str] = {
    # Backgrounds
    "__T_BG__":              "#f5f5f7",
    "__T_SIDEBAR_BG__":      "#ebebef",
    "__T_SURFACE__":         "#ffffff",
    "__T_SURFACE2__":        "#f8f8fa",
    "__T_SURFACE_HOVER__":   "#e8e8ec",
    "__T_SURFACE_CHK__":     "__ACCENT_BG__",  # expands in 2nd pass
    "__T_TOPBAR_BG__":       "#fafafa",
    "__T_DIALOG_BG__":       "#ffffff",
    "__T_SECTION_BG__":      "#f0f0f4",
    "__T_CARD_BG__":         "#ffffff",
    "__T_CARD_HOVER__":      "#f5f5fa",
    "__T_ENV_HDR_BG__":      "#f0f0f4",
    "__T_COMBO_BG__":        "#ffffff",
    # Borders
    "__T_BORDER__":          "#d4d4d8",
    "__T_BORDER2__":         "#e0e0e4",
    "__T_BORDER3__":         "#dcdce0",
    "__T_BORDER_H__":        "#c4c4c8",
    "__T_COMBO_BORDER__":    "#c4c4cf",
    "__T_SEC_CHK_BORDER__":  "__ACCENT__",  # expands in 2nd pass
    "__T_ENV_ROW_BDR__":     "#ebebef",
    # Text
    "__T_TEXT__":            "#18181b",
    "__T_TEXT2__":           "#3f3f46",
    "__T_TEXT3__":           "#52525b",
    "__T_TEXT4__":           "#71717a",
    "__T_TEXT5__":           "#71717a",
    "__T_TEXT6__":           "#a1a1aa",
    "__T_TEXT7__":           "#52525b",
    "__T_TEXT8__":           "#71717a",
    "__T_TEXT_DISABLED__":   "#a1a1aa",
    "__T_PILL_FG__":         "#166534",
    "__T_PILL_BG__":         "#dcfce7",
    "__T_PILL_WARN_FG__":    "#92400e",
    "__T_PILL_WARN_BG__":    "#fef3c7",
    "__T_PILL_ERR_FG__":     "#991b1b",
    "__T_PILL_ERR_BG__":     "#fee2e2",
    "__T_PILL_PEND_FG__":    "#71717a",
    "__T_PILL_PEND_BG__":    "#e4e4e8",
    "__T_PLACEHOLDER__":     "#c4c4cf",
    "__T_MUTED__":           "#c4c4cf",
    "__T_EMPTY__":           "#c4c4cf",
    # Interactive
    "__T_HOVER__":           "#f0f0f4",
    "__T_HOVER2__":          "#e0e0e5",
    "__T_SEG_HOVER__":       "#e4e4e8",
    "__T_WINBTN_PRESS__":    "#e0e0e4",
    "__T_BTN_HOVER_OVERLAY__": "rgba(0,0,0,0.04)",
    # Misc
    "__T_SCROLLBAR__":       "#c4c4cf",
    "__T_SEPARATOR__":       "#d4d4d8",
    # Log & tooltip
    "__T_LOG_BG__":          "#f0f2f5",
    "__T_LOG_TEXT__":        "#18181b",
    "__T_LOG_BORDER__":      "#d4d4d8",
    "__T_TOOLTIP_BG__":      "#ffffff",
    # Danger button states
    "__T_DANGER_HOVER__":    "#fff0f0",
    "__T_DANGER_PRESS__":    "#ffe0e0",
    "__T_ENVDEL_PRESS__":    "#fff0f0",
    # New semantic tokens
    "__T_STAT_BG__":         "#f0f0f4",
    "__T_CAT_BADGE_FG__":    "#3730a3",
    "__T_CAT_BADGE_BG__":    "#e0e7ff",
    "__T_SEG_BG__":          "#e8e8ec",
    "__T_STEAM_WARN_BG__":   "#f3f0ff",
    "__T_STEAM_WARN_BORDER__": "#c4b5fd",
}


@functools.lru_cache(maxsize=1)
def _load_stylesheet() -> str:
    """Load the QSS stylesheet from nago-launcher.qss next to this script.
    Result is cached — the file never changes at runtime.
    Falls back to an empty string so the app still launches if the file is missing."""
    qss_path = _nago_asset("nago-launcher.qss")
    try:
        return qss_path.read_text(encoding="utf-8")
    except FileNotFoundError:
        import sys
        print(f"Warning: stylesheet not found at {qss_path}", file=sys.stderr)
        return ""


def _hex_to_rgba(hex_color: str, opacity: float) -> str:
    """Convert a #rrggbb hex color to an rgba() string for QSS."""
    c = QColor(hex_color)
    return f"rgba({c.red()},{c.green()},{c.blue()},{opacity})"


def _lighten_hex(hex_color: str, amount: int = 20) -> str:
    """Lighten a hex color by adding amount to each RGB channel (clamped to 255)."""
    c = QColor(hex_color)
    return QColor(min(255, c.red()+amount),
                  min(255, c.green()+amount),
                  min(255, c.blue()+amount)).name()


def _darken_hex(hex_color: str, amount: int = 20) -> str:
    """Darken a hex color by subtracting amount from each RGB channel (clamped to 0)."""
    c = QColor(hex_color)
    return QColor(max(0, c.red()-amount),
                  max(0, c.green()-amount),
                  max(0, c.blue()-amount)).name()






def _apply_card_width(width: int):
    """Update all CARD_W-derived module globals. Call before reload()."""
    global CARD_W, COVER_H, CARD_H, CARD_RADIUS, COVER_RADIUS
    CARD_W       = max(140, min(280, int(width)))
    COVER_H      = CARD_W * 3 // 2
    CARD_H       = COVER_H
    CARD_RADIUS  = round(CARD_W * 0.0667)
    COVER_RADIUS = CARD_RADIUS - 2
    _SHADOW_CACHE.clear()


_SHADOW_CACHE: dict[tuple, "QPixmap"] = {}
_SHADOW_BLUR  = 16   # logical px
_SHADOW_OY    =  6   # downward offset
_SHADOW_M     = _SHADOW_BLUR + 6   # margin around card


def _build_shadow_pixmap(card_w: int, card_h: int, radius: int) -> "QPixmap":
    """Render a proper Gaussian drop-shadow using Pillow.
    Falls back to a simple radial gradient if Pillow is unavailable."""
    screen = QApplication.primaryScreen()
    dpr    = screen.devicePixelRatio() if screen else 1.0
    blur   = _SHADOW_BLUR
    oy     = _SHADOW_OY
    m      = _SHADOW_M
    pw_l   = card_w + m * 2
    ph_l   = card_h + m * 2 + oy
    pw_p   = round(pw_l * dpr)
    ph_p   = round(ph_l * dpr)

    try:
        from PIL import Image, ImageFilter, ImageDraw
        blur_p   = max(1, round(blur * dpr * 0.55))
        r_p      = round(radius * dpr)
        x0, y0   = round(m * dpr), round((m + oy) * dpr)
        x1, y1   = x0 + round(card_w * dpr), y0 + round(card_h * dpr)

        mask = Image.new("L", (pw_p, ph_p), 0)
        draw = ImageDraw.Draw(mask)
        try:
            draw.rounded_rectangle([x0, y0, x1, y1], radius=r_p, fill=225)
        except AttributeError:
            draw.rectangle([x0, y0, x1, y1], fill=230)   # Pillow < 8.2 fallback

        blurred  = mask.filter(ImageFilter.GaussianBlur(radius=blur_p * 0.5))
        black    = Image.new("L", (pw_p, ph_p), 0)
        shadow   = Image.merge("RGBA", [black, black, black, blurred])
        raw      = shadow.tobytes()
        qimg     = QImage(raw, pw_p, ph_p, pw_p * 4,
                          QImage.Format.Format_RGBA8888)
        # Keep a reference so the buffer isn't freed before QPixmap copies it
        qimg._raw = raw
        px = QPixmap.fromImage(qimg)

    except ImportError:
        # Pillow not installed — plain semi-transparent rect as last resort
        px = QPixmap(pw_p, ph_p)
        px.fill(Qt.GlobalColor.transparent)
        p = QPainter(px)
        p.setPen(QPen(Qt.PenStyle.NoPen))
        p.setBrush(QColor(0, 0, 0, 80))
        p.drawRoundedRect(
            QRectF(round(m * dpr), round((m + oy) * dpr),
                   round(card_w * dpr), round(card_h * dpr)),
            radius * dpr, radius * dpr)
        p.end()

    px.setDevicePixelRatio(dpr)
    return px


def _card_shadow_px() -> "QPixmap":
    screen = QApplication.primaryScreen()
    dpr    = round((screen.devicePixelRatio() if screen else 1.0) * 4) / 4
    key    = (CARD_W, CARD_H, CARD_RADIUS, dpr)
    if key not in _SHADOW_CACHE:
        _SHADOW_CACHE[key] = _build_shadow_pixmap(CARD_W, CARD_H, CARD_RADIUS)
    return _SHADOW_CACHE[key]


class _LibraryGrid(QWidget):
    """Card grid container — uses manual absolute positioning (flow layout).

    Responsibilities:
    - Positions all GameCard widgets manually via move() in reflow().
    - Manages container height so QScrollArea knows the scroll extent.
    - Paints Gaussian shadow pixmaps behind every card in paintEvent.
    - Owns all drag logic via pure mouse tracking (no QDrag / MIME).
      Cards are display-only widgets; _LibraryGrid owns the full drag lifecycle.

    Drag design:
    - On press+move past threshold: hide source card, show floating ghost label.
    - While dragging: other cards shift to open a gap whose position is determined
      by card-center hit testing. Single source-of-truth function _gap_idx_for_pos
      is used for both layout and commit — no drift possible.
    - On release: emit reorder_requested(src_id, target_id_or_-1), restore layout.
    """

    reorder_requested = pyqtSignal(int, int)   # (src_game_id, target_game_id_or_-1)

    # Layout constants
    _PAD_X  = 24
    _PAD_Y  = 24
    _GAP_X  = 20
    _GAP_Y  = 20

    # Drag: minimum manhattan distance before a drag starts (matches Qt default)
    _DRAG_THRESHOLD = 8

    def __init__(self, parent=None):
        super().__init__(parent)
        self._accent_color: str = "#6366f1"

        # Flow state
        self._cols: int = 1
        self._ordered: list = []   # list of GameCard, in display order

        # Drag state — all None/empty when no drag is active
        self._drag_src_card    = None   # GameCard being dragged
        self._drag_press_pos   = None   # QPoint where mouse was pressed (in container coords)
        self._drag_cursor_pos  = None   # current cursor QPoint (container coords)
        self._drag_hotspot     = None   # QPoint: press pos within the source card
        self._drag_gap_idx     = None   # int: current gap insertion index (0..n-1 of non-src cards)
        self._drag_ordered_ex  = []     # _ordered minus source card
        self._ghost             = None  # QLabel used as the floating ghost

        # Auto-scroll during drag
        self._scroll_timer = QTimer(self)
        self._scroll_timer.setInterval(30)          # 30ms tick → ~33 fps
        self._scroll_timer.timeout.connect(self._do_scroll)
        self._scroll_dir   = 0                      # -1 up, 0 none, +1 down

    def set_accent(self, color: str):
        self._accent_color = color

    # ── Layout helpers ────────────────────────────────────────────────────────

    def _col_count(self, viewport_w: int) -> int:
        avail = viewport_w - self._PAD_X * 2
        cols  = max(1, (avail + self._GAP_X) // (CARD_W + self._GAP_X))
        return int(cols)

    def _card_xy(self, idx: int, cols: int) -> tuple:
        row, col = divmod(idx, cols)
        x = self._PAD_X + col * (CARD_W  + self._GAP_X)
        y = self._PAD_Y + row * (CARD_H  + self._GAP_Y)
        return x, y

    def _total_height(self, n: int, cols: int) -> int:
        if n == 0:
            return self._PAD_Y * 2
        rows = (n + cols - 1) // cols
        return self._PAD_Y + rows * (CARD_H + self._GAP_Y) - self._GAP_Y + self._PAD_Y

    def reflow(self, ordered: list, viewport_w: int):
        """Position all visible cards. Called by LibraryPage after any
        show/hide change or resize."""
        self._ordered = ordered
        cols = self._col_count(viewport_w)
        self._cols = cols
        for i, card in enumerate(ordered):
            x, y = self._card_xy(i, cols)
            card.move(x, y)
            card.setVisible(True)
        self.setFixedHeight(self._total_height(len(ordered), cols))
        self.update()  # repaint shadows at new positions — move() only repaints children

    # ── Drag helpers ──────────────────────────────────────────────────────────

    def _gap_idx_for_pos(self, cursor_pos) -> int:
        """Return the gap insertion index (0 .. len(non-src cards)) for the
        given cursor position (in container coordinates).

        IMPORTANT: Hit test uses BASELINE positions (no gap) — i.e. as if all
        non-source cards were packed contiguously starting at slot 0.
        This means card positions used for hit-testing never change during a
        drag, so there is no feedback loop and no oscillation at boundaries.
        The gap is purely visual; it does not affect where the midpoints are.
        """
        ex   = self._drag_ordered_ex
        n    = len(ex)
        cols = self._cols

        if n == 0:
            return 0

        # Ghost center X/Y — cursor adjusted by hotspot so we track card center.
        # Both row and column hit tests use ghost center for consistency.
        hx = self._drag_hotspot.x() if self._drag_hotspot else CARD_W // 2
        hy = self._drag_hotspot.y() if self._drag_hotspot else CARD_H // 2
        cx = cursor_pos.x() - hx + CARD_W // 2
        cy = cursor_pos.y() - hy + CARD_H // 2

        # Baseline positions: card i sits at slot i (no gap applied)
        positions = [self._card_xy(i, cols) for i in range(n)]

        # Build row center Y values from the full grid (n+1 slots, including the
        # gap slot) so all rows are always represented even when the dragged card
        # was the only card in its row. Using only ex positions would drop that
        # row from row_ys, causing the row above to absorb all Y positions below.
        full_rows = (n + cols) // cols
        row_ys = {r: self._PAD_Y + r * (CARD_H + self._GAP_Y) + CARD_H // 2
                  for r in range(full_rows)}
        if not row_ys:
            return 0
        # Find which row the cursor is in by comparing against midpoints between
        # adjacent row centers — same principle as the column hit test.
        sorted_rows = sorted(row_ys.keys())
        cur_row = sorted_rows[-1]  # default: last row
        for idx, r in enumerate(sorted_rows):
            if idx + 1 < len(sorted_rows):
                next_r = sorted_rows[idx + 1]
                boundary = (row_ys[r] + row_ys[next_r]) // 2
            else:
                boundary = float("inf")
            if cy <= boundary:
                cur_row = r
                break
        row_start = cur_row * cols
        row_end   = min(row_start + cols, n)

        # Within that row, find the insertion point by comparing cursor X against
        # the midpoints between adjacent card centers. This gives each card an
        # equal-width hit zone rather than splitting on the card center itself.
        row_cards = list(range(row_start, row_end))
        if not row_cards:
            return row_end
        centers = [positions[i][0] + CARD_W // 2 for i in row_cards]
        best_idx = row_end
        for j, card_cx in enumerate(centers):
            # Boundary is halfway between this card center and the next, or
            # at the card center itself for the last card in the row.
            if j + 1 < len(centers):
                boundary = (card_cx + centers[j + 1]) // 2
            else:
                boundary = card_cx
            if cx <= boundary:
                best_idx = row_cards[j]
                break

        # If the row is full (no empty trailing slots), don't allow best_idx to
        # reach row_end from within this row — that slot is the first position of
        # the next row. The user must move the cursor into the next row's Y zone
        # to trigger that insertion point.
        if best_idx == row_end and row_end == row_start + cols:
            best_idx = row_end - 1

        return best_idx

    def _apply_gap_layout(self):
        """Move non-source cards to open a gap at _drag_gap_idx."""
        if self._drag_gap_idx is None:
            return
        ex   = self._drag_ordered_ex
        n    = len(ex)
        cols = self._cols
        ins  = min(self._drag_gap_idx, n)

        self.setUpdatesEnabled(False)
        try:
            for i, card in enumerate(ex):
                slot = i if i < ins else i + 1
                x, y = self._card_xy(slot, cols)
                card.move(x, y)
            self.setFixedHeight(self._total_height(n + 1, cols))
        finally:
            self.setUpdatesEnabled(True)
        self.update()

    def _restore_layout(self):
        """Restore all cards (including source) to their normal positions."""
        if not self._ordered:
            return
        self.setUpdatesEnabled(False)
        try:
            cols = self._cols
            for i, card in enumerate(self._ordered):
                x, y = self._card_xy(i, cols)
                card.move(x, y)
            self.setFixedHeight(self._total_height(len(self._ordered), cols))
        finally:
            self.setUpdatesEnabled(True)
        self.update()

    def _make_ghost(self, src_card) -> "QLabel":
        """Grab the source card into a translucent floating QLabel ghost."""
        src_card._hover_overlay.hide()
        snap = src_card.grab()
        src_card._hover_overlay.show()

        px = QPixmap(snap.size())
        px.setDevicePixelRatio(snap.devicePixelRatioF())
        px.fill(Qt.GlobalColor.transparent)
        p = QPainter(px)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        clip = QPainterPath()
        clip.addRoundedRect(QRectF(0, 0, src_card.width(), src_card.height()),
                            CARD_RADIUS, CARD_RADIUS)
        p.setClipPath(clip)
        p.setOpacity(0.82)
        p.drawPixmap(0, 0, snap)
        p.end()

        # Parent to the viewport so the ghost is clipped to the scroll area
        # and can't paint over the status bar or other widgets outside the grid.
        viewport = self.parent() if self.parent() else self
        ghost = QLabel(viewport)
        ghost.setPixmap(px)
        ghost.setFixedSize(src_card.size())
        ghost.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
        ghost.raise_()
        ghost.show()
        return ghost

    def _move_ghost(self, cursor_pos):
        """Position the ghost so the grab point stays under the cursor."""
        if self._ghost is None or self._drag_hotspot is None:
            return
        hx = self._drag_hotspot.x()
        hy = self._drag_hotspot.y()
        # cursor_pos is in grid coords — map to parent (viewport) coords
        parent = self._ghost.parent()
        if parent and parent is not self:
            mapped = self.mapTo(parent, cursor_pos)
            self._ghost.move(mapped.x() - hx, mapped.y() - hy)
        else:
            self._ghost.move(cursor_pos.x() - hx, cursor_pos.y() - hy)

    def _end_drag(self, commit: bool):
        """Tear down all drag state. If commit=True, emit reorder_requested."""
        src_card   = self._drag_src_card
        gap_idx    = self._drag_gap_idx
        ordered_ex = list(self._drag_ordered_ex)

        # Destroy ghost
        if self._ghost is not None:
            self._ghost.hide()
            self._ghost.deleteLater()
            self._ghost = None

        # Clear state BEFORE emitting so signal handlers see clean state
        self._drag_src_card   = None
        self._drag_press_pos  = None
        self._drag_cursor_pos = None
        self._drag_hotspot    = None
        self._drag_gap_idx    = None
        self._drag_ordered_ex = []

        # Remove app-level event filter and stop scroll timer
        QApplication.instance().removeEventFilter(self)
        self._scroll_timer.stop()
        self._scroll_dir = 0

        # Restore layout and make source visible again
        self._restore_layout()
        if src_card is not None:
            src_card.show()

        if commit and src_card is not None:
            n         = len(ordered_ex)
            ins       = min(gap_idx, n) if gap_idx is not None else n
            target_id = ordered_ex[ins].game["id"] if ins < n else -1
            self.reorder_requested.emit(src_card.game["id"], target_id)

    # ── Mouse events ──────────────────────────────────────────────────────────

    # ── Auto-scroll helpers ──────────────────────────────────────────────────

    def _scroll_area(self):
        """Return the parent QScrollArea. Parent chain: grid → viewport → scroll."""
        p = self.parent()
        if p is None:
            return None
        p2 = p.parent()
        from PyQt6.QtWidgets import QScrollArea as _QSA
        return p2 if isinstance(p2, _QSA) else None

    def _update_scroll_dir(self, global_y: int):
        """Determine scroll direction based on cursor proximity to scroll viewport edges.
        Trigger zone = 25% of CARD_H from top or bottom of the visible viewport."""
        sa = self._scroll_area()
        if sa is None:
            self._scroll_dir = 0
            return
        vp       = sa.viewport()
        vp_top   = vp.mapToGlobal(QPoint(0, 0)).y()
        vp_bot   = vp_top + vp.height()
        zone     = max(30, CARD_H // 4)   # 25% of card height, min 30px
        if global_y < vp_top + zone:
            self._scroll_dir = -1
        elif global_y > vp_bot - zone:
            self._scroll_dir = 1
        else:
            self._scroll_dir = 0

        if self._scroll_dir != 0 and not self._scroll_timer.isActive():
            self._scroll_timer.start()
        elif self._scroll_dir == 0 and self._scroll_timer.isActive():
            self._scroll_timer.stop()

    def _do_scroll(self):
        """Called by scroll timer — advances the scroll area by 20px per tick."""
        sa = self._scroll_area()
        if sa is None or self._scroll_dir == 0:
            self._scroll_timer.stop()
            return
        sb = sa.verticalScrollBar()
        sb.setValue(sb.value() + self._scroll_dir * 20)

    def eventFilter(self, obj, event):
        """App-level filter active only during a drag.
        Intercepts MouseMove and MouseButtonRelease from any widget,
        translates coordinates to container space, and forwards to our handlers.
        This is the Wayland-safe alternative to grabMouse()."""
        if self._drag_gap_idx is None:
            # Not dragging — pass everything through
            return False
        t = event.type()
        if t == QEvent.Type.MouseMove:
            # Map global cursor pos to container coordinates
            global_pos = event.globalPosition().toPoint()
            local_pos  = self.mapFromGlobal(global_pos)
            # Clamp to container bounds so sidebar / out-of-bounds cursor positions
            # don't produce negative X or Y values that break the hit test.
            clamped = QPoint(
                max(0, min(local_pos.x(), self.width()  - 1)),
                max(0, min(local_pos.y(), self.height() - 1)),
            )
            self._drag_cursor_pos = clamped
            self._move_ghost(local_pos)   # ghost follows real cursor, not clamped
            new_idx = self._gap_idx_for_pos(clamped)
            if new_idx != self._drag_gap_idx:
                self._drag_gap_idx = new_idx
                self._apply_gap_layout()
            # Auto-scroll when cursor is near top/bottom of viewport
            self._update_scroll_dir(global_pos.y())
            return True   # consume — don't let the card/viewport also handle it
        if t == QEvent.Type.MouseButtonRelease:
            if event.button() == Qt.MouseButton.LeftButton:
                self._end_drag(commit=True)
                return True
        return False

    def mousePressEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return super().mousePressEvent(event)

        # Find which card was pressed
        child = self.childAt(event.position().toPoint())
        # Walk up in case the click landed on an overlay/label inside the card
        card = None
        w = child
        while w is not None and w is not self:
            from PyQt6.QtWidgets import QFrame
            if isinstance(w, GameCard):
                card = w
                break
            w = w.parentWidget()

        if card is None:
            return super().mousePressEvent(event)

        # Record press — drag starts in mouseMoveEvent after threshold
        self._drag_src_card  = card
        self._drag_press_pos = event.position().toPoint()
        self._drag_hotspot   = event.position().toPoint() - card.pos()
        event.accept()

    def mouseMoveEvent(self, event):
        if self._drag_src_card is None:
            return super().mouseMoveEvent(event)

        pos = event.position().toPoint()

        # ── Drag not yet started — check threshold ────────────────────────
        if self._drag_gap_idx is None:
            if (pos - self._drag_press_pos).manhattanLength() < self._DRAG_THRESHOLD:
                return
            # Threshold crossed — start the drag
            src = self._drag_src_card
            self._drag_ordered_ex = [c for c in self._ordered
                                     if c.game["id"] != src.game["id"]]
            self._drag_gap_idx    = 0   # initialise before first gap calculation
            self._drag_cursor_pos = pos

            # Hide source card, build ghost
            src.hide()
            self._ghost = self._make_ghost(src)
            self._move_ghost(pos)

            # Compute initial gap — pass 0 as current_ins (no gap yet)
            self._drag_gap_idx = self._gap_idx_for_pos(pos)
            self._apply_gap_layout()

            # Install app-level event filter so MouseMove/Release reach us
            # even when the cursor is over child widgets or outside the scroll area.
            # This works on Wayland (grabMouse does not).
            QApplication.instance().installEventFilter(self)
            return

        # ── Drag in progress ──────────────────────────────────────────────
        self._drag_cursor_pos = pos
        self._move_ghost(pos)

        # Pass current gap as current_ins so hit-test uses actual card positions
        new_idx = self._gap_idx_for_pos(pos)
        if new_idx != self._drag_gap_idx:
            self._drag_gap_idx = new_idx
            self._apply_gap_layout()

    def mouseReleaseEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return super().mouseReleaseEvent(event)

        if self._drag_src_card is None:
            return super().mouseReleaseEvent(event)

        drag_was_active = self._drag_gap_idx is not None
        self._end_drag(commit=drag_was_active)
        event.accept()

    # ── Paint ─────────────────────────────────────────────────────────────────

    def paintEvent(self, event):
        super().paintEvent(event)
        shadow = _card_shadow_px()
        m      = _SHADOW_M
        p      = QPainter(self)
        for card in self._ordered:
            if card.isVisible():
                geo = card.geometry()
                p.drawPixmap(geo.x() - m, geo.y() - m, shadow)
        p.end()




def _apply_palette(app: "QApplication", cfg: dict):
    """Set Qt's application-wide QPalette for dark or light theme.
    Called from _apply_stylesheet — no need to call directly."""
    theme = cfg.get("theme", "dark")
    accent = cfg.get("accent_color", DEFAULT_ACCENT)
    pal = QPalette()
    _c  = QColor
    if theme == "light":
        pal.setColor(QPalette.ColorRole.Window,          _c("#f5f5f7"))
        pal.setColor(QPalette.ColorRole.WindowText,      _c("#18181b"))
        pal.setColor(QPalette.ColorRole.Base,            _c("#ffffff"))
        pal.setColor(QPalette.ColorRole.AlternateBase,   _c("#f0f0f4"))
        pal.setColor(QPalette.ColorRole.ToolTipBase,     _c("#ffffff"))
        pal.setColor(QPalette.ColorRole.ToolTipText,     _c("#18181b"))
        pal.setColor(QPalette.ColorRole.Text,            _c("#18181b"))
        pal.setColor(QPalette.ColorRole.Button,          _c("#ffffff"))
        pal.setColor(QPalette.ColorRole.ButtonText,      _c("#18181b"))
        pal.setColor(QPalette.ColorRole.BrightText,      _c("#000000"))
        pal.setColor(QPalette.ColorRole.Link,            _c(accent))
        pal.setColor(QPalette.ColorRole.Highlight,       _c(accent))
        pal.setColor(QPalette.ColorRole.HighlightedText, _c("#ffffff"))
        pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.Text,       _c("#a1a1aa"))
        pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.ButtonText, _c("#a1a1aa"))
        pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.WindowText, _c("#a1a1aa"))
    else:
        pal.setColor(QPalette.ColorRole.Window,          _c("#1d1d20"))
        pal.setColor(QPalette.ColorRole.WindowText,      _c("#f4f4f5"))
        pal.setColor(QPalette.ColorRole.Base,            _c("#2d2d32"))
        pal.setColor(QPalette.ColorRole.AlternateBase,   _c("#2a2a30"))
        pal.setColor(QPalette.ColorRole.ToolTipBase,     _c("#2d2d32"))
        pal.setColor(QPalette.ColorRole.ToolTipText,     _c("#f4f4f5"))
        pal.setColor(QPalette.ColorRole.Text,            _c("#f4f4f5"))
        pal.setColor(QPalette.ColorRole.Button,          _c("#2d2d32"))
        pal.setColor(QPalette.ColorRole.ButtonText,      _c("#f4f4f5"))
        pal.setColor(QPalette.ColorRole.BrightText,      _c("#ffffff"))
        pal.setColor(QPalette.ColorRole.Link,            _c("#818cf8"))
        pal.setColor(QPalette.ColorRole.Highlight,       _c("#6366f1"))
        pal.setColor(QPalette.ColorRole.HighlightedText, _c("#ffffff"))
        pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.Text,       _c("#505058"))
        pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.ButtonText, _c("#505058"))
        pal.setColor(QPalette.ColorGroup.Disabled, QPalette.ColorRole.WindowText, _c("#505058"))
    app.setPalette(pal)


def _apply_stylesheet(app: "QApplication", cfg: dict):
    """Load QSS, substitute theme tokens then accent tokens, apply to app.
    Also updates the QPalette via _apply_palette."""
    _apply_card_width(cfg.get("card_width", CARD_W))
    theme   = cfg.get("theme", "dark")
    accent  = cfg.get("accent_color", DEFAULT_ACCENT)
    accent2 = ACCENT_COLORS.get(accent, DEFAULT_ACCENT2)
    app.setProperty("nagoAccent",  accent)
    app.setProperty("nagoAccent2", accent2)
    app.setProperty("nagoTheme",   theme)

    tokens = LIGHT_TOKENS if theme == "light" else DARK_TOKENS
    style  = _load_stylesheet()
    # Pass 1: theme tokens (some light values contain __ACCENT__ for 2nd-pass expansion)
    for token, value in tokens.items():
        style = style.replace(token, value)
    # Pass 2: accent tokens
    style = (style
             .replace("__ACCENT__",       accent)
             .replace("__ACCENT2__",      accent2)
             .replace("__ACCENT_LIGHT__", _lighten_hex(accent, 35))
             .replace("__ACCENT_DARK__",  _darken_hex(accent, 20))
             .replace("__ACCENT_BG__",    _hex_to_rgba(accent, 0.18))
             .replace("__ACCENT_BG2__",   _hex_to_rgba(accent, 0.3))
             .replace("__CARD_RADIUS__",  f"{CARD_RADIUS}px"))
    _apply_palette(app, cfg)
    app.setStyleSheet(style)



# ── Database ───────────────────────────────────────────────────────────────────
def _migrate_umu_to_tools():
    """
    One-time migration: move ~/.local/share/nago-launcher/umu/ →
    ~/.local/share/nago-launcher/tools/umu/ so all managed tools live together.
    Safe to call every startup — no-ops if already migrated or never installed.
    """
    old_umu = NAGO_HOME / "umu"
    if old_umu.exists() and not UMU_HOME.exists():
        try:
            TOOLS_HOME.mkdir(parents=True, exist_ok=True)
            old_umu.rename(UMU_HOME)
        except Exception as e:
            print(f"[nago] umu migration failed: {e}")

def init_db():
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    ART_PATH.mkdir(parents=True, exist_ok=True)
    PREFIXES_PATH.mkdir(parents=True, exist_ok=True)
    TOOLS_HOME.mkdir(parents=True, exist_ok=True)
    _migrate_umu_to_tools()
    con = sqlite3.connect(DB_PATH)
    con.execute("""
        CREATE TABLE IF NOT EXISTS games (
            id       INTEGER PRIMARY KEY AUTOINCREMENT,
            name     TEXT NOT NULL,
            exe_path TEXT NOT NULL,
            game_type TEXT DEFAULT 'native',
            proton_path TEXT,
            cover_path  TEXT,
            grid_id     INTEGER,
            last_played TEXT,
            playtime    INTEGER DEFAULT 0,
            notes       TEXT DEFAULT '',
            umu_enabled INTEGER DEFAULT 0,
            umu_gameid  TEXT DEFAULT '',
            umu_store   TEXT DEFAULT 'none',
            launch_args     TEXT DEFAULT '',
            env_vars        TEXT DEFAULT '',
            pre_launch_cmd  TEXT DEFAULT '',
            post_exit_cmd   TEXT DEFAULT '',
            auto_backup     INTEGER DEFAULT 0,
            gamescope_enabled INTEGER DEFAULT 0,
            upscale_enabled INTEGER DEFAULT 0,
            upscale_model   TEXT DEFAULT 'fast',
            hdr_enabled     INTEGER DEFAULT 0,
            hdr_monitor     TEXT DEFAULT '',
            fsr4_upgrade    TEXT DEFAULT '',
            optiscaler_dll  TEXT DEFAULT '',
            fsr4_indicator  INTEGER DEFAULT 0,
            install_dir     TEXT DEFAULT ''
        )
    """)
    # Migrate existing DBs that pre-date the umu_* columns
    cur = con.execute("PRAGMA table_info(games)")
    existing_cols = {row[1] for row in cur.fetchall()}
    for col, ddl in [
        ("umu_enabled",    "INTEGER DEFAULT 0"),
        ("umu_gameid",     "TEXT DEFAULT ''"),
        ("umu_store",      "TEXT DEFAULT 'none'"),
        ("sort_pos",       "INTEGER DEFAULT 0"),
        ("launch_args",    "TEXT DEFAULT ''"),
        ("env_vars",       "TEXT DEFAULT ''"),
        ("pre_launch_cmd",   "TEXT DEFAULT ''"),
        ("post_exit_cmd",    "TEXT DEFAULT ''"),
        ("auto_backup",      "INTEGER DEFAULT 0"),
        ("gamescope_enabled", "INTEGER DEFAULT 0"),
        ("playtime_minutes", "INTEGER DEFAULT 0"),
        ("added_at",         "TEXT DEFAULT ''"),
        ("vn_jp_locale",     "INTEGER DEFAULT 0"),
        ("use_wined3d",      "INTEGER DEFAULT 0"),
        ("use_wow64",        "INTEGER DEFAULT 0"),
        ("use_wayland",      "INTEGER DEFAULT 0"),
        ("no_esync",         "INTEGER DEFAULT 0"),
        ("no_fsync",         "INTEGER DEFAULT 0"),
        ("no_ntsync",        "INTEGER DEFAULT 0"),
        ("legacy_mediaconv", "INTEGER DEFAULT 0"),
        ("video_decode_mode","TEXT DEFAULT 'default'"),
        ("last_session_minutes", "INTEGER DEFAULT 0"),
        ("upscale_enabled",  "INTEGER DEFAULT 0"),
        ("upscale_model",    "TEXT DEFAULT 'fast'"),
        ("hdr_enabled",      "INTEGER DEFAULT 0"),
        ("hdr_monitor",      "TEXT DEFAULT ''"),
        ("hidden",           "INTEGER DEFAULT 0"),
        ("fsr4_upgrade",     "TEXT DEFAULT ''"),
        ("optiscaler_dll",   "TEXT DEFAULT ''"),
        ("fsr4_indicator",   "INTEGER DEFAULT 0"),
        ("install_dir",      "TEXT DEFAULT ''"),
    ]:
        if col not in existing_cols:
            con.execute(f"ALTER TABLE games ADD COLUMN {col} {ddl}")
    con.execute("""
        CREATE TABLE IF NOT EXISTS categories (
            id       INTEGER PRIMARY KEY AUTOINCREMENT,
            name     TEXT NOT NULL UNIQUE,
            sort_pos INTEGER DEFAULT 0
        )
    """)
    con.execute("""
        CREATE TABLE IF NOT EXISTS game_categories (
            game_id     INTEGER NOT NULL,
            category_id INTEGER NOT NULL,
            sort_pos    INTEGER DEFAULT 0,
            PRIMARY KEY (game_id, category_id),
            FOREIGN KEY (game_id)     REFERENCES games(id)      ON DELETE CASCADE,
            FOREIGN KEY (category_id) REFERENCES categories(id) ON DELETE CASCADE
        )
    """)
    con.execute("""
        CREATE TABLE IF NOT EXISTS playtime_archive (
            id                   INTEGER PRIMARY KEY AUTOINCREMENT,
            exe_filename         TEXT NOT NULL,
            game_type            TEXT NOT NULL,
            store_key            TEXT DEFAULT '',
            game_name            TEXT NOT NULL,
            playtime_minutes     INTEGER DEFAULT 0,
            last_session_minutes INTEGER DEFAULT 0,
            last_played          TEXT DEFAULT '',
            archived_at          TEXT NOT NULL,
            prefix_path          TEXT DEFAULT '',
            -- per-game config fields
            launch_args          TEXT DEFAULT '',
            env_vars             TEXT DEFAULT '',
            pre_launch_cmd       TEXT DEFAULT '',
            post_exit_cmd        TEXT DEFAULT '',
            auto_backup          INTEGER DEFAULT 0,
            ludusavi_title       TEXT DEFAULT '',
            gamescope_enabled    INTEGER DEFAULT 0,
            upscale_enabled      INTEGER DEFAULT 0,
            upscale_model        TEXT DEFAULT 'fast',
            hdr_enabled          INTEGER DEFAULT 0,
            fsr4_upgrade         TEXT DEFAULT '',
            optiscaler_dll       TEXT DEFAULT '',
            use_wined3d          INTEGER DEFAULT 0,
            use_wow64            INTEGER DEFAULT 0,
            use_wayland          INTEGER DEFAULT 0,
            no_esync             INTEGER DEFAULT 0,
            no_fsync             INTEGER DEFAULT 0,
            no_ntsync            INTEGER DEFAULT 0,
            legacy_mediaconv     INTEGER DEFAULT 0,
            video_decode_mode    TEXT DEFAULT 'default',
            vn_jp_locale         INTEGER DEFAULT 0,
            added_at             TEXT DEFAULT '',
            category_names       TEXT DEFAULT ''
        )
    """)
    # Migrate playtime_archive to add prefix_path if missing
    cur = con.execute("PRAGMA table_info(playtime_archive)")
    pa_cols = {row[1] for row in cur.fetchall()}
    if "prefix_path" not in pa_cols:
        con.execute("ALTER TABLE playtime_archive ADD COLUMN prefix_path TEXT DEFAULT ''")
    if "last_session_minutes" not in pa_cols:
        con.execute("ALTER TABLE playtime_archive ADD COLUMN last_session_minutes INTEGER DEFAULT 0")
    # Config archive columns — added as a batch; each guarded individually for safety
    for _pac, _padef in [
        ("launch_args",       "TEXT DEFAULT ''"),
        ("env_vars",          "TEXT DEFAULT ''"),
        ("pre_launch_cmd",    "TEXT DEFAULT ''"),
        ("post_exit_cmd",     "TEXT DEFAULT ''"),
        ("auto_backup",       "INTEGER DEFAULT 0"),
        ("ludusavi_title",    "TEXT DEFAULT ''"),
        ("gamescope_enabled", "INTEGER DEFAULT 0"),
        ("upscale_enabled",   "INTEGER DEFAULT 0"),
        ("upscale_model",     "TEXT DEFAULT 'fast'"),
        ("hdr_enabled",       "INTEGER DEFAULT 0"),
        ("fsr4_upgrade",      "TEXT DEFAULT ''"),
        ("optiscaler_dll",    "TEXT DEFAULT ''"),
        ("use_wined3d",       "INTEGER DEFAULT 0"),
        ("use_wow64",         "INTEGER DEFAULT 0"),
        ("use_wayland",       "INTEGER DEFAULT 0"),
        ("no_esync",          "INTEGER DEFAULT 0"),
        ("no_fsync",          "INTEGER DEFAULT 0"),
        ("no_ntsync",         "INTEGER DEFAULT 0"),
        ("legacy_mediaconv",  "INTEGER DEFAULT 0"),
        ("video_decode_mode", "TEXT DEFAULT 'default'"),
        ("vn_jp_locale",      "INTEGER DEFAULT 0"),
        ("added_at",           "TEXT DEFAULT ''"),
        ("category_names",     "TEXT DEFAULT ''"),
    ]:
        if _pac not in pa_cols:
            con.execute(f"ALTER TABLE playtime_archive ADD COLUMN {_pac} {_padef}")
    # Migrate games to add prefix_path override if missing
    cur = con.execute("PRAGMA table_info(games)")
    existing_cols = {row[1] for row in cur.fetchall()}
    if "prefix_path" not in existing_cols:
        con.execute("ALTER TABLE games ADD COLUMN prefix_path TEXT DEFAULT ''")
    # Ludusavi save-backup: resolved manifest title override + last successful backup stamp
    if "ludusavi_title" not in existing_cols:
        con.execute("ALTER TABLE games ADD COLUMN ludusavi_title TEXT DEFAULT ''")
    if "last_backup" not in existing_cols:
        con.execute("ALTER TABLE games ADD COLUMN last_backup TEXT DEFAULT ''")
    # Absolute path to the ludusavi backup folder for this game (verified at
    # backup time). Lets the Save Backups card check the backup still exists
    # on disk instead of blindly trusting the last_backup timestamp.
    if "backup_location" not in existing_cols:
        con.execute("ALTER TABLE games ADD COLUMN backup_location TEXT DEFAULT ''")
    # GOG store ID (from goggame-<id>.info) — enables GOG-ID matching in ludusavi
    # find (more reliable than name) and lets the <storeGameId> placeholder resolve
    # for GOG games whose manifest save paths use it.
    if "gog_id" not in existing_cols:
        con.execute("ALTER TABLE games ADD COLUMN gog_id TEXT DEFAULT ''")
    if "backup_summary" not in existing_cols:
        con.execute("ALTER TABLE games ADD COLUMN backup_summary TEXT DEFAULT ''")
    if "last_auto_backup" not in existing_cols:
        con.execute("ALTER TABLE games ADD COLUMN last_auto_backup TEXT DEFAULT ''")
    if "auto_backup_summary" not in existing_cols:
        con.execute("ALTER TABLE games ADD COLUMN auto_backup_summary TEXT DEFAULT ''")
    if "renpy_save_dir" not in existing_cols:
        con.execute("ALTER TABLE games ADD COLUMN renpy_save_dir TEXT DEFAULT ''")

    # Steam stale-flag cleanup: NAGO doesn't own the Steam launch lifetime, so
    # hdr_enabled/gamescope_enabled/upscale_enabled can never take effect for
    # Steam-type games. Older builds let these flags leak in when a user
    # switched a saved Proton/native game to Steam. Clear them in-place once at
    # startup — cheap, idempotent, fixes existing DBs without manual editing.
    con.execute("""
        UPDATE games
        SET hdr_enabled = 0,
            gamescope_enabled = 0,
            upscale_enabled = 0
        WHERE game_type = 'steam'
          AND (hdr_enabled = 1 OR gamescope_enabled = 1 OR upscale_enabled = 1)
    """)

    # Migrate game_categories to add sort_pos if missing
    cur = con.execute("PRAGMA table_info(game_categories)")
    gc_cols = {row[1] for row in cur.fetchall()}
    if "sort_pos" not in gc_cols:
        con.execute("ALTER TABLE game_categories ADD COLUMN sort_pos INTEGER DEFAULT 0")
    con.commit()
    con.close()

    # Clean up orphaned temp covers (slug_0.png) left by crashes during Add/Edit Game.
    # These are pending covers that were never committed because NAGO didn't exit cleanly.
    if ART_PATH.exists():
        referenced = set()
        try:
            c = sqlite3.connect(DB_PATH)
            for row in c.execute("SELECT cover_path FROM games WHERE cover_path != ''"):
                if row[0]:
                    referenced.add(row[0])
            c.close()
        except Exception as e:
            _NAGOLog.session(f"[warn] init_db: failed to query referenced covers: {e}")
        for f in ART_PATH.glob("*_0.*"):
            if str(f) not in referenced:
                try:
                    f.unlink()
                except Exception as e:
                    _NAGOLog.session(f"[warn] init_db: failed to remove orphan cover {f.name}: {e}")

    # Playtime archive — survives game deletion, keyed by exe filename + game type
def db_con():
    """Open and return a SQLite connection to the NAGO database.
    Caller is responsible for calling con.close() when done."""
    return sqlite3.connect(DB_PATH)

def load_config():
    """Load config from disk. Result is cached — call save_config() to persist
    changes, which also invalidates the cache so the next call re-reads."""
    global _config_cache
    if _config_cache is not None:
        return dict(_config_cache)  # return a copy so callers can't mutate the cache
    CFG_PATH.parent.mkdir(parents=True, exist_ok=True)
    if CFG_PATH.exists():
        with open(CFG_PATH) as f:
            _config_cache = json.load(f)
    else:
        _config_cache = {
            "sgdb_key": "", "steam_api_key": "", "default_proton": "",
            "umu_default_enabled": True, "global_env": "",
            "accent_color": DEFAULT_ACCENT, "card_width": 185,
        }
    return dict(_config_cache)

def save_config(cfg: dict):
    """Persist config to disk and update the in-memory cache."""
    global _config_cache
    CFG_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(CFG_PATH, "w") as f:
        json.dump(cfg, f, indent=2)
    _config_cache = dict(cfg)  # update cache to match what was written

# ── Steam playtime helpers ─────────────────────────────────────────────────────
def steam_playtime_for_appid(appid: str, api_key: str) -> int:
    """
    Return playtime in minutes for the given Steam appid via the Steam Web API.
    Returns 0 if no key is provided, the game is not found, or any error occurs.
    """
    api_key = (api_key or "").strip()
    if not api_key:
        return 0
    userid = _get_local_steam_userid()
    if not userid:
        return 0
    try:
        url = "https://api.steampowered.com/IPlayerService/GetOwnedGames/v1/"
        params = {
            "key":                       api_key,
            "steamid":                   userid,
            "include_played_free_games": 1,
            "appids_filter[0]":          appid,
            "format":                    "json",
        }
        resp = _requests().get(url, params=params, timeout=8)
        resp.raise_for_status()
        data = resp.json()
        games = data.get("response", {}).get("games", [])
        for g in games:
            if str(g.get("appid", "")) == str(appid):
                return int(g.get("playtime_forever", 0))
        return 0
    except Exception as e:
        _NAGOLog.session(f"[warn] steam_playtime_for_appid({appid}): {e}")
        return 0


def _get_local_steam_userid() -> str:
    """
    Resolve the Steam64 ID of the locally-logged-in Steam user by reading
    loginusers.vdf. This file is written by all Steam clients (native, Flatpak,
    and snap) at install time and updated on every login — it's login metadata,
    not playtime, so it's still available offline.

    Returns the SteamID of the most recently used account, or empty string if
    Steam isn't installed locally. Note: Steam's Web API doesn't expose any way
    to resolve a user without already knowing their SteamID, so this disk-based
    lookup is the only practical option.
    """
    for candidate in (
        Path.home() / ".steam" / "steam" / "config" / "loginusers.vdf",
        XDG_DATA / "Steam" / "config" / "loginusers.vdf",
        Path.home() / ".var" / "app" / "com.valvesoftware.Steam" / "data" / "Steam" / "config" / "loginusers.vdf",
    ):
        if not candidate.exists():
            continue
        try:
            text = candidate.read_text(errors="replace")
        except OSError:
            continue
        # Simple line-by-line scan — we only need the numeric steam id keys
        # and the mostrecent flag; no need for a full VDF parser.
        last_id = ""
        current_id = ""
        for line in text.splitlines():
            line = line.strip().strip('"')
            if line.isdigit() and len(line) > 10:
                current_id = line
                last_id = line
            if line == "1" and current_id:
                # mostrecent "1" — this is the active user
                return current_id
        if last_id:
            return last_id
    return ""

def steam_bulk_playtime_fetch(api_key: str) -> dict:
    """
    Fetch playtime for every game in the user's Steam library in one API call.
    Returns {str(appid): int(minutes_forever)}.
    Returns {} on any error or if no API key is provided.
    Only used at startup to avoid N individual API calls.
    """
    api_key = (api_key or "").strip()
    if not api_key:
        return {}
    userid = _get_local_steam_userid()
    if not userid:
        return {}
    try:
        url = "https://api.steampowered.com/IPlayerService/GetOwnedGames/v1/"
        params = {
            "key":                       api_key,
            "steamid":                   userid,
            "include_played_free_games": 1,
            "format":                    "json",
        }
        resp = _requests().get(url, params=params, timeout=12)
        resp.raise_for_status()
        data = resp.json()
        games = data.get("response", {}).get("games", [])
        return {str(g["appid"]): int(g.get("playtime_forever", 0)) for g in games}
    except Exception as e:
        _NAGOLog.session(f"[warn] steam_bulk_playtime_fetch: {e}")
        return {}


def format_playtime(minutes: int) -> str:
    """Convert total minutes to '86h 23m', '45m', or '' for zero."""
    if not minutes or minutes <= 0:
        return ""
    h, m = divmod(int(minutes), 60)
    if h > 0:
        return f"{h}h {m:02d}m"
    return f"{m}m"




# ──────────────────────────────────────────────────────────────────────────────

def db_get_categories() -> list[dict]:
    con = db_con()
    try:
        cur = con.execute("SELECT id, name FROM categories ORDER BY sort_pos, name COLLATE NOCASE")
        return [{"id": r[0], "name": r[1]} for r in cur.fetchall()]
    finally:
        con.close()

def db_add_category(name: str) -> int:
    con = db_con()
    try:
        cur = con.execute("INSERT INTO categories (name, sort_pos) VALUES (?, (SELECT COALESCE(MAX(sort_pos),0)+1 FROM categories))", (name,))
        cid = cur.lastrowid
        con.commit()
        return cid
    finally:
        con.close()

def db_rename_category(cid: int, name: str):
    con = db_con()
    try:
        con.execute("UPDATE categories SET name=? WHERE id=?", (name, cid))
        con.commit()
    finally:
        con.close()

def db_delete_category(cid: int):
    con = db_con()
    try:
        con.execute("DELETE FROM categories WHERE id=?", (cid,))
        con.commit()
    finally:
        con.close()

def db_get_game_categories(game_id: int) -> list[int]:
    con = db_con()
    try:
        cur = con.execute("SELECT category_id FROM game_categories WHERE game_id=?", (game_id,))
        return [r[0] for r in cur.fetchall()]
    finally:
        con.close()

def db_set_game_categories(game_id: int, category_ids: list[int]):
    con = db_con()
    try:
        con.execute("DELETE FROM game_categories WHERE game_id=?", (game_id,))
        for cid in category_ids:
            con.execute("""
                INSERT OR IGNORE INTO game_categories (game_id, category_id, sort_pos)
                VALUES (?, ?, (SELECT COALESCE(MAX(sort_pos),0)+1 FROM game_categories WHERE category_id=?))
            """, (game_id, cid, cid))
        con.commit()
    finally:
        con.close()

# ── SteamGridDB Worker ─────────────────────────────────────────────────────────
class SGDBWorker(_NAGOThread):
    _log_lifecycle   = False             # fires on every search keystroke — too noisy
    results_ready    = pyqtSignal(list)      # list of {id, name, url, thumb}
    covers_ready     = pyqtSignal(list)      # list of {url, thumb, style, mood}
    error            = pyqtSignal(str)
    cover_downloaded = pyqtSignal(int, str)  # game_id, local_path

    def __init__(self, api_key: str):
        super().__init__()
        self.api_key        = api_key
        self._mode          = None
        self._query         = None
        self._game_id       = None
        self._cover_url     = None
        self._local_game_id = None
        self._game_name     = ""

    def _headers(self):
        key = self.api_key.strip().strip('"').strip("'")
        return {"Authorization": f"Bearer {key}"}

    def _search_url(self, query: str) -> str:
        return f"https://www.steamgriddb.com/api/v2/search/autocomplete/{_requests().utils.quote(query.strip())}"

    @staticmethod
    def _slugify(name: str) -> str:
        """Turn 'Kingdom Come: Deliverance II' into 'Kingdom_Come_Deliverance_II'."""
        return slugify(name, fallback="cover")

    def search_game(self, query: str):
        self._mode  = "search"
        self._query = query
        self.start()

    def fetch_covers(self, sgdb_game_id: int):
        self._mode    = "covers"
        self._game_id = sgdb_game_id
        self.start()

    def download_cover(self, cover_url: str, local_game_id: int, game_name: str = ""):
        self._mode          = "download"
        self._cover_url     = cover_url
        self._local_game_id = local_game_id
        self._game_name     = game_name
        self.start()

    def run(self):
        try:
            if self._mode == "search":
                if not self.api_key:
                    self.error.emit("No API key set — add your SteamGridDB key in Settings.")
                    return
                url = self._search_url(self._query)
                r = _requests().get(url, headers=self._headers(), timeout=10)
                if r.status_code == 401:
                    self.error.emit("Invalid API key — check your SteamGridDB key in Settings.")
                    return
                if r.status_code == 403:
                    self.error.emit("API key forbidden — make sure it has read access on SteamGridDB.")
                    return
                if r.status_code == 404:
                    self.error.emit("No games found matching that name.")
                    return
                if not r.text.strip():
                    self.error.emit(f"Empty response from SteamGridDB (HTTP {r.status_code}).")
                    return
                data = r.json()
                if data.get("success"):
                    self.results_ready.emit(data.get("data", []))
                else:
                    self.error.emit((data.get("errors") or ["Unknown error"])[0])

            elif self._mode == "covers":
                r = _requests().get(
                    f"https://www.steamgriddb.com/api/v2/grids/game/{self._game_id}",
                    params={"dimensions": "600x900,342x482", "limit": 50},
                    headers=self._headers(), timeout=10
                )
                if r.status_code == 401:
                    self.error.emit("Invalid API key — check your SteamGridDB key in Settings.")
                    return
                if not r.text.strip():
                    self.error.emit(f"Empty response from SteamGridDB (HTTP {r.status_code}).")
                    return
                data = r.json()
                if data.get("success"):
                    covers = []
                    for item in data.get("data", []):
                        covers.append({
                            "url":   item.get("url", ""),
                            "thumb": item.get("thumb", item.get("url", "")),
                            "style": item.get("style", ""),
                            "mood":  item.get("mood", ""),
                            "width": item.get("width", 0),
                            "height": item.get("height", 0),
                        })
                    self.covers_ready.emit(covers)
                else:
                    self.error.emit("No covers found for this game.")

            elif self._mode == "download":
                r = _requests().get(self._cover_url, timeout=30)
                r.raise_for_status()
                if not r.content:
                    self.error.emit("Cover download failed — server returned an empty file.")
                    return
                img = _pil_image().open(io.BytesIO(r.content)).convert("RGBA")
                slug = self._slugify(self._game_name)
                # Suffix with the game id so covers stay unique even if two games share a name
                # PNG is lossless — no compression artifacts softening the cover at display size.
                filename = f"{slug}_{self._local_game_id}.png"
                out_path = ART_PATH / filename
                img.save(str(out_path), "PNG")
                self.cover_downloaded.emit(self._local_game_id, str(out_path))

        except Exception as e:
            self.error.emit(str(e))

# ── Cover thumbnail loader ─────────────────────────────────────────────────────
class ThumbnailWorker(_NAGOThread):
    _log_lifecycle = False  # spawns frequently during library load — too noisy
    loaded = pyqtSignal(int, QPixmap)   # game_id, pixmap

    def __init__(self, tasks: list):    # [(game_id, path)]
        super().__init__()
        self.tasks = tasks

    def run(self):
        for gid, path in self.tasks:
            try:
                px = QPixmap(path)
                if not px.isNull():
                    # Don't scale here — the worker can't query devicePixelRatio of a widget.
                    # Pass the original through; set_cover() does the HiDPI-aware scaling.
                    self.loaded.emit(gid, px)
            except Exception as e:
                _NAGOLog.session(f"[warn] ThumbnailWorker: failed to load cover for game {gid}: {e}")

# ── Sidebar Resize Handle ─────────────────────────────────────────────────────
class _SidebarHandle(QWidget):
    """Thin drag handle on the right edge of the sidebar.
    Updates sidebar.setFixedWidth in real time while dragging.
    MainWindow persists the final width on close.
    """
    _MIN_W = 180
    _MAX_W = 320

    def __init__(self, sidebar: QWidget, parent=None):
        super().__init__(parent)
        self._sidebar = sidebar
        self._dragging = False
        self._drag_start_x = 0
        self._drag_start_w = 0
        self.setFixedWidth(6)
        self.setCursor(Qt.CursorShape.SizeHorCursor)
        self.setMouseTracking(True)
        self.setAttribute(Qt.WidgetAttribute.WA_Hover, True)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._dragging = True
            self._drag_start_x = event.globalPosition().toPoint().x()
            self._drag_start_w = self._sidebar.width()
            event.accept()

    def mouseMoveEvent(self, event):
        if self._dragging:
            delta = event.globalPosition().toPoint().x() - self._drag_start_x
            new_w = max(self._MIN_W, min(self._MAX_W, self._drag_start_w + delta))
            self._sidebar.setFixedWidth(new_w)
            event.accept()

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._dragging = False
            event.accept()


# ── Category Drop Container ───────────────────────────────────────────────────
class _CatDropContainer(QWidget):
    """The sidebar VBox that holds all DraggableCategoryButton widgets.
    Owns all drop logic for category reordering — buttons are source-only.
    Draws an insertion-line indicator while a drag is active.

    Auto-scrolls the enclosing QScrollArea when the cursor approaches the
    top/bottom edge during a drag, so dropping into off-screen positions is
    possible without first scrolling manually.
    """

    reorder_requested = pyqtSignal(int, int)  # (src_cat_id, target_cat_id_or_-1)

    MIME = "application/x-nago-category-id"

    # Auto-scroll tuning.  EDGE is how close (in viewport pixels) the cursor
    # must be to the top/bottom edge of the scroll area to trigger scrolling.
    # STEP is the per-tick scroll delta; INTERVAL is the timer period in ms.
    # The values give a smooth ~120px/sec scroll without feeling laggy.
    _AUTOSCROLL_EDGE_PX = 28
    _AUTOSCROLL_STEP_PX = 6
    _AUTOSCROLL_INTERVAL_MS = 30

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAcceptDrops(True)
        self._drag_insert_idx: int | None = None
        # The source button's own cat_id while a drag is active, so we can
        # detect "hovering over a self-gap" and dim the indicator instead of
        # showing a misleading drop target.
        self._drag_src_id: int | None = None
        self._accent_color: str = "#6366f1"
        # Auto-scroll state during drag.
        self._autoscroll_timer = QTimer(self)
        self._autoscroll_timer.setInterval(self._AUTOSCROLL_INTERVAL_MS)
        self._autoscroll_timer.timeout.connect(self._on_autoscroll_tick)
        self._autoscroll_dir: int = 0  # -1 = up, 0 = idle, +1 = down

    def set_accent(self, color: str):
        self._accent_color = color

    def _buttons(self) -> list:
        """Return DraggableCategoryButton children in layout order.
        Uses `not isHidden()` rather than `isVisible()` so freshly-added
        buttons that haven't been painted yet still register — `isVisible()`
        returns False until the first paint, which can race with drop events
        during a rebuild."""
        lyt = self.layout()
        if lyt is None:
            return []
        result = []
        for i in range(lyt.count()):
            it = lyt.itemAt(i)
            w = it.widget() if it else None
            if w and isinstance(w, DraggableCategoryButton) and not w.isHidden():
                result.append(w)
        return result

    def _scroll_area(self) -> QScrollArea | None:
        """Walk up the parent chain to find the enclosing QScrollArea (or None
        if this container isn't inside one).  Cached on first call."""
        if hasattr(self, "_cached_scroll_area"):
            return self._cached_scroll_area
        p = self.parentWidget()
        while p is not None:
            if isinstance(p, QScrollArea):
                self._cached_scroll_area = p
                return p
            p = p.parentWidget()
        self._cached_scroll_area = None
        return None

    def _is_self_gap(self, insert_idx: int) -> bool:
        """True if dropping at insert_idx would be a no-op because the gap is
        immediately above or immediately below the source button itself."""
        if self._drag_src_id is None:
            return False
        btns = self._buttons()
        n = len(btns)
        if n == 0:
            return False
        # Find the source's current position.
        src_pos = next((i for i, b in enumerate(btns) if b.cat_id == self._drag_src_id), -1)
        if src_pos < 0:
            return False
        # The gap *above* src (insert_idx == src_pos) and the gap *below* src
        # (insert_idx == src_pos + 1) both resolve to the same position.
        return insert_idx == src_pos or insert_idx == src_pos + 1

    def _insert_idx_for_pos(self, pos) -> int:
        """Return insertion index based on Y position among buttons."""
        btns = self._buttons()
        n = len(btns)
        if n == 0:
            return 0
        py = pos.y()
        for i, btn in enumerate(btns):
            mid = btn.geometry().center().y()
            if py < mid:
                return i
        return n

    def _indicator_y(self, insert_idx: int) -> int:
        """Y coordinate (top of gap) for the insertion indicator."""
        btns = self._buttons()
        n = len(btns)
        if n == 0:
            return self.layout().contentsMargins().top() if self.layout() else 0
        if insert_idx >= n:
            return btns[-1].geometry().bottom() + 2
        geo = btns[insert_idx].geometry()
        if insert_idx == 0:
            return geo.top() - 2
        prev_geo = btns[insert_idx - 1].geometry()
        return (prev_geo.bottom() + geo.top()) // 2

    # ── Auto-scroll during drag ───────────────────────────────────────────────

    def _update_autoscroll(self, event_pos):
        """Decide whether to be scrolling up/down based on the cursor's
        proximity to the viewport edges.  Called from dragMoveEvent."""
        sa = self._scroll_area()
        if sa is None:
            self._stop_autoscroll()
            return
        vp = sa.viewport()
        # Translate the event position (in container coords) to viewport coords.
        global_pt = self.mapToGlobal(event_pos.toPoint() if hasattr(event_pos, "toPoint") else event_pos)
        local_in_vp = vp.mapFromGlobal(global_pt)
        y = local_in_vp.y()
        h = vp.height()
        edge = self._AUTOSCROLL_EDGE_PX
        if y < edge and y >= 0:
            self._start_autoscroll(-1)
        elif y > h - edge and y <= h:
            self._start_autoscroll(+1)
        else:
            self._stop_autoscroll()

    def _start_autoscroll(self, direction: int):
        if self._autoscroll_dir == direction:
            return
        self._autoscroll_dir = direction
        if not self._autoscroll_timer.isActive():
            self._autoscroll_timer.start()

    def _stop_autoscroll(self):
        if self._autoscroll_dir != 0:
            self._autoscroll_dir = 0
        if self._autoscroll_timer.isActive():
            self._autoscroll_timer.stop()

    def _on_autoscroll_tick(self):
        sa = self._scroll_area()
        if sa is None or self._autoscroll_dir == 0:
            self._stop_autoscroll()
            return
        bar = sa.verticalScrollBar()
        bar.setValue(bar.value() + self._autoscroll_dir * self._AUTOSCROLL_STEP_PX)
        # Re-evaluate the insertion index — the buttons under the cursor have
        # moved, so the gap our indicator points at must move with them.
        self.update()

    # ── Drag events ───────────────────────────────────────────────────────────

    def dragEnterEvent(self, event):
        if event.mimeData().hasFormat(self.MIME):
            event.acceptProposedAction()
            # Cache the source id so _is_self_gap can dim the indicator while
            # hovering over no-op positions.
            try:
                self._drag_src_id = int(bytes(event.mimeData().data(self.MIME)).decode())
            except Exception:
                self._drag_src_id = None
            self._drag_insert_idx = self._insert_idx_for_pos(event.position())
            self.update()
        else:
            event.ignore()

    def dragMoveEvent(self, event):
        if event.mimeData().hasFormat(self.MIME):
            event.acceptProposedAction()
            new_idx = self._insert_idx_for_pos(event.position())
            if new_idx != self._drag_insert_idx:
                self._drag_insert_idx = new_idx
                self.update()
            self._update_autoscroll(event.position())
        else:
            event.ignore()

    def dragLeaveEvent(self, event):
        self._drag_insert_idx = None
        self._drag_src_id = None
        self._stop_autoscroll()
        self.update()
        super().dragLeaveEvent(event)

    def dropEvent(self, event):
        self._drag_insert_idx = None
        self._stop_autoscroll()
        self.update()
        if not event.mimeData().hasFormat(self.MIME):
            self._drag_src_id = None
            return event.ignore()
        try:
            src_id = int(bytes(event.mimeData().data(self.MIME)).decode())
        except Exception:
            self._drag_src_id = None
            return event.ignore()
        insert_idx = self._insert_idx_for_pos(event.position())
        btns = self._buttons()
        n = len(btns)
        # Resolve insert_idx (a *gap* index, 0..n) to a target_id (the button
        # that the source should land just before).  target_id == -1 means
        # "append at end".
        #
        # The elif fallback handles the "dropped onto own gap" case: if the
        # candidate at insert_idx IS the source itself, we point at the next
        # button instead.  _reorder_categories then computes a no-op move,
        # which is the correct behavior — the user dropped where the source
        # already was.
        target_id = -1
        if insert_idx < n:
            candidate = btns[insert_idx]
            if candidate.cat_id != src_id:
                target_id = candidate.cat_id
            elif insert_idx + 1 < n:
                target_id = btns[insert_idx + 1].cat_id
        event.acceptProposedAction()
        self._drag_src_id = None
        self.reorder_requested.emit(src_id, target_id)

    def paintEvent(self, event):
        super().paintEvent(event)
        if self._drag_insert_idx is None:
            return
        y = self._indicator_y(self._drag_insert_idx)
        lm = self.layout().contentsMargins().left() if self.layout() else 4
        rm = self.layout().contentsMargins().right() if self.layout() else 4
        # Inset the pill from the column walls so it reads as a floating
        # indicator rather than something glued to the edges.
        side_inset = 8
        x1 = lm + side_inset
        x2 = self.width() - rm - side_inset
        if x2 <= x1:
            return
        # Pill geometry: thin, centered on y.  Halo is a softer, larger pill
        # behind it for a subtle glow without the harsh line cap of QPen.
        pill_h = 2
        halo_h = 6
        pill_rect = QRectF(x1, y - pill_h / 2, x2 - x1, pill_h)
        halo_rect = QRectF(x1 - 4, y - halo_h / 2, (x2 - x1) + 8, halo_h)

        # Dim the indicator when hovering over a self-gap (drop = no-op) so the
        # user gets feedback that they're at the source's current position.
        dim = self._is_self_gap(self._drag_insert_idx)
        accent = QColor(self._accent_color)
        halo = QColor(self._accent_color)
        if dim:
            accent.setAlpha(90)
            halo.setAlpha(18)
        else:
            accent.setAlpha(255)
            halo.setAlpha(55)

        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setPen(Qt.PenStyle.NoPen)
        # Halo first, then pill on top.
        p.setBrush(QBrush(halo))
        p.drawRoundedRect(halo_rect, halo_h / 2, halo_h / 2)
        p.setBrush(QBrush(accent))
        p.drawRoundedRect(pill_rect, pill_h / 2, pill_h / 2)
        p.end()


# ── Draggable Category Button ──────────────────────────────────────────────────
class DraggableCategoryButton(QPushButton):
    """A category sidebar button that initiates a drag to reorder.
    Drop logic lives entirely in _CatDropContainer — this widget is drag-source only.

    Keyboard: emits delete_requested / rename_requested when the button has
    keyboard focus and Delete or F2 is pressed.  Scoping to focused-button-only
    (rather than to the active category) means the user must have explicitly
    interacted with the button — protecting against accidental destructive
    actions while the user is elsewhere in the UI.
    """

    MIME = "application/x-nago-category-id"

    delete_requested = pyqtSignal(int)  # cat_id
    rename_requested = pyqtSignal(int)  # cat_id

    def __init__(self, text: str, cat_id: int, parent=None):
        super().__init__(text, parent)
        self.cat_id = cat_id
        self._drag_start_pos: QPoint | None = None

    def keyPressEvent(self, event):
        # Only fire when focus is on this button; QShortcut would be global,
        # which is not what we want for a destructive action.
        k = event.key()
        if k == Qt.Key.Key_Delete:
            self.delete_requested.emit(self.cat_id)
            event.accept()
            return
        if k == Qt.Key.Key_F2:
            self.rename_requested.emit(self.cat_id)
            event.accept()
            return
        super().keyPressEvent(event)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._drag_start_pos = event.pos()
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if not (event.buttons() & Qt.MouseButton.LeftButton):
            return super().mouseMoveEvent(event)
        if self._drag_start_pos is None:
            return super().mouseMoveEvent(event)
        if (event.pos() - self._drag_start_pos).manhattanLength() < QApplication.startDragDistance():
            return super().mouseMoveEvent(event)
        drag = QDrag(self)
        mime = QMimeData()
        mime.setData(self.MIME, str(self.cat_id).encode("utf-8"))
        drag.setMimeData(mime)
        snap = self.grab()
        # Match canvas DPR to snap so HiDPI screens get a crisp preview.
        preview = QPixmap(snap.size())
        preview.setDevicePixelRatio(snap.devicePixelRatioF())
        preview.fill(Qt.GlobalColor.transparent)
        p = QPainter(preview)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)
        p.setOpacity(0.88)
        p.drawPixmap(0, 0, snap)
        p.end()
        drag.setPixmap(preview)
        drag.setHotSpot(self._drag_start_pos)
        drag.exec(Qt.DropAction.MoveAction)
        self._drag_start_pos = None


# ── Game Card Widget ───────────────────────────────────────────────────────────
class _CardHoverOverlay(QWidget):
    """Transparent overlay widget that draws the accent hover outline and a
    centered play button over the cover area.  Clicking the play button (or
    anywhere inside the play circle) immediately emits play_clicked so the
    game launches without waiting for Qt's double-click timer."""

    play_clicked = pyqtSignal()

    # Radius of the play-button circle as a fraction of cover width.
    _BTN_RATIO = 0.15

    def __init__(self, accent_color: str, parent=None):
        super().__init__(parent)
        self._accent_color = accent_color
        # Do NOT set WA_TransparentForMouseEvents — we need clicks on the
        # play button.  The cover area below the meta strip is where the
        # button lives; clicks outside that circle fall through via ignore().
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)
        self.setAutoFillBackground(False)
        self.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        self._btn_rect = QRect()   # updated in paintEvent
        self._is_running = False
        self._play_visible = True
        self._btn_hovered = False  # True when cursor is inside the play circle
        self.setMouseTracking(True)

    def set_accent(self, color: str):
        self._accent_color = color
        self.update()

    def set_play_visible(self, visible: bool):
        """Show or hide the play button (controlled by Settings)."""
        self._play_visible = visible
        self.update()

    def set_running(self, running: bool):
        """When the game is running, suppress the play button."""
        self._is_running = running
        self._btn_hovered = False
        self.update()

    def hideEvent(self, event):
        """Reset hover state when the overlay is hidden (mouse left the card)."""
        self._btn_hovered = False
        super().hideEvent(event)

    def fade_in(self):
        """Show overlay."""
        self.show()

    def fade_out(self):
        """Hide overlay."""
        self.hide()

    def _cover_h(self) -> int:
        """Height of the cover — full card height, no strip."""
        return self.height()

    def _btn_center(self) -> QPoint:
        return QPoint(self.width() // 2, self._cover_h() // 2)

    def _btn_radius(self) -> int:
        return max(18, int(self.width() * self._BTN_RATIO))

    def mouseMoveEvent(self, event):
        r = self._btn_radius()
        delta = event.pos() - self._btn_center()
        inside = (delta.x() ** 2 + delta.y() ** 2) <= r ** 2
        if inside != self._btn_hovered:
            self._btn_hovered = inside
            self.update()
        event.ignore()

    def mousePressEvent(self, event):
        # Right-click: set the context-menu-open flag on the parent card so
        # paintEvent draws the tint immediately, then ignore so the event
        # propagates to GameCard.contextMenuEvent.
        if event.button() == Qt.MouseButton.RightButton:
            card = self.parent()
            if card is not None:
                card._context_menu_open = True
                self.show()
                self.setWindowOpacity(1.0)
                self.repaint()   # synchronous — must flush before exec() blocks
            event.ignore()
            return
        # Accept press inside the circle to prevent it falling through to drag,
        # but don't launch yet — wait for release.
        if event.button() == Qt.MouseButton.LeftButton and not self._is_running and self._play_visible:
            r = self._btn_radius()
            delta = event.pos() - self._btn_center()
            if delta.x() ** 2 + delta.y() ** 2 <= r ** 2:
                event.accept()
                return
        event.ignore()

    def mouseReleaseEvent(self, event):
        # Only launch if the button was released inside the circle —
        # dragging away from the circle cancels the action.
        if event.button() == Qt.MouseButton.LeftButton and not self._is_running and self._play_visible:
            r = self._btn_radius()
            delta = event.pos() - self._btn_center()
            if delta.x() ** 2 + delta.y() ** 2 <= r ** 2:
                self.play_clicked.emit()
                event.accept()
                return
        event.ignore()

    def paintEvent(self, event):
        if self.width() <= 0 or self.height() <= 0:
            return
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setClipRect(self.rect())

        # ── Context-menu tint + boosted outline ─────────────────────────────
        card = self.parent()
        ctx_open = getattr(card, "_context_menu_open", False)
        if ctx_open:
            accent_tint = QColor(self._accent_color)
            accent_tint.setAlpha(50)
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QBrush(accent_tint))
            p.drawRoundedRect(self.rect(), CARD_RADIUS, CARD_RADIUS)

        # ── Accent outline ────────────────────────────────────────────────
        # Pen is 3px normally; boosted to 5px while context menu is open.
        # Drawn centered on the rect edge — inset by 1px so stroke sits just
        # inside the card border. Radius reduced by 1 to match the visual corner.
        outline_w = 5 if ctx_open else 3
        pen = QPen(QColor(self._accent_color), outline_w)
        pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
        p.setPen(pen)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawRoundedRect(self.rect().adjusted(1, 1, -1, -1), CARD_RADIUS - 1, CARD_RADIUS - 1)

        # ── Play button (suppressed while game is running or hidden by settings) ──
        if self._is_running or not self._play_visible:
            p.end()
            return
        cx = self.width() // 2
        cy = (self._cover_h() - 70) // 2 + 30
        r  = self._btn_radius()

        hovered = self._btn_hovered
        accent  = QColor(self._accent_color)

        # Circle background — solid accent fill on hover, dark otherwise
        p.setPen(Qt.PenStyle.NoPen)
        if hovered:
            bg = QColor(accent)
            bg.setAlpha(220)
        else:
            bg = QColor(0, 0, 0, 200)
        p.setBrush(QBrush(bg))
        p.drawEllipse(QPoint(cx, cy), r, r)

        # Ring — white on hover (contrasts against accent fill), accent otherwise
        if hovered:
            ring_color = QColor(255, 255, 255, 160)
        else:
            ring_color = QColor(accent)
            ring_color.setAlpha(200)
        ring_pen = QPen(ring_color, 1.5)
        p.setPen(ring_pen)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawEllipse(QPoint(cx, cy), r, r)

        # Play triangle — white always, slightly larger on hover
        tri_size = max(6, int(r * 0.42 * (1.15 if hovered else 1.0)))
        tx = cx - tri_size // 2
        ty = cy
        triangle = QPainterPath()
        triangle.moveTo(tx,                   ty - tri_size)
        triangle.lineTo(tx + tri_size * 1.55, ty)
        triangle.lineTo(tx,                   ty + tri_size)
        triangle.closeSubpath()
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(QColor(255, 255, 255, 255)))
        p.drawPath(triangle)

        p.end()


class GameCard(QFrame):
    launch_requested       = pyqtSignal(dict)
    edit_requested         = pyqtSignal(dict)
    delete_requested       = pyqtSignal(int)
    delete_prefix_requested= pyqtSignal(dict)
    cover_requested        = pyqtSignal(dict)
    categories_requested   = pyqtSignal(dict)
    show_log_requested     = pyqtSignal(dict)
    hide_requested         = pyqtSignal(dict)   # (game dict) — toggle hidden state
    force_terminate_requested = pyqtSignal(dict)
    run_in_prefix_requested   = pyqtSignal(dict)   # (game dict) — right-click "Run File in Prefix"
    stop_prefix_run_requested = pyqtSignal(dict)   # (game dict) — right-click "Stop Run in Prefix"

    def __init__(self, game: dict, accent_color: str = DEFAULT_ACCENT, parent=None):
        super().__init__(parent)
        self.game = game
        self._accent_color = accent_color
        self.setObjectName("gameCard")
        self.setFixedSize(CARD_W, CARD_H)
        self.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        # Clip all child widget painting to the card's rounded outline.
        # QSS border-radius only affects the frame's own background paint —
        # it doesn't clip children. setMask() creates a real pixel-level clip
        # that applies to everything rendered inside the widget.
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, False)
        self._build()
        # Shadow is painted by _LibraryGrid.paintEvent using a cached
        # Pillow-generated Gaussian pixmap — no per-card graphics effect.

        # Transparent overlay raised above all children — draws the hover outline
        # and play button on top of the cover image without affecting layout.
        self._hover_overlay = _CardHoverOverlay(self._accent_color, self)
        self._hover_overlay.setGeometry(0, 0, CARD_W, CARD_H)
        self._hover_overlay.hide()
        self._hover_overlay.raise_()
        # Hover delay timer — shows play button after 300ms
        self._hover_timer = QTimer(self)
        self._hover_timer.setSingleShot(True)
        self._hover_timer.timeout.connect(
            lambda: self._hover_overlay.set_play_visible(self._play_button_enabled)
        )
        self._hover_overlay.play_clicked.connect(
            lambda: self.launch_requested.emit(self.game)
        )
        # Respect the "show play button" setting — read from config at card creation.
        # Updated live via update_play_button() when settings change.
        self._play_button_enabled = bool(load_config().get("show_play_button", True))

        # True while the right-click context menu is open — used by the hover
        # overlay to hold the accent outline + tint even though leaveEvent fires
        # when the menu takes focus.
        self._context_menu_open = False

    def resizeEvent(self, event):
        super().resizeEvent(event)
        w = self.width()
        h = self.height()
        LABEL_H = 64
        LABEL_BOTTOM_OFFSET = 8
        if hasattr(self, '_name_label'):
            self._name_label.setGeometry(4, h - LABEL_H - LABEL_BOTTOM_OFFSET, w - 8, LABEL_H)
        if hasattr(self, '_playtime_label'):
            self._playtime_label.move(w - self._playtime_label.width() - 7, 7)
        if hasattr(self, '_hover_overlay') and self._hover_overlay.width() > 0:
            self._hover_overlay.setGeometry(0, 0, w, h)

    def update_accent(self, accent_color: str):
        self._accent_color = accent_color
        self._hover_overlay.set_accent(accent_color)
        if not self._has_cover:
            self._set_placeholder()

    def update_play_button(self, visible: bool):
        """Enable or disable the play button on this card."""
        self._play_button_enabled = visible

    def enterEvent(self, event):
        self._hover_overlay.set_play_visible(False)
        self._hover_overlay.fade_in()
        self._hover_timer.start(300)
        super().enterEvent(event)

    def leaveEvent(self, event):
        self._hover_timer.stop()
        self._hover_overlay.set_play_visible(False)
        # Do not hide the overlay while the context menu is open — the menu
        # opening causes Qt to send leaveEvent which would kill the tint.
        if not self._context_menu_open:
            self._hover_overlay.fade_out()
        super().leaveEvent(event)

    def _build(self):
        # ── No QLayout — the card is a fixed canvas ───────────────────────
        # Cover pixmap is stored and drawn in paintEvent directly.
        # All child widgets are positioned absolutely with move()/setGeometry().
        # Nothing participates in a layout so card size never shifts.

        self._cover_pixmap: QPixmap | None = None
        self._has_cover = False
        self._cover_w = CARD_W
        self._cover_h = COVER_H

        # ── Title label — inside cover, bottom-aligned over gradient ────────
        STRIP_H = 44
        LABEL_H = 64
        LABEL_BOTTOM_OFFSET = 8
        self._name_label = QLabel(self.game["name"], self)
        self._name_label.setWordWrap(True)
        self._name_label.setAlignment(Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignBottom)
        self._name_label.setObjectName("cardNameLabel")
        # Geometry deferred to resizeEvent — card may be resized after _build (dialog cover)
        self._name_label.setGeometry(4, COVER_H - LABEL_H - LABEL_BOTTOM_OFFSET, CARD_W - 8, LABEL_H)

        # ── Running indicator — top-left ─────────────────────────────────
        self.is_running = False
        self.is_prefix_running = False   # True while this card's Run File in Prefix is active
        self._running_dot = QLabel("● Running", self)
        self._running_dot.setObjectName("runningDot")
        self._running_dot.adjustSize()
        self._running_dot.move(7, 7)
        self._running_dot.hide()

        # ── Auto-backup pill — same position as running dot (appears after exit) ─
        self._backup_pill = QLabel("", self)
        self._backup_pill.setWordWrap(False)
        self._backup_pill.adjustSize()
        self._backup_pill.move(7, 7)
        self._backup_pill.hide()

        # ── Playtime badge — top-right ────────────────────────────────────
        pt_minutes = self.game.get("playtime_minutes") or 0
        pt_text = format_playtime(pt_minutes)
        self._playtime_label = QLabel(self)
        self._playtime_label.setTextFormat(Qt.TextFormat.RichText)
        self._playtime_label.setObjectName("playtimeBadge")
        self._set_playtime_text(pt_text)
        self._playtime_label.adjustSize()
        self._playtime_label.move(
            CARD_W - self._playtime_label.width() - 7,
            7,
        )
        self._playtime_label.setVisible(bool(pt_text))

        # Build placeholder cover
        self._set_placeholder()

    def _set_playtime_text(self, text: str):
        """Set playtime label with a small clock icon prefix using Phosphor font."""
        ph_fam = _ph_family()
        clock_char = chr(PH["clock"])
        if ph_fam and text:
            self._playtime_label.setText(
                f"<span style='font-family:{ph_fam}; font-size:11px;'>{clock_char}</span>"
                f"<span style='font-size:12px;'> {text}</span>"
            )
        else:
            self._playtime_label.setText(text)

    def update_playtime(self, minutes: int):
        """Refresh the playtime badge on the cover without a full reload."""
        self.game["playtime_minutes"] = minutes
        text = format_playtime(minutes)
        self._set_playtime_text(text)
        self._playtime_label.adjustSize()
        self._playtime_label.move(
            self._cover_w - self._playtime_label.width() - 7,
            7,
        )
        self._playtime_label.setVisible(bool(text))

    def update_game_data(self, d: dict):
        """Update card metadata in-place after an edit — no rebuild, no flash."""
        self.game.update(d)
        self._name_label.setText(d.get("name", self.game.get("name", "")))

    def _set_placeholder(self, all_corners: bool = False, size: tuple = None):
        # Render at physical pixels — same DPR logic as set_cover.
        screen = self.screen() or QApplication.primaryScreen()
        dpr    = screen.devicePixelRatio() if screen else 1.0
        if size:
            pw = max(1, round(size[0] * dpr))
            ph = max(1, round(size[1] * dpr))
        else:
            pw = max(1, round(self._cover_w * dpr))
            ph = max(1, round(self._cover_h * dpr))

        base = QPixmap(pw, ph)
        base.fill(Qt.GlobalColor.transparent)
        p = QPainter(base)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing)

        # Background gradient — adapts to current theme
        _is_light = _current_theme() == "light"
        grad = QLinearGradient(0, 0, 0, ph)
        if _is_light:
            grad.setColorAt(0.0, QColor("#e8e8ec"))
            grad.setColorAt(1.0, QColor("#dcdce0"))
        else:
            grad.setColorAt(0.0, QColor("#2a2a30"))
            grad.setColorAt(1.0, QColor("#222227"))
        p.setBrush(QBrush(grad))
        p.setPen(Qt.PenStyle.NoPen)
        p.drawRect(0, 0, pw, ph)

        # Game initials — up to 2 chars, centered
        name = self.game.get("name", "")
        words = name.split()
        if len(words) >= 2:
            initials = (words[0][0] + words[1][0]).upper()
        elif words:
            initials = words[0][:2].upper()
        else:
            initials = "?"

        font_size = max(12, int(pw * 0.28))
        font = QFont("Segoe UI", font_size)
        font.setWeight(QFont.Weight.Bold)
        p.setFont(font)
        p.setPen(QColor("#c4c4cf") if _is_light else QColor("#3a3a42"))
        fm = QFontMetrics(font)
        tw = fm.horizontalAdvance(initials)
        th = fm.height()
        p.drawText((pw - tw) // 2, (ph - th) // 2 + fm.ascent(), initials)

        # Subtle accent line at bottom
        accent = self._accent_color
        line_h = max(2, int(ph * 0.018))
        grad2 = QLinearGradient(0, 0, pw, 0)
        grad2.setColorAt(0.0, Qt.GlobalColor.transparent)
        grad2.setColorAt(0.4, QColor(accent))
        grad2.setColorAt(0.6, QColor(accent))
        grad2.setColorAt(1.0, Qt.GlobalColor.transparent)
        p.setBrush(QBrush(grad2))
        p.setPen(Qt.PenStyle.NoPen)
        p.drawRect(0, ph - line_h, pw, line_h)

        p.end()

        # Round corners — top only for library cards, all 4 for dialog covers
        r = COVER_RADIUS * dpr
        rounded = QPixmap(pw, ph)
        rounded.fill(Qt.GlobalColor.transparent)
        rp = QPainter(rounded)
        rp.setRenderHint(QPainter.RenderHint.Antialiasing)
        clip = QPainterPath()
        if all_corners:
            clip.moveTo(r, 0)
            clip.lineTo(pw - r, 0)
            clip.arcTo(pw - r*2, 0,         r*2, r*2,  90, -90)
            clip.lineTo(pw, ph - r)
            clip.arcTo(pw - r*2, ph - r*2,  r*2, r*2,   0, -90)
            clip.lineTo(r, ph)
            clip.arcTo(0,         ph - r*2,  r*2, r*2, 270, -90)
            clip.lineTo(0, r)
            clip.arcTo(0,         0,          r*2, r*2, 180, -90)
        else:
            clip.moveTo(r, 0)
            clip.lineTo(pw - r, 0)
            clip.arcTo(pw - r * 2, 0, r * 2, r * 2, 90, -90)
            clip.lineTo(pw, ph)
            clip.lineTo(0, ph)
            clip.arcTo(0, 0, r * 2, r * 2, 180, -90)
        clip.closeSubpath()
        rp.setClipPath(clip)
        rp.drawPixmap(0, 0, base)
        rp.end()
        rounded.setDevicePixelRatio(dpr)
        self._cover_pixmap = rounded
        self.update()

    def set_cover(self, pixmap: QPixmap):
        cw, ch = self._cover_w, self._cover_h

        # Use the label's actual rendered pixel size as the scale target.
        # round(logical * dpr) can land on a fractional logical size at non-integer
        # DPR (e.g. 1.25x: 171 * 1.25 = 213.75 → 214px → 171.2 logical), which
        # forces Qt to nudge a sub-pixel and introduces softness.
        # cover_label.devicePixelRatio() is what Qt actually uses to map this
        # pixmap back to the screen — always consistent with the physical slot.
        screen = self.screen() or QApplication.primaryScreen()
        dpr = screen.devicePixelRatio() if screen else 1.0
        pw = max(1, round(self._cover_w * dpr))
        ph = max(1, round(self._cover_h * dpr))

        # Normalise incoming pixmap to DPR=1 so width()/height() are true pixels.
        src = QPixmap(pixmap)
        src.setDevicePixelRatio(1.0)
        raw_w = int(pixmap.width()  / (pixmap.devicePixelRatioF() or 1.0))
        raw_h = int(pixmap.height() / (pixmap.devicePixelRatioF() or 1.0))
        if raw_w != src.width() or raw_h != src.height():
            src = src.scaled(raw_w, raw_h,
                             Qt.AspectRatioMode.IgnoreAspectRatio,
                             Qt.TransformationMode.SmoothTransformation)

        # Two-pass downscale to physical target: halve first when source is >2×
        # the target in either dimension, then hit the exact physical size.
        # KeepAspectRatioByExpanding = scale until the card is fully covered,
        # then center-crop the overflow. Correct for any input aspect ratio:
        # 2:3 SteamGridDB covers fit exactly with no crop; VNDB covers with
        # different ratios lose only their edges rather than getting stretched.
        if src.width() > pw * 2 or src.height() > ph * 2:
            src = src.scaled(max(pw, src.width() // 2),
                             max(ph, src.height() // 2),
                             Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                             Qt.TransformationMode.SmoothTransformation)
        result = src.scaled(pw, ph,
                            Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                            Qt.TransformationMode.SmoothTransformation)
        # Center-crop any overflow from the expand
        if result.width() > pw or result.height() > ph:
            x = (result.width()  - pw) // 2
            y = (result.height() - ph) // 2
            result = result.copy(x, y, pw, ph)

        # Round top corners only — radius scales with COVER_RADIUS and DPR.
        r = COVER_RADIUS * dpr
        rounded = QPixmap(pw, ph)
        rounded.fill(Qt.GlobalColor.transparent)
        rp = QPainter(rounded)
        rp.setRenderHint(QPainter.RenderHint.Antialiasing)
        clip = QPainterPath()
        clip.moveTo(r, 0)
        clip.lineTo(pw - r, 0)
        clip.arcTo(pw - r * 2, 0, r * 2, r * 2, 90, -90)
        clip.lineTo(pw, ph)
        clip.lineTo(0, ph)
        clip.arcTo(0, 0, r * 2, r * 2, 180, -90)
        clip.closeSubpath()
        rp.setClipPath(clip)
        rp.drawPixmap(0, 0, result)
        rp.end()

        # Tell Qt this pixmap is DPR-scaled — displays at logical cw×ch.
        rounded.setDevicePixelRatio(dpr)
        self._has_cover = True
        self._cover_pixmap = rounded
        self.update()

    def paintEvent(self, event):
        """Draw the card background and cover image directly — no QLabel involved."""
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.SmoothPixmapTransform)

        w = self.width()
        h = self.height()
        r = CARD_RADIUS

        # ── Clip everything to the rounded card shape ─────────────────────
        clip = QPainterPath()
        clip.addRoundedRect(0, 0, w, h, r, r)
        p.setClipPath(clip)

        # ── Card background ───────────────────────────────────────────────
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(QColor(_t("#2a2a30", "#f0f0f4"))))
        p.drawRoundedRect(QRectF(0, 0, w, h), r, r)

        # ── Cover image ───────────────────────────────────────────────────
        if self._cover_pixmap:
            p.drawPixmap(QRect(1, 1, self._cover_w - 2, self._cover_h - 1), self._cover_pixmap)

        # ── Cover gradient — dark scrim over bottom of cover for name legibility ──
        if not getattr(self, '_no_gradient', False):
            _grad_h = min(70, self._cover_h)
            _grad_y = self._cover_h - _grad_h
            _cg = QLinearGradient(0, _grad_y, 0, self._cover_h)
            _cg.setColorAt(0.0, QColor(0, 0, 0, 0))
            _cg.setColorAt(0.5, QColor(0, 0, 0, 170))
            _cg.setColorAt(1.0, QColor(0, 0, 0, 255))
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QBrush(_cg))
            p.drawRect(QRect(1, _grad_y, self._cover_w - 2, _grad_h))

        # ── Bottom strip (only when card is taller than cover area) ───────
        strip_h = h - self._cover_h
        if strip_h > 0:
            p.setBrush(QBrush(QColor(_t("#2a2a30", "#f0f0f4"))))
            p.setPen(Qt.PenStyle.NoPen)
            p.drawRect(QRect(0, self._cover_h, w, strip_h))

        # ── Border ────────────────────────────────────────────────────────
        pen = QPen(QColor(_t("#3d3d44", "#d4d4d8")), 1.5)
        pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
        p.setPen(pen)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawRoundedRect(QRectF(1, 1, w - 2, h - 2), r, r)

        p.end()

    def show_backup_pill(self, state: str) -> None:
        """
        Show the auto-backup result pill on the card.
        state: 'running' | 'success' | 'failed'
        Auto-dismisses after 2s (success) or 3s (failed).
        """
        _STYLES = {
            "running": ("Backing up…",   "rgba(10,25,45,0.92)",  "rgba(59,130,246,0.45)",  "#93c5fd"),
            "success": ("Saved ✓",       "rgba(15,35,20,0.92)",  "rgba(34,197,94,0.45)",   "#4ade80"),
            "failed":  ("Backup failed", "rgba(45,10,10,0.92)",  "rgba(239,68,68,0.45)",   "#f87171"),
        }
        text, bg, border, color = _STYLES.get(state, _STYLES["running"])
        self._backup_pill.setText(text)
        self._backup_pill.setStyleSheet(
            f"font-size:12px; font-weight:700; padding:4px 9px; border-radius:6px;"
            f"background:{bg}; border:1px solid {border}; color:{color};"
        )
        self._backup_pill.adjustSize()
        self._backup_pill.move(7, 7)
        self._backup_pill.show()
        self._backup_pill.raise_()
        delay = {"success": 3000, "failed": 5000}.get(state, 0)
        if delay:
            QTimer.singleShot(delay, self._backup_pill.hide)

    def set_running(self, running: bool):
        """Show or hide the green 'Running' badge; hide playtime while running."""
        self.is_running = running
        if running:
            self._backup_pill.hide()   # clear any leftover backup pill on relaunch
            self._running_dot.show()
            self._running_dot.raise_()
            self._playtime_label.hide()
        else:
            self._running_dot.hide()
            # Only restore playtime if there's something to show
            if format_playtime(self.game.get("playtime_minutes") or 0):
                self._playtime_label.show()
        # Play button should not appear while the game is already running
        self._hover_overlay.set_running(running)

    def set_prefix_running(self, running: bool):
        """Flip the flag the context menu reads to swap 'Run File in Prefix'
        for 'Stop Run in Prefix'. No badge/visual change on the card itself —
        unlike the main game running state, this is a quick background
        install/tool run, not something worth a persistent on-card
        indicator."""
        self.is_prefix_running = running

    def mouseDoubleClickEvent(self, event):
        if self.is_running:
            return
        self.launch_requested.emit(self.game)

    def contextMenuEvent(self, event):
        menu = QMenu(self)
        menu.setWindowFlags(menu.windowFlags()
                            | Qt.WindowType.FramelessWindowHint
                            | Qt.WindowType.NoDropShadowWindowHint)
        menu.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        menu.setStyleSheet(_menu_stylesheet())

        _running = self.is_running

        launch_act, launch_row = _make_menu_row(menu, "play-circle",   "Launch",        disabled=_running)
        menu.addAction(launch_act)
        force_term_act = None
        if _running:
            force_term_act, force_term_row = _make_menu_row(menu, "x-circle", "Force Terminate")
            menu.addAction(force_term_act)
        menu.addSeparator()
        edit_act,   edit_row   = _make_menu_row(menu, "pencil-simple", "Edit",           disabled=_running)
        menu.addAction(edit_act)
        cover_act,  cover_row  = _make_menu_row(menu, "image",         "Get Cover Art")
        menu.addAction(cover_act)
        cat_act,    cat_row    = _make_menu_row(menu, "tag",            "Assign Categories")
        menu.addAction(cat_act)
        log_act,    log_row    = _make_menu_row(menu, "scroll",         "Show Log")
        menu.addAction(log_act)
        menu.addSeparator()
        _is_hidden = bool(self.game.get("hidden", 0))
        hide_label = "Unhide" if _is_hidden else "Hide"
        hide_icon  = "eye"    if _is_hidden else "eye-slash"
        hide_act,   hide_row   = _make_menu_row(menu, hide_icon, hide_label)
        menu.addAction(hide_act)
        menu.addSeparator()
        del_act,    del_row    = _make_menu_row(menu, "trash",          "Remove",         disabled=_running)
        menu.addAction(del_act)

        # Open Saves Backup — only shown when a backup folder exists on disk.
        open_bk_act = None
        _bk_title = (self.game.get("ludusavi_title") or self.game.get("name") or "").strip()
        _manual_bk = LUDUSAVI_MANUAL_BACKUPS / _ludusavi_sanitize_title(_bk_title) if _bk_title else None
        _auto_bk   = LUDUSAVI_AUTO_BACKUPS   / _ludusavi_sanitize_title(_bk_title) if _bk_title else None
        _bk_folder = None
        _manual_ok = bool(_manual_bk and _manual_bk.is_dir() and (_manual_bk / "mapping.yaml").exists())
        _auto_ok   = bool(_auto_bk   and _auto_bk.is_dir()   and (_auto_bk   / "mapping.yaml").exists())
        if _manual_ok and _auto_ok:
            _bk_folder = LUDUSAVI_BACKUPS          # both present — open root so both visible
        elif _manual_ok:
            _bk_folder = _manual_bk
        elif _auto_ok:
            _bk_folder = _auto_bk.parent           # _auto/ root

        # Open Game Folder — all game types
        _game_folder = _resolve_game_folder(self.game)
        open_folder_act = None

        # Resolve prefix now so we know whether to include it in the folder group
        _gt = self.game.get("game_type", "native")
        open_pfx_act = None
        del_pfx_act  = None
        _pfx         = None
        if _gt in ("proton", "gog"):
            _pfx_override = (self.game.get("prefix_path") or "").strip()
            if _pfx_override and Path(_pfx_override).exists():
                _pfx = Path(_pfx_override)
            else:
                if _pfx_override and not Path(_pfx_override).exists():
                    try:
                        _con = db_con()
                        _con.execute("UPDATE games SET prefix_path='' WHERE id=?",
                                     (self.game["id"],))
                        _con.commit()
                        _con.close()
                        self.game["prefix_path"] = ""
                    except Exception as e:
                        _NAGOLog.session(f"[warn] contextMenuEvent: failed to clear stale prefix_path for game {self.game.get('id')}: {e}")
                _slug    = slugify(self.game.get("name", ""))
                _gid     = self.game["id"]
                _derived = get_prefixes_root() / f"{_slug}_{_gid}"
                if _derived.exists():
                    _pfx = _derived
                else:
                    _root = get_prefixes_root()
                    _prefix = f"{_slug}_"
                    _matches = [p for p in (_root.iterdir() if _root.exists() else [])
                                if p.is_dir() and p.name.startswith(_prefix)]
                    if len(_matches) == 1:
                        _pfx = _matches[0]
                        try:
                            _con = db_con()
                            _con.execute("UPDATE games SET prefix_path=? WHERE id=?",
                                         (str(_pfx), _gid))
                            _con.commit()
                            _con.close()
                            self.game["prefix_path"] = str(_pfx)
                        except Exception as e:
                            _NAGOLog.session(f"[warn] contextMenuEvent: failed to persist prefix_path for game {_gid}: {e}")

        # One separator for the whole folder group
        _has_folder_group = bool(_bk_folder) or bool(_game_folder) or _gt in ("proton", "gog")
        if _has_folder_group:
            menu.addSeparator()

        if _game_folder:
            open_folder_act, _ = _make_menu_row(menu, "folder-open", "Open Game Folder")
            menu.addAction(open_folder_act)

        if _bk_folder:
            open_bk_act, _ = _make_menu_row(menu, "floppy-disk", "Open Saves Backup")
            menu.addAction(open_bk_act)

        # Prefix-tools sub-group: Run File in Prefix is shown for any
        # proton/gog game regardless of whether the prefix exists yet —
        # umu bootstraps it on first run, same as it would on a normal
        # launch. Open/Delete Prefix still require one to already exist.
        # Single row that swaps label+icon to Stop while a run is active,
        # rather than a second always-visible row (no extra information is
        # conveyed by keeping a disabled "Run" row visible underneath an
        # active "Stop" one).
        run_pfx_act = None
        if _gt in ("proton", "gog"):
            if _game_folder or _bk_folder:
                menu.addSeparator()
            if self.is_prefix_running:
                run_pfx_act, run_pfx_row = _make_menu_row(menu, "x-circle", "Stop Run in Prefix")
            else:
                run_pfx_act, run_pfx_row = _make_menu_row(menu, "file-archive", "Run File in Prefix")
            menu.addAction(run_pfx_act)
            if _pfx and _pfx.exists():
                open_pfx_act, open_pfx_row = _make_menu_row(menu, "app-window", "Open Prefix")
                menu.addAction(open_pfx_act)
                del_pfx_act, del_pfx_row = _make_menu_row(menu, "x", "Delete Prefix", disabled=_running)
                menu.addAction(del_pfx_act)

        # Show accent outline + tint while the menu is open.
        # Two entry paths:
        # 1) Overlay was visible (hover) — overlay.mousePressEvent already set
        #    the flag and called update(); nothing more needed here.
        # 2) Overlay was hidden (no prior hover) — right-click went straight to
        #    GameCard, so we must show/update the overlay ourselves.
        if not self._context_menu_open:
            self._context_menu_open = True
            self._hover_overlay.show()
            self._hover_overlay.setWindowOpacity(1.0)
            self._hover_overlay.repaint()   # repaint() flushes synchronously before exec()

        action = menu.exec(event.globalPos())

        self._context_menu_open = False
        # If the cursor is still over the card, enterEvent won't re-fire —
        # restore the hover state manually; otherwise hide the overlay.
        if self.underMouse():
            self._hover_overlay.fade_in()
        else:
            self._hover_overlay.fade_out()

        if action == launch_act and not _running:
            self.launch_requested.emit(self.game)
        elif force_term_act and action == force_term_act:
            self.force_terminate_requested.emit(self.game)
        elif action == cover_act:
            self.cover_requested.emit(self.game)
        elif action == cat_act:
            self.categories_requested.emit(self.game)
        elif action == edit_act and not _running:
            self.edit_requested.emit(self.game)
        elif action == log_act:
            self.show_log_requested.emit(self.game)
        elif action == hide_act:
            self.hide_requested.emit(self.game)
        elif action == del_act and not _running:
            self.delete_requested.emit(self.game["id"])
        elif open_folder_act and action == open_folder_act:
            subprocess.Popen(["xdg-open", _game_folder])
        elif open_bk_act and action == open_bk_act:
            subprocess.Popen(["xdg-open", str(_bk_folder)])
        elif run_pfx_act and action == run_pfx_act:
            if self.is_prefix_running:
                self.stop_prefix_run_requested.emit(self.game)
            else:
                self.run_in_prefix_requested.emit(self.game)
        elif open_pfx_act and action == open_pfx_act:
            subprocess.Popen(["xdg-open", str(_pfx)])
        elif del_pfx_act and action == del_pfx_act and not _running:
            self.delete_prefix_requested.emit(self.game)


def _menu_stylesheet() -> str:
    """Return the QMenu stylesheet for the current theme."""
    bg  = _t("#2a2a30", "#ffffff")
    bdr = _t("#424248", "#d4d4d8")
    sep = _t("#3a3a42", "#e0e0e4")
    return (
        f"QMenu {{ background: {bg}; border: 1px solid {bdr}; border-radius: 8px; padding: 4px; }}"
        f"QMenu::item {{ height: 0px; padding: 0px; }}"
        f"QMenu::separator {{ background: {sep}; height: 1px; margin: 4px 10px; }}"
    )


def _make_menu_row(menu: "QMenu", icon_name: str, label: str, disabled: bool = False):
    """Build a QWidgetAction with a Phosphor icon + text row for custom context menus.
    Returns (QWidgetAction, row_widget). Bypasses Qt/KDE icon column sizing.
    Pass disabled=True to render the row dimmed and non-interactive."""
    from PyQt6.QtWidgets import QWidgetAction
    row = QWidget()
    row.setObjectName("menuRow")
    _hover_bg  = _t("#3d3d42", "#f0f0f4")
    _text_col  = _t("#f4f4f5", "#18181b")  if not disabled else _t("#505058", "#a1a1aa")
    _icon_col  = _t("#a1a1aa", "#71717a")  if not disabled else _t("#3d3d44", "#c4c4cf")
    row.setStyleSheet(f"""
        QWidget#menuRow {{
            background: transparent; border-radius: 4px;
            padding: 0px;
        }}
        QWidget#menuRow:hover {{ background: {'transparent' if disabled else _hover_bg}; }}
    """)
    if disabled:
        row.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
    hl = QHBoxLayout(row)
    hl.setContentsMargins(10, 7, 18, 7)
    hl.setSpacing(10)
    ico = ph_label(icon_name, 16, _icon_col)
    ico.setFixedSize(20, 20)
    txt = QLabel(label)
    if not disabled:
        txt.setObjectName("menuRowText")
    else:
        txt.setStyleSheet(f"color: {_text_col}; background: transparent;")
    txt.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents, True)
    hl.addWidget(ico)
    hl.addWidget(txt)
    hl.addStretch()
    wa = QWidgetAction(menu)
    wa.setDefaultWidget(row)
    return wa, row


# ── Combo separator delegate ───────────────────────────────────────────────────
# Qt's QAbstractItemView::separator QSS rule is unreliable on Linux — the style
# engine often ignores it entirely. This delegate draws separators manually.
# ── Custom ComboBox with styled popup ─────────────────────────────────────────
class _NAGOComboPopup(QFrame):
    """Floating popup for NAGOComboBox — rounded, dark, matches option-C mockup."""
    item_selected = pyqtSignal(int)  # model row index

    _SHADOW = 8  # shadow radius in pixels

    def __init__(self, combo: "NAGOComboBox"):
        super().__init__(combo.window(), Qt.WindowType.Popup)
        self._combo = combo
        self.setObjectName("nagoComboPopup")
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        s = self._SHADOW
        lyt = QVBoxLayout(self)
        lyt.setContentsMargins(s, s + 2, s, s)
        lyt.setSpacing(0)
        self._rows: list[QWidget] = []
        self._build()

    def paintEvent(self, event):
        s = self._SHADOW
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        # Draw layered shadow rings
        rect = QRectF(self.rect()).adjusted(s, s, -s, -s)
        for i in range(s, 0, -1):
            alpha = int(55 * (1 - i / s) ** 2)
            shadow_rect = rect.adjusted(-i, -i, i, i)
            shadow_path = QPainterPath()
            shadow_path.addRoundedRect(shadow_rect, 10 + i * 0.5, 10 + i * 0.5)
            painter.fillPath(shadow_path, QColor(0, 0, 0, alpha))
        # Draw main background
        path = QPainterPath()
        path.addRoundedRect(rect, 10, 10)
        painter.fillPath(path, QColor(_t("#2a2a30", "#ffffff")))
        painter.setPen(QPen(QColor(_t("#3d3d43", "#d4d4d8")), 1))
        painter.drawPath(path)
        painter.end()

    def _build(self):
        combo = self._combo
        model = combo.model()
        accent = QApplication.instance().property("nagoAccent") or "#4ade80"
        self._focusable: list[int] = []  # model rows that are selectable
        for row in range(model.rowCount()):
            idx = model.index(row, 0)
            is_sep = idx.data(Qt.ItemDataRole.AccessibleDescriptionRole) == "separator"
            if is_sep:
                sep = QFrame()
                sep.setFixedHeight(9)
                sep.setObjectName("transparentBg")
                line = QFrame(sep)
                line.setFrameShape(QFrame.Shape.HLine)
                line.setObjectName("comboSepLine")
                line.setGeometry(8, 4, 9999, 1)
                self.layout().addWidget(sep)
                self._rows.append(None)
            else:
                text = idx.data(Qt.ItemDataRole.DisplayRole) or ""
                is_cur = (row == combo.currentIndex())
                is_disabled = not (model.flags(idx) & Qt.ItemFlag.ItemIsEnabled)
                item = QLabel(text)
                item.setContentsMargins(12, 7, 12, 7)
                item.setFixedHeight(34)
                if is_disabled:
                    item.setObjectName("comboItemDisabled")
                elif is_cur:
                    item.setObjectName("comboItemCurrent")
                    item.setStyleSheet(f"color: {accent}; font-size: 13px; background: transparent;")
                else:
                    item.setObjectName("comboItemNormal")
                item.setProperty("row", row)
                item.setProperty("disabled", is_disabled)
                item.installEventFilter(self)
                self.layout().addWidget(item)
                self._rows.append(item)
                if not is_disabled:
                    self._focusable.append(row)

        # keyboard cursor starts at current index
        cur = combo.currentIndex()
        self._kbd_row = cur if cur in self._focusable else (self._focusable[0] if self._focusable else -1)

    def _set_kbd_highlight(self, row: int):
        """Move keyboard highlight to the given row."""
        accent = QApplication.instance().property("nagoAccent") or "#4ade80"
        for item in self._rows:
            if item is None:
                continue
            r = item.property("row")
            is_cur = (r == self._combo.currentIndex())
            is_kbd = (r == row)
            if is_kbd:
                item.setStyleSheet(f"color: {_t('#e4e4e7', '#18181b') if not is_cur else accent}; font-size: 13px; background: {_t('#3d3d42', '#e8e8ec')}; border-radius: 6px; margin: 0 4px;")
            else:
                col = accent if is_cur else _t('#e4e4e7', '#18181b')
                item.setStyleSheet(f"color: {col}; font-size: 13px; background: transparent; border-radius: 0; margin: 0;")
        self._kbd_row = row

    def eventFilter(self, obj, event):
        if event.type() == QEvent.Type.Enter and not obj.property("disabled"):
            row = obj.property("row")
            self._set_kbd_highlight(row)
        elif event.type() == QEvent.Type.Leave and not obj.property("disabled"):
            row = obj.property("row")
            accent = QApplication.instance().property("nagoAccent") or "#4ade80"
            is_cur = (row == self._combo.currentIndex())
            col = accent if is_cur else _t("#e4e4e7", "#18181b")
            obj.setStyleSheet(f"color: {col}; font-size: 13px; background: transparent; border-radius: 0; margin: 0;")
        elif event.type() == QEvent.Type.MouseButtonPress and not obj.property("disabled"):
            self.item_selected.emit(obj.property("row"))
            self.hide()
        return False

    def keyPressEvent(self, event):
        key = event.key()
        if key == Qt.Key.Key_Escape:
            self.hide()
        elif key in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
            if self._kbd_row >= 0:
                self.item_selected.emit(self._kbd_row)
            self.hide()
        elif key == Qt.Key.Key_Down:
            idx = self._focusable.index(self._kbd_row) if self._kbd_row in self._focusable else -1
            if idx < len(self._focusable) - 1:
                self._set_kbd_highlight(self._focusable[idx + 1])
        elif key == Qt.Key.Key_Up:
            idx = self._focusable.index(self._kbd_row) if self._kbd_row in self._focusable else len(self._focusable)
            if idx > 0:
                self._set_kbd_highlight(self._focusable[idx - 1])
        else:
            super().keyPressEvent(event)

    def showUnder(self, combo: "NAGOComboBox"):
        s = self._SHADOW
        gpos = combo.mapToGlobal(combo.rect().bottomLeft())
        self.setFixedWidth(combo.width() + s * 2)
        self.adjustSize()
        self.move(gpos.x() - s, gpos.y() - s + 2)
        self.show()
        self.raise_()
        # Scroll kbd highlight into view
        if self._kbd_row >= 0 and self._kbd_row < len(self._rows):
            item = self._rows[self._kbd_row]
            if item:
                self._set_kbd_highlight(self._kbd_row)

    def wheelEvent(self, event):
        if not self._focusable:
            return
        idx = self._focusable.index(self._kbd_row) if self._kbd_row in self._focusable else 0
        if event.angleDelta().y() < 0 and idx < len(self._focusable) - 1:
            self._set_kbd_highlight(self._focusable[idx + 1])
        elif event.angleDelta().y() > 0 and idx > 0:
            self._set_kbd_highlight(self._focusable[idx - 1])


class _AdaptiveStack(QStackedWidget):
    """QStackedWidget that sizes to the current page only.
    The default implementation returns the maximum sizeHint across all pages,
    which leaves a gap when switching from a tall page (Import) to a short one
    (Native/Proton). Overriding sizeHint and minimumSizeHint to use the current
    page's hint fixes the layout jump without any external coordination."""
    def sizeHint(self):
        w = self.currentWidget()
        return w.sizeHint() if w else super().sizeHint()

    def minimumSizeHint(self):
        w = self.currentWidget()
        return w.minimumSizeHint() if w else super().minimumSizeHint()


class NAGOComboBox(QComboBox):

    """Drop-in QComboBox replacement with a fully styled custom popup."""
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("dlgCombo")
        self._popup: _NAGOComboPopup | None = None

    def paintEvent(self, event):
        super().paintEvent(event)
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        # Divider line before drop zone
        x = self.width() - 28
        painter.setPen(QPen(QColor("#333338"), 1))
        painter.drawLine(x, 6, x, self.height() - 6)
        # Chevron: two lines forming a V
        cx = x + 14
        cy = self.height() // 2
        painter.setPen(QPen(QColor("#6b6b75"), 1.5,
                            Qt.PenStyle.SolidLine,
                            Qt.PenCapStyle.RoundCap,
                            Qt.PenJoinStyle.RoundJoin))
        path = QPainterPath()
        path.moveTo(cx - 4, cy - 2)
        path.lineTo(cx,     cy + 2)
        path.lineTo(cx + 4, cy - 2)
        painter.drawPath(path)
        painter.end()

    def showPopup(self):
        if self._popup:
            self._popup.hide()
            self._popup.deleteLater()
        self._popup = _NAGOComboPopup(self)
        self._popup.item_selected.connect(self._on_item_selected)
        self._popup.showUnder(self)

    def hidePopup(self):
        if self._popup:
            self._popup.hide()
        super().hidePopup()

    def _on_item_selected(self, row: int):
        if self.itemData(row) is None:  # separator — skip
            return
        self.setCurrentIndex(row)



class ComboSeparatorDelegate(QStyledItemDelegate):
    SEP_HEIGHT = 9
    LINE_COLOR = QColor("#3a3a42")

    def paint(self, painter, option, index):
        if index.data(Qt.ItemDataRole.AccessibleDescriptionRole) == "separator":
            painter.save()
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, False)
            painter.fillRect(option.rect, QColor(_t("#141417", "#f8f8fa")))
            y = option.rect.center().y()
            x1 = option.rect.left()  + 10
            x2 = option.rect.right() - 10
            painter.setPen(QPen(self.LINE_COLOR, 1))
            painter.drawLine(x1, y, x2, y)
            painter.restore()
        else:
            super().paint(painter, option, index)

    def sizeHint(self, option, index):
        if index.data(Qt.ItemDataRole.AccessibleDescriptionRole) == "separator":
            from PyQt6.QtCore import QSize
            return QSize(0, self.SEP_HEIGHT)
        return super().sizeHint(option, index)


# ── Proton Selector Widget ─────────────────────────────────────────────────────
class ProtonComboBox(QWidget):
    """
    A combo box that lists auto-detected Proton installations,
    with a 'Custom…' option that reveals a manual path entry.

    horizontal=False (default, game dialog):
        Vertical layout — combo row on top, custom path row appears below
        when Custom is selected (show/hide).

    horizontal=True (settings):
        Single row — combo+rescan on the left half, custom path input+Browse
        always visible on the right half but dimmed/disabled unless Custom
        is selected. Hint label sits below the full row.

    Accepts optional extra_buttons (list of QPushButton) appended to the
    combo row (used by game dialog for Winecfg / Winetricks).
    """
    size_changed = pyqtSignal()  # fired when the visible content area shrinks/grows

    def __init__(self, current_path: str = "", extra_buttons: list = None,
                 horizontal: bool = False, config: dict = None, parent=None):
        super().__init__(parent)
        self._installs      = find_proton_installations()
        self._extra_buttons = extra_buttons or []
        self._horizontal    = horizontal
        self._config        = config  # used by _browse() to remember the last folder browsed
        self._build(current_path)

    def _build(self, current_path: str):
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(6)

        # ── Shared: combo box ─────────────────────────────────────────────────
        self.combo = NAGOComboBox()
        self.combo.setObjectName("dlgCombo")
        self._fill_combo(self._installs)

        # ── Shared: rescan button (icon + text in horizontal mode) ────────────
        rescan_btn = QPushButton()
        rescan_btn.setObjectName("secondary")
        rescan_btn.setToolTip("Rescan for Proton installations")
        rescan_btn.clicked.connect(self._rescan)
        if self._horizontal:
            rescan_btn.setIcon(ph_icon("atom", 22))
            rescan_btn.setText("  Rescan")
            rescan_btn.setFixedHeight(36)
        else:
            rescan_btn.setIcon(ph_icon("atom", 22))
            rescan_btn.setFixedSize(36, 36)

        # ── Shared: custom path widgets ───────────────────────────────────────
        self.custom_input = QLineEdit()
        self.custom_input.setObjectName("dlgInput")
        self.custom_input.setPlaceholderText("/path/to/proton")
        self._browse_btn = QPushButton("Browse")
        self._browse_btn.setObjectName("secondary")
        self._browse_btn.clicked.connect(self._browse)

        if self._horizontal:
            self.combo.setFixedWidth(280)
            main_row = QHBoxLayout()
            main_row.setContentsMargins(0, 0, 0, 0)
            main_row.setSpacing(8)

            # Left half: combo + rescan
            left = QHBoxLayout()
            left.setContentsMargins(0, 0, 0, 0)
            left.setSpacing(6)
            left.addWidget(self.combo)
            left.addWidget(rescan_btn)
            for btn in self._extra_buttons:
                left.addWidget(btn)

            # Right half: custom input + browse (always present, dim when inactive)
            right = QHBoxLayout()
            right.setContentsMargins(0, 0, 0, 0)
            right.setSpacing(6)
            right.addWidget(self.custom_input, 1)
            right.addWidget(self._browse_btn)

            # Wrap right side in a widget so we can opacity-effect the whole thing
            self._custom_side = QWidget()
            self._custom_side.setLayout(right)

            main_row.addLayout(left, 0)
            main_row.addWidget(self._custom_side, 1)
            layout.addLayout(main_row)

            # custom_widget alias kept for _set_current / _on_combo_change compat
            self.custom_widget = self._custom_side

        else:
            # ── Vertical layout (original, game dialog) ───────────────────────
            combo_row = QHBoxLayout()
            combo_row.setContentsMargins(0, 0, 0, 0)
            combo_row.setSpacing(6)
            combo_row.addWidget(self.combo, 1)
            combo_row.addWidget(rescan_btn)
            for btn in self._extra_buttons:
                combo_row.addWidget(btn)
            layout.addLayout(combo_row)

            self.custom_widget = QWidget()
            cw_layout = QHBoxLayout(self.custom_widget)
            cw_layout.setContentsMargins(0, 0, 0, 0)
            cw_layout.setSpacing(6)
            cw_layout.addWidget(self.custom_input)
            cw_layout.addWidget(self._browse_btn)
            self.custom_widget.setVisible(False)
            layout.addWidget(self.custom_widget)

        # ── Hint label (vertical mode only — horizontal mode uses a pill in the card header) ──
        count = len(self._installs)
        if not self._horizontal:
            self.hint_lbl = QLabel(
                f"Found {count} Proton installation{'s' if count != 1 else ''}." if count
                else "No Proton installations detected. Install Proton via Steam or use a custom path."
            )
            self.hint_lbl.setObjectName("coverHintLbl")
            layout.addWidget(self.hint_lbl)
        else:
            self.hint_lbl = None   # not shown; settings card owns the pill

        self.combo.currentIndexChanged.connect(self._on_combo_change)
        self._set_current(current_path)

    def _fill_combo(self, installs: list):
        """Populate self.combo from an installs list. Always ends with separator + Custom."""
        # Auto-managed options first — let umu resolve/download Proton instead of pinning
        # a path. UMU_DEFAULT_SENTINEL ("__umu_default__") means "set no PROTONPATH",
        # which umu treats as its UMU-Proton stable default (auto-downloaded if absent).
        # GE-Proton is umu's only real codename; it auto-fetches the latest GE build.
        # The sentinel is a distinct non-empty value on purpose: empty string is already
        # overloaded in the launch path's `or` fallthrough as "nothing selected → default",
        # so a literal "" here would let a game pinned to UMU-Proton fall through to the
        # global default. A truthy sentinel survives the `or` and is honoured.
        self.combo.addItem("UMU-Proton (auto · stable)", userData=UMU_DEFAULT_SENTINEL)
        self.combo.addItem("GE-Proton (auto · latest)",  userData="GE-Proton")
        self.combo.insertSeparator(self.combo.count())
        if installs:
            for inst in installs:
                self.combo.addItem(inst["label"], userData=inst["path"])
        else:
            self.combo.addItem("No Proton found — use Custom below", userData="")
        self.combo.insertSeparator(self.combo.count())
        self.combo.addItem("Custom path…", userData="__custom__")
        self.combo.setItemDelegate(ComboSeparatorDelegate(self.combo))

    def _set_custom_side_active(self, active: bool):
        """In horizontal mode: enable/disable and fade the custom path side."""
        if not self._horizontal:
            return
        self.custom_input.setEnabled(active)
        self._browse_btn.setEnabled(active)
        opacity = 1.0 if active else 0.3
        effect = QGraphicsOpacityEffect(self._custom_side)
        effect.setOpacity(opacity)
        self._custom_side.setGraphicsEffect(effect)

    def _set_current(self, path: str):
        was_visible = self.custom_widget.isVisible() if not self._horizontal else None
        if not path:
            # No saved Proton → select the "GE-Proton (auto · latest)" item, because an
            # empty/legacy value floors to GE-Proton at launch. Selecting index 0
            # (UMU-Proton) instead would make the UI claim UMU while launch used GE — a
            # display/behaviour mismatch. Find GE-Proton by userData rather than a magic
            # index so it survives reordering.
            idx = 0
            for i in range(self.combo.count()):
                if self.combo.itemData(i) == "GE-Proton":
                    idx = i
                    break
            if self.combo.count() > 0:
                self.combo.setCurrentIndex(idx)
            if self._horizontal:
                self._set_custom_side_active(False)
            else:
                self.custom_widget.setVisible(False)
        else:
            matched = False
            for i in range(self.combo.count()):
                if self.combo.itemData(i) == path:
                    self.combo.setCurrentIndex(i)
                    if self._horizontal:
                        self._set_custom_side_active(False)
                    else:
                        self.custom_widget.setVisible(False)
                    matched = True
                    break
            if not matched:
                self.combo.setCurrentIndex(self.combo.count() - 1)  # "Custom path…"
                self.custom_input.setText(path)
                if self._horizontal:
                    self._set_custom_side_active(True)
                else:
                    self.custom_widget.setVisible(True)
        if not self._horizontal and self.custom_widget.isVisible() != was_visible:
            self.size_changed.emit()

    def _on_combo_change(self, idx):
        if self.combo.itemData(idx) is None:
            self.combo.setCurrentIndex(idx + 1)
            return
        is_custom = self.combo.itemData(idx) == "__custom__"
        if self._horizontal:
            self._set_custom_side_active(is_custom)
        else:
            was_visible = self.custom_widget.isVisible()
            self.custom_widget.setVisible(is_custom)
            if is_custom != was_visible:
                self.size_changed.emit()

    def _browse(self):
        # Dedicated key, not the shared last_browse_dir — Proton installs
        # typically live in one consistent location separate from wherever
        # game exes/covers/installers were last browsed from, so sharing
        # the key would usually point this dialog somewhere unhelpful.
        #
        # Reads/writes config.json directly (load_config()/save_config())
        # rather than relying on self._config alone — self._config is only
        # ever flushed to disk when Settings' Save button runs, so a plain
        # in-place mutation here would survive for the rest of the running
        # process but be lost on the next launch. Same fix pattern already
        # used correctly by the cover-image picker's browse button.
        #
        # getOpenFileName, not getExistingDirectory — every other Browse
        # button in the app (exe, GOG exe, cover, Run in Prefix) uses the
        # file picker and all confirmed to remember their folder correctly
        # across a full app restart. The folder picker this used to use
        # apparently doesn't share that memory on KDE's native dialog —
        # folder-select and file-select are different native dialogs
        # under the hood, not just different arguments to the same one.
        # Selecting the proton binary directly is also strictly more
        # precise than the old approach, which picked a folder and then
        # guessed proton lived inside it.
        cfg = load_config()
        start_dir = cfg.get("last_proton_browse_dir", str(Path.home()))
        path, _ = QFileDialog.getOpenFileName(
            self.window(), "Select Proton Executable", start_dir
        )
        if not path:
            return
        cfg["last_proton_browse_dir"] = str(Path(path).parent)
        save_config(cfg)
        if self._config is not None:
            # Keep the live in-memory copy in sync too, so anything else in
            # this same session reading self._config sees the fresh value
            # without needing its own disk round-trip.
            self._config["last_proton_browse_dir"] = cfg["last_proton_browse_dir"]
        self.custom_input.setText(path)

    def _rescan(self):
        _invalidate_proton_cache()
        self._installs = find_proton_installations()
        current = self.selected_path()
        # Rebuild combo items (keep Custom at end)
        self.combo.blockSignals(True)
        self.combo.clear()
        self._fill_combo(self._installs)
        self.combo.blockSignals(False)
        count = len(self._installs)
        if self.hint_lbl is not None:
            self.hint_lbl.setText(
                f"Found {count} Proton installation{'s' if count != 1 else ''}." if count
                else "No Proton installations detected."
            )
        self.size_changed.emit()
        self._set_current(current)

    def selected_path(self) -> str:
        data = self.combo.currentData()
        if data == "__custom__" or data is None:
            return self.custom_input.text().strip()
        return data or ""


# ── umu options widget (used in GameDialog, inside the Proton card) ───────────────────
class UmuOptionsWidget(QWidget):
    """
    umu-launcher protonfix status row.
    Lives inside the Proton card in GameDialog (below the divider).
    umu is unconditional for all Proton games — no toggle.
    Store combo + match pill are always shown when this widget is visible.
    """
    state_changed = pyqtSignal()  # emitted whenever _gameid/_store changes

    def __init__(self, *, enabled: bool = True, gameid: str, store: str,
                 show_inherit_hint: bool = False,
                 store_combo=None, show_store: bool = True, parent=None):
        super().__init__(parent)
        self._show_inherit_hint = show_inherit_hint
        self._last_search = ""   # tracks the most recent search name — for _on_db_ready replay only
        self._gameid = gameid
        self._matched_title = ""  # umu-DB title for the current match — display only, not persisted
        self._store  = store if store in UMU_STORES else "none"
        self._store_combo = store_combo
        self._show_store = show_store
        self._build()

    def _build(self):
        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(10)

        # Store combo — injected from GameDialog, shown inline
        if self._store_combo is not None:
            self._store_combo.setFixedWidth(130)
            _sp = self._store_combo.sizePolicy()
            _sp.setRetainSizeWhenHidden(True)
            self._store_combo.setSizePolicy(_sp)
            self._store_combo.setVisible(self._show_store)
            layout.addWidget(self._store_combo)

        # Separator dot — only when store combo is shown
        self._sep_lbl = QLabel("·")
        self._sep_lbl.setObjectName("mutedHint")
        self._sep_lbl.setVisible(self._show_store and self._store_combo is not None)
        layout.addWidget(self._sep_lbl)

        layout.addStretch()

        # Status pill (match found / no match / loading)
        self._pill_lbl = QLabel("")
        self._pill_lbl.setTextFormat(Qt.TextFormat.RichText)
        self._pill_lbl.setObjectName("dialogPill")
        layout.addWidget(self._pill_lbl)

        # Game ID chip — shown only when matched
        self._id_lbl = QLabel("")
        self._id_lbl.setTextFormat(Qt.TextFormat.RichText)
        self._id_lbl.setObjectName("dialogIdLbl")
        self._id_lbl.setVisible(False)
        layout.addWidget(self._id_lbl)

        # Ensure DB is available — no search at build time.
        # All searches are triggered explicitly from GameDialog.
        self._ensure_db_ready()
        if UMU_DB_CSV.exists():
            self._set_pill_no_match()  # default state: "Using defaults"

    def _ensure_db_ready(self):
        # Protonfix disabled (NAGO 04:20): never download or check the protonfix
        # DB. The matcher (search()) is neutered, so there is nothing to feed.
        # Body below preserved (dormant) for re-enable.
        return
        if not UMU_DB_CSV.exists():
            self._set_pill_loading()
        elif not UmuDatabase.needs_download():
            return
        self._dbw = UmuDatabaseDownloadWorker()
        self._dbw.finished_ok.connect(self._on_db_ready)
        self._dbw.failed.connect(lambda err: self._set_pill_no_match())
        self._dbw.finished.connect(self._dbw.deleteLater)
        self._dbw.start()

    def search(self, name: str):
        """Protonfix auto-matching disabled (NAGO 04:20) — umu's per-game protonfix
        system was applying the wrong game's fix (loose 'starts-with' matcher, e.g.
        RDR2's fix firing on RDR1) and GE-Proton already bundles the common fixes.
        Neutered at this single entry point so every call site (name input, browse,
        GOG mode, reopen) becomes a safe no-op; the dormant matcher code below is
        preserved for a future cleanup/removal pass. To re-enable: restore the body
        to `self._last_search = name; self._populate_from_name(name)`."""
        self._last_search = ""
        self._gameid = ""
        self._store  = "none"
        self._matched_title = ""
        return

    def clear_match(self):
        """Clear any current match. Call when switching modes or when no search should be shown."""
        self._last_search = ""
        self._gameid = ""
        self._store  = "none"
        self._matched_title = ""
        self._set_pill_no_match()
        self._id_lbl.setVisible(False)
        self.state_changed.emit()

    def _on_db_ready(self):
        """Called when DB download completes — replay the last search if any."""
        UmuDatabase._entries = []
        if self._last_search:
            self._populate_from_name(self._last_search)

    def _populate_from_name(self, name: str):
        """Auto-match against the umu DB; update pill and ID chip."""
        if not name:
            self._gameid = ""
            self._store  = "none"
            self._matched_title = ""
            self._set_pill_no_match()
            self._id_lbl.setVisible(False)
            self.state_changed.emit()
            return

        if not UMU_DB_CSV.exists():
            self._set_pill_loading()
            return

        results = UmuDatabase.search(name, limit=50)

        if not results:
            self._gameid = ""
            self._store  = "none"
            self._matched_title = ""
            self._set_pill_no_match()
            self.state_changed.emit()
            return

        # Auto-pick: exact or prefix title match → strong; else weak.
        # Weak match: show the pill for reference but don't apply the id/store —
        # a wrong protonfix is worse than no protonfix.
        top = results[0]
        top_title = top["title"].lower()
        q = (name or "").strip().lower()
        strong = top_title == q or top_title.startswith(q)

        if strong:
            self._gameid = top.get("umu_id", "")
            self._store  = (top.get("store") or "none")
            if self._store not in UMU_STORES:
                self._store = "none"
            self._matched_title = top.get("title", "")
            self._set_pill_match(self._gameid)
        else:
            # Keep gameid/store empty — don't save a wrong match.
            # Still record the title so the weak-match chip shows what it matched.
            self._gameid = ""
            self._store  = "none"
            self._matched_title = top.get("title", "")
            self._set_pill_weak(top.get("umu_id", ""))
        self.state_changed.emit()

    # ── pill state helpers ────────────────────────────────────────────────────────────────────────────

    def _set_pill_loading(self):
        self._pill_lbl.setText(
            f"<span style='color:{_t('#52525b','#71717a')}; background:{_t('#1c1c20','#f0f0f4')}; "
            f"border:1px solid {_t('#2d2d32','#d4d4d8')}; border-radius:4px; "
            "padding:1px 6px;'>Loading…</span>"
        )
        self._id_lbl.setVisible(False)

    def _set_pill_no_match(self):
        self._pill_lbl.setText(
            f"<span style='color:{_t('#52525b','#71717a')}; background:{_t('#1c1c20','#f0f0f4')}; "
            f"border:1px solid {_t('#2d2d32','#d4d4d8')}; border-radius:4px; "
            "padding:1px 6px;'>Using defaults</span>"
        )
        self._id_lbl.setVisible(False)

    def _set_id_chip(self, gameid: str):
        """Render the ID chip: matched title (if known) + the umu id, e.g. 'Hades · umu-1174180'.
        Shows just the id when no title is available (e.g. DB not loaded)."""
        if not gameid:
            self._id_lbl.setVisible(False)
            return
        import html
        title = (self._matched_title or "").strip()
        gid_html = f"<span style='font-family:monospace;'>{html.escape(gameid)}</span>"
        if title:
            inner = (
                f"<span style='color:{_t('#a1a1aa','#3f3f46')};'>{html.escape(title)}</span>"
                f"<span style='color:{_t('#52525b','#a1a1aa')};'> · </span>"
                f"{gid_html}"
            )
        else:
            inner = gid_html
        self._id_lbl.setText(
            f"<span style='color:{_t('#7e7e88','#52525b')}; background:{_t('#1c1c20','#f0f0f4')}; "
            f"border:1px solid {_t('#2d2d32','#d4d4d8')}; border-radius:4px; "
            f"padding:1px 6px;'>{inner}</span>"
        )
        self._id_lbl.setVisible(True)

    def _set_pill_match(self, gameid: str):
        self._pill_lbl.setText(
            f"<span style='color:{_t('#34d399','#166534')}; background:{_t('#0d2e1f','#dcfce7')}; "
            f"border:1px solid {_t('#1a4a30','#86efac')}; border-radius:4px; "
            "padding:1px 6px;'>✓ Using protonfix</span>"
        )
        self._set_id_chip(gameid)

    def _set_pill_weak(self, gameid: str):
        self._pill_lbl.setText(
            f"<span style='color:{_t('#fbbf24','#92400e')}; background:{_t('#2a1f00','#fef3c7')}; "
            f"border:1px solid {_t('#3d2e00','#fcd34d')}; border-radius:4px; "
            "padding:1px 6px;'>⚠ Weak match · not applied</span>"
        )
        self._set_id_chip(gameid)

    def set_show_store(self, visible: bool):
        """Show or hide the store combo (called when runner type changes)."""
        self._show_store = visible
        if self._store_combo is not None:
            self._store_combo.setVisible(visible)
        self._sep_lbl.setVisible(visible and self._store_combo is not None)

    def set_store(self, store: str):
        """Override the store for the current match without re-searching.
        Lets the store dropdown change a matched fix's store while keeping its gameid."""
        self._store = store if store in UMU_STORES else "none"
        self.state_changed.emit()

    def values(self) -> dict:
        # Protonfix disabled (NAGO 04:20): gameid is always empty so umu never
        # receives a GAMEID and applies no per-game fix. Store is left to flow
        # (GOG="gog" for the runner badge; Proton combo is hidden so always "none").
        return {
            "enabled": True,  # unconditional
            "gameid":  "",
            "store":   self._store,
        }

def _format_last_played(last_played: str) -> str:
    """Convert a stored datetime string to a human-readable relative time."""
    if not last_played:
        return "Never"
    try:
        from datetime import datetime, timezone
        dt = datetime.fromisoformat(last_played.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        now = datetime.now(timezone.utc)
        delta = now - dt
        days = delta.days
        if days == 0:
            return "Today"
        elif days == 1:
            return "Yesterday"
        elif days < 7:
            return f"{days} days ago"
        elif days < 30:
            weeks = days // 7
            return f"{weeks}w ago"
        elif days < 365:
            months = days // 30
            return f"{months}mo ago"
        else:
            years = days // 365
            return f"{years}y ago"
    except Exception:
        return "Unknown"



# ── Add / Edit Game Dialog ─────────────────────────────────────────────────────
# Module-level keepalive for cover-download workers detached from a closing
# GameDialog. A dialog can be dismissed (Cancel or Save) while a cover download
# is still mid-request. SGDBWorker.run() is a blocking network call with no event
# loop, so it can't be interrupted cleanly — quit()/wait() would either no-op or
# freeze the GUI for the request timeout. Instead we disconnect the dialog's slots
# (so nothing fires into the dead dialog) and park the worker here so it isn't
# garbage-collected while its thread is still alive — which would crash on SIP
# cleanup. Each worker self-evicts from the set when it finishes.
_DETACHED_COVER_WORKERS: "set" = set()


class GameDialog(_NAGODialog):
    def __init__(self, config: dict, game: dict = None, parent=None):
        super().__init__(parent)
        self.config = config
        self.game   = game or {}
        self.setWindowTitle("Add Game" if not game else "Edit Game")
        self.setMinimumWidth(620 + self._SHADOW * 2)
        self.setMaximumWidth(620 + self._SHADOW * 2)
        self.setWindowFlags(Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self._pending_cover_path = ""
        self._tmp_prefix_path: "Path | None" = None   # prefix created before game is saved
        self._browse_exe_stash: str = ""   # exe path stashed when switching to Install mode
        self._run_in_prefix_worker = None   # set while an installer/exe is running in the prefix
        self._runner_btns = []
        self._dw = None
        # Tracks whether gog_combo.currentIndexChanged is wired to _on_gog_game_picked.
        # PyQt6's connect() does NOT raise on a duplicate, so we can't rely on
        # try/except to stay single-connected — we track state explicitly instead.
        self._gog_picked_connected = False
        self._build()
        self._cap_size_to_screen()
        self._centered_once = False

    def _dlg_switch_tab(self, idx: int):
        """Switch GameDialog tab and update button states."""
        accent = self.config.get("accent_color", DEFAULT_ACCENT)
        for i, (btn, icon_name) in enumerate(self._dlg_tab_btns):
            active = (i == idx)
            btn.setChecked(active)
            btn.setIcon(ph_icon(icon_name, 15, accent if active else "#7e7e88"))
        self._tabs.setCurrentIndex(idx)
        self._dlg_panel.set_active_tab(idx)

    def _cap_size_to_screen(self):
        """Set a maximum height that fits within the screen's available area."""
        screen = self._target_screen()
        if screen is None:
            return
        avail = screen.availableGeometry()
        margin = 24
        max_h = max(self.minimumHeight() or 200, avail.height() - margin * 2)
        self.setMaximumHeight(max_h)
        # Width is fixed at 620 — no max_w override needed

    def _target_screen(self):
        screen = None
        if self.parent() is not None and self.parent().window() is not None:
            screen = self.parent().window().screen()
        if screen is None:
            screen = QApplication.screenAt(QCursor.pos()) or QApplication.primaryScreen()
        return screen

    def showEvent(self, event):
        super().showEvent(event)
        if not self._centered_once:
            self._centered_once = True
            self._cap_size_to_screen()

    def _lock_height(self):
        if self.game:
            gt = self.game.get("game_type", "proton")
            if gt == "steam":
                EDIT_STEAM_H = 660
                h = EDIT_STEAM_H
            elif gt == "native":
                EDIT_NATIVE_H = 660
                h = EDIT_NATIVE_H
            else:  # proton and gog both use the same layout
                EDIT_PROTON_H = 690
                h = EDIT_PROTON_H
        else:
            ADD_GAME_H = 750
            h = ADD_GAME_H

        self.setFixedHeight(h)

    def _build(self):
        # Outer transparent layout — QDialog itself is transparent so rounded corners work
        outer = QVBoxLayout(self)
        outer.setContentsMargins(self._SHADOW, self._SHADOW, self._SHADOW, self._SHADOW)
        outer.setSpacing(0)
        root = QFrame()
        root.setObjectName("dialogRoot")
        outer.addWidget(root)

        layout = QVBoxLayout(root)
        layout.setContentsMargins(28, 24, 28, 24)
        layout.setSpacing(14)

        # Default to Proton for the Add flow; keep the stored value when editing
        cur = self.game.get("game_type") or ("proton" if not self.game else "native")

        # ── Cover + Info header ────────────────────────────────────────────
        info_header = QWidget()
        info_h = QHBoxLayout(info_header)
        info_h.setContentsMargins(0, 0, 0, 0)
        info_h.setSpacing(10)

        # Cover thumbnail (120×160)
        # Add mode needs extra height: runner toggle (~34px) eats into the info
        # panel, leaving the title label too cramped to wrap on long names.
        HEADER_H = 188
        COVER_W   = round(HEADER_H * 2 / 3)  # 2:3 ratio matches 600×900 SGDB covers

        # Reuse GameCard — inherits all cover rendering, DPR, rounding, placeholder.
        # Hide the bottom name strip directly — no layout to iterate.
        _dlg_game_ref = self.game if self.game else {"name": "", "game_type": "proton"}
        self._dlg_cover_card = GameCard(_dlg_game_ref, accent_color=self.config.get("accent_color", DEFAULT_ACCENT), parent=self)
        self._dlg_cover_card._name_label.hide()
        self._dlg_cover_card._playtime_label.hide()
        # Resize to dialog thumbnail dimensions
        self._dlg_cover_card.setFixedSize(COVER_W, HEADER_H)
        # Cover area fills the full card in the dialog (no bottom strip)
        _cv_w = COVER_W
        _cv_h = HEADER_H
        self._dlg_cover_card._cover_w = _cv_w
        self._dlg_cover_card._cover_h = _cv_h
        # Disable hover overlay and drop shadow
        self._dlg_cover_card._hover_overlay.setGeometry(0, 0, 0, 0)
        self._dlg_cover_card.setCursor(QCursor(Qt.CursorShape.ArrowCursor))
        self._dlg_cover_card.setGraphicsEffect(None)
        self._dlg_cover_card._no_gradient = True
        # Re-render placeholder at correct dialog dimensions
        _cp = _dlg_game_ref.get("cover_path", "")
        if _cp and Path(_cp).exists():
            # Render cover directly at the known pixel dimensions — don't use
            # set_cover() which reads cover_label.size() before layout is done.
            _screen = QApplication.primaryScreen()
            _dpr    = _screen.devicePixelRatio() if _screen else 1.0
            _cw     = self._dlg_cover_card._cover_w
            _ch     = self._dlg_cover_card._cover_h
            _pw     = max(1, round(_cw * _dpr))
            _ph     = max(1, round(_ch * _dpr))
            _src    = QPixmap(_cp)
            _src.setDevicePixelRatio(1.0)
            _scaled = _src.scaled(_pw, _ph,
                                  Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                                  Qt.TransformationMode.SmoothTransformation)
            if _scaled.width() > _pw or _scaled.height() > _ph:
                _cx = (_scaled.width()  - _pw) // 2
                _cy = (_scaled.height() - _ph) // 2
                _scaled = _scaled.copy(_cx, _cy, _pw, _ph)
            # All four corners rounded
            _r   = COVER_RADIUS * _dpr
            _out = QPixmap(_pw, _ph)
            _out.fill(Qt.GlobalColor.transparent)
            _rp  = QPainter(_out)
            _rp.setRenderHint(QPainter.RenderHint.Antialiasing)
            _path = QPainterPath()
            _path.moveTo(_r, 0)
            _path.lineTo(_pw - _r, 0)
            _path.arcTo(_pw - _r*2, 0,        _r*2, _r*2,  90, -90)
            _path.lineTo(_pw, _ph - _r)
            _path.arcTo(_pw - _r*2, _ph - _r*2, _r*2, _r*2,   0, -90)
            _path.lineTo(_r, _ph)
            _path.arcTo(0,          _ph - _r*2, _r*2, _r*2, 270, -90)
            _path.lineTo(0, _r)
            _path.arcTo(0,          0,          _r*2, _r*2, 180, -90)
            _path.closeSubpath()
            _rp.setClipPath(_path)
            _rp.drawPixmap(0, 0, _scaled)
            _rp.end()
            _out.setDevicePixelRatio(_dpr)
            self._dlg_cover_card._cover_pixmap = _out
            self._dlg_cover_card._has_cover = True
            self._dlg_cover_card.update()
        else:
            self._dlg_cover_card._set_placeholder(all_corners=True, size=(_cv_w, _cv_h))
        # Cover card — clickable, pointer cursor signals it
        cover_col = QWidget()
        cover_col.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        cover_col_v = QVBoxLayout(cover_col)
        cover_col_v.setContentsMargins(0, 0, 0, 0)
        cover_col_v.setSpacing(0)
        cover_col_v.addWidget(self._dlg_cover_card)
        cover_col.mousePressEvent = lambda e: self._open_cover_picker()
        info_h.addWidget(cover_col, 0, Qt.AlignmentFlag.AlignTop)

        # Right column: single merged card, flush with cover height
        right_col = QWidget()
        right_col.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        right_col.setFixedHeight(HEADER_H)
        right_col_v = QVBoxLayout(right_col)
        right_col_v.setContentsMargins(0, 0, 0, 0)
        right_col_v.setSpacing(0)

        # ── Single merged card ────────────────────────────────────────────
        merged_card = QFrame()
        merged_card.setObjectName("settingsSection")
        merged_card_v = QVBoxLayout(merged_card)
        merged_card_v.setContentsMargins(12, 10, 12, 10)
        merged_card_v.setSpacing(0)
        ip = merged_card_v  # alias so runner badge / title code below still works

        # ── Runner selector (Add flow) or badge (Edit flow) ───────────────
        if not self.game:
            _is_lt = _current_theme() == "light"

            # Detect available import sources once — used by both the Import
            # runner button's enabled state and the sub-picker below.
            _steam_ok      = _is_steam_installed()
            _heroic_ok     = _is_heroic_installed()
            _lutris_ok     = _is_lutris_installed()
            _any_import_ok = _steam_ok or _heroic_ok or _lutris_ok

            # ── Runner segmented control: Native / Proton / Import ────────
            # Each option carries its own active background + foreground so
            # the checked pill is colour-coded by runner type.
            _RUNNER_OPTIONS = [
                ("Native", "native", "#dcfce7" if _is_lt else "#0d3320", "#166534" if _is_lt else "#6ee7b7"),
                ("Proton", "proton", "#fef3c7" if _is_lt else "#2a1f00", "#92400e" if _is_lt else "#fbbf24"),
                ("Import", "import", "#e0f2fe" if _is_lt else "#0d2540", "#0369a1" if _is_lt else "#7dd3fc"),
            ]
            _inactive_col = _t("#71717a", "#71717a")

            _seg_frame = QFrame()
            _seg_frame.setObjectName("runnerSegFrame")
            _seg_frame.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
            _seg_layout = QHBoxLayout(_seg_frame)
            _seg_layout.setContentsMargins(3, 3, 3, 3)
            _seg_layout.setSpacing(2)

            self._runner_btns = []

            def _runner_btn_stylesheet(active_bg, active_fg, is_active):
                """Return the stylesheet for a runner pill button."""
                _ic = _t("#71717a", "#71717a")
                _hover_bg = _t("rgba(255,255,255,0.06)", "rgba(0,0,0,0.06)")
                if is_active:
                    return (
                        f"QPushButton {{ background: {active_bg}; color: {active_fg};"
                        f" border: none; border-radius: 5px;"
                        f" font-size: 12px; font-weight: 700; padding: 5px 0px; }}"
                        f"QPushButton:hover {{ background: {active_bg}; color: {active_fg}; }}"
                    )
                return (
                    f"QPushButton {{ background: transparent; color: {_ic};"
                    f" border: none; border-radius: 5px;"
                    f" font-size: 12px; font-weight: 700; padding: 5px 0px; }}"
                    f"QPushButton:hover {{ background: {_hover_bg}; color: {_ic}; }}"
                )

            def _make_runner_handler(_val, _bg, _fg):
                """Return the toggled handler for a runner pill button."""
                def _handler(checked):
                    if not checked:
                        return
                    # Re-style all pills — checked one gets active colours,
                    # rest go back to inactive.
                    for _b in self._runner_btns:
                        _bv  = _b.property("runnerValue")
                        _bbg = _b.property("activeBg")
                        _bfg = _b.property("activeFg")
                        _active = (_bv == _val)
                        _b.setChecked(_active)
                        if _b.isEnabled():
                            _b.setStyleSheet(_runner_btn_stylesheet(_bbg, _bfg, _active))
                    # Sync type_combo for native/proton — import waits for
                    # sub-picker selection before setting a game type.
                    _idx = {"native": 0, "proton": 1}.get(_val)
                    if _idx is not None:
                        self.type_combo.setCurrentIndex(_idx)
                    # Row 1: switch top-row (toggle / picker / empty)
                    _r1 = {"native": 0, "proton": 1, "import": 2}
                    if hasattr(self, "_row1_stack"):
                        self._row1_stack.setCurrentIndex(_r1.get(_val, 0))
                    # Row 2: exe row for Native/Proton; Import handled by _on_import_source_picked
                    if hasattr(self, "_row2_stack") and _val in ("native", "proton"):
                        self._row2_stack.setCurrentIndex(0)
                    if _val == "import":
                        if self._import_src_btns:
                            self._on_import_source_picked(
                                self._import_src_btns[0].text().strip().lower()
                            )
                    else:
                        for _isb in self._import_src_btns:
                            _isb.setChecked(False)
                        self._gog_import_source = None
                    # Reset Proton install mode to Browse whenever leaving Proton
                    # so returning to Proton (e.g. via auto-switch) always starts
                    # in Browse mode, not a stale Install state.
                    if _val != "proton":
                        self._proton_install_mode = "browse"
                        for _b in self._install_mode_btns:
                            _b.setChecked(_b.text() == "Browse")
                return _handler

            for _rl, _rv, _rbg, _rfg in _RUNNER_OPTIONS:
                _btn = QPushButton(_rl)
                _btn.setCheckable(True)
                _btn.setChecked(_rv == cur)
                _btn.setProperty("runnerValue", _rv)
                _btn.setProperty("activeBg", _rbg)
                _btn.setProperty("activeFg", _rfg)

                if _rv == "import" and not _any_import_ok:
                    # No importable launcher present — button visible but
                    # disabled, tooltip explains why.
                    _btn.setEnabled(False)
                    _btn.setToolTip(
                        "No supported launcher detected — install Steam, Heroic, "
                        "or Lutris to import games from it."
                    )
                    _btn.setStyleSheet(
                        f"QPushButton {{ background: transparent;"
                        f" color: {_t('#3f3f46', '#d4d4d8')};"
                        f" border: none; border-radius: 5px;"
                        f" font-size: 12px; font-weight: 700; padding: 5px 0px; }}"
                    )
                else:
                    _btn.setStyleSheet(
                        _runner_btn_stylesheet(_rbg, _rfg, _rv == cur)
                    )

                # toggled: fires on both programmatic and user changes — used
                # to keep pill visuals in sync when auto-switching runner from
                # _browse_exe (setChecked calls).
                _btn.toggled.connect(_make_runner_handler(_rv, _rbg, _rfg))
                # clicked: only genuine user interaction — clears the stale
                # Browse field when the user manually switches runner.
                _btn.clicked.connect(self._clear_exe_browse_field)

                _seg_layout.addWidget(_btn, 1)
                self._runner_btns.append(_btn)

            # ── Import source sub-picker: Steam / Heroic / Lutris ─────────
            # Only the detected launchers get a button; hidden until Import
            # runner is selected.
            self._import_row = QWidget()
            _ir = QHBoxLayout(self._import_row)
            _ir.setContentsMargins(0, 0, 0, 0)
            _ir.setSpacing(6)

            self._import_src_btns = []
            # SVG filenames for each import source — matches files in icons/
            _IMPORT_SOURCES = (
                ("Steam",  "steam",  "steam",               _steam_ok),
                ("Heroic", "heroic", "heroicgameslauncher",  _heroic_ok),
                ("Lutris", "lutris", "lutris",               _lutris_ok),
            )
            _si_color = "#18181b" if _current_theme() == "light" else "#ffffff"
            for _il, _iv, _svg_name, _idetected in _IMPORT_SOURCES:
                if not _idetected:
                    continue
                _ibtn = QPushButton(f"  {_il}")
                _ibtn.setIcon(store_icon(_svg_name, 18, _si_color))
                _ibtn.setIconSize(QSize(18, 18))
                _ibtn.setObjectName("secondary")
                _ibtn.setCheckable(True)
                _ibtn.setFixedWidth(110)
                _ibtn.clicked.connect(
                    lambda _=False, v=_iv: self._on_import_source_picked(v)
                )
                _ir.addWidget(_ibtn)
                self._import_src_btns.append(_ibtn)
            _ir.addStretch(1)

            self._import_row.setVisible(True)
            # _seg_frame and _import_row are both added to the layout in the
            # unified top-section block further below.
        if self.game:
            _gt = self.game.get("game_type", "native")
            _umu_store = (self.game.get("umu_store") or "none").lower()

            # (label, dark-bg, fg-text)
            # bg = very dark tint of brand color; fg = brand accent color
            _is_lt3 = _current_theme() == "light"
            def _sc(dark_bg, light_bg, dark_fg, light_fg):
                return (light_bg if _is_lt3 else dark_bg, light_fg if _is_lt3 else dark_fg)
            _STORE_COLORS = {
                "gog":         ("GOG",        *_sc("#1e0d4a", "#f3e8ff", "#c084fc", "#7e22ce")),
                "egs":         ("Epic",        *_sc("#002d4a", "#e0f9ff", "#38d0ff", "#0e7490")),
                "steam":       ("Steam",       *_sc("#0d2540", "#e0f2fe", "#7dd3fc", "#0369a1")),
                "amazon":      ("Amazon",      *_sc("#3a2200", "#fff7ed", "#ffaa22", "#c2410c")),
                "battlenet":   ("Battle.net",  *_sc("#002244", "#eff6ff", "#22b8ff", "#1d4ed8")),
                "ea":          ("EA",          *_sc("#3a1800", "#fff7ed", "#fb8c4a", "#c2410c")),
                "humble":      ("Humble",      *_sc("#3a1200", "#fff7ed", "#e8804d", "#9a3412")),
                "itchio":      ("itch.io",     *_sc("#3a0d0d", "#fff1f2", "#ff7070", "#be123c")),
                "ubisoft":     ("Ubisoft",     *_sc("#001a38", "#eff6ff", "#2288f0", "#1d4ed8")),
                "zoomplatform":("Zoom",        *_sc("#001a38", "#eff6ff", "#60aeff", "#1d4ed8")),
            }
            _is_lt2 = _current_theme() == "light"
            _runner_labels = {
                "native": ("Native", "#dcfce7" if _is_lt2 else "#0d3320", "#166534" if _is_lt2 else "#6ee7b7"),
                "proton": ("Proton", "#fef3c7" if _is_lt2 else "#2a1f00", "#92400e" if _is_lt2 else "#fbbf24"),
                "steam":  ("Steam",  "#e0f2fe" if _is_lt2 else "#0d2540", "#0369a1" if _is_lt2 else "#7dd3fc"),
            }

            # For Proton games, show the store badge if a known store is set
            if _gt == "proton" and _umu_store in _STORE_COLORS:
                _runner_label, _runner_bg, _runner_fg = _STORE_COLORS[_umu_store]
            elif _gt == "gog":
                _runner_label, _runner_bg, _runner_fg = _STORE_COLORS["gog"]
            elif _gt == "steam":
                _runner_label, _runner_bg, _runner_fg = _runner_labels["steam"]
            else:
                _runner_label, _runner_bg, _runner_fg = _runner_labels.get(
                    _gt, ("Unknown", _t("#2d2d32", "#e4e4e8"), _t("#a1a1aa", "#71717a")))

            runner_badge = QLabel(_runner_label)
            runner_badge.setStyleSheet(
                f"color: {_runner_fg}; background: {_runner_bg};"
                f"border-radius: 5px; padding: 2px 9px;"
                f"font-size: 11px; font-weight: 700;"
            )
            runner_badge.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)

        # ── Badge/toggle top, name centered middle, stats bottom ──────────
        _initial_title = self.game.get("name", "") if self.game else ""

        if self.game:
            # Badge floats top-right; name is centered to the full card width.
            # Use a container with QGridLayout so both occupy the same cell —
            # badge aligned TopRight, name_input centered — no flow height cost.
            _header_container = QWidget()
            _header_container.setObjectName("transparentBg")
            _hg = QGridLayout(_header_container)
            _hg.setContentsMargins(0, 0, 0, 0)
            _hg.setSpacing(0)
            ip.addWidget(_header_container)
        else:
            ip.addWidget(_seg_frame)
            ip.addStretch()

        # Name input — centered, borderless, bold
        class _CenteredPlaceholderTextEdit(QTextEdit):
            """QTextEdit's native placeholderText always renders left-aligned,
            ignoring the document's centered defaultTextOption — confirmed by
            direct render test, not assumed. Paint it manually instead so an
            empty Add-flow field ("New Game") centers the same way a typed
            name does. setPlaceholderText is overridden (not the real Qt one)
            so existing call sites don't need to change."""
            def __init__(self, *_a, **_kw):
                super().__init__(*_a, **_kw)
                self._ph_text = ""

            def setPlaceholderText(self, text):
                self._ph_text = text

            def paintEvent(self, event):
                super().paintEvent(event)
                if self.document().isEmpty() and self._ph_text:
                    _p = QPainter(self.viewport())
                    _p.setFont(self.font())
                    _col = self.palette().color(self.foregroundRole())
                    _col.setAlpha(128)  # matches Qt's own default placeholder
                    # dimming convention (text color at 50% alpha) — the QSS
                    # ::placeholder color rule was confirmed inert, so this
                    # was already the effective color; only alignment changes.
                    _p.setPen(_col)
                    _p.drawText(self.viewport().rect(),
                                Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignTop,
                                self._ph_text)
                    _p.end()

        self.name_input = _CenteredPlaceholderTextEdit(_initial_title)
        self.name_input.setObjectName("dlgNameInput")
        self.name_input.setPlaceholderText("New Game")
        self.name_input.setAcceptRichText(False)
        # Names that wrap past two visual lines used to be clipped with no way to
        # reach the hidden text (height is fixed at two lines, scrollbars off).
        # Allow the vertical scrollbar to appear on demand so nothing is ever lost;
        # short one/two-line names — the common case — still show no scrollbar.
        self.name_input.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.name_input.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.name_input.setLineWrapMode(QTextEdit.LineWrapMode.WidgetWidth)
        self.name_input.document().setDocumentMargin(0)
        self.name_input.setContentsMargins(0, 0, 0, 0)
        # Center-align the document text
        def _apply_center_align():
            _opt = self.name_input.document().defaultTextOption()
            _opt.setAlignment(Qt.AlignmentFlag.AlignHCenter)
            self.name_input.document().setDefaultTextOption(_opt)
        _apply_center_align()
        # Enforce max 2 lines and strip newlines on paste
        def _enforce_two_lines():
            _doc = self.name_input.document()
            if _doc.blockCount() > 2:
                _cursor = self.name_input.textCursor()
                _cursor.movePosition(_cursor.MoveOperation.End)
                while _doc.blockCount() > 2:
                    _cursor.movePosition(_cursor.MoveOperation.StartOfBlock, _cursor.MoveMode.KeepAnchor)
                    _cursor.movePosition(_cursor.MoveOperation.PreviousCharacter, _cursor.MoveMode.KeepAnchor)
                    _cursor.removeSelectedText()
                self.name_input.setTextCursor(_cursor)
            _apply_center_align()
        self.name_input.document().contentsChanged.connect(_enforce_two_lines)
        # Fix height to 2 lines — set font explicitly so metrics match QSS 20px
        _name_font = self.name_input.font()
        _name_font.setPixelSize(22)
        _name_font.setBold(True)
        self.name_input.setFont(_name_font)
        _fm = self.name_input.fontMetrics()
        _line_h = _fm.lineSpacing()
        self.name_input.setFixedHeight(_line_h * 2 + 16)
        if self.game:
            # Fill full cell width — AlignHCenter would shrink to sizeHint.
            # Text centering is handled by the document's defaultTextOption.
            # Right margin reserves space so the text never flows under the badge.
            self.name_input.setViewportMargins(0, 0, 72, 0)
            _hg.addWidget(self.name_input, 0, 0,
                          Qt.AlignmentFlag.AlignVCenter)
            # Badge overlaid top-right in the same cell
            _hg.addWidget(runner_badge, 0, 0,
                          Qt.AlignmentFlag.AlignTop | Qt.AlignmentFlag.AlignRight)
        else:
            ip.addWidget(self.name_input)
            ip.addStretch()

        # _header_title_lbl alias — input IS the display
        self._header_title_lbl = self.name_input

        # ── Exe path hint — no-op kept for compatibility ──────────────────
        self._header_exe_hint = QLabel("")
        self._header_exe_hint.setVisible(False)

        # ── Stats bottom section inside merged card ────────────────────────
        def _stat_widget(label: str, value: str) -> QWidget:
            w = QFrame()
            w.setObjectName("statWidget")
            w.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
            w.setSizePolicy(QSizePolicy.Policy.Ignored, QSizePolicy.Policy.Minimum)
            wv = QVBoxLayout(w)
            wv.setContentsMargins(8, 6, 8, 6)
            wv.setSpacing(2)
            lbl = QLabel(label.upper())
            lbl.setObjectName("statLabel")
            val = QLabel(value if value else "—")
            val.setObjectName("statValue")
            wv.addWidget(lbl)
            wv.addWidget(val)
            return w

        # Always read playtime stats fresh from DB so the dialog shows accurate
        # values even if the in-memory game dict is stale (e.g. opened right
        # after a session ended, or re-opened without a full library reload).
        _gid = self.game.get("id") if self.game else None
        if _gid:
            _scon = None
            try:
                _scon = db_con()
                _srow = _scon.execute(
                    "SELECT playtime_minutes, last_session_minutes, last_played "
                    "FROM games WHERE id=?", (_gid,)
                ).fetchone()
                if _srow:
                    _pt_minutes = int(_srow[0] or 0)
                    _ls_minutes = int(_srow[1] or 0)
                    _lp_raw     = _srow[2] or ""
                else:
                    _pt_minutes, _ls_minutes, _lp_raw = 0, 0, ""
            except Exception:
                _pt_minutes = self.game.get("playtime_minutes", 0)
                _ls_minutes = self.game.get("last_session_minutes", 0)
                _lp_raw     = self.game.get("last_played", "")
            finally:
                if _scon is not None:
                    _scon.close()
        else:
            _pt_minutes = self.game.get("playtime_minutes", 0) if self.game else 0
            _ls_minutes = self.game.get("last_session_minutes", 0) if self.game else 0
            _lp_raw     = self.game.get("last_played", "") if self.game else ""
        _pt_text = format_playtime(_pt_minutes) or "—"
        _ls_text = format_playtime(_ls_minutes) if _ls_minutes else "—"
        _lp_text = _format_last_played(_lp_raw)

        stats_row = QWidget()
        stats_h = QHBoxLayout(stats_row)
        stats_h.setContentsMargins(0, 0, 0, 0)
        stats_h.setSpacing(6)
        stats_h.addWidget(_stat_widget("Playtime", _pt_text))
        stats_h.addWidget(_stat_widget("Last session", _ls_text))
        stats_h.addWidget(_stat_widget("Last played", _lp_text))
        ip.addStretch()
        ip.addWidget(stats_row)

        # Category badges — separator + right-aligned row, only if game has categories
        if self.game and self.game.get("id"):
            _cat_ids = db_get_game_categories(self.game["id"])
            if _cat_ids:
                _all_cats = {c["id"]: c["name"] for c in db_get_categories()}
                _sep = QFrame()
                _sep.setFrameShape(QFrame.Shape.HLine)
                _sep.setObjectName("dialogSep")
                ip.addWidget(_sep)
                cat_row = QWidget()
                cat_h = QHBoxLayout(cat_row)
                cat_h.setContentsMargins(0, 0, 0, 0)
                cat_h.setSpacing(5)
                cat_h.addStretch()
                for _cid in _cat_ids[:7]:
                    _cname = _all_cats.get(_cid)
                    if not _cname:
                        continue
                    cat_badge = QLabel(_cname)
                    cat_badge.setObjectName("catBadge")
                    cat_badge.setFixedHeight(24)
                    cat_h.addWidget(cat_badge)
                ip.addWidget(cat_row)

        right_col_v.addWidget(merged_card)
        info_h.addWidget(right_col)

        # ── Tab widget: General | Advanced ────────────────────────────────────
        self._tabs = QTabWidget()
        self._tabs.setObjectName("dlgTabs")
        self._tabs.setDocumentMode(True)
        layout.addWidget(self._tabs, 1)

        # ── General tab page ───────────────────────────────────────────────
        general_page = QWidget()
        general_layout = QVBoxLayout(general_page)
        general_layout.setContentsMargins(0, 8, 0, 0)
        general_layout.setSpacing(14)

        # The existing cards used to be added directly to `layout`; redirect them to
        # `general_layout` instead. We keep the local name `layout` for the original
        # references below… so use a temporary alias so the old code keeps working.
        _orig_layout = layout
        layout = general_layout

        # Cover + info header lives inside the General tab
        layout.addWidget(info_header, 0, Qt.AlignmentFlag.AlignTop)

        # ── Hidden type combo — still needed for save/type-change logic ────
        # Runner is fixed after creation; hidden in the Edit flow entirely.
        # In the Add flow it remains accessible via _on_type_change but not shown.
        self.type_combo = NAGOComboBox()
        self.type_combo.setObjectName("dlgCombo")
        for label, value in [("Native", "native"), ("Proton", "proton"),
                              ("GOG", "gog"), ("Steam", "steam")]:
            self.type_combo.addItem(label, userData=value)
        idx_for_type = {"native": 0, "proton": 1, "gog": 2, "steam": 3}.get(cur, 0)
        self.type_combo.setCurrentIndex(idx_for_type)
        self.type_combo.setVisible(False)  # never shown — runner badge in header is read-only display
        layout.addWidget(self.type_combo)  # must be parented so signal wiring works

        # ── Row 1: Store (left) + Executable path (right) ─────────────────
        store_exe_row = QWidget()
        ser = QHBoxLayout(store_exe_row)
        ser.setContentsMargins(0, 0, 0, 0)
        ser.setSpacing(10)

        # Store card — only shown for Proton games
        self._store_card = QFrame()
        self._store_card.setObjectName("settingsSection")
        self._store_card.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Minimum)
        scv = QVBoxLayout(self._store_card)
        scv.setSpacing(8)
        scv.addWidget(self._section_label("Store"))
        self.store_combo = NAGOComboBox()
        self.store_combo.setToolTip("Store this game came from — used by umu-launcher for Protonfixes")
        for slabel, sval in [
            ("No store",   "none"),
            ("Epic",       "egs"),   ("Amazon",     "amazon"),
            ("Battle.net", "battlenet"), ("EA",     "ea"),
            ("Humble",     "humble"), ("itch.io",   "itchio"),
            ("Ubisoft",    "ubisoft"), ("Zoom",     "zoomplatform"),
        ]:
            self.store_combo.addItem(slabel, userData=sval)
        saved_store = self.game.get("umu_store", "none") if self.game else "none"
        for i in range(self.store_combo.count()):
            if self.store_combo.itemData(i) == saved_store:
                self.store_combo.setCurrentIndex(i)
                break
        scv.addWidget(self.store_combo)
        ser.addWidget(self._store_card, 2, Qt.AlignmentFlag.AlignTop)
        self._store_card.setVisible(False)  # store moved inline into umu row
        # Protonfix disabled (NAGO 04:20): the store combo existed only to feed
        # umu's protonfix database search. Force it to "No store" (none), disable
        # it, and keep it hidden everywhere. Kept alive (not removed) so the
        # .currentData()/.count() call sites elsewhere stay valid and return "none".
        for _i in range(self.store_combo.count()):
            if self.store_combo.itemData(_i) == "none":
                self.store_combo.setCurrentIndex(_i)
                break
        self.store_combo.setEnabled(False)
        self.store_combo.setVisible(False)



        # ── Row 2: Executable Path (full width) ────────────────────────────
        # ── Source card ───────────────────────────────────────────────────
        # QStackedWidget whose pages map to runner states.
        #
        # Add flow layout:
        #   Stack page 0 (Native):  empty — collapses, exe row below carries content
        #   Stack page 1 (Proton):  Browse/Install toggle + installer options
        #   Stack page 2 (Import):  source sub-picker + Steam/GOG combo
        #   Below stack (shared):   exe input + Browse btn + hint  [hidden on Import]
        #
        # Edit flow layout:
        #   Stack page 0 (Native/Proton):  exe input + Browse
        #   Stack page 1 (Steam):           steam combo + Rescan
        #   Stack page 2 (GOG):             gog inner stack (import/browse)

        source_frame = QFrame()
        source_frame.setObjectName("settingsSection")
        source_frame.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)

        sv = QVBoxLayout(source_frame)
        sv.setContentsMargins(10, 15, 10, 10)
        sv.setSpacing(4)
        sv.setAlignment(Qt.AlignmentFlag.AlignTop)

        if not self.game:
            # ── Add flow ──────────────────────────────────────────────────
            #
            # Row 1 — runner-specific top row (pills / toggle)
            #   Native:  hidden (zero height via _AdaptiveStack)
            #   Proton:  Browse / Install toggle pills
            #   Import:  Steam / Heroic / Lutris source pills
            #
            # Row 2 — input / combo (same visual weight across runners)
            #   Native + Proton:  exe path input  +  Browse button
            #   Import → Steam:   steam combo     +  Rescan button
            #   Import → GOG:     gog combo       +  Rescan button
            #
            # Row 3 — hint label (always present; empty until populated)
            #
            # Row 4 — installer options (Proton+Install only; hidden otherwise)
            #
            # Both Row 1 and Row 2 are _AdaptiveStack so Native's empty
            # top row collapses cleanly without pushing Row 2 down.

            # ── Row 1: top-row stack ──────────────────────────────────────
            self._row1_stack = _AdaptiveStack()
            self._row1_stack.setSizePolicy(
                QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed
            )
            self._row1_stack.currentChanged.connect(
                lambda _: (
                    self._row1_stack.updateGeometry(),
                    source_frame.adjustSize(),
                )
            )

            # Page 0 — Native: no top row
            _r1_native = QWidget()
            _r1_native.setFixedHeight(0)
            self._row1_stack.addWidget(_r1_native)   # index 0

            # Page 1 — Proton: Browse / Install toggle
            _r1_proton = QWidget()
            _r1_proton_h = QHBoxLayout(_r1_proton)
            _r1_proton_h.setContentsMargins(0, 0, 0, 0)
            _r1_proton_h.setSpacing(6)
            self._install_mode_row = _r1_proton
            self._install_mode_btns = []
            for _ml, _mv in (("Browse", "browse"), ("Install", "install")):
                _mbtn = QPushButton(_ml)
                _mbtn.setObjectName("secondary")
                _mbtn.setCheckable(True)
                _mbtn.setChecked(_mv == "browse")
                _mbtn.setFixedWidth(110)
                _mbtn.clicked.connect(
                    lambda _=False, v=_mv: self._on_proton_mode_picked(v)
                )
                _r1_proton_h.addWidget(_mbtn)
                self._install_mode_btns.append(_mbtn)
            _r1_proton_h.addStretch(1)
            self._proton_install_mode = "browse"
            self._row1_stack.addWidget(_r1_proton)   # index 1

            # Page 2 — Import: Steam / Heroic / Lutris source picker
            # _import_row is already a QWidget with HBoxLayout + buttons —
            # add it directly, no wrapper needed.
            self._row1_stack.addWidget(self._import_row)   # index 2

            # Spacers around _row1_stack — only visible when row1 has content
            # (Proton or Import). Native's page is empty so spacers are hidden.
            sv.addWidget(self._row1_stack)
            sv.addSpacing(6)

            # ── Row 2: input / combo stack (with hint label per page) ────
            # Each page contains its input row + its own hint label so the
            # hint is always adjacent to its field. No separate hint row in
            # sv means _inst_options_row appears directly below with no gap.
            self._row2_stack = _AdaptiveStack()
            self._row2_stack.setSizePolicy(
                QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed
            )
            self._row2_stack.currentChanged.connect(
                lambda _: self._row2_stack.updateGeometry()
            )

            # Page 0 — exe input + Browse + hint (Native + Proton)
            _r2_exe = QWidget()
            _r2_exe_v = QVBoxLayout(_r2_exe)
            _r2_exe_v.setContentsMargins(0, 0, 0, 0)
            _r2_exe_v.setSpacing(4)
            _r2_exe_row = QHBoxLayout()
            _r2_exe_row.setContentsMargins(0, 0, 0, 0)
            _r2_exe_row.setSpacing(8)
            self.exe_input = QLineEdit("")
            self.exe_input.setObjectName("dlgInput")
            self.exe_input.setPlaceholderText("Path to game executable")
            self._exe_browse_btn = QPushButton("Browse")
            self._exe_browse_btn.setObjectName("secondary")
            self._exe_browse_btn.clicked.connect(self._on_exe_browse_btn_clicked)
            _r2_exe_row.addWidget(self.exe_input, 1)
            _r2_exe_row.addWidget(self._exe_browse_btn)
            _r2_exe_v.addLayout(_r2_exe_row)
            self.exe_hint = QLabel("")
            self.exe_hint.setObjectName("fieldHint")
            self.exe_hint.setVisible(False)
            _r2_install_widget = QWidget()
            _r2_install_widget.setContentsMargins(0, 6, 0, 0)
            _r2_install_v = QVBoxLayout(_r2_install_widget)
            _r2_install_v.setContentsMargins(0, 0, 0, 0)
            _r2_install_v.setSpacing(4)
            _r2_install_row = QHBoxLayout()
            _r2_install_row.setContentsMargins(0, 0, 0, 0)
            _r2_install_row.setSpacing(8)
            self._install_dir_input = QLineEdit("")
            self._install_dir_input.setObjectName("dlgInput")
            self._install_dir_input.setPlaceholderText("Game install folder")
            self._install_dir_browse_btn = QPushButton("Browse")
            self._install_dir_browse_btn.setObjectName("secondary")
            self._install_dir_browse_btn.clicked.connect(self._browse_install_dir)
            _r2_install_row.addWidget(self._install_dir_input, 1)
            _r2_install_row.addWidget(self._install_dir_browse_btn)
            _r2_install_v.addLayout(_r2_install_row)
            _r2_exe_v.addWidget(_r2_install_widget)
            self._install_dir_widget = _r2_install_widget
            self._row2_stack.addWidget(_r2_exe)   # index 0

            # Page 1 — Steam combo + Rescan + hint
            _r2_steam = QWidget()
            _r2_steam_v = QVBoxLayout(_r2_steam)
            _r2_steam_v.setContentsMargins(0, 0, 0, 0)
            _r2_steam_v.setSpacing(4)
            _r2_steam_row = QHBoxLayout()
            _r2_steam_row.setContentsMargins(0, 0, 0, 0)
            _r2_steam_row.setSpacing(8)
            self.steam_combo = NAGOComboBox()
            self.steam_combo.setObjectName("dlgCombo")
            self.steam_combo.currentIndexChanged.connect(self._on_steam_game_picked)
            _r2_steam_row.addWidget(self.steam_combo, 1)
            self._steam_rescan_btn = QPushButton("↺  Rescan")
            self._steam_rescan_btn.setObjectName("secondary")
            self._steam_rescan_btn.clicked.connect(self._rescan_steam)
            _r2_steam_row.addWidget(self._steam_rescan_btn)
            _r2_steam_v.addLayout(_r2_steam_row)
            self.steam_hint = QLabel("")
            self.steam_hint.setObjectName("fieldHint")
            _r2_steam_v.addWidget(self.steam_hint)
            self._row2_stack.addWidget(_r2_steam)   # index 1

            # Page 2 — GOG combo + Rescan + hint
            _r2_gog = QWidget()
            _r2_gog_v = QVBoxLayout(_r2_gog)
            _r2_gog_v.setContentsMargins(0, 0, 0, 0)
            _r2_gog_v.setSpacing(4)
            _r2_gog_row = QHBoxLayout()
            _r2_gog_row.setContentsMargins(0, 0, 0, 0)
            _r2_gog_row.setSpacing(8)
            self.gog_combo = NAGOComboBox()
            self.gog_combo.setObjectName("dlgCombo")
            _r2_gog_row.addWidget(self.gog_combo, 1)
            _gog_rescan_btn = QPushButton("↺  Rescan")
            _gog_rescan_btn.setObjectName("secondary")
            _gog_rescan_btn.clicked.connect(self._rescan_gog)
            _r2_gog_row.addWidget(_gog_rescan_btn)
            _r2_gog_v.addLayout(_r2_gog_row)
            self.gog_hint = QLabel("")
            self.gog_hint.setObjectName("fieldHint")
            _r2_gog_v.addWidget(self.gog_hint)
            self._row2_stack.addWidget(_r2_gog)   # index 2

            sv.addWidget(self._row2_stack)

            # ── Row 4: installer options (Proton+Install only) ────────────
            self._inst_options_row = QWidget()
            _ior = QHBoxLayout(self._inst_options_row)
            _ior.setContentsMargins(0, 0, 0, 0)
            _ior.setSpacing(20)
            self._inst_scale_cb = NAGOCheckBox("Scale")
            self._inst_scale_cb.setChecked(True)
            self._inst_scale_cb.setToolTip(
                "Sets Wine screen DPI to match your display's logical DPI for this\n"
                "installer run only. Restored (key deleted) when the installer exits."
            )
            self._inst_jp_locale_cb = NAGOCheckBox("Japanese locale")
            self._inst_jp_locale_cb.setChecked(False)
            self._inst_jp_locale_cb.setToolTip(
                "Adds LANG=ja_JP.UTF-8  LC_ALL=ja_JP.UTF-8  LANGUAGE=ja_JP\n"
                "to the installer environment. Also saved as the game's launch locale."
            )
            _ior.addWidget(self._inst_scale_cb)
            _ior.addWidget(self._inst_jp_locale_cb)
            _ior.addStretch(1)
            self._inst_options_row.setVisible(False)
            sv.addWidget(self._inst_options_row)

            # ── Stubs for attributes not built in Add flow ────────────────
            self._gog_stack         = None
            self._gog_import_widget = None
            self._gog_browse_widget = None
            self.gog_exe_input      = QLineEdit()
            self._gog_browse_hint   = QLabel("")
            self._steam_name_lbl    = QLabel()
            self.steam_widget       = _r2_steam
            self.gog_widget         = _r2_gog
            self._exe_row_widget    = _r2_exe
            self._content_stack     = self._row2_stack
            self._src_stack         = self._row1_stack

            self.gog_combo.currentIndexChanged.connect(self._on_gog_game_picked)
            self._gog_picked_connected = True

            # Set initial pages to match starting runner
            _R1 = {"native": 0, "proton": 1, "import": 2}
            _R2 = {"native": 0, "proton": 0, "import": 0}  # exe row by default
            self._row1_stack.setCurrentIndex(_R1.get(cur, 1))
            self._row2_stack.setCurrentIndex(_R2.get(cur, 0))

        else:
            # ── Edit flow ─────────────────────────────────────────────────
            # Simple QStackedWidget — type is fixed at open, never switches.
            self._src_stack = _AdaptiveStack()
            self._src_stack.setSizePolicy(
                QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed
            )
            sv.setAlignment(Qt.AlignmentFlag.AlignTop)

            # Page 0 — Native / Proton: exe input + Browse
            _pg_exe = QWidget()
            _pge_v = QVBoxLayout(_pg_exe)
            _pge_v.setContentsMargins(0, 0, 0, 0)
            _pge_v.setSpacing(4)
            _pge_row = QHBoxLayout()
            _pge_row.setContentsMargins(0, 0, 0, 0)
            _pge_row.setSpacing(8)
            self.exe_input = QLineEdit(
                self.game.get("exe_path", "") if cur not in ("steam", "gog") else ""
            )
            self.exe_input.setObjectName("dlgInput")
            self.exe_input.setPlaceholderText("Path to game executable")
            self._exe_browse_btn = QPushButton("Browse")
            self._exe_browse_btn.setObjectName("secondary")
            self._exe_browse_btn.clicked.connect(self._on_exe_browse_btn_clicked)
            _pge_row.addWidget(self.exe_input, 1)
            _pge_row.addWidget(self._exe_browse_btn)
            _pge_v.addLayout(_pge_row)
            self._src_stack.addWidget(_pg_exe)   # index 0

            # Page 1 — Steam: combo + name label + Rescan
            _pg_steam = QWidget()
            _pgs_v = QVBoxLayout(_pg_steam)
            _pgs_v.setContentsMargins(0, 0, 0, 0)
            _pgs_v.setSpacing(4)
            _pgs_row = QHBoxLayout()
            _pgs_row.setContentsMargins(0, 0, 0, 0)
            _pgs_row.setSpacing(8)
            self.steam_combo = NAGOComboBox()
            self.steam_combo.setObjectName("dlgCombo")
            self.steam_combo.currentIndexChanged.connect(self._on_steam_game_picked)
            _pgs_row.addWidget(self.steam_combo, 1)
            self._steam_name_lbl = QLabel()
            self._steam_name_lbl.setObjectName("dlgReadOnly")
            self._steam_name_lbl.setVisible(False)
            _pgs_row.addWidget(self._steam_name_lbl, 1)
            self._steam_rescan_btn = QPushButton("↺  Rescan")
            self._steam_rescan_btn.setObjectName("secondary")
            self._steam_rescan_btn.clicked.connect(self._rescan_steam)
            _pgs_row.addWidget(self._steam_rescan_btn)
            _pgs_v.addLayout(_pgs_row)
            self.steam_hint = QLabel("")
            self.steam_hint.setObjectName("fieldHint")
            _pgs_v.addWidget(self.steam_hint)
            self._src_stack.addWidget(_pg_steam)   # index 1

            # Page 2 — GOG: inner stack (import combo / browse path)
            _pg_gog = QWidget()
            self._gog_mode          = "import"
            self._gog_import_source = None
            self._gog_browse_name   = ""
            _pgg_v = QVBoxLayout(_pg_gog)
            _pgg_v.setContentsMargins(0, 0, 0, 0)
            _pgg_v.setSpacing(4)
            self._gog_stack = QStackedWidget()
            self._gog_import_widget = QWidget()
            _giw_v = QVBoxLayout(self._gog_import_widget)
            _giw_v.setContentsMargins(0, 0, 0, 0)
            _giw_v.setSpacing(4)
            _giw_row = QHBoxLayout()
            _giw_row.setContentsMargins(0, 0, 0, 0)
            _giw_row.setSpacing(8)
            self.gog_combo = NAGOComboBox()
            self.gog_combo.setObjectName("dlgCombo")
            _giw_row.addWidget(self.gog_combo, 1)
            _gog_rescan_btn = QPushButton("↺  Rescan")
            _gog_rescan_btn.setObjectName("secondary")
            _gog_rescan_btn.clicked.connect(self._rescan_gog)
            _giw_row.addWidget(_gog_rescan_btn)
            _giw_v.addLayout(_giw_row)
            self.gog_hint = QLabel("")
            self.gog_hint.setObjectName("fieldHint")
            _giw_v.addWidget(self.gog_hint)
            self._gog_stack.addWidget(self._gog_import_widget)
            self._gog_browse_widget = QWidget()
            _gbw_v = QVBoxLayout(self._gog_browse_widget)
            _gbw_v.setContentsMargins(0, 0, 0, 0)
            _gbw_v.setSpacing(4)
            _gbw_row = QHBoxLayout()
            _gbw_row.setContentsMargins(0, 0, 0, 0)
            _gbw_row.setSpacing(8)
            self.gog_exe_input = QLineEdit()
            self.gog_exe_input.setObjectName("dlgInput")
            self.gog_exe_input.setPlaceholderText("Path to game executable…")
            _gbw_row.addWidget(self.gog_exe_input, 1)
            _gog_browse_file_btn = QPushButton("Browse")
            _gog_browse_file_btn.setObjectName("secondary")
            _gog_browse_file_btn.clicked.connect(self._browse_gog_exe)
            _gbw_row.addWidget(_gog_browse_file_btn)
            _gbw_v.addLayout(_gbw_row)
            self._gog_browse_hint = QLabel("")
            self._gog_browse_hint.setObjectName("fieldHint")
            # install_dir field not shown in Edit Game — stub only so shared
            # methods (_auto_populate_install_dir, _browse_install_dir) don't crash.
            self._gog_install_dir_input = QLineEdit()
            self._gog_stack.addWidget(self._gog_browse_widget)
            _pgg_v.addWidget(self._gog_stack)
            self._src_stack.addWidget(_pg_gog)   # index 2

            self.steam_widget       = _pg_steam
            self.gog_widget         = _pg_gog
            self.exe_hint           = None
            self._exe_row_widget    = None
            self._content_stack     = None
            self._row1_stack        = None
            self._row2_stack        = None
            self._install_mode_row  = None
            self._install_mode_btns = []
            self._proton_install_mode = "browse"
            self._inst_options_row  = None
            self._inst_scale_cb     = None
            self._inst_jp_locale_cb = None

            self.gog_combo.currentIndexChanged.connect(self._on_gog_game_picked)
            self._gog_picked_connected = True

            _EDIT_PAGE = {"native": 0, "proton": 0, "steam": 1, "gog": 2}
            self._src_stack.setCurrentIndex(_EDIT_PAGE.get(cur, 0))
            sv.addWidget(self._src_stack)

        self._exe_store_row = self._src_stack if self.game else self._row1_stack

        # Store detection hint — shown below the exe input when a store marker
        # is found (GOG/Epic).  Shared between Add and Edit flows.
        self._store_hint_lbl = QLabel("")
        self._store_hint_lbl.setObjectName("fieldHint")
        self._store_hint_widget = self._store_hint_lbl
        self._store_hint_widget.setVisible(False)
        sv.addWidget(self._store_hint_widget)

        ser.addWidget(source_frame, 5, Qt.AlignmentFlag.AlignTop)
        layout.addWidget(store_exe_row, 0, Qt.AlignmentFlag.AlignTop)


        # ── Steam info card — standalone, below source frame ──────────────
        self._steam_general_info_card = QFrame()
        self._steam_general_info_card.setObjectName("settingsSection")
        _sgi_layout = QVBoxLayout(self._steam_general_info_card)
        _sgi_layout.setContentsMargins(12, 10, 12, 10)
        self._steam_general_info = QLabel(
            "Steam manages launch arguments, environment variables, and hooks for its own games. "
            "To configure these, right-click the game in Steam → Properties → General → Launch Options. "
            "Japanese locale must also be set through Steam's own language settings."
        )
        self._steam_general_info.setWordWrap(True)
        self._steam_general_info.setObjectName("asiLabel")
        _sgi_layout.addWidget(self._steam_general_info)
        self._steam_general_info_card.setVisible(False)
        layout.addWidget(self._steam_general_info_card, 0, Qt.AlignmentFlag.AlignTop)

        # Populate pickers and set initial visibility
        self._populate_steam_games()
        self._populate_gog_games()
        if cur == "steam":
            saved_appid = self.game.get("exe_path", "")
            if saved_appid:
                for i in range(self.steam_combo.count()):
                    if self.steam_combo.itemData(i) == saved_appid:
                        self.steam_combo.setCurrentIndex(i)
                        break
            # Edit flow — show label instead of combo; hide rescan
            if self.game and self.game.get("id"):
                name = self.steam_combo.currentText() or saved_appid or "Unknown"
                self._steam_name_lbl.setText(name)
                self.steam_combo.setVisible(False)
                self._steam_name_lbl.setVisible(True)
                self._steam_rescan_btn.setVisible(False)
        elif cur == "gog":
            saved_exe = self.game.get("exe_path", "")
            if saved_exe:
                # Try to find in Heroic/Lutris list first
                _found_in_import = False
                for i in range(self.gog_combo.count()):
                    d = self.gog_combo.itemData(i) or {}
                    if d.get("exe_path") == saved_exe:
                        self.gog_combo.setCurrentIndex(i)
                        _found_in_import = True
                        break
                if not _found_in_import:
                    # Not in Heroic/Lutris — was saved via Browse mode
                    self._set_gog_mode("browse")
                    self.gog_exe_input.setText(saved_exe)
                    # Prime _gog_browse_name so mode switches work correctly.
                    # umu_options doesn't exist yet here — the dialog open trigger
                    # handles the actual search after build via self.game["name"].
                    result = scan_install_dir_for_store(saved_exe)
                    self._gog_browse_name = (result["name"] or
                        Path(saved_exe).stem.replace("_", " ").title())
                    if result["store"] == "gog":
                        self._set_store_hint("✓ GOG install detected")

        # _src_stack page already set to match `cur` during card construction above.

        # Reset FSR scan guard when exe path changes — harmless no-op in Add flow.
        self.exe_input.editingFinished.connect(
            lambda: setattr(self, "_fsr_scan_done", False)
        )

        # ── Proton row: version selector + icon-only tool buttons inline ───
        self._proton_row_widget = QWidget()
        self._proton_row_widget.setSizePolicy(
            QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Minimum
        )
        proton_row_h = QHBoxLayout(self._proton_row_widget)
        proton_row_h.setContentsMargins(0, 0, 0, 0)
        proton_row_h.setSpacing(10)

        # ── Single card: Proton version selector + inline icon-only tool buttons
        self.proton_frame = QFrame()
        self.proton_frame.setObjectName("settingsSection")
        self.proton_frame.setSizePolicy(
            QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Minimum
        )
        pv = QVBoxLayout(self.proton_frame)
        pv.setSpacing(10)
        pv.addWidget(self._section_label("Proton / umu"))

        # Browse/Install toggle now lives on the exe path card above (see
        # source_frame construction) — kept this comment as a pointer since
        # it's easy to go looking for it here next to the Proton selector
        # it used to sit above.


        default_proton = self.game.get("proton_path") or self.config.get("default_proton", "")

        # Build Winecfg + Winetricks buttons first — passed into ProtonComboBox
        # so they sit inline on the same row as the combo and Rescan button.
        self._winecfg_btn = QPushButton()
        self._winecfg_btn.setIcon(ph_icon("paint-brush", 22))
        self._winecfg_btn.setObjectName("secondary")
        self._winecfg_btn.setToolTip("Winecfg — configure this game's Wine prefix")
        self._winecfg_btn.setFixedSize(36, 36)
        self._winecfg_btn.clicked.connect(self._run_winecfg)

        self._winetricks_btn = QPushButton()
        self._winetricks_btn.setIcon(ph_icon("wrench", 22))
        self._winetricks_btn.setObjectName("secondary")
        self._winetricks_btn.setToolTip("Winetricks — install DLLs and runtimes into this prefix")
        self._winetricks_btn.setFixedSize(36, 36)
        self._winetricks_btn.clicked.connect(self._run_winetricks)

        self._run_in_prefix_btn = QPushButton()
        self._run_in_prefix_btn.setIcon(ph_icon("file-archive", 22))
        self._run_in_prefix_btn.setObjectName("secondary")
        self._run_in_prefix_btn.setToolTip("Run executable in prefix — install software (e.g. Ubisoft Connect)\ninto this game's Wine prefix")
        self._run_in_prefix_btn.setFixedSize(36, 36)
        self._run_in_prefix_btn.clicked.connect(lambda: self._run_exe_in_prefix())

        self.proton_selector = ProtonComboBox(
            default_proton,
            extra_buttons=[self._winecfg_btn, self._winetricks_btn, self._run_in_prefix_btn],
            config=self.config,
        )

        pv.addWidget(self.proton_selector, 1)
        proton_row_h.addWidget(self.proton_frame)
        # Proton selection change (including after Rescan) → re-run umu search
        self.proton_selector.combo.currentIndexChanged.connect(
            lambda: self.umu_options.search(self.name_input.toPlainText().strip())
            if hasattr(self, "umu_options") and self.name_input.toPlainText().strip()
            else None
        )
        # Re-evaluate Winetricks availability whenever the Proton selection changes —
        # winetricks only works on protonfixes-bundling builds, not plain Valve Proton.
        self.proton_selector.combo.currentIndexChanged.connect(
            lambda: self._sync_winetricks_for_proton()
        )

        # Disable Winetricks/Winecfg for unsaved games — they need a Wine install inside
        # the prefix which requires umu to initialise it first.  Run in Prefix is allowed
        # because it IS the tool used to set the prefix up before first launch.
        if not self.game.get("id"):
            self._winetricks_btn.setEnabled(False)
            self._winecfg_btn.setEnabled(False)
            _tip = "Save the game, or use Run in Prefix, to create its prefix first"
            self._winetricks_btn.setToolTip(_tip)
            self._winecfg_btn.setToolTip(_tip)
        else:
            # Saved game: prefix exists, so apply the Proton-capability gate to winetricks.
            self._sync_winetricks_for_proton()

        # umu_options is built below and added to the Advanced tab Compatibility card
        # umu is unconditional for Proton — no enabled flag needed
        self.umu_options = UmuOptionsWidget(
            gameid ="",
            store  =self.game.get("umu_store", "none") if self.game else "",
            store_combo=self.store_combo,
            show_store=False,  # protonfix disabled (NAGO 04:20): store row never shown
        )
        self._store_card.setVisible(False)

        self._proton_row_widget.setVisible(cur in ("proton", "gog"))

        # ── store_combo change handler intentionally NOT wired (NAGO 04:20) ───
        # It drove _umu_on_store_changed → protonfix auto-search, now disabled.
        # The combo is force-set to "none", disabled and hidden above.

        # ── HDR checkbox ────────────────────────────────────────────────────
        # Lives in the dialog footer (added near the Cancel/Save row below), not
        # in a body card — keeps it visible from both tabs and frees General-tab
        # space. The detected-monitor list, which used to sit inline beside the
        # box, is now appended to the tooltip (the footer has no room for a label).
        _hdr_enabled = bool(self.game.get("hdr_enabled", 0) if self.game else 0)
        self._hdr_cb = NAGOCheckBox("Enable HDR")
        self._hdr_cb.setChecked(_hdr_enabled)
        # Base tooltip text — the monitor scan result is appended to this after a
        # scan, so we keep the base around to rebuild the full tooltip each time.
        self._hdr_tooltip_base = (
            "Enables HDR + wide colour gamut on all HDR-capable monitors before the\n"
            "game starts, and restores SDR on exit.\n"
            "KDE Plasma: uses kscreen-doctor.\n"
            "GNOME 48+:  uses gdctl.\n"
            "Silently skipped if the required tool is not found.\n"
            "\n"
            "Applies to all game types (native, Proton, GOG) — flips the monitor at\n"
            "the OS level regardless. For Proton/GOG also sets PROTON_ENABLE_WAYLAND=1\n"
            "and PROTON_ENABLE_HDR=1 so the runtime emits HDR signals."
        )
        self._hdr_cb.setToolTip(self._hdr_tooltip_base)

        def _hdr_scan_monitors():
            # Off-thread scan: kscreen-doctor / gdctl + EDID reads can take a
            # few hundred ms or hit a 3s timeout, which used to freeze the
            # dialog. The worker is parentless (Qt would otherwise destroy it
            # before accept/reject teardown) and kept alive via a class-level
            # set until finished; the result slot tolerates the dialog being
            # closed mid-scan via try/except RuntimeError on the widget.
            _worker = _HDRScanWorker()
            _HDRScanWorker._keepalive.add(_worker)

            def _on_done(items):
                if items:
                    _detected = "Detected HDR-capable monitors:\n  " + "\n  ".join(items)
                else:
                    _detected = "No HDR-capable monitors detected."
                try:
                    self._hdr_cb.setToolTip(self._hdr_tooltip_base + "\n\n" + _detected)
                except RuntimeError:
                    # Dialog destroyed mid-scan — drop the result silently.
                    pass

            def _on_finished():
                _HDRScanWorker._keepalive.discard(_worker)

            _worker.result_ready.connect(_on_done)
            _worker.finished.connect(_on_finished)
            _worker.finished.connect(_worker.deleteLater)
            _worker.start()

        def _on_hdr_toggled(enabled: bool):
            if enabled:
                _hdr_scan_monitors()
            # HDR requires PROTON_ENABLE_WAYLAND=1 — keep the Wayland checkbox in sync
            self._sync_upscale_conflicts()

        self._hdr_cb.toggled.connect(_on_hdr_toggled)

        # If already enabled on open, populate the tooltip — but defer to the
        # next event loop tick so the dialog paints first. The scan itself now
        # runs on a worker thread, so the dialog stays responsive throughout.
        if _hdr_enabled:
            QTimer.singleShot(0, _hdr_scan_monitors)

        # ── Gamescope checkbox — created here (before _on_type_change fires),
        # placed into the footer row below. Same pattern as _hdr_cb.
        _gs_enabled = bool(self.game.get("gamescope_enabled", 0) if self.game else 0)
        self._gamescope_cb = NAGOCheckBox("Gamescope")
        self._gamescope_cb.setChecked(_gs_enabled)
        self._gamescope_cb.setToolTip(
            "Wraps the launch command with gamescope.\n"
            "Resolution is auto-detected from your primary screen.\n"
            "When HDR is also on: adds --hdr-enabled and injects DXVK_HDR=1.\n"
            "Requires gamescope to be installed (dnf install gamescope).\n"
            "Not applied to Steam-type games."
        )
        # Disable + grey the checkbox at dialog init if gamescope isn't installed.
        # Saves the user from checking it and only discovering at launch that it
        # was silently skipped. We stash the original DB value in
        # _gs_missing_pref so a user's preference isn't silently lost on save
        # just because they happened to open the dialog while gamescope was
        # uninstalled — the save path honours the stash when it exists.
        if not shutil.which("gamescope"):
            self._gs_missing_pref = _gs_enabled
            self._gamescope_cb.setChecked(False)
            self._gamescope_cb.setEnabled(False)
            self._gamescope_cb.setToolTip(
                "Gamescope is not installed.\n"
                "Install via:  dnf install gamescope\n"
                "Then reopen this dialog."
            )

        # Gamescope on/off changes whether HDR needs PROTON_ENABLE_WAYLAND —
        # re-sync the Wayland checkbox whenever gamescope is toggled.
        self._gamescope_cb.toggled.connect(lambda _: self._sync_upscale_conflicts())

        # ── Bottom cards row ─────────────────────────────────────────────
        # Edit: Display (+ Save Backups). Add: Proton/umu card instead —
        # swapped with the Compatibility tab, which gets Display for Add.
        # Forked because the two flows now show different things here;
        # the underlying widgets (_display_card_frame / _proton_row_widget)
        # are each still built exactly once.
        _cards_row = QHBoxLayout()
        _cards_row.setSpacing(8)
        if self.game:
            self._build_display_card(_cards_row)
            if self.game.get("id"):
                self._build_backup_card(_cards_row)
        else:
            _cards_row.addWidget(self._proton_row_widget, 1, Qt.AlignmentFlag.AlignTop)
        general_layout.addLayout(_cards_row)

        general_layout.addStretch()
        # End of General tab — restore the dialog-level layout for tab + footer
        self._tabs.addTab(general_page, "General")
        layout = _orig_layout

        # ── Compatibility tab page ─────────────────────────────────────────
        compat_page = QWidget()
        compat_layout = QVBoxLayout(compat_page)
        compat_layout.setContentsMargins(0, 8, 0, 0)
        compat_layout.setSpacing(14)

        # Proton / umu card on Edit (unchanged). Add gets the Display card
        # here instead — swapped with the General tab's Bottom cards row.
        if self.game:
            compat_layout.addWidget(self._proton_row_widget, 0, Qt.AlignmentFlag.AlignTop)
        else:
            self._build_display_card(compat_layout)

        # Compatibility card and AI Upscaling card are appended below
        # after they are constructed in the Advanced block (they need
        # widgets built there first). See _compat_layout ref below.
        self._compat_layout = compat_layout  # used below to adopt cards

        self._tabs.addTab(compat_page, "Compatibility")

        # ── Advanced tab page ──────────────────────────────────────────────
        advanced_page = QWidget()
        adv_layout = QVBoxLayout(advanced_page)
        adv_layout.setContentsMargins(0, 8, 0, 0)
        adv_layout.setSpacing(14)

        # Steam info card — shown instead of field cards for Steam-type games
        self._adv_steam_info_card = QFrame()
        self._adv_steam_info_card.setObjectName("settingsSection")
        _asi_layout = QVBoxLayout(self._adv_steam_info_card)
        _asi_layout.setContentsMargins(12, 10, 12, 10)
        _asi_label = QLabel(
            "Steam manages launch arguments, environment variables, and hooks for its own games.\n\n"
            "To set launch options: right-click the game in Steam → Properties → General → Launch Options."
        )
        _asi_label.setWordWrap(True)
        _asi_label.setObjectName("asiLabel")
        _asi_layout.addWidget(_asi_label)
        self._adv_steam_info_card.setVisible(False)
        adv_layout.addWidget(self._adv_steam_info_card)

        # Card: Launch Arguments — appended to the game's executable as argv
        args_frame = QFrame()
        args_frame.setObjectName("settingsSection")
        af = QVBoxLayout(args_frame)
        af.setSpacing(8)
        af.addWidget(self._section_label("Launch Arguments"))
        self.launch_args_input = QLineEdit(self.game.get("launch_args", "") if self.game else "")
        self.launch_args_input.setObjectName("dlgInputMono")
        self.launch_args_input.setPlaceholderText("e.g. -windowed -novid -skipintro")
        self.launch_args_input.setToolTip("Appended to the game's executable as command-line arguments.\nIgnored for Steam-type games (Steam manages launch options itself).")
        af.addWidget(self.launch_args_input)
        adv_layout.addWidget(args_frame)
        self._adv_args_frame = args_frame

        # Card: Environment Variables — KEY=VALUE pairs, space-separated
        env_frame = QFrame()
        env_frame.setObjectName("settingsSection")
        ef = QVBoxLayout(env_frame)
        ef.setSpacing(10)
        ef.addWidget(self._section_label("Environment Variables"))
        self.env_vars_input = QLineEdit(self.game.get("env_vars", "") if self.game else "")
        self.env_vars_input.setObjectName("dlgInputMono")
        self.env_vars_input.setPlaceholderText("e.g. PROTON_LOG=1 DXVK_HUD=fps MANGOHUD=1")
        self.env_vars_input.setToolTip("Prepended to the launch command.\nUseful for DXVK/VKD3D tuning, Proton flags, MangoHud, FSR overrides.\nQuote values with spaces.")
        ef.addWidget(self.env_vars_input)
        # Steam-type warning — shown in place of the normal fields when type=steam
        self._steam_adv_warning = QLabel(
            "Steam manages environment variables, launch arguments, and hooks for its own games. "  
            "Set these in Steam instead: right-click the game \u2192 Properties \u2192 General \u2192 Launch Options."
        )
        self._steam_adv_warning.setObjectName("steamAdvWarning")
        self._steam_adv_warning.setWordWrap(True)
        self._steam_adv_warning.setVisible(False)
        ef.addWidget(self._steam_adv_warning)
        adv_layout.addWidget(env_frame)
        self._adv_env_frame = env_frame

        # Card: Launch Hooks — pre/post commands stacked vertically
        hooks_frame = QFrame()
        hooks_frame.setObjectName("settingsSection")
        hf = QVBoxLayout(hooks_frame)
        hf.setSpacing(8)

        hf.addWidget(self._section_label("Launch Hooks"))

        self.pre_launch_input = QLineEdit(self.game.get("pre_launch_cmd", "") if self.game else "")
        self.pre_launch_input.setObjectName("dlgInputMono")
        self.pre_launch_input.setPlaceholderText("Pre-launch command")
        self.pre_launch_input.setToolTip("Runs once before the game starts.")
        hf.addWidget(self.pre_launch_input)

        self.post_exit_input = QLineEdit(self.game.get("post_exit_cmd", "") if self.game else "")
        self.post_exit_input.setObjectName("dlgInputMono")
        self.post_exit_input.setPlaceholderText("Post-exit command")
        self.post_exit_input.setToolTip("Runs once after the game exits.")
        hf.addWidget(self.post_exit_input)

        adv_layout.addWidget(hooks_frame)
        self._adv_hooks_frame = hooks_frame

        # Card: Compatibility — title header + three body rows
        vn_frame = QFrame()
        vn_frame.setObjectName("settingsSection")
        vf = QVBoxLayout(vn_frame)
        vf.setSpacing(0)
        vf.setContentsMargins(0, 0, 0, 0)

        # ── Header: "Compatibility" title — tight bottom padding ──────────────
        _compat_header = QWidget()
        _compat_header.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        _compat_header_h = QHBoxLayout(_compat_header)
        _compat_header_h.setContentsMargins(12, 9, 12, 4)
        _compat_header_h.setSpacing(0)
        _compat_header_h.addWidget(self._section_label("Compatibility"))
        _compat_header_h.addStretch()
        vf.addWidget(_compat_header)

        def _hsep():
            s = QFrame()
            s.setFrameShape(QFrame.Shape.HLine)
            s.setObjectName("dialogSepFlush")
            return s

        def _cv():
            s = QFrame()
            s.setFrameShape(QFrame.Shape.NoFrame)
            s.setFixedSize(1, 14)
            s.setObjectName("dialogSepV")
            return s

        # ── Body grid: outer grid holds rows; inner cbx_grid aligns checkboxes across rows ──
        _compat_grid = QWidget()
        _compat_grid.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        _grid = QGridLayout(_compat_grid)
        _grid.setContentsMargins(12, 0, 12, 0)
        _grid.setHorizontalSpacing(0)
        _grid.setVerticalSpacing(0)
        _grid.setColumnStretch(0, 1)

        # Shared inner grid for checkbox rows — 7 cols: cb0 | vsep | cb1 | vsep | cb2 | vsep | cb3
        # Fixed column widths ensure vseps land on the same x across both rows.
        _cbx_grid = QWidget()
        _cbx_grid.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        _cbx_grid.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        _cg = QGridLayout(_cbx_grid)
        _cg.setContentsMargins(0, 8, 0, 8)
        _cg.setHorizontalSpacing(10)
        _cg.setVerticalSpacing(8)
        for col in (1, 3, 5):
            _cg.setColumnMinimumWidth(col, 1)
        for col in (0, 2, 4, 6):
            _cg.setColumnStretch(col, 0)

        def _cvsep(r, c):
            """Insert a vertical separator at grid row r, col c."""
            _s = QFrame()
            _s.setFrameShape(QFrame.Shape.NoFrame)
            _s.setFixedSize(1, 14)
            _s.setObjectName("dialogSepV")
            _cg.addWidget(_s, r, c, Qt.AlignmentFlag.AlignCenter)

        def _crow(r, w0, w1, w2, w3):
            """Add 4 checkboxes with vseps into shared grid row r."""
            _cg.addWidget(w0, r, 0, Qt.AlignmentFlag.AlignVCenter)
            _cvsep(r, 1)
            _cg.addWidget(w1, r, 2, Qt.AlignmentFlag.AlignVCenter)
            _cvsep(r, 3)
            _cg.addWidget(w2, r, 4, Qt.AlignmentFlag.AlignVCenter)
            _cvsep(r, 5)
            _cg.addWidget(w3, r, 6, Qt.AlignmentFlag.AlignVCenter)

        # ── Row 0 checkboxes ──────────────────────────────────────────────────
        _vd_saved       = (self.game.get("video_decode_mode", "default") if self.game else "default") or "default"
        _wined3d_active = bool(self.game.get("use_wined3d",  0) if self.game else 0)
        _wow64_active   = bool(self.game.get("use_wow64",    0) if self.game else 0)
        _wayland_active = bool(self.game.get("use_wayland",  0) if self.game else 0)

        self._use_gstreamer_cb = NAGOCheckBox("Force GStreamer")
        self._use_gstreamer_cb.setChecked(_vd_saved == "winegstreamer")
        self._use_gstreamer_cb.setToolTip(
            "Sets PROTON_MEDIA_USE_GST=1 — use winegstreamer instead of the default winedmo backend.\n"
            "Useful for games with video that worked in Proton 9 but broke in Proton 10+."
        )
        self._use_wined3d_cb = NAGOCheckBox("Use wined3d")
        self._use_wined3d_cb.setChecked(_wined3d_active)
        self._use_wined3d_cb.setToolTip("Sets PROTON_USE_WINED3D=1 — use OpenGL-based wined3d\ninstead of Vulkan/DXVK for d3d11/d3d10")

        self._use_wow64_cb = NAGOCheckBox("Use wow64")
        self._use_wow64_cb.setChecked(_wow64_active)
        self._use_wow64_cb.setToolTip("Sets PROTON_USE_WOW64=1 — enables wow64 for running\n32-bit games on 64-bit Wine")

        self._use_wayland_cb = NAGOCheckBox("Use Wayland")
        self._use_wayland_cb.setChecked(_wayland_active)
        self._use_wayland_cb.setToolTip("Sets PROTON_ENABLE_WAYLAND=1 — use the native Wayland backend\ninstead of X11/XWayland")
        # Remember the user's intended Wayland state. When AI upscaling is enabled it
        # force-disables this box (the upscaler forces XWayland), so we stash the real
        # preference here and restore it if upscaling is turned back off. blockSignals
        # around programmatic setChecked keeps this handler firing only on genuine clicks.
        self._wayland_user_pref = _wayland_active
        self._use_wayland_cb.toggled.connect(
            lambda c: setattr(self, "_wayland_user_pref", c)
        )

        _crow(0, self._use_wayland_cb, self._use_wined3d_cb, self._use_wow64_cb, self._use_gstreamer_cb)

        # HLine between rows
        _hsep_inner = QFrame()
        _hsep_inner.setFrameShape(QFrame.Shape.HLine)
        _hsep_inner.setObjectName("dialogSepFlush")
        _cg.addWidget(_hsep_inner, 1, 0, 1, 7)

        # ── Row 2 checkboxes ──────────────────────────────────────────────────
        _jp_active = bool(self.game.get("vn_jp_locale", 0) if self.game else 0)
        _no_esync  = bool(self.game.get("no_esync",     0) if self.game else 0)
        _no_fsync  = bool(self.game.get("no_fsync",     0) if self.game else 0)
        _no_ntsync = bool(self.game.get("no_ntsync",    0) if self.game else 0)

        self._vn_jp_locale_cb = NAGOCheckBox("Japanese locale")
        self._vn_jp_locale_cb.setChecked(_jp_active)
        self._vn_jp_locale_cb.setToolTip("Appends LANG=ja_JP.UTF-8  HOST_LC_ALL=ja_JP.UTF-8  LANGUAGE=ja_JP\nto environment at launch")

        self._no_esync_cb = NAGOCheckBox("No esync")
        self._no_esync_cb.setChecked(_no_esync)
        self._no_esync_cb.setToolTip("Sets PROTON_NO_ESYNC=1 — disable eventfd-based in-process synchronization.\nTry if games hang or crash on launch.")

        self._no_fsync_cb = NAGOCheckBox("No fsync")
        self._no_fsync_cb.setChecked(_no_fsync)
        self._no_fsync_cb.setToolTip("Sets PROTON_NO_FSYNC=1 — disable futex-based in-process synchronization.\nTry if esync alone doesn't fix hangs.")

        self._no_ntsync_cb = NAGOCheckBox("No ntsync")
        self._no_ntsync_cb.setChecked(_no_ntsync)
        self._no_ntsync_cb.setToolTip("Sets PROTON_NO_NTSYNC=1 and PROTON_USE_NTSYNC=0 — disable\nntsync. Two vars because GE-Proton versions disagree on which\none they read.")

        _crow(2, self._no_ntsync_cb, self._no_esync_cb, self._no_fsync_cb, self._vn_jp_locale_cb)

        _grid.addWidget(_cbx_grid, 0, 0)
        # Protonfix disabled (NAGO 04:20): the row-1 _hsep() divider used to separate
        # the checkbox grid from the umu Protonfixes row below it. That row is now
        # hidden, so the divider is dropped too — it would otherwise dangle under the
        # checkboxes dividing them from empty space. (Row index 2 for _umu_outer is
        # unaffected; an empty grid row collapses to zero height.)

        # umu Protonfixes row
        _umu_outer = QWidget()
        _umu_outer.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        _umu_outer_v = QVBoxLayout(_umu_outer)
        _umu_outer_v.setContentsMargins(0, 8, 0, 8)
        _umu_outer_v.setSpacing(4)
        # Top line: label · store combo · status pill
        _umu_top_h = QHBoxLayout()
        _umu_top_h.setContentsMargins(0, 0, 0, 0)
        _umu_top_h.setSpacing(10)
        _protonfix_lbl = QLabel("umu Protonfixes")
        _umu_top_h.addWidget(_protonfix_lbl)
        _umu_top_h.addWidget(_cv())
        _umu_top_h.addWidget(self.store_combo)
        _umu_top_h.addWidget(self.umu_options._pill_lbl)
        _umu_top_h.addStretch()
        _umu_outer_v.addLayout(_umu_top_h)
        # Second line: matched title · id chip. Word-wraps downward for long
        # titles; the chip hides itself when there's no match, collapsing the row.
        self.umu_options._id_lbl.setWordWrap(True)
        _umu_outer_v.addWidget(self.umu_options._id_lbl)
        _grid.addWidget(_umu_outer, 2, 0)

        # umu_options kept alive for logic but not shown
        self.umu_options.setVisible(False)
        # Protonfix disabled (NAGO 04:20): hide the entire protonfix row — the
        # "umu Protonfixes" label, separator, store combo, status pill and id chip
        # all live inside _umu_outer. Hiding the container removes the whole row
        # (and collapses its layout space) in both Add and Edit. Widgets kept
        # constructed/parented so existing references stay valid.
        _umu_outer.hide()

        vf.addWidget(_compat_grid)

        self._compat_layout.addWidget(vn_frame)
        self._adv_vn_frame = vn_frame

        # ── Card: In-Game Upscaling (FSR4 / OptiScaler) ──────────────────
        # Proton/GOG only — same visibility gating as the AI Upscaling card.
        self._ingame_upscale_frame = QFrame()
        self._ingame_upscale_frame.setObjectName("settingsSection")
        _iu_v = QVBoxLayout(self._ingame_upscale_frame)
        _iu_v.setSpacing(8)

        # Header row: title left, detection result centered, CachyOS hint right
        _iu_header = QHBoxLayout()
        _iu_header.setContentsMargins(0, 0, 0, 0)
        _iu_header.setSpacing(8)
        _iu_header.addWidget(self._section_label("FSR / OptiScaler"))
        _iu_header.addStretch()
        self._fsr_detect_lbl = QLabel("")
        self._fsr_detect_lbl.setObjectName("fieldHint")
        self._fsr_detect_lbl.setVisible(False)
        _iu_header.addWidget(self._fsr_detect_lbl)
        _iu_v.addLayout(_iu_header)

        # ── Single row: FSR4 + OptiScaler ────────────────────────────────
        _iu_row = QHBoxLayout()
        _iu_row.setSpacing(12)
        _iu_row.setContentsMargins(0, 0, 0, 0)

        _saved_fsr4 = (self.game.get("fsr4_upgrade", "") if self.game else "") or ""
        self._fsr4_cb = NAGOCheckBox("FSR4 Upgrade")
        self._fsr4_cb.setChecked(bool(_saved_fsr4))
        self._fsr4_cb.setToolTip(
            "Upgrades FSR 3.1+ games to FSR 4. No effect on FSR 1/2.\n"
            "May break games with native FSR 4 — disable if stutters occur.\n"
            "Requires GE-Proton or Proton-CachyOS."
        )
        _iu_row.addWidget(self._fsr4_cb)

        _FSR4_VERSIONS = [
            ("4.1.0", "4.1.0"),
            ("4.0.3", "4.0.3"),
            ("4.0.2", "4.0.2"),
            ("4.0.1", "4.0.1"),
            ("4.0.0", "4.0.0"),
        ]
        self._fsr4_combo = NAGOComboBox()
        self._fsr4_combo.setObjectName("dlgCombo")
        for _fv, _fl in _FSR4_VERSIONS:
            self._fsr4_combo.addItem(_fl, userData=_fv)
        _fsr4_val = _saved_fsr4 if _saved_fsr4 else "4.1.0"
        for _i in range(self._fsr4_combo.count()):
            if self._fsr4_combo.itemData(_i) == _fsr4_val:
                self._fsr4_combo.setCurrentIndex(_i)
                break
        self._fsr4_combo.setEnabled(bool(_saved_fsr4))
        _iu_row.addWidget(self._fsr4_combo)
        _iu_row.addSpacing(8)

        _iu_sep = QFrame()
        _iu_sep.setFrameShape(QFrame.Shape.VLine)
        _iu_sep.setFixedWidth(1)
        _iu_sep.setStyleSheet("QFrame { background: #3a3a3f; border: none; }")
        _iu_row.addWidget(_iu_sep)
        _iu_row.addSpacing(8)

        _saved_opti = (self.game.get("optiscaler_dll", "") if self.game else "") or ""
        self._opti_cb = NAGOCheckBox("OptiScaler")
        self._opti_cb.setChecked(bool(_saved_opti))
        self._opti_cb.setToolTip(
            "Injects OptiScaler to redirect in-game upscaler calls (DLSS/XeSS/FSR).\n"
            "Requires Proton-CachyOS — will have no effect on other Proton builds.\n"
            "Combine with FSR4 Upgrade to use FSR 4 via OptiScaler."
        )
        _iu_row.addWidget(self._opti_cb)

        _OPTI_DLLS = ["dxgi.dll", "d3d12.dll", "dbghelp.dll"]
        self._opti_dll_combo = NAGOComboBox()
        self._opti_dll_combo.setObjectName("dlgCombo")
        for _dll in _OPTI_DLLS:
            self._opti_dll_combo.addItem(_dll, userData=_dll)
        _opti_dll_val = _saved_opti if _saved_opti else "dxgi.dll"
        for _i in range(self._opti_dll_combo.count()):
            if self._opti_dll_combo.itemData(_i) == _opti_dll_val:
                self._opti_dll_combo.setCurrentIndex(_i)
                break
        self._opti_dll_combo.setEnabled(bool(_saved_opti))
        _iu_row.addWidget(self._opti_dll_combo)
        _iu_row.addStretch()
        _iu_v.addLayout(_iu_row)

        self._fsr4_cb.toggled.connect(self._fsr4_combo.setEnabled)
        self._fsr4_cb.toggled.connect(self._on_fsr4_toggled)
        self._fsr_scan_done: bool = False  # guard: scan runs once per exe path
        self._opti_cb.toggled.connect(self._opti_dll_combo.setEnabled)

        # Scan once on dialog open if FSR4 was already saved for this game.
        if self.game and self._fsr4_cb.isChecked():
            QTimer.singleShot(0, self._run_fsr_scan)

        self._compat_layout.addWidget(self._ingame_upscale_frame)
        self._upscale_frame = QFrame()
        self._upscale_frame.setObjectName("settingsSection")
        _upscale_v = QVBoxLayout(self._upscale_frame)
        _upscale_v.setSpacing(8)
        _upscale_v.addWidget(self._section_label("AI Upscaling"))

        _upscale_row = QHBoxLayout()
        _upscale_row.setSpacing(12)
        _upscale_row.setContentsMargins(0, 0, 0, 0)

        _upscale_enabled = bool(self.game.get("upscale_enabled", 0) if self.game else 0)
        self._upscale_cb = NAGOCheckBox("Enable AI upscaling")
        self._upscale_cb.setChecked(_upscale_enabled)
        self._upscale_cb.setToolTip(
            "Launches linux-rt-upscaler alongside this game.\n"
            "Requires 'upscale' command to be installed (pip install linux-rt-upscaler).\n"
            "For Proton/GOG games, PROTON_ENABLE_WAYLAND=0 is injected automatically.")
        _upscale_row.addWidget(self._upscale_cb)
        _upscale_row.addSpacing(16)

        _UPSCALE_MODELS = [
            ("veryfast", "veryfast — fastest, lowest quality"),
            ("faster",   "faster"),
            ("fast",     "fast — default, recommended"),
            ("3x12",     "3x12"),
            ("4x12",     "4x12"),
            ("4x16",     "4x16"),
            ("4x24",     "4x24 — balanced"),
            ("4x32",     "4x32"),
            ("8x32",     "8x32 — highest quality, slowest"),
        ]
        self._upscale_model_combo = NAGOComboBox()
        self._upscale_model_combo.setObjectName("dlgCombo")
        for _mv, _ml in _UPSCALE_MODELS:
            self._upscale_model_combo.addItem(_ml, userData=_mv)
        _saved_model = (self.game.get("upscale_model", "fast") if self.game else "fast") or "fast"
        for _i in range(self._upscale_model_combo.count()):
            if self._upscale_model_combo.itemData(_i) == _saved_model:
                self._upscale_model_combo.setCurrentIndex(_i)
                break
        self._upscale_model_combo.setEnabled(_upscale_enabled)
        _upscale_row.addWidget(self._upscale_model_combo)
        _upscale_row.addStretch()

        self._upscale_cb.toggled.connect(self._upscale_model_combo.setEnabled)
        # Upscaling forces XWayland, so the Wayland toggle can't apply while it's on —
        # keep the UI honest by syncing the Wayland box whenever upscaling changes.
        self._upscale_cb.toggled.connect(lambda _=False: self._sync_upscale_conflicts())
        _upscale_v.addLayout(_upscale_row)

        self._compat_layout.addWidget(self._upscale_frame)
        self._upscale_frame.setVisible(cur != "steam")
        self._ingame_upscale_frame.setVisible(cur in ("proton", "gog"))
        self._compat_layout.addStretch()

        adv_layout.addStretch()
        self._tabs.addTab(advanced_page, "Advanced")

        # Compatibility and Advanced tabs only make sense once the game exists —
        # hide them in Add flow.
        if not self.game:
            self._tabs.setTabVisible(1, False)
            self._tabs.setTabVisible(2, False)

        # Connect signal now — all widgets exist, no hasattr guards needed.
        # Then fire once to set the correct initial state.
        self.type_combo.currentIndexChanged.connect(self._on_type_change)
        self._on_type_change(idx_for_type)

        # ── Initial umu search on dialog open ─────────────────────────────────
        # Must run AFTER the forced _on_type_change above — that call runs
        # clear_match() for any non-GOG runner, which would wipe a restored
        # gameid if this ran earlier.
        # Edit flow: if a gameid is already stored, trust it and show the match
        # pill without re-searching — a search could overwrite a valid stored value
        # with a weak/empty result. Only search if nothing is stored yet.
        # Protonfix disabled (NAGO 04:20): never restore or re-search a stored
        # match. Any umu_gameid left in the DB from older builds is ignored — the
        # pill stays "Using defaults" and no GAMEID is ever applied at launch.
        # (search() is a neutered no-op now, but we skip these calls outright so
        # the dialog doesn't touch the dormant matcher or UmuDatabase at all.)
        pass

        # ── Footer: Cancel / Save Game ─────────────────────────────────────
        footer_row = QHBoxLayout()
        # "Added on" label — Edit Game only, left-aligned, muted
        if self.game and self.game.get("added_at"):
            try:
                _added_dt = datetime.datetime.fromisoformat(self.game["added_at"])
                _added_str = _added_dt.strftime("%d %b %Y")
            except Exception:
                _added_str = self.game["added_at"]
            _added_lbl = QLabel(f"Added  {_added_str}")
            _added_lbl.setObjectName("fieldHint")
            footer_row.addWidget(_added_lbl)
        footer_row.addStretch()
        cancel_btn = QPushButton("  Cancel")
        cancel_btn.setIcon(ph_icon("x", 22))
        cancel_btn.setObjectName("secondary")
        cancel_btn.clicked.connect(self.reject)
        footer_row.addWidget(cancel_btn)
        save_btn = QPushButton("  Save Game")
        save_btn.setIcon(ph_icon("floppy-disk", 22, "#ffffff"))
        save_btn.setObjectName("primary")
        save_btn.setFixedWidth(140)
        save_btn.clicked.connect(self._save)
        footer_row.addWidget(save_btn)
        layout.addLayout(footer_row)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if hasattr(self, '_stack'):
            self._switch_tab(self._stack.currentIndex())

    def _section_label(self, text: str) -> QLabel:
        lbl = QLabel(text)
        lbl.setObjectName("cardTitle")
        return lbl

    # ── Display card (HDR + Gamescope) ────────────────────────────────────────
    def _build_display_card(self, parent_layout):
        """Build the Display card (HDR + Gamescope) on the General tab."""
        self._display_card_frame = QFrame()
        self._display_card_frame.setObjectName("settingsSection")
        self._display_card_frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        v = QVBoxLayout(self._display_card_frame)
        v.setContentsMargins(12, 10, 12, 12)
        v.setSpacing(10)

        v.addWidget(self._section_label("Display"))
        v.addWidget(self._hdr_cb)
        v.addWidget(self._gamescope_cb)
        v.addStretch()

        _is_steam = (self.game.get("game_type") if self.game else None) == "steam"
        self._display_card_frame.setVisible(not _is_steam)
        self._display_card_frame.setSizePolicy(
            QSizePolicy.Policy.Preferred,
            QSizePolicy.Policy.Expanding,
        )
        parent_layout.addWidget(self._display_card_frame, 0)

    # ── Save Backups card (Ludusavi) ──────────────────────────────────────────
    def _build_backup_card(self, parent_layout):
        """
        Build the Save Backups card on the General tab (Edit flow only).
        Mechanism differs by game type — see ludusavi_roots_for_game(). v1 is
        file-based backups only; registry saves for Proton/GOG are deferred.
        """
        frame = QFrame()
        frame.setObjectName("settingsSection")
        frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        v = QVBoxLayout(frame)
        v.setContentsMargins(12, 10, 12, 12)
        v.setSpacing(8)

        title_row = QHBoxLayout()
        title_row.setSpacing(8)
        title_row.addWidget(self._section_label("Save Backups"))
        title_row.addStretch()
        self._bk_status = QLabel("")
        self._bk_status.setObjectName("fieldHint")
        self._bk_status.hide()
        title_row.addWidget(self._bk_status)
        v.addLayout(title_row)

        # Manual / Auto backup status labels
        info_row = QHBoxLayout()
        info_row.setSpacing(12)
        self._bk_manual_lbl = QLabel("")
        self._bk_manual_lbl.setObjectName("fieldHint")
        self._bk_manual_lbl.hide()
        self._bk_auto_lbl = QLabel("")
        self._bk_auto_lbl.setObjectName("fieldHint")
        self._bk_auto_lbl.hide()
        info_row.addWidget(self._bk_manual_lbl)
        info_row.addStretch()
        info_row.addWidget(self._bk_auto_lbl)
        v.addLayout(info_row)
        v.addStretch()

        # Title-match picker (hidden until needed)
        gt = (self.game.get("game_type") or "").strip()
        if gt in ("proton", "gog"):
            _bk_tip = "Backs up file-based saves only. Registry saves aren't covered yet."
        elif gt == "steam":
            _bk_tip = "Steam Cloud may already cover this — a local copy never hurts."
        else:
            _bk_tip = "Backs up save files found in your Linux home directories."

        # Buttons row
        btn_row = QHBoxLayout()
        btn_row.setSpacing(8)
        self._bk_backup_btn = QPushButton("  Back up")
        self._bk_backup_btn.setIcon(ph_icon("floppy-disk", 18))
        self._bk_backup_btn.setIconSize(QSize(18, 18))
        self._bk_backup_btn.setObjectName("secondary")
        self._bk_backup_btn.setToolTip(_bk_tip)
        self._bk_backup_btn.clicked.connect(self._on_backup_now)
        self._bk_restore_btn = QPushButton("  Restore…")
        self._bk_restore_btn.setIcon(ph_icon("arrows-counter-clockwise", 18))
        self._bk_restore_btn.setIconSize(QSize(18, 18))
        self._bk_restore_btn.setObjectName("secondary")
        self._bk_restore_btn.setToolTip("Restores save files from the most recent backup.")
        self._bk_restore_btn.clicked.connect(self._on_restore)
        btn_row.addWidget(self._bk_backup_btn)
        btn_row.addWidget(self._bk_restore_btn)
        btn_row.addStretch()
        self._bk_auto_cb = NAGOCheckBox("Auto-backup")
        self._bk_auto_cb.setChecked(bool(self.game.get("auto_backup", 0)))
        self._bk_auto_cb.setToolTip("Automatically back up saves when the game exits.")
        btn_row.addWidget(self._bk_auto_cb)
        v.addLayout(btn_row)

        # Title-match picker (hidden until needed)
        self._bk_match_row = QWidget()
        mr = QHBoxLayout(self._bk_match_row)
        mr.setContentsMargins(0, 0, 0, 0)
        mr.setSpacing(8)
        _ml = QLabel("Match:")
        _ml.setObjectName("fieldHintSm")
        mr.addWidget(_ml)
        self._bk_match_combo = NAGOComboBox()
        self._bk_match_combo.setMinimumWidth(220)
        mr.addWidget(self._bk_match_combo, 1)
        self._bk_match_use = QPushButton("  Use")
        self._bk_match_use.setIcon(ph_icon("check", 18))
        self._bk_match_use.setIconSize(QSize(18, 18))
        self._bk_match_use.setObjectName("secondary")
        self._bk_match_use.clicked.connect(self._on_match_chosen)
        mr.addWidget(self._bk_match_use)
        v.addWidget(self._bk_match_row)
        self._bk_match_row.hide()

        frame.setSizePolicy(
            QSizePolicy.Policy.Expanding,
            QSizePolicy.Policy.Expanding,
        )
        parent_layout.addWidget(frame, 1)

        self._bk_worker = None
        self._refresh_backup_card()

    def _bk_db_read(self) -> tuple:
        """Return (ludusavi_title, last_manual, backup_location, manual_summary,
                   last_auto, auto_summary)."""
        gid = self.game.get("id")
        if not gid:
            return "", "", "", "", "", ""
        try:
            con = db_con()
            row = con.execute(
                "SELECT ludusavi_title, last_backup, backup_location, backup_summary,"
                "       last_auto_backup, auto_backup_summary"
                " FROM games WHERE id=?",
                (gid,)
            ).fetchone()
            con.close()
            if row:
                return tuple(v or "" for v in row)
        except Exception as e:
            _NAGOLog.session(f"[warn] _bk_db_read: {e}")
        return "", "", "", "", "", ""

    def _bk_db_write(self, *, title: str = None, last_backup: str = None,
                     backup_location: str = None, backup_summary: str = None,
                     last_auto_backup: str = None, auto_backup_summary: str = None):
        gid = self.game.get("id")
        if not gid:
            return
        try:
            con = db_con()
            if title is not None:
                con.execute("UPDATE games SET ludusavi_title=? WHERE id=?", (title, gid))
            if last_backup is not None:
                con.execute("UPDATE games SET last_backup=? WHERE id=?", (last_backup, gid))
            if backup_location is not None:
                con.execute("UPDATE games SET backup_location=? WHERE id=?", (backup_location, gid))
            if backup_summary is not None:
                con.execute("UPDATE games SET backup_summary=? WHERE id=?", (backup_summary, gid))
            if last_auto_backup is not None:
                con.execute("UPDATE games SET last_auto_backup=? WHERE id=?", (last_auto_backup, gid))
            if auto_backup_summary is not None:
                con.execute("UPDATE games SET auto_backup_summary=? WHERE id=?", (auto_backup_summary, gid))
            con.commit()
            con.close()
        except Exception as e:
            _NAGOLog.session(f"[warn] _bk_db_write: {e}")

    def _refresh_backup_card(self):
        installed = bool(LUDUSAVI_BIN.exists() or shutil.which("ludusavi"))
        if not installed:
            self._bk_status.setText("Ludusavi not installed -- Settings -> Ludusavi")
            self._bk_status.show()
            self._bk_manual_lbl.hide()
            self._bk_auto_lbl.hide()
            self._bk_backup_btn.setEnabled(False)
            self._bk_restore_btn.setEnabled(False)
            if hasattr(self, "_bk_auto_cb"):
                self._bk_auto_cb.setEnabled(False)
            return
        self._bk_backup_btn.setEnabled(True)
        if hasattr(self, "_bk_auto_cb"):
            self._bk_auto_cb.setEnabled(True)

        title, last_manual, _location, manual_summary, last_auto, auto_summary = self._bk_db_read()

        # Check whether each backup folder actually exists on disk.
        def _folder_exists(root: "Path") -> bool:
            if not title:
                return False
            p = root / _ludusavi_sanitize_title(title)
            return p.is_dir() and (p / "mapping.yaml").exists()

        manual_exists = bool(last_manual) and _folder_exists(LUDUSAVI_MANUAL_BACKUPS)
        auto_exists   = bool(last_auto)   and _folder_exists(LUDUSAVI_AUTO_BACKUPS)

        # Hide operation status label, show info labels.
        self._bk_status.hide()

        if manual_exists:
            _m = f"Manual: {last_manual}  ·  {manual_summary}" if manual_summary else f"Manual: {last_manual}"
            self._bk_manual_lbl.setText(_m)
            self._bk_manual_lbl.show()
        elif last_manual:
            self._bk_manual_lbl.setText("No backup on disk")
            self._bk_manual_lbl.show()
        else:
            self._bk_manual_lbl.hide()

        if auto_exists:
            _a = f"Auto: {last_auto}  ·  {auto_summary}" if auto_summary else f"Auto: {last_auto}"
            self._bk_auto_lbl.setText(_a)
            self._bk_auto_lbl.show()
        elif last_auto:
            self._bk_auto_lbl.setText("No backup on disk")
            self._bk_auto_lbl.show()
        else:
            self._bk_auto_lbl.hide()

        # Restore only makes sense when at least one backup exists on disk.
        self._bk_restore_btn.setEnabled(manual_exists or auto_exists)

    def _bk_set_busy(self, busy: bool, msg: str = ""):
        if busy:
            self._bk_backup_btn.setEnabled(False)
            self._bk_restore_btn.setEnabled(False)
            if msg:
                self._bk_status.setText(msg)
                self._bk_status.show()
        else:
            self._bk_status.hide()
            self._refresh_backup_card()

    # -- Backup flow ----------------------------------------------------------
    # Runs find first, unless a cached title triggers the stored-title shortcut
    # (which still self-heals via one preview before trusting the cache).

    def _current_exe_from_ui(self) -> str:
        """Read the exe path directly from the live UI widgets.
        This reflects whatever the user has typed/browsed, even before Save."""
        kind = self.game.get("game_type", "")
        try:
            if kind == "gog":
                if getattr(self, "_gog_mode", "import") == "browse":
                    return getattr(self, "gog_exe_input", None) and self.gog_exe_input.text().strip() or ""
                else:
                    data = getattr(self, "gog_combo", None) and self.gog_combo.currentData()
                    return (data or {}).get("exe_path", "") if data else ""
            elif kind in ("proton", "native"):
                return self._active_exe_input().text().strip()
        except Exception:
            pass
        return ""

    def _on_backup_now(self):
        if not LUDUSAVI_BIN.exists() and not shutil.which("ludusavi"):
            NAGOMessageBox.warning(self, "Ludusavi Not Installed",
                "Install Ludusavi first from Settings -> Ludusavi.")
            return
        # Read exe path directly from live UI — reflects unsaved edits.
        live_exe = self._current_exe_from_ui()
        if live_exe:
            self.game = dict(self.game, exe_path=live_exe)
        # Inject stored ludusavi_title from DB into the game dict so
        # LudusaviFindWorker can short-circuit find for confirmed titles.
        stored_title, _, _, _, _, _ = self._bk_db_read()
        game_for_find = dict(self.game, ludusavi_title=stored_title or "")
        self._bk_pending_action = "backup"
        # ── RenPy save-dir resolution ─────────────────────────────────
        if _detect_renpy((self.game.get("exe_path") or "").strip()):
            stored = (self.game.get("renpy_save_dir") or "").strip()
            if stored:
                _NAGOLog.session(f"[ludusavi][find] RenPy save dir (stored): '{stored}'")
            else:
                cands = _find_renpy_save_dir_candidates(self.game)
                if len(cands) == 1:
                    _NAGOLog.session(f"[ludusavi][find] RenPy save dir (scanned): '{cands[0]}'")
                    _renpy_store_save_dir(self.game["id"], cands[0])
                    self.game = dict(self.game, renpy_save_dir=cands[0])
                    game_for_find = dict(game_for_find, renpy_save_dir=cands[0])
                elif len(cands) > 1:
                    _NAGOLog.session(f"[ludusavi][find] RenPy save dir ambiguous: {cands} — showing picker")
                    self._show_renpy_dir_picker(cands)
                    return
                else:
                    _NAGOLog.session(f"[ludusavi][find] RenPy save dir not found — using glob fallback")
        self._bk_set_busy(True, "Matching...")
        self._bk_find = LudusaviFindWorker(game_for_find)
        self._bk_find.resolved.connect(self._on_find_resolved_for_backup)
        self._bk_find.candidates.connect(self._on_find_candidates)
        self._bk_find.failed.connect(self._on_find_failed)
        self._bk_find.finished.connect(self._bk_find.deleteLater)
        self._bk_find.start()

    def _on_find_resolved_for_backup(self, titles: list):
        # The find worker hands us a LIST of verified-backable titles. Usually
        # one; occasionally several (same game, multiple manifest entries that
        # each resolve real saves — e.g. base + a special edition with distinct
        # save folders). Back them all up sequentially via a queue.
        if not titles:
            self._on_find_candidates([])
            return
        # Capture whether this was an unambiguous single-title resolution, so
        # _finish_backup_batch knows it may cache the title after a clean backup.
        # Read it now — the worker is deleteLater'd once it finishes.
        self._bk_autocache = bool(getattr(self._bk_find, "autocacheable", False))
        self._bk_queue = list(titles)
        self._bk_results = []   # accumulates per-title summaries
        self._backup_next_in_queue()

    def _backup_next_in_queue(self):
        if not self._bk_queue:
            self._finish_backup_batch()
            return
        title = self._bk_queue.pop(0)
        self._bk_current_title = title
        n_done = len(self._bk_results) + 1
        self._bk_set_busy(True, f"Backing up ({n_done})...")
        self._bk_worker = LudusaviBackupWorker(self.game, title)
        self._bk_worker.progress.connect(lambda m: (self._bk_status.setText(m), self._bk_status.show()))
        self._bk_worker.done.connect(self._on_backup_one_done)
        self._bk_worker.failed.connect(self._on_backup_failed)
        self._bk_worker.finished.connect(self._bk_worker.deleteLater)
        self._bk_worker.start()

    def _on_backup_one_done(self, summary: dict):
        # Record this title's result and move to the next in the queue.
        summary = dict(summary)
        summary.setdefault("resolvedTitle", self._bk_current_title)
        self._bk_results.append(summary)
        self._backup_next_in_queue()

    def _finish_backup_batch(self):
        import datetime as _dt
        results = getattr(self, "_bk_results", [])
        # Keep only titles that actually backed up files.
        good = [r for r in results
                if r.get("processedGames", 0) >= 1 and r.get("fileCount", 0) >= 1]
        if not good:
            _NAGOLog.session(
                f"[ludusavi][backup] no saves found for '{self.game.get('name', '')}'  "
                f"titles tried: {[r.get('resolvedTitle', '') for r in results]}"
            )
            self._refresh_backup_card()
            self._bk_status.setText(
                "No saves found — try Back up again and pick a different match"
            )
            self._bk_status.show()
            return
        stamp = _fmt_stamp_short(_dt.datetime.now())
        # Persist the primary (first/largest) title as the diagnostic record.
        primary = max(good, key=lambda r: r.get("totalBytes", 0))
        resolved = primary.get("resolvedTitle", "")
        # Auto-cache the resolved title so future backups can use the stored-title
        # shortcut (skip find+verify entirely). Only when BOTH:
        #   • the find step resolved a single title unambiguously (autocacheable), and
        #   • exactly one title actually backed up files (no sibling ambiguity).
        # The manual picker path sets ludusavi_title itself, so we never overwrite
        # a user-confirmed title here. The shortcut self-heals on the next backup
        # if this cached title ever stops resolving saves.
        _cache_title = None
        if getattr(self, "_bk_autocache", False) and len(good) == 1 and resolved:
            _cache_title = resolved
        total_files = sum(r.get("fileCount", 0) for r in good)
        total_mb = sum(r.get("totalBytes", 0) for r in good) / (1024 * 1024)
        if len(good) == 1:
            _summary = f"{total_files} file(s) ({total_mb:.1f} MB)"
        else:
            _summary = f"{len(good)} titles, {total_files} file(s) ({total_mb:.1f} MB)"
        self._bk_db_write(last_backup=stamp, backup_location="",
                          title=_cache_title, backup_summary=_summary)
        _bk_root = getattr(self._bk_worker, "_backup_root", "") if self._bk_worker else ""
        _NAGOLog.session(
            f"[ludusavi][backup] success  game='{self.game.get('name', '')}'  "
            f"title='{primary.get('resolvedTitle', '')}'  "
            f"files={total_files}  size={total_mb:.2f} MB  "
            f"path='{_bk_root or '(default)'}'"
        )
        if _cache_title:
            _NAGOLog.session(f"[ludusavi][backup] cached title for shortcut: '{_cache_title}'")
        self._refresh_backup_card()

    def _on_find_candidates(self, titles: list):
        self._bk_match_combo.clear()
        if titles:
            for t in titles:
                self._bk_match_combo.addItem(t, userData=t)
            self._bk_status.setText("Pick the matching title:")
            self._bk_status.show()
        else:
            self._bk_match_combo.addItem("(no match - type the exact PCGamingWiki title)")
            self._bk_match_combo.setEditable(True)
            self._bk_status.setText("Not recognized - enter the title manually:")
            self._bk_status.show()
        self._bk_match_row.show()
        self._bk_backup_btn.setEnabled(True)
        self._bk_restore_btn.setEnabled(False)

    def _show_renpy_dir_picker(self, candidates: list) -> None:
        """Show the match combo pre-loaded with ~/.renpy/ folder candidates."""
        self._renpy_pick_mode = True
        self._bk_match_combo.clear()
        self._bk_match_combo.setEditable(False)
        for c in candidates:
            self._bk_match_combo.addItem(c, userData=c)
        self._bk_status.setText("Multiple save folders found — pick the right one:")
        self._bk_status.show()
        self._bk_match_row.show()
        self._bk_set_busy(False)

    def _on_match_chosen(self):
        # ── RenPy folder picker ───────────────────────────────────────────
        if getattr(self, "_renpy_pick_mode", False):
            self._renpy_pick_mode = False
            folder = (self._bk_match_combo.currentData()
                      or self._bk_match_combo.currentText() or "").strip()
            if not folder:
                return
            self._bk_match_row.hide()
            gid = self.game.get("id")
            if gid:
                _renpy_store_save_dir(gid, folder)
            self.game = dict(self.game, renpy_save_dir=folder)
            # Re-trigger the original action with the resolved dir.
            action = getattr(self, "_bk_pending_action", "backup")
            if action == "restore":
                self._on_restore()
            else:
                self._on_backup_now()
            return
        # ── Ludusavi title picker (existing behaviour) ────────────────────
        title = (self._bk_match_combo.currentData()
                 or self._bk_match_combo.currentText() or "").strip()
        if not title or title.startswith("(no match"):
            return
        self._bk_match_row.hide()
        # Persist the confirmed title so future backups skip find entirely.
        # This is the fix for trilogy false-positives: once the user confirms
        # "The Shell Part II: Purgatorio", NAGO never fuzzy-matches siblings again.
        self._bk_db_write(title=title)
        action = getattr(self, "_bk_pending_action", "backup")
        if action == "restore":
            self._start_restore(title)
        else:
            # Manual pick → single-title backup via the queue path.
            self._bk_queue = [title]
            self._bk_results = []
            self._backup_next_in_queue()

    def _on_find_failed(self, msg: str):
        # find returned nothing -- show the manual picker with an empty combo.
        _NAGOLog.session(
            f"[ludusavi][find] failed for '{self.game.get('name', '')}'  reason: {msg}"
        )
        self._on_find_candidates([])

    def _on_backup_failed(self, msg: str):
        _NAGOLog.session(
            f"[ludusavi][backup] failed for '{self.game.get('name', '')}'  reason: {msg}"
        )
        self._refresh_backup_card()
        NAGOMessageBox.warning(self, "Backup Failed", msg)

    # -- Restore flow ---------------------------------------------------------
    # Also runs find first -- same reasoning as backup.

    def _on_restore(self):
        if not LUDUSAVI_BIN.exists() and not shutil.which("ludusavi"):
            NAGOMessageBox.warning(self, "Ludusavi Not Installed",
                "Install Ludusavi first from Settings -> Ludusavi.")
            return
        stored_title, last_manual, _, manual_summary, last_auto, auto_summary = self._bk_db_read()

        def _folder_exists(root) -> bool:
            if not stored_title:
                return False
            p = root / _ludusavi_sanitize_title(stored_title)
            return p.is_dir() and (p / "mapping.yaml").exists()

        manual_exists = _folder_exists(LUDUSAVI_MANUAL_BACKUPS)
        auto_exists   = _folder_exists(LUDUSAVI_AUTO_BACKUPS)

        if not manual_exists and not auto_exists:
            NAGOMessageBox.warning(self, "No Backup Found",
                "No backup files were found on disk for this game.")
            return

        if manual_exists and auto_exists:
            chosen = self._pick_restore_source(
                last_manual, manual_summary, last_auto, auto_summary
            )
            if chosen is None:
                return
            self._bk_restore_root = str(LUDUSAVI_MANUAL_BACKUPS if chosen == "manual"
                                        else LUDUSAVI_AUTO_BACKUPS)
        else:
            source = "manual" if manual_exists else "auto"
            self._bk_restore_root = str(LUDUSAVI_MANUAL_BACKUPS if source == "manual"
                                        else LUDUSAVI_AUTO_BACKUPS)
            if NAGOMessageBox.question(
                self, "Restore Saves",
                f"Restore \"{self.game.get('name', '')}\" saves from the "
                f"{source} backup?\n\nThis overwrites current save files."
            ) != QMessageBox.StandardButton.Yes:
                return

        live_exe = self._current_exe_from_ui()
        if live_exe:
            self.game = dict(self.game, exe_path=live_exe)
        game_for_find = dict(self.game, ludusavi_title=stored_title or "")
        self._bk_pending_action = "restore"
        # ── RenPy save-dir resolution ─────────────────────────────────
        if _detect_renpy((self.game.get("exe_path") or "").strip()):
            stored = (self.game.get("renpy_save_dir") or "").strip()
            if not stored:
                cands = _find_renpy_save_dir_candidates(self.game)
                if len(cands) == 1:
                    _renpy_store_save_dir(self.game["id"], cands[0])
                    self.game = dict(self.game, renpy_save_dir=cands[0])
                    game_for_find = dict(game_for_find, renpy_save_dir=cands[0])
                elif len(cands) > 1:
                    self._show_renpy_dir_picker(cands)
                    return
        self._bk_set_busy(True, "Matching...")
        self._bk_find = LudusaviFindWorker(game_for_find)
        self._bk_find.resolved.connect(self._on_find_resolved_for_restore)
        self._bk_find.candidates.connect(self._on_find_candidates)
        self._bk_find.failed.connect(self._on_find_failed)
        self._bk_find.finished.connect(self._bk_find.deleteLater)
        self._bk_find.start()

    def _pick_restore_source(self, last_manual: str, manual_summary: str,
                              last_auto: str, auto_summary: str) -> "str | None":
        """Show a picker dialog; return 'manual', 'auto', or None (cancelled)."""
        import datetime as _dt

        def _parse_stamp(s: str):
            try:
                d, t = s.split(" ")
                day, mon, year = d.split("-")
                h, m = t.split(":")
                _MONTHS = {"Jan":1,"Feb":2,"Mar":3,"Apr":4,"May":5,"Jun":6,
                           "Jul":7,"Aug":8,"Sep":9,"Oct":10,"Nov":11,"Dec":12}
                return _dt.datetime(int(year), _MONTHS[mon], int(day), int(h), int(m))
            except Exception:
                return _dt.datetime.min

        suggest_manual = _parse_stamp(last_manual) >= _parse_stamp(last_auto)

        dlg = QDialog(self)
        dlg.setWindowTitle("Restore Saves")
        dlg.setWindowFlags(dlg.windowFlags() & ~Qt.WindowType.WindowContextHelpButtonHint)
        lay = QVBoxLayout(dlg)
        lay.setSpacing(12)
        lay.setContentsMargins(20, 20, 20, 20)

        lay.addWidget(QLabel(f"<b>Restore saves for <i>{self.game.get('name', '')}</i></b>"))
        lay.addWidget(QLabel("Choose which backup to restore from:"))

        manual_info = f"{last_manual}  ·  {manual_summary}" if manual_summary else last_manual
        auto_info   = f"{last_auto}  ·  {auto_summary}"     if auto_summary   else last_auto

        rb_manual = QRadioButton(f"Manual    {manual_info}")
        rb_auto   = QRadioButton(f"Auto        {auto_info}")
        rb_manual.setChecked(suggest_manual)
        rb_auto.setChecked(not suggest_manual)

        lay.addWidget(rb_manual)
        lay.addWidget(rb_auto)

        btn_row = QHBoxLayout()
        btn_cancel  = QPushButton("Cancel")
        btn_restore = QPushButton("Restore")
        btn_restore.setObjectName("primary")
        btn_cancel.clicked.connect(dlg.reject)
        btn_restore.clicked.connect(dlg.accept)
        btn_row.addStretch()
        btn_row.addWidget(btn_cancel)
        btn_row.addWidget(btn_restore)
        lay.addLayout(btn_row)

        if dlg.exec() != QDialog.DialogCode.Accepted:
            return None
        return "manual" if rb_manual.isChecked() else "auto"

    def _on_find_resolved_for_restore(self, titles: list):
        # Restore every verified title (mirrors backup). Sequential queue.
        if not titles:
            self._on_find_candidates([])
            return
        self._rs_queue = list(titles)
        self._rs_results = []
        self._restore_next_in_queue()

    def _restore_next_in_queue(self):
        if not self._rs_queue:
            self._finish_restore_batch()
            return
        title = self._rs_queue.pop(0)
        n_done = len(self._rs_results) + 1
        self._bk_set_busy(True, f"Restoring ({n_done})...")
        self._bk_worker = LudusaviRestoreWorker(self.game, title,
                                                restore_root=getattr(self, "_bk_restore_root", ""))
        self._bk_worker.progress.connect(lambda m: (self._bk_status.setText(m), self._bk_status.show()))
        self._bk_worker.done.connect(self._on_restore_one_done)
        self._bk_worker.failed.connect(self._on_restore_failed)
        self._bk_worker.finished.connect(self._bk_worker.deleteLater)
        self._bk_worker.start()

    def _on_restore_one_done(self, summary: dict):
        self._rs_results.append(dict(summary))
        self._restore_next_in_queue()

    def _start_restore(self, title: str):
        # Manual-pick path → single-title restore via the queue.
        self._rs_queue = [title]
        self._rs_results = []
        self._restore_next_in_queue()

    def _finish_restore_batch(self):
        results = getattr(self, "_rs_results", [])
        good = [r for r in results if r.get("processedGames", 0) >= 1]
        self._refresh_backup_card()
        if not good:
            self._bk_status.setText("Nothing restored — no backup data found")
            self._bk_status.show()
            return
        total_mb = sum(r.get("totalBytes", 0) for r in good) / (1024 * 1024)
        total_files = sum(r.get("fileCount", 0) for r in good)
        self._bk_status.setText(f"Restored {total_files} file(s) ({total_mb:.1f} MB)")
        self._bk_status.show()

    def _on_restore_failed(self, msg: str):
        _NAGOLog.session(
            f"[ludusavi][restore] failed for '{self.game.get('name', '')}'  reason: {msg}"
        )
        self._refresh_backup_card()
        NAGOMessageBox.warning(self, "Restore Failed", msg)

    def _open_cover_picker(self):
        """Open the cover picker dialog for both new and existing games."""
        key = self.config.get("sgdb_key", "").strip().strip('"').strip("'")
        search_name = self.name_input.toPlainText().strip() or self.game.get("name", "")
        dlg = CoverPickerDialog(key, search_name, self)
        # Signals just store the selection — nothing is downloaded or applied until Save
        _selected_url   = [None]
        _selected_local = [None]
        _cleared        = [False]
        dlg.cover_selected.connect(lambda url:  _selected_url.__setitem__(0, url))
        dlg.cover_local.connect(   lambda path: _selected_local.__setitem__(0, path))
        dlg.cover_cleared.connect( lambda:      _cleared.__setitem__(0, True))
        result = dlg.exec()

        if result != QDialog.DialogCode.Accepted:
            return  # Cancel — do nothing, keep existing cover

        # Save — apply the selection now
        if _cleared[0]:
            self._on_cover_cleared()
        elif _selected_local[0]:
            self._on_cover_picked_local(_selected_local[0])
        elif _selected_url[0]:
            self._on_cover_picked_url(_selected_url[0])

        # Pull back name from picker search field if still empty
        if not self.name_input.toPlainText().strip():
            picked_name = dlg.search_input.text().strip()
            if picked_name:
                self.name_input.setPlainText(picked_name)

    def _teardown_cover_worker(self):
        """Detach any in-flight cover-download worker from this dialog.

        Disconnects the dialog's slots so a late-finishing download can't call
        into a dialog that's closing, and — if the worker is still running its
        blocking request — parks it in the module keepalive set so it isn't
        garbage-collected mid-thread (which would crash on SIP cleanup). The
        worker self-evicts and self-deletes when it finishes."""
        dw = self._dw
        self._dw = None
        if dw is None:
            return
        try:
            running = dw.isRunning()
        except RuntimeError:
            return  # underlying C++ object already gone (normal finish path)
        for _sig in (dw.cover_downloaded, dw.error, dw.finished):
            try:
                _sig.disconnect()
            except (TypeError, RuntimeError):
                pass
        if running:
            _DETACHED_COVER_WORKERS.add(dw)
            dw.finished.connect(lambda: _DETACHED_COVER_WORKERS.discard(dw))
            dw.finished.connect(dw.deleteLater)
        else:
            dw.deleteLater()

    def _on_cover_picked_url(self, url: str):
        """Download cover — only called after user clicks Save in picker."""
        name = self.game.get("name") or self.name_input.toPlainText().strip() or "game"
        # Detach any previous worker (parks it if still running) before starting a new one.
        self._teardown_cover_worker()
        self._dw = SGDBWorker(self.config.get("sgdb_key", ""))
        self._dw.cover_downloaded.connect(self._on_cover_downloaded)
        self._dw.error.connect(lambda e: NAGOMessageBox.warning(self, "Cover error", e))
        self._dw.finished.connect(self._dw.deleteLater)
        self._dw.download_cover(url, 0, name)

    def _on_cover_downloaded(self, gid: int, path: str):
        """Cover downloaded — hold as pending, never write to DB yet."""
        if (self._pending_cover_path
                and self._pending_cover_path != "__cleared__"
                and self._pending_cover_path != path):
            if Path(self._pending_cover_path).exists():
                Path(self._pending_cover_path).unlink(missing_ok=True)
        self._pending_cover_path = path
        self._refresh_header_cover(path)

    def _on_cover_picked_local(self, path: str):
        """Copy a local image as pending cover, refresh header thumbnail."""
        try:
            ART_PATH.mkdir(parents=True, exist_ok=True)
            name = self.game.get("name") or self.name_input.toPlainText().strip() or "game"
            slug = slugify(name)
            # Use _0 suffix so we never overwrite the existing cover (which uses real id)
            dest = ART_PATH / f"{slug}_0.png"
            # Clean up the previously pending cover FIRST, and never delete the file
            # we're about to write: picking a local cover twice for the same game
            # resolves to the same dest, so unlinking after the save would wipe it.
            _old = self._pending_cover_path
            if _old and _old != "__cleared__" and Path(_old) != dest:
                Path(_old).unlink(missing_ok=True)
            img  = _pil_image().open(path).convert("RGBA")
            img.save(str(dest), "PNG")
            self._pending_cover_path = str(dest)
            self._refresh_header_cover(str(dest))
        except Exception as e:
            NAGOMessageBox.warning(self, "Cover error", str(e))

    def _on_cover_cleared(self):
        """Mark cover as cleared — applied to DB only on Save."""
        if self._pending_cover_path and Path(self._pending_cover_path).exists():
            Path(self._pending_cover_path).unlink(missing_ok=True)
        self._pending_cover_path = "__cleared__"
        self._dlg_cover_card._set_placeholder(all_corners=True)

    def _refresh_header_cover(self, path: str):
        """Re-render the header thumbnail after a cover change."""
        _screen = QApplication.primaryScreen()
        _dpr    = _screen.devicePixelRatio() if _screen else 1.0
        _cw     = self._dlg_cover_card._cover_w
        _ch     = self._dlg_cover_card._cover_h
        _pw     = max(1, round(_cw * _dpr))
        _ph     = max(1, round(_ch * _dpr))
        # Load via QImage to bypass Qt's pixmap cache — same filename is reused
        # for pending covers so the cache would return the stale image otherwise.
        _src = QPixmap.fromImage(QImage(path))
        if _src.isNull():
            return
        _src.setDevicePixelRatio(1.0)
        _scaled = _src.scaled(_pw, _ph,
                              Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                              Qt.TransformationMode.SmoothTransformation)
        if _scaled.width() > _pw or _scaled.height() > _ph:
            _cx = (_scaled.width()  - _pw) // 2
            _cy = (_scaled.height() - _ph) // 2
            _scaled = _scaled.copy(_cx, _cy, _pw, _ph)
        _r   = COVER_RADIUS * _dpr
        _out = QPixmap(_pw, _ph)
        _out.fill(Qt.GlobalColor.transparent)
        _rp  = QPainter(_out)
        _rp.setRenderHint(QPainter.RenderHint.Antialiasing)
        _pp  = QPainterPath()
        _pp.moveTo(_r, 0)
        _pp.lineTo(_pw - _r, 0)
        _pp.arcTo(_pw - _r*2, 0,          _r*2, _r*2,  90, -90)
        _pp.lineTo(_pw, _ph - _r)
        _pp.arcTo(_pw - _r*2, _ph - _r*2,  _r*2, _r*2,   0, -90)
        _pp.lineTo(_r, _ph)
        _pp.arcTo(0,          _ph - _r*2,  _r*2, _r*2, 270, -90)
        _pp.lineTo(0, _r)
        _pp.arcTo(0,          0,           _r*2, _r*2, 180, -90)
        _pp.closeSubpath()
        _rp.setClipPath(_pp)
        _rp.drawPixmap(0, 0, _scaled)
        _rp.end()
        _out.setDevicePixelRatio(_dpr)
        self._dlg_cover_card._cover_pixmap = _out
        self._dlg_cover_card._has_cover = True
        self._dlg_cover_card.update()

    def _sync_upscale_conflicts(self):
        """Keep Wayland and HDR checkboxes consistent with the runner and AI upscaling.

        When AI upscaling is on, the upscaler forces XWayland (PROTON_ENABLE_WAYLAND=0),
        so neither Wayland nor HDR can be active. Both checkboxes are forced off and
        disabled. The user's HDR preference is stashed and restored when upscaling is
        switched off, same as the existing Wayland stash."""
        kind  = self.type_combo.currentData()
        is_pg = kind in ("proton", "gog")
        upscaling = bool(getattr(self, "_upscale_cb", None) and self._upscale_cb.isChecked())
        cb = self._use_wayland_cb
        if is_pg and upscaling:
            # Wayland checkbox — force off, disabled
            cb.blockSignals(True)
            cb.setChecked(False)
            cb.blockSignals(False)
            cb.setEnabled(False)
            cb.setToolTip(
                "Disabled while AI upscaling is on —\n"
                "the upscaler forces XWayland (PROTON_ENABLE_WAYLAND=0)\n"
                "so it can capture the game window."
            )
            # HDR checkbox — force off, disabled (HDR requires Wayland)
            if hasattr(self, "_hdr_cb"):
                if not hasattr(self, "_hdr_user_pref"):
                    self._hdr_user_pref = self._hdr_cb.isChecked()
                self._hdr_cb.blockSignals(True)
                self._hdr_cb.setChecked(False)
                self._hdr_cb.blockSignals(False)
                self._hdr_cb.setEnabled(False)
                self._hdr_cb.setToolTip(
                    "Disabled while AI upscaling is on —\n"
                    "HDR requires PROTON_ENABLE_WAYLAND=1 which conflicts\n"
                    "with the upscaler's XWayland requirement."
                )
            # Gamescope checkbox — force off, disabled (gamescope owns compositor, conflicts with upscaler)
            if hasattr(self, "_gamescope_cb"):
                if not hasattr(self, "_gamescope_user_pref"):
                    self._gamescope_user_pref = self._gamescope_cb.isChecked()
                self._gamescope_cb.blockSignals(True)
                self._gamescope_cb.setChecked(False)
                self._gamescope_cb.blockSignals(False)
                self._gamescope_cb.setEnabled(False)
                # Pick the more useful tooltip: if the binary is missing,
                # that's the fundamental blocker the user needs to know about.
                # "Disabled while AI upscaling is on" only tells half the story.
                if not shutil.which("gamescope"):
                    self._gamescope_cb.setToolTip(
                        "Gamescope is not installed.\n"
                        "Install via:  dnf install gamescope\n"
                        "Then reopen this dialog."
                    )
                else:
                    self._gamescope_cb.setToolTip(
                        "Disabled while AI upscaling is on —\n"
                        "gamescope creates its own compositor which prevents\n"
                        "the upscaler from capturing the game window."
                    )
        else:
            cb.setEnabled(is_pg)
            cb.setToolTip(
                "Sets PROTON_ENABLE_WAYLAND=1 — use the native Wayland backend\ninstead of X11/XWayland"
            )
            if is_pg:
                cb.blockSignals(True)
                cb.setChecked(bool(self._wayland_user_pref))
                cb.blockSignals(False)
            # HDR requires PROTON_ENABLE_WAYLAND=1 — force wayland ON and
            # disable the checkbox so the user can't accidentally uncheck it.
            # Exception: when gamescope is also on, gamescope owns the HDR
            # pipeline (DXVK_HDR=1 only) and PROTON_ENABLE_WAYLAND is not
            # injected, so no Wayland forcing is needed.
            _hdr_on = bool(getattr(self, "_hdr_cb",      None) and self._hdr_cb.isChecked())
            _gs_on  = bool(getattr(self, "_gamescope_cb", None) and self._gamescope_cb.isChecked())
            if is_pg and _hdr_on and not _gs_on:
                cb.blockSignals(True)
                cb.setChecked(True)
                cb.blockSignals(False)
                cb.setEnabled(False)
                cb.setToolTip(
                    "Forced on by HDR — PROTON_ENABLE_WAYLAND=1 is required\n"
                    "for HDR output without Gamescope.\n"
                    "Enable Gamescope or disable HDR to change this."
                )
            # Restore HDR checkbox — only if we previously disabled it
            if hasattr(self, "_hdr_cb") and hasattr(self, "_hdr_user_pref"):
                self._hdr_cb.setEnabled(True)
                self._hdr_cb.blockSignals(True)
                self._hdr_cb.setChecked(bool(self._hdr_user_pref))
                self._hdr_cb.blockSignals(False)
                self._hdr_cb.setToolTip(self._hdr_tooltip_base)
                del self._hdr_user_pref
            # Restore gamescope checkbox — but only re-enable it if gamescope is
            # actually installed. The init-time disable-when-missing logic would
            # otherwise be clobbered here every time the user toggles upscale off.
            if hasattr(self, "_gamescope_cb") and hasattr(self, "_gamescope_user_pref"):
                _gs_installed = bool(shutil.which("gamescope"))
                self._gamescope_cb.blockSignals(True)
                # Stashed pref can only be honoured if the binary is on PATH;
                # otherwise force off (matches the init-time disabled state).
                self._gamescope_cb.setChecked(bool(self._gamescope_user_pref) if _gs_installed else False)
                self._gamescope_cb.blockSignals(False)
                self._gamescope_cb.setEnabled(_gs_installed)
                if _gs_installed:
                    self._gamescope_cb.setToolTip(
                        "Wraps the launch command with gamescope.\n"
                        "Resolution is auto-detected from your primary screen.\n"
                        "When HDR is also on: adds --hdr-enabled and injects DXVK_HDR=1.\n"
                        "Requires gamescope to be installed (dnf install gamescope).\n"
                        "Not applied to Steam-type games."
                    )
                else:
                    self._gamescope_cb.setToolTip(
                        "Gamescope is not installed.\n"
                        "Install via:  dnf install gamescope\n"
                        "Then reopen this dialog."
                    )
                del self._gamescope_user_pref

    def _on_type_change(self, idx):
        kind = self.type_combo.itemData(idx)
        is_proton = (kind == "proton")
        is_steam  = (kind == "steam")
        is_gog    = (kind == "gog")
        is_manual = kind in ("native", "proton")  # types with a manual exe path

        self._proton_row_widget.setVisible(is_proton or is_gog)
        # Clear any stale store hint from a previous browse — switching runner
        # means whatever was detected is no longer relevant.
        self._set_store_hint("")
        self._store_card.setVisible(False)

        # Switch the source card to the page for this runner type.
        # Add flow pages:  0=Native  1=Proton  2=Import(Steam/GOG)
        # Edit flow pages: 0=Native/Proton exe  1=Steam  2=GOG
        if not self.game:
            # In Add flow, kind can be "native", "proton", "steam", or "gog".
            # "steam" and "gog" are sub-states of the Import runner — the row1
            # stack must stay on page 2 (Import picker). Only switch row1 for
            # genuine runner changes (native/proton/import).
            _r1 = {"native": 0, "proton": 1}
            if kind in _r1:
                if hasattr(self, "_row1_stack"):
                    self._row1_stack.setCurrentIndex(_r1[kind])
                if hasattr(self, "_row2_stack"):
                    self._row2_stack.setCurrentIndex(0)
            # "steam"/"gog" from Import sub-picker: row1 stays on page 2,
            # row2/_hint already switched by _on_import_source_picked.
            self._sync_exe_browse_btn_state()
        else:
            _page = {"steam": 1, "gog": 2}.get(kind, 0)
            self._src_stack.setCurrentIndex(_page)
        # Protonfix disabled (NAGO 04:20): the store combo and protonfix pill no
        # longer toggle with runner type — they live inside the always-hidden
        # _umu_outer row. Force them hidden regardless of runner so switching to
        # Proton/GOG can't re-show them. clear_match() stays (harmless no-op now).
        if hasattr(self, "store_combo"):
            self.store_combo.setVisible(False)
        if hasattr(self, "umu_options"):
            self.umu_options._pill_lbl.setVisible(False)
            self.umu_options._id_lbl.setVisible(False)
            if not is_gog:
                self.umu_options.clear_match()

        # Update source card title — Edit only now; Add shows the Import
        # picker in this slot instead (see _src_header_row construction).
        if hasattr(self, "_source_title"):
            if is_steam:
                self._source_title.setText("Steam Game")
            elif is_gog:
                self._source_title.setText("GOG Game")
            else:
                self._source_title.setText("Executable Path")

        # Mirror selected game title into the name field; respect current GOG mode.
        # In the add flow, clear a stale auto-populated name when switching to a
        # manual type so the field doesn't mislead before the user browses.
        _is_new = not (self.game and self.game.get("id"))
        if is_steam:
            self._on_steam_game_picked(self.steam_combo.currentIndex())
        elif is_gog:
            if getattr(self, "_gog_mode", "import") == "browse":
                # Restore Browse mode's search using _gog_browse_name
                browse_name = getattr(self, "_gog_browse_name", "")
                if browse_name:
                    self.umu_options.search(browse_name)
                else:
                    self.umu_options.clear_match()
            else:
                self._on_gog_game_picked(self.gog_combo.currentIndex())
        elif is_manual and _is_new:
            # Switching to Proton/Native in add flow — clear auto-populated name
            # only if the exe field is also empty (nothing browsed yet)
            if not self._active_exe_input().text().strip():
                self.name_input.setPlainText("")

        # Compatibility tab: hidden entirely for Steam (nothing there applies).
        # In Add flow both Compatibility and Advanced are always hidden.
        if self.game:
            self._tabs.setTabVisible(1, not is_steam)
            if is_steam and self._tabs.currentIndex() == 1:
                self._tabs.setCurrentIndex(0)
            self._tabs.setTabEnabled(2, True)
        self._adv_steam_info_card.setVisible(is_steam)
        self._adv_args_frame.setVisible(not is_steam)
        self._adv_env_frame.setVisible(not is_steam)
        self._adv_hooks_frame.setVisible(not is_steam)
        self._adv_vn_frame.setVisible(is_proton or is_gog)
        self._vn_jp_locale_cb.setEnabled(is_proton or is_gog)
        self._use_wined3d_cb.setEnabled(is_proton or is_gog)
        self._use_wow64_cb.setEnabled(is_proton or is_gog)
        self._sync_upscale_conflicts()
        self._use_gstreamer_cb.setEnabled(is_proton or is_gog)
        self._no_esync_cb.setEnabled(is_proton or is_gog)
        self._no_fsync_cb.setEnabled(is_proton or is_gog)
        self._no_ntsync_cb.setEnabled(is_proton or is_gog)
        for w in (self.launch_args_input, self.env_vars_input,
                  self.pre_launch_input, self.post_exit_input):
            w.setEnabled(not is_steam)
        self._steam_adv_warning.setVisible(False)  # legacy — no longer used
        self._steam_general_info_card.setVisible(False)  # moved to Advanced tab
        if hasattr(self, "_upscale_frame"):
            self._upscale_frame.setVisible(not is_steam)
        if hasattr(self, "_ingame_upscale_frame"):
            self._ingame_upscale_frame.setVisible(is_proton or is_gog)
        if hasattr(self, "_hdr_cb"):
            # HDR is hidden only for Steam — NAGO doesn't own the Steam launch
            # path, so flipping the host display from here would leak state into
            # Steam's own launcher. For native/Proton/GOG the kscreen-doctor mode
            # flip applies the same way; the PROTON_ENABLE_HDR env var only does
            # anything inside Proton but is harmless elsewhere.
            self._hdr_cb.setVisible(not is_steam)
        if hasattr(self, "_gamescope_cb"):
            self._gamescope_cb.setVisible(not is_steam)
        if hasattr(self, "_display_card_frame"):
            # Card shows whenever any child is visible (gamescope ok for native).
            self._display_card_frame.setVisible(not is_steam)
        # Resize dialog to fit the new layout, then re-center if needed
        self._lock_height()
        QTimer.singleShot(0, self._snap_inside_screen)

    def _snap_inside_screen(self):
        """Nudge the dialog back inside the screen if any edge spilled over."""
        screen = self._target_screen()
        if screen is None:
            return
        avail = screen.availableGeometry()
        geo = self.frameGeometry()
        x, y = geo.left(), geo.top()
        # Bottom edge first, then right
        if geo.bottom() > avail.bottom():
            y = max(avail.top(), avail.bottom() - geo.height())
        if geo.right() > avail.right():
            x = max(avail.left(), avail.right() - geo.width())
        if geo.top() < avail.top():
            y = avail.top()
        if geo.left() < avail.left():
            x = avail.left()
        if (x, y) != (geo.left(), geo.top()):
            self.move(x, y)

    def _populate_steam_games(self):
        games = find_steam_games()
        self.steam_combo.blockSignals(True)
        self.steam_combo.clear()
        if not games:
            self.steam_combo.addItem("No Steam games detected", userData="")
            self.steam_hint.setText("No Steam games found.")
        else:
            for g in games:
                label = f"{g['name']}  —  appid {g['appid']}"
                self.steam_combo.addItem(label, userData=g["appid"])
            self.steam_hint.setText(f"Found {len(games)} Steam game{'s' if len(games) != 1 else ''}.")
        self.steam_combo.blockSignals(False)

    def _rescan_steam(self):
        current = self.steam_combo.currentData()
        self._populate_steam_games()
        if current:
            for i in range(self.steam_combo.count()):
                if self.steam_combo.itemData(i) == current:
                    self.steam_combo.setCurrentIndex(i)
                    break

    def _on_steam_game_picked(self, idx: int):
        """When a Steam game is selected, the Game Name field always reflects its title."""
        if idx < 0:
            return
        appid = self.steam_combo.itemData(idx)
        if not appid:
            return
        label = self.steam_combo.itemText(idx)
        # Strip the "  —  appid 12345" suffix to get just the title
        title = label.rsplit("  —  appid", 1)[0].strip()
        if title:
            self.name_input.setPlainText(title)

    def _populate_gog_games(self, source: "str | None" = None):
        # Default (no source): today's merged, deduplicated Heroic+Lutris list —
        # used by the unconditional build-time call and by Edit's match lookup,
        # both of which must keep seeing every detected install regardless of
        # origin. source="lutris"/"heroic" is only passed by the Add flow's
        # Import sub-picker, which is filtering to one source on purpose.
        if source == "heroic":
            games = find_gog_games_heroic()
            _src_label = "Heroic"
        elif source == "lutris":
            games = find_gog_games_lutris()
            _src_label = "Lutris"
        else:
            games = find_all_gog_games()
            _src_label = ""
        self.gog_combo.blockSignals(True)
        self.gog_combo.clear()
        if not games:
            self.gog_combo.addItem(
                f"No {_src_label} games detected" if _src_label else "No games detected",
                userData={}
            )
            self.gog_hint.setText(
                f"No {_src_label} games found." if _src_label
                else "No games found. Install via Heroic or Lutris first."
            )
        else:
            for g in games:
                # Not "GOG" — Heroic/Lutris may surface other stores later
                # (Amazon, Epic, etc.), so this stays generic on purpose.
                item_source = g.get("source", "")
                label = f"{g['name']}  —  {item_source}"
                self.gog_combo.addItem(label, userData=g)
            self.gog_hint.setText(
                f"Found {len(games)} {_src_label} game{'s' if len(games) != 1 else ''}."
                if _src_label else
                f"Found {len(games)} game{'s' if len(games) != 1 else ''}."
            )
        self.gog_combo.blockSignals(False)

    def _rescan_gog(self):
        """GOG Rescan button: repopulate list, restore selection.
        _on_gog_game_picked fires via currentIndexChanged when selection is restored,
        handling the umu search — no need to call it explicitly here."""
        current_exe = (self.gog_combo.currentData() or {}).get("exe_path", "")
        self._populate_gog_games(source=getattr(self, "_gog_import_source", None))
        if current_exe:
            for i in range(self.gog_combo.count()):
                d = self.gog_combo.itemData(i) or {}
                if d.get("exe_path") == current_exe:
                    self.gog_combo.setCurrentIndex(i)
                    break
        else:
            # No previous selection — fire search for whatever landed as current
            self._on_gog_game_picked(self.gog_combo.currentIndex())

    def _on_gog_game_picked(self, idx: int):
        """GOG Import: combo item selected → update name + search umu.
        Guard against being called during build before umu_options exists —
        the dialog open trigger handles the initial search after build."""
        if idx < 0:
            return
        data = self.gog_combo.itemData(idx)
        if not data or not isinstance(data, dict):
            return
        title = data.get("name", "")
        if title:
            self.name_input.setPlainText(title)
        if not hasattr(self, "umu_options"):
            return
        if title:
            self.umu_options.search(title)
        else:
            self.umu_options.clear_match()

    def _active_exe_input(self):
        """Return the shared exe QLineEdit. Kept as a method so all call
        sites are unchanged — exe_input is now a single shared widget in
        both Add and Edit flows (no per-page duplication needed)."""
        return self.exe_input

    def _active_exe_hint(self):
        """Return the shared exe hint QLabel."""
        return self.exe_hint

    def _on_proton_mode_picked(self, mode: str):
        """Browse/Install mode toggle — lives on the exe path card (Add flow,
        Proton runner only). Browse is the existing default (today's
        exe_input flow, untouched); Install repurposes the exe row's Browse
        button to run a Windows installer into this game's prefix instead of
        opening the file picker (see _on_exe_browse_btn_clicked).

        Switching to Install: stashes any existing exe path and clears the
        field — the field is irrelevant while in Install mode and a stale
        path would be confusing.
        Switching to Browse: restores the stashed path so the user doesn't
        lose a path they already picked."""
        _exe = self._active_exe_input()
        if mode == "install":
            # Stash current path and clear the field
            self._browse_exe_stash = _exe.text()
            _exe.setText("")
            _h = self._active_exe_hint()
            _h.setText("")
            _h.setVisible(False)
            self._set_store_hint("")
        elif mode == "browse":
            # Restore stashed path if we have one
            if self._browse_exe_stash:
                _exe.setText(self._browse_exe_stash)
                self._scan_exe_for_store(self._browse_exe_stash)
        for b in self._install_mode_btns:
            b.setChecked(b.text().lower() == mode)
        self._proton_install_mode = mode
        self._sync_exe_browse_btn_state()

    def _exe_browse_is_install_mode(self) -> bool:
        """True when the exe Browse button is in Install mode — Proton, Add flow only."""
        return bool(
            not self.game
            and getattr(self, "_install_mode_row", None) is not None
            and getattr(self, "_row1_stack", None) is not None
            and self._row1_stack.currentIndex() == 1   # Proton page
            and getattr(self, "_proton_install_mode", "browse") == "install"
        )

    def _sync_exe_browse_btn_state(self):
        """Single source of truth for the doubled exe Browse/Install button's
        visual state (text/icon/tooltip) — Proton-only, Add flow. Called from
        both the toggle handler and _on_type_change instead of duplicating
        this logic at each call site, the same lesson learned from the
        tooltip-duplication bug fixed earlier this session."""
        if not hasattr(self, "_exe_browse_btn"):
            return
        _is_install = self._exe_browse_is_install_mode()
        if _is_install:
            self._set_prefix_run_button_state(self._exe_browse_btn, running=False)
        else:
            self._exe_browse_btn.setIcon(QIcon())
            self._exe_browse_btn.setText("Browse")
            self._exe_browse_btn.setToolTip("")
        _h = self._active_exe_hint()
        _h.setText("")
        _h.setVisible(False)
        if hasattr(self, "_inst_options_row"):
            self._inst_options_row.setVisible(_is_install)
        if hasattr(self, "_install_dir_widget"):
            self._install_dir_widget.setVisible(not _is_install)
        if _is_install:
            self._exe_browse_btn.setToolTip(
                "Runs a Windows installer (.exe/.msi) inside this game's prefix.\n"
                "Set the game executable via Browse afterward."
            )

    def _on_exe_browse_btn_clicked(self):
        """Browse button doubles as the Install trigger when the Browse/
        Install toggle is set to Install — same physical button, different
        action depending on mode. Browse mode (default, and the only
        behavior outside Proton): pick an already-installed exe via the
        existing _browse_exe. Install mode: run a Windows installer into
        this game's prefix via the existing _run_exe_in_prefix engine — same
        button doubles as Stop while a run is in progress (handled inside
        that method; the toggle itself locks for the duration, see
        _set_prefix_run_button_state)."""
        if self._exe_browse_is_install_mode():
            self._run_exe_in_prefix(button=self._exe_browse_btn)
        else:
            self._browse_exe()

    def _on_import_source_picked(self, val: str):
        """Import sub-picker (Steam/Lutris/Heroic) — Add flow only."""
        for b in self._import_src_btns:
            b.setChecked(b.text().strip().lower() == val)
        if hasattr(self, "_row2_stack"):
            self._row2_stack.setCurrentIndex(1 if val == "steam" else 2)
        if val == "steam":
            self._gog_import_source = None
            self.type_combo.setCurrentIndex(3)
            # If already on Steam (type_combo stays at 3), force name refresh.
            if self.type_combo.currentIndex() == 3:
                self._on_steam_game_picked(self.steam_combo.currentIndex())
        else:
            self._gog_import_source = val
            # Populate BEFORE setting type_combo so the combo has games when
            # _on_type_change fires _on_gog_game_picked.
            self._populate_gog_games(source=val)
            self.type_combo.setCurrentIndex(2)
            # If type_combo was already on index 2 (switching Heroic↔Lutris),
            # setCurrentIndex is a no-op and _on_type_change never fires —
            # force name population from whatever landed at index 0.
            if self.type_combo.currentIndex() == 2:
                self._on_gog_game_picked(self.gog_combo.currentIndex())

    def _set_gog_mode(self, mode: str):
        """Switch GOG card between Import (Heroic/Lutris) and Browse (manual path) modes."""
        self._gog_mode = mode
        is_import = mode == "import"
        if self._gog_stack is not None:
            self._gog_stack.setCurrentIndex(0 if is_import else 1)
        if is_import:
            # The detected-store hint only means something mid-Browse — it
            # used to disappear for free when its old home (_gog_browse_hint)
            # was on a stack page that just became hidden. Now that it lives
            # in the always-visible card header, it needs clearing explicitly.
            self._set_store_hint("")

        # Swap signals — only the active page is wired.
        # connect()/disconnect() are gated on self._gog_picked_connected because
        # PyQt6 silently allows duplicate connects (no TypeError), which would make
        # Swap signals — only the active page is wired.
        # connect()/disconnect() are gated on self._gog_picked_connected because
        # PyQt6 silently allows duplicate connects (no TypeError), which would make
        # _on_gog_game_picked fire more than once per selection.
        # gog_exe_input.editingFinished is intentionally NOT connected — detection
        # runs on Browse button click only, never on focus-loss from manual typing.
        if is_import:
            try:
                self.gog_exe_input.editingFinished.disconnect(self._on_gog_browse_editingfinished)
            except (TypeError, RuntimeError, AttributeError):
                pass
            if not self._gog_picked_connected:
                self.gog_combo.currentIndexChanged.connect(self._on_gog_game_picked)
                self._gog_picked_connected = True
        else:
            if self._gog_picked_connected:
                try:
                    self.gog_combo.currentIndexChanged.disconnect(self._on_gog_game_picked)
                except (TypeError, RuntimeError):
                    pass
                self._gog_picked_connected = False

        # Rescan umu for the now-active mode.
        # Guard: umu_options may not exist yet during _build (Edit GOG restore calls
        # _set_gog_mode("browse") before umu_options is constructed). The dialog
        # open trigger handles the initial search after build via game["name"].
        if not hasattr(self, "umu_options"):
            return
        if is_import:
            idx = self.gog_combo.currentIndex()
            data = self.gog_combo.itemData(idx) if idx >= 0 else None
            search_name = (data.get("name", "") if isinstance(data, dict) else "")
            self.name_input.setPlainText(search_name)
            if search_name:
                self.umu_options.search(search_name)
            else:
                self.umu_options.clear_match()
        else:
            browse_name = getattr(self, "_gog_browse_name", "")
            self.name_input.setPlainText(browse_name)
            if browse_name:
                self.umu_options.search(browse_name)
            else:
                self.umu_options.clear_match()

    def _auto_populate_install_dir(self, exe_path: str) -> None:
        """Auto-populate the install_dir field after an exe is set.
        Uses _find_install_dir (GOG/Epic breadcrumb walk, falls back to
        exe.parent).  Called on Browse confirm and editingFinished.
        Silently skips if the exe doesn't exist or no field is present
        (Edit Game Steam, GOG import).
        Add Game always uses _install_dir_input regardless of kind —
        _gog_install_dir_input only exists in Edit Game's GOG page."""
        if not exe_path or not Path(exe_path).is_file():
            return
        detected = _find_install_dir(exe_path)
        if not self.game:
            inp = getattr(self, "_install_dir_input", None)
        else:
            kind = self.type_combo.currentData()
            inp = getattr(self, "_gog_install_dir_input" if kind == "gog"
                          else "_install_dir_input", None)
        if inp is not None:
            inp.setText(detected)

    def _browse_install_dir(self) -> None:
        """Folder picker for the install_dir field (both Native/Proton and
        GOG browse).  Uses QFileDialog.getExistingDirectory.
        Add Game always uses _install_dir_input; Edit Game picks by kind."""
        if not self.game:
            inp = getattr(self, "_install_dir_input", None)
        else:
            kind = self.type_combo.currentData()
            inp = getattr(self, "_gog_install_dir_input" if kind == "gog"
                          else "_install_dir_input", None)
        if inp is None:
            return
        start = inp.text().strip() or self.config.get("last_browse_dir", str(Path.home()))
        folder = QFileDialog.getExistingDirectory(self, "Select Install Folder", start)
        if folder:
            inp.setText(folder)

    def _browse_gog_exe(self):
        """GOG Browse button: pick file → run path scan immediately."""
        start_dir = self.config.get("last_browse_dir", str(Path.home()))
        path, _ = QFileDialog.getOpenFileName(self, "Select GOG Executable", start_dir)
        if not path:
            return
        self.config["last_browse_dir"] = str(Path(path).parent)
        self.gog_exe_input.setText(path)
        self._on_gog_browse_path_changed(path)

    def _on_gog_browse_path_changed(self, path: str):
        """GOG Browse: path entered → scan for GOG markers, update name, trigger
        umu search. _gog_browse_hint now mirrors exe_hint's own found/not-found
        convention (always shown, per-field); the 'which store did we detect'
        message moved to the card header's _store_hint_widget — the single
        place that now reports a detected store regardless of which Browse
        field triggered it or whether the runner type ends up switching (see
        _scan_exe_for_store, which reaches this same function when GOG markers
        are found while browsing under Proton)."""
        self._auto_populate_install_dir(path)
        if not path:
            self._gog_browse_name = ""
            self._set_store_hint("")
            self.umu_options.clear_match()
            return
        result = scan_install_dir_for_store(path)
        if result["name"]:
            self.name_input.setPlainText(result["name"])
            self._gog_browse_name = result["name"]
        else:
            _fallback = Path(path).stem.replace("_", " ").title()
            if not self.name_input.toPlainText():
                self.name_input.setPlainText(_fallback)
            self._gog_browse_name = _fallback
        if result["store"] == "gog":
            self._set_store_hint("✓ GOG install detected")
            self.umu_options.search(self._gog_browse_name)
        else:
            self._set_store_hint("")
            # Not a GOG install — still show defaults, no umu search
            self.umu_options.clear_match()

    def _umu_on_store_changed(self):
        """Proton store combo changed.
        'No store' means no protonfix — clears the match entirely (gameid included),
        since a fix without a store is meaningless and the user is explicitly opting out.
        Any real store selection on an existing match overrides just the store tag,
        keeping the gameid — switching stores shouldn't re-trigger a search that
        could replace a known-good match.
        If there's no gameid yet, a real store picks runs a fresh search."""
        chosen = self.store_combo.currentData() or "none"
        if chosen == "none":
            self.umu_options.clear_match()
            return
        if self.umu_options._gameid:
            self.umu_options.set_store(chosen)
            return
        name = self.name_input.toPlainText().strip()
        if name:
            self.umu_options.search(name)

    def _get_wine_binaries(self, proton_path_str: str) -> tuple[str, str]:
        """
        Given the path to the 'proton' script, find both the wine and wine64
        binaries inside the Proton installation.
        Returns (wine_bin, wine64_bin) — either may be '' if not found.
        """
        if not proton_path_str:
            return "", ""
        proton_dir = Path(proton_path_str).parent
        wine_bin   = ""
        wine64_bin = ""
        for prefix in ("files/bin", "dist/bin"):
            d = proton_dir / prefix
            w   = d / "wine"
            w64 = d / "wine64"
            if w.exists() and not wine_bin:
                wine_bin = str(w)
            if w64.exists() and not wine64_bin:
                wine64_bin = str(w64)
            if wine_bin and wine64_bin:
                break
        return wine_bin, wine64_bin

    def _winetricks_supported(self) -> bool:
        """True if the currently selected Proton supports umu's winetricks verb.
        Plain Valve Proton (steamapps/common) does not — see proton_supports_winetricks."""
        try:
            return proton_supports_winetricks(self.proton_selector.selected_path())
        except Exception:
            return True  # never wrongly block on an unexpected error

    # ── FSR version detection ──────────────────────────────────────────────

    def _on_fsr4_toggled(self, checked: bool) -> None:
        """Scan when FSR4 checkbox is ticked; hide hint when unticked.
        Only active in Edit Game — Compatibility tab is hidden in Add Game flow.
        Scan runs at most once per exe path: if already done, reticking just
        restores the label without re-scanning."""
        if not self.game:
            return
        lbl = getattr(self, "_fsr_detect_lbl", None)
        if lbl is None:
            return
        if checked:
            if self._fsr_scan_done:
                # Scan already ran — restore label if it has content
                if lbl.text():
                    lbl.setVisible(True)
            else:
                self._run_fsr_scan()
        else:
            lbl.setVisible(False)

    def _run_fsr_scan(self) -> None:
        """Scan near the game's exe for upscaler DLLs and update the hint label."""
        lbl = getattr(self, "_fsr_detect_lbl", None)
        if lbl is None:
            return
        exe = (self.game.get("exe_path") or "").strip()
        if not exe or not Path(exe).exists():
            lbl.setVisible(False)
            return
        install_dir = (self.game.get("install_dir") or "").strip()
        parts, _ = _detect_upscaler_dlls(exe, install_dir=install_dir)
        if parts:
            # FSR 4 and FSR 3.1 are upgrade-relevant — highlight green.
            # DLSS and XeSS keep a consistent neutral regardless of what else
            # is detected.  Using rich text so each part is colored individually.
            _GRN = "#4ade80"
            _DIM = "#a1a1aa"
            _SEP = '<span style="color:#52525b;"> | </span>'
            _UPGRADE = {"FSR 4", "FSR 3.1 — upgrade supported"}
            frags = []
            for p in parts:
                c = _GRN if p in _UPGRADE else _DIM
                frags.append(f'<span style="color:{c};">{p}</span>')
            lbl.setTextFormat(Qt.TextFormat.RichText)
            lbl.setStyleSheet("")
            lbl.setText(_SEP.join(frags))
            lbl.setVisible(True)
        else:
            lbl.setVisible(False)
        self._fsr_scan_done = True

    def _sync_winetricks_for_proton(self):
        """Enable/disable the Winetricks button based on the selected Proton.

        winetricks needs a protonfixes-bundling build (UMU/GE/CachyOS/EM/etc.); plain
        Valve Proton makes `umu-run winetricks` fail or hang. We only ever ADD a
        Proton-based block on top of the existing prefix-existence gating — we never
        force-enable, so a button disabled because the prefix doesn't exist yet stays
        disabled. Winecfg is untouched: it's a Wine builtin present in every Proton.
        """
        btn = getattr(self, "_winetricks_btn", None)
        if btn is None:
            return
        if self._winetricks_supported():
            # Capable Proton: restore the standard tooltip. Leave enabled-state alone —
            # prefix-existence logic owns that. Only clear a Proton-block tooltip.
            if btn.toolTip().startswith("Winetricks needs"):
                btn.setToolTip("Run Winetricks GUI")
                # If a prefix exists (button would otherwise be usable), re-enable.
                if self.game.get("id") or (self._tmp_prefix_path and self._tmp_prefix_path.exists()):
                    btn.setEnabled(True)
        else:
            btn.setEnabled(False)
            btn.setToolTip(
                "Winetricks needs GE-Proton, UMU-Proton, or another protonfixes build.\n"
                "Plain Valve Proton (Steam's Proton Experimental / 9.0 / Hotfix) isn't supported\n"
                "— umu can't run winetricks against it. Switch Proton to use this."
            )

    def _get_prefix_tool_env(self) -> tuple[dict, str, str]:
        """
        Build the umu environment for running Winetricks or Winecfg against this
        game's prefix THROUGH umu — the same path the game itself launches by.
        Returns (env, umu_bin, error_message). If error_message is non-empty, abort.

        We pass the TOP-LEVEL prefix as WINEPREFIX; umu/Proton create and use the
        'pfx' subdirectory themselves, exactly as at launch. No /pfx adjustment here
        (that was only needed when these tools ran via raw wine).

        Works for both saved games (uses DB prefix path) and unsaved Add Game
        dialogs (uses self._tmp_prefix_path created by Run in Prefix).
        """
        umu_bin = find_umu_run()
        if not umu_bin:
            return {}, "", ("umu-launcher is required to run Winetricks/Winecfg "
                            "against a Proton prefix.\n\nInstall it from "
                            "Settings → umu-launcher.")

        game_id   = self.game.get("id")
        game_name = self.game.get("name", "")

        if game_id:
            _pfx_override = (self.game.get("prefix_path") or "").strip()
            if _pfx_override and Path(_pfx_override).exists():
                pfx = _pfx_override
            else:
                pfx = str(get_game_prefix(game_id, game_name))
        elif self._tmp_prefix_path and self._tmp_prefix_path.exists():
            pfx = str(self._tmp_prefix_path)
        else:
            return {}, "", "Run an executable in the prefix first to create it."

        # Resolve the Proton selection to a directory (umu's PROTONPATH wants a dir,
        # not the 'proton' script). Same logic as _launch_game / _run_exe_in_prefix.
        proton_path_str = self.proton_selector.selected_path()
        proton_arg = ""
        if proton_path_str in (UMU_DEFAULT_SENTINEL, "GE-Proton"):
            # Auto options pass straight through; build_umu_env interprets them.
            proton_arg = proton_path_str
        elif proton_path_str:
            p = Path(proton_path_str).resolve()
            if p.is_file() and p.name == "proton":
                proton_arg = str(p.parent)
            elif p.is_dir():
                proton_arg = str(p)
            else:
                proton_arg = proton_path_str
        if not proton_arg:
            proton_arg = "GE-Proton"

        env = build_umu_env(
            os.environ.copy(),
            wineprefix=pfx,
            proton_path=proton_arg,
            game_id="umu-default",
            store="",
        )

        # Apply per-game env vars from the dialog (DXVK_HUD, MANGOHUD, PROTON_LOG, etc.)
        raw_env = self.env_vars_input.text().strip()
        if raw_env:
            for key, value in LibraryPage._parse_env_vars(raw_env).items():
                env[key] = value

        return env, umu_bin, ""

    def _run_winetricks(self):
        if not self._winetricks_supported():
            NAGOMessageBox.warning(
                self, "Winetricks Not Supported",
                "The selected Proton (plain Valve Proton) doesn't support winetricks "
                "through umu.\n\nSwitch to GE-Proton, UMU-Proton, or another "
                "protonfixes-based build, then try again."
            )
            return
        wt_bin = find_winetricks()
        if not wt_bin:
            NAGOMessageBox.warning(self, "Winetricks Not Found",
                                "winetricks was not found.\n\n"
                                "Install it from Settings → Winetricks, or via your package manager:\n"
                                "  Fedora:        sudo dnf install winetricks\n"
                                "  Arch/Manjaro:  sudo pacman -S winetricks\n"
                                "  Ubuntu/Debian: sudo apt install winetricks")
            return
        env, umu_bin, err = self._get_prefix_tool_env()
        if err:
            NAGOMessageBox.warning(self, "Cannot Run Winetricks", err)
            return

        # Disable button while running
        self._winetricks_btn.setEnabled(False)
        self._winetricks_spinner = _ButtonSpinner(self._winetricks_btn)
        self._winetricks_spinner.start()

        # Write header to Winetricks log
        _ts = _fmt_stamp(datetime.datetime.now())
        for _hl in ["=" * 64, f"WINETRICKS (GUI)  {_ts}", "=" * 64]:
            _NAGOLog.winetricks(_hl)
            _winetricks_bridge.line_ready.emit(_hl)

        # Run winetricks through umu so it uses the same Proton prefix the game does.
        cmd = [umu_bin, wt_bin, "--gui"]

        class _WinetricksGUIWorker(_NAGOThread):
            finished_ok = pyqtSignal()
            failed      = pyqtSignal(str)

            def __init__(self, cmd, env):
                super().__init__()
                self._cmd = cmd
                self._env = env

            def run(self):
                try:
                    proc = subprocess.Popen(
                        self._cmd,
                        env=self._env,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.STDOUT,
                        text=True,
                        errors="replace",
                    )
                    for line in proc.stdout:
                        stripped = line.rstrip()
                        _NAGOLog.winetricks(stripped)
                        _winetricks_bridge.line_ready.emit(stripped)
                    proc.wait()
                    self.finished_ok.emit()
                except Exception as e:
                    self.failed.emit(str(e))

        worker = _WinetricksGUIWorker(cmd, env)

        def _on_done():
            try:
                self._winetricks_spinner.stop()
                self._winetricks_btn.setEnabled(True)
                _footer = f"--- winetricks GUI closed ---"
                _NAGOLog.winetricks(_footer)
                _winetricks_bridge.line_ready.emit(_footer)
            except RuntimeError:
                pass

        def _on_failed(err: str):
            try:
                self._winetricks_spinner.stop()
                self._winetricks_btn.setEnabled(True)
                NAGOMessageBox.warning(self, "Winetricks Error", err)
            except RuntimeError:
                pass

        worker.finished_ok.connect(_on_done)
        worker.failed.connect(_on_failed)
        worker.finished.connect(worker.deleteLater)
        worker.start()
        self._winetricks_worker = worker  # keep reference

    # TODO: Option D — winetricks stdout viewer
    # Show a non-modal dialog with live stdout from winetricks while a preset runs.
    # WinetricksPresetWorker would need to stream stdout line-by-line via a signal
    # instead of waiting for process exit. Useful for long installs (dotnet, vcrun)
    # where the user has no idea if anything is happening.
    def _run_winetricks_preset(self, verbs: str, btn: QPushButton):
        """Run a fixed set of winetricks verbs in a background thread with button feedback."""
        wt_bin = find_winetricks()
        if not wt_bin:
            NAGOMessageBox.warning(self, "Winetricks Not Found",
                                "winetricks was not found.\n\n"
                                "Install it from Settings → Winetricks, or via your package manager:\n"
                                "  Fedora:        sudo dnf install winetricks\n"
                                "  Arch/Manjaro:  sudo pacman -S winetricks\n"
                                "  Ubuntu/Debian: sudo apt install winetricks")
            return
        env, umu_bin, err = self._get_prefix_tool_env()
        if err:
            NAGOMessageBox.warning(self, "Cannot Run Winetricks Preset", err)
            return

        original_text = btn.text().strip()
        btn.setEnabled(False)
        btn.setText("  Installing…")
        spinner = _ButtonSpinner(btn)
        spinner.start()

        worker = WinetricksPresetWorker(umu_bin, wt_bin, verbs.split(), env)

        def _on_done(verbs_done: str):
            try:
                spinner.stop()
                btn.setEnabled(True)
                btn.setText(f"  {original_text}")
            except RuntimeError:
                pass  # dialog closed while running

        def _on_failed(error: str):
            try:
                spinner.stop()
                btn.setEnabled(True)
                btn.setText(f"  {original_text}")
                NAGOMessageBox.warning(self, "Winetricks Error", error)
            except RuntimeError:
                pass

        worker.finished_ok.connect(_on_done)
        worker.failed.connect(_on_failed)
        worker.finished.connect(worker.deleteLater)
        worker.start()
        # Keep a reference so it isn't GC'd mid-run
        self._preset_worker = worker

    def _run_winecfg(self):
        env, umu_bin, err = self._get_prefix_tool_env()
        if err:
            NAGOMessageBox.warning(self, "Cannot Run Winecfg", err)
            return

        # Spin the button while umu initializes the prefix and winecfg is open.
        # umu-run blocks until winecfg is closed, so we run it in a worker and
        # spin until it exits — giving feedback during the (sometimes slow) first
        # init / Proton download, and showing the tool is active while open.
        self._winecfg_btn.setEnabled(False)
        self._winecfg_spinner = _ButtonSpinner(self._winecfg_btn)
        self._winecfg_spinner.start()

        class _WinecfgWorker(_NAGOThread):
            done = pyqtSignal(str)   # error string, "" on success

            def __init__(self, umu_bin, env):
                super().__init__()
                self._umu_bin = umu_bin
                self._env     = env

            def run(self):
                try:
                    proc = subprocess.Popen([self._umu_bin, "winecfg"], env=self._env)
                    proc.wait()
                    self.done.emit("")
                except Exception as e:
                    self.done.emit(str(e))

        worker = _WinecfgWorker(umu_bin, env)

        def _on_done(err: str):
            try:
                self._winecfg_spinner.stop()
                self._winecfg_btn.setEnabled(True)
                if err:
                    NAGOMessageBox.warning(self, "Winecfg Error", err)
            except RuntimeError:
                pass  # dialog closed while running

        worker.done.connect(_on_done)
        worker.finished.connect(worker.deleteLater)
        worker.start()
        self._winecfg_worker = worker  # keep a reference so it isn't GC'd mid-run

    def _set_prefix_run_button_state(self, button, running: bool):
        """Toggle a run-in-prefix-style button between idle and running/Stop
        visual state. Shared by the small icon-only _run_in_prefix_btn and the
        labeled exe-card _exe_browse_btn (Install mode, doubling as the old
        Run Installer button) so both can drive the same _run_exe_in_prefix
        engine without duplicating the icon/tooltip/text logic per call site.
        Detects which kind of button it is by whether it currently has text
        (icon-only buttons never do)."""
        _is_labeled = bool(button.text())
        _icon_size = 18 if _is_labeled else 22
        if running:
            button.setIcon(ph_icon("x-circle", _icon_size))
            if _is_labeled:
                button.setText("  Stop")
                button.setToolTip("Stop — force-terminate this installer run")
            else:
                button.setToolTip("Stop — force-terminate this run")
        else:
            button.setIcon(ph_icon("file-archive", _icon_size))
            if _is_labeled:
                button.setText("  Run Installer")
                button.setToolTip(
                    "Run a Windows installer (.exe/.msi) inside this game's prefix. "
                    "Files need to land under your home folder to be visible afterward."
                )
            else:
                button.setToolTip(
                    "Run executable in prefix — install software (e.g. Ubisoft Connect)\ninto this game's Wine prefix"
                )
        # The exe-card Browse button doubles as Install — lock the toggle
        # while it's mid-run so switching back to Browse can't desync the
        # button's label from a still-running installer underneath it.
        if hasattr(self, "_install_mode_btns") and button is getattr(self, "_exe_browse_btn", None):
            for b in self._install_mode_btns:
                b.setEnabled(not running)

    def _run_exe_in_prefix(self, button=None):
        """
        Pick an arbitrary .exe and run it inside this game's Wine prefix using
        umu + the game's configured Proton version. Useful for installing software
        (e.g. Ubisoft Connect) into the prefix before the game itself is run, and
        reused as-is by the exe card's doubled Browse/Install button (Install
        mode) in the Add flow — same engine, same temp-prefix-then-rename-on-
        save behavior, just a different button driving the visual
        running/idle state via the `button` param.

        Works for both saved games (uses the real game id/name prefix) and
        unsaved Add Game dialogs (creates a NewGame_<timestamp> prefix that is
        renamed to the real slug_id path once the game is saved).

        While a run is in progress, the same button doubles as Stop — clicking
        it calls terminate_now() on the active worker instead of opening the
        file picker again. Only one run-in-prefix operation is ever in flight
        at a time, regardless of which button started it.
        """
        btn = button or self._run_in_prefix_btn
        try:
            _worker_running = (self._run_in_prefix_worker is not None and
                               self._run_in_prefix_worker.isRunning())
        except RuntimeError:
            self._run_in_prefix_worker = None
            _worker_running = False
        if _worker_running:
            self._run_in_prefix_worker.terminate_now()
            return

        # Must have umu available
        umu_bin = find_umu_run()
        if not umu_bin:
            NAGOMessageBox.warning(
                self, "umu-launcher Not Found",
                "umu-launcher is required to run executables in a Proton prefix.\n\n"
                "Install it from Settings → umu-launcher."
            )
            return

        # Pick the exe — resume from last browsed location, fall back to
        # Downloads, then home (matches the exe/GOG browse pattern elsewhere).
        downloads = Path.home() / "Downloads"
        fallback_dir = str(downloads) if downloads.exists() else str(Path.home())
        start_dir = self.config.get("last_browse_dir", fallback_dir)
        exe_path, _ = QFileDialog.getOpenFileName(
            self, "Select File to Run in Prefix", start_dir,
            "Windows files (*.exe *.msi *.bat *.cmd);;All files (*)"
        )
        if not exe_path:
            return
        self.config["last_browse_dir"] = str(Path(exe_path).parent)

        # ── Installer vs game classification ──────────────────────────────────
        # Only applies in the Add flow (no self.game) when the doubled
        # Browse/Install button is in Install mode. If the selected file looks
        # like a game rather than an installer, silently flip to Browse mode,
        # populate the exe field with the path, and bail out — no prefix run.
        if not self.game and self._exe_browse_is_install_mode():
            # Fast path: if scan_install_dir_for_store already recognises this
            # as a known store install (GOG/Epic), it's definitely a game — no
            # need to run the full heuristic classifier.
            #
            # Extra Steam signal: an exe living under a real steamapps/common
            # library with a matching appmanifest is unconditionally a game (no
            # installer ever sits inside a Steam library claimed by a manifest).
            # This closes the gap where _classify_exe returns 'unknown' for a
            # Steam game whose engine fingerprint isn't in the listed signatures
            # — additive, the heuristic and store fast-path are unchanged.
            _store_result = scan_install_dir_for_store(exe_path)
            if _store_result["store"] or steam_appid_from_exe_path(exe_path):
                _verdict = "game"
            else:
                _verdict = _classify_exe(exe_path)
            if _verdict == "game":
                self._proton_install_mode = "browse"
                self._browse_exe_stash = ""  # new path takes over; don't restore old stash
                for _b in self._install_mode_btns:
                    _b.setChecked(_b.text() == "Browse")
                if self._inst_options_row is not None:
                    self._inst_options_row.setVisible(False)
                self._sync_exe_browse_btn_state()
                self._active_exe_input().setText(exe_path)
                self._scan_exe_for_store(exe_path)
                return

        # ── Resolve prefix path ───────────────────────────────────────────────
        game_id   = self.game.get("id")
        game_name = self.game.get("name", "")

        if game_id:
            # Saved game — respect stored prefix_path override, else derive
            _pfx_override = (self.game.get("prefix_path") or "").strip()
            if _pfx_override and Path(_pfx_override).exists():
                pfx = _pfx_override
            else:
                pfx = str(get_game_prefix(game_id, game_name))
        else:
            # Unsaved game — reuse existing tmp prefix or create a new one
            if self._tmp_prefix_path and self._tmp_prefix_path.exists():
                pfx = str(self._tmp_prefix_path)
            else:
                ts = int(time.time())
                # Use whatever the user has typed in the name field; fall back to NewGame
                _dlg_name = self.name_input.toPlainText().strip()
                _slug = slugify(_dlg_name) if _dlg_name else f"NewGame_{ts}"
                tmp_dir = get_prefixes_root() / f"{_slug}_{ts}"
                tmp_dir.mkdir(parents=True, exist_ok=True)
                self._tmp_prefix_path = tmp_dir
                pfx = str(tmp_dir)

        # Build umu env using the game's Proton selection
        proton_path_str = self.proton_selector.selected_path()
        proton_arg = ""
        if proton_path_str in (UMU_DEFAULT_SENTINEL, "GE-Proton"):
            # Auto options pass straight through; build_umu_env interprets them.
            proton_arg = proton_path_str
        elif proton_path_str:
            p = Path(proton_path_str).resolve()
            if p.is_file() and p.name == "proton":
                proton_arg = str(p.parent)
            elif p.is_dir():
                proton_arg = str(p)
            else:
                proton_arg = proton_path_str
        if not proton_arg:
            proton_arg = "GE-Proton"

        env = build_umu_env(
            os.environ.copy(),
            wineprefix=pfx,
            proton_path=proton_arg,
            game_id="umu-default",
            store="",
            extra_share_paths=[exe_path],
        )
        raw_env = self.env_vars_input.text().strip()
        if raw_env:
            for key, value in LibraryPage._parse_env_vars(raw_env).items():
                env[key] = value

        # ── Installer options ─────────────────────────────────────────────────
        _inst_scale = (self._inst_scale_cb is not None and
                       self._inst_scale_cb.isChecked() and
                       self._exe_browse_is_install_mode())
        _inst_jp    = (self._inst_jp_locale_cb is not None and
                       self._inst_jp_locale_cb.isChecked() and
                       self._exe_browse_is_install_mode())

        if _inst_jp:
            env["LANG"]     = "ja_JP.UTF-8"
            env["LC_ALL"]   = "ja_JP.UTF-8"
            env["LANGUAGE"] = "ja_JP"

        if _inst_scale:
            # Match Wine's screen DPI to the monitor's actual pixel density so
            # the installer renders at a sane size. _installer_dpi uses physical
            # DPI directly (DE-agnostic, no scale-factor math) with a clamp +
            # scale-factor fallback for monitors whose EDID misreports size.
            _logical_dpi = _installer_dpi()
            _dpi_set_ok = _set_prefix_dpi(umu_bin, env, _logical_dpi)
            if _dpi_set_ok:
                _NAGOLog.prefix_run(f"[installer] Scale ON — set Wine LogPixels={_logical_dpi}")
                _prefix_run_bridge.line_ready.emit(
                    f"[installer] Scale ON — set Wine LogPixels={_logical_dpi}")
            else:
                _NAGOLog.prefix_run("[installer] Scale: reg write failed — running at default DPI")
                _prefix_run_bridge.line_ready.emit(
                    "[installer] Scale: reg write failed — running at default DPI")
        else:
            _dpi_set_ok = False
        # Switch button into Stop mode — stays clickable so a hung installer
        # can be force-terminated (matches the wineserver -k + process-group
        # kill that Force Terminate uses for the main game launch).
        self._set_prefix_run_button_state(btn, running=True)
        self._run_in_prefix_spinner = _ButtonSpinner(btn)
        self._run_in_prefix_spinner.start()

        exe_name = Path(exe_path).name
        # Name used in the log banner — saved games use the real name; an
        # unsaved Add Game dialog uses whatever's typed in the name field
        # (matches the slug used for its tmp prefix dir above).
        _banner_name = self.game.get("name") or self.name_input.toPlainText().strip() or "Unsaved Game"

        cwd = str(Path(exe_path).parent)
        worker = _RunInPrefixWorker(umu_bin, exe_path, env, cwd)

        def _restore_dpi_log():
            if _dpi_set_ok:
                _restore_prefix_dpi(umu_bin, env)
                _NAGOLog.prefix_run("[installer] Scale OFF — Wine LogPixels key deleted")
                _prefix_run_bridge.line_ready.emit(
                    "[installer] Scale OFF — Wine LogPixels key deleted")

        def _on_done():
            self._run_in_prefix_worker = None
            _restore_dpi_log()
            try:
                self._run_in_prefix_spinner.stop()
                self._set_prefix_run_button_state(btn, running=False)
                # For unsaved games, the prefix now exists — unlock Winetricks/Winecfg.
                # Proton comes from the dialog's selector so it's always available.
                if not self.game.get("id") and self._tmp_prefix_path and self._tmp_prefix_path.exists():
                    self._winetricks_btn.setEnabled(True)
                    self._winetricks_btn.setToolTip("Run Winetricks GUI")
                    self._winecfg_btn.setEnabled(True)
                    self._winecfg_btn.setToolTip("Open Winecfg for this prefix")
                    # ...but re-apply the Proton gate: winetricks stays off for Valve Proton.
                    self._sync_winetricks_for_proton()
            except RuntimeError:
                pass  # dialog closed while running
            _prefix_run_log_footer(_banner_name, "finished ok")

        def _on_failed(err: str):
            self._run_in_prefix_worker = None
            _restore_dpi_log()
            try:
                self._run_in_prefix_spinner.stop()
                self._set_prefix_run_button_state(btn, running=False)
                NAGOMessageBox.warning(self, "Run in Prefix Failed", f"Failed to run {exe_name}:\n{err}")
            except RuntimeError:
                pass
            _prefix_run_log_footer(_banner_name, f"failed: {err}")

        def _on_cancelled():
            self._run_in_prefix_worker = None
            _restore_dpi_log()
            try:
                self._run_in_prefix_spinner.stop()
                self._set_prefix_run_button_state(btn, running=False)
                _NAGOLog.launch(f"[run-in-prefix] {exe_name} force-terminated")
            except RuntimeError:
                pass  # dialog closed while running
            _prefix_run_log_footer(_banner_name, "force-terminated")

        worker.finished_ok.connect(_on_done)
        worker.failed.connect(_on_failed)
        worker.cancelled.connect(_on_cancelled)
        worker.start()
        self._run_in_prefix_worker = worker  # keep reference

        _NAGOLog.launch(f"[run-in-prefix] {exe_name} → prefix={pfx}  proton={proton_arg}  umu={umu_bin}")
        _prefix_run_log_header(_banner_name, exe_path, pfx, proton_arg, umu_bin, raw_env,
                                share_paths=env.get("STEAM_COMPAT_LIBRARY_PATHS", ""))

    def _browse_exe(self):
        """Proton Browse button: pick exe → switch runner by file type → scan
        store markers → fire umu search."""
        start_dir = self.config.get("last_browse_dir", str(Path.home()))
        path, _ = QFileDialog.getOpenFileName(self, "Select Executable", start_dir)
        if not path:
            return
        self.config["last_browse_dir"] = str(Path(path).parent)
        self._active_exe_input().setText(path)

        # Auto-switch runner based on file type, BEFORE scanning for store
        # markers below:
        # non-.exe (sh, py, no extension) → Native
        # .exe while currently Native → Proton
        # Order matters — a runner switch fires _on_type_change, which clears
        # the detected-store hint on every switch (so a stale hint from a
        # PREVIOUS browse can't linger). Switching first means that clear
        # happens before this browse's own hint gets set below, not after —
        # otherwise a GOG/Epic install found while starting from Native had
        # its own fresh hint wiped out immediately by its own switch to Proton.
        suffix = Path(path).suffix.lower()
        switched_to_native = False
        if suffix != ".exe" and hasattr(self, "_runner_btns"):
            for _b in self._runner_btns:
                if _b.property("runnerValue") == "native":
                    _b.setChecked(True)
                    switched_to_native = True
                    break
        elif suffix == ".exe" and hasattr(self, "_runner_btns"):
            current_runner = next(
                (_b.property("runnerValue") for _b in self._runner_btns if _b.isChecked()), None
            )
            if current_runner == "native":
                for _b in self._runner_btns:
                    if _b.property("runnerValue") == "proton":
                        _b.setChecked(True)
                        break

        # If the scan detected a Steam-library game and took over (switched to
        # the Steam importer), stop here — the rest of this method is Proton/
        # Native follow-up (umu search) that doesn't apply to a Steam game.
        if self._scan_exe_for_store(path):
            return

        self._auto_populate_install_dir(path)
        self._fsr_scan_done = False

        # Fire umu search only for Proton — not for native games
        if not switched_to_native:
            name = self.name_input.toPlainText().strip()
            if name:
                self.umu_options.search(name)

    def _clear_exe_browse_field(self):
        """Clear the manual exe Browse field (and its found/not-found hint
        and any detected-store hint) on a genuine manual runner-picker
        click — see the .clicked connection in the runner button loop for
        why this is wired to clicked rather than toggled. Deliberately does
        NOT touch name_input: a name you already typed shouldn't vanish
        just because you're reconsidering the runner."""
        if hasattr(self, "exe_input"):
            self._active_exe_input().setText("")
        _h = self._active_exe_hint()
        _h.setText("")
        _h.setVisible(False)
        self._set_store_hint("")

    def _select_store_combo(self, store_value: str):
        """Select store_combo's entry matching store_value, if present."""
        for i in range(self.store_combo.count()):
            if self.store_combo.itemData(i) == store_value:
                self.store_combo.setCurrentIndex(i)
                return

    def _set_store_hint(self, text: str):
        """Single source of truth for the exe-card header's 'detected store'
        hint (e.g. 'Epic Games Store install detected', '✓ GOG install
        detected') — shared by every Browse-triggered detection path
        (Proton/Native exe browse via _scan_exe_for_store, and GOG's own
        Browse field via _on_gog_browse_path_changed) instead of each one
        toggling visibility/text on its own label in a different part of
        the card. Empty text hides the row."""
        if not hasattr(self, "_store_hint_widget"):
            return
        self._store_hint_lbl.setText(text)
        self._store_hint_widget.setVisible(bool(text))

    def _scan_exe_for_store(self, path: str):
        """Scan the install directory for store markers; auto-fill name and store."""
        # Add-only: surface found/not-found feedback in exe_hint, mirroring
        # steam_hint/gog_hint's "Found N games" wording. exe_hint only exists
        # when self.game is falsy (Add flow), so this is a no-op in Edit.
        result = scan_install_dir_for_store(path)

        # ── Steam library detection (Add flow only) ───────────────────────────
        # Steam leaves no breadcrumb in the game folder, so scan_install_dir_for_store
        # can't see it. Instead, resolve the owning appid from the steamapps/common
        # path + appmanifest. If the path is under a real Steam library AND the appid
        # is present in the user's scanned Steam list (the combo), switch to the Steam
        # importer and select that entry — a legit Steam game can only launch through
        # Steam, so running its raw exe via Proton would just bounce through Steam
        # anyway. If the appid isn't in the combo (pirated / manually-dropped copy not
        # in the real library), fall through to normal Proton handling.
        if not self.game and hasattr(self, "steam_combo"):
            _steam_appid = steam_appid_from_exe_path(path)
            if _steam_appid:
                # Refresh the combo from disk before comparing, so a game the
                # user installed after opening this dialog isn't missed. The
                # combo populate just reads the (tiny) .acf manifests, so the
                # cost is negligible. blockSignals avoids _on_steam_game_picked
                # firing mid-refresh and clobbering the name field.
                self.steam_combo.blockSignals(True)
                self._populate_steam_games()
                self.steam_combo.blockSignals(False)
                _match_idx = -1
                for i in range(self.steam_combo.count()):
                    if self.steam_combo.itemData(i) == _steam_appid:
                        _match_idx = i
                        break
                if _match_idx >= 0:
                    # Legit installed Steam game — switch to Steam importer + select it.
                    # The visible runner pills (Native/Proton/Import) are a separate
                    # button set from type_combo and the import sub-picker; they only
                    # restyle/switch when their own handler fires. So we drive the
                    # Import runner button directly (setChecked → its toggled handler
                    # does the full visual switch: restyle pills, _row1_stack→Import,
                    # and calls _on_import_source_picked with the first sub-source).
                    # Then we force the Steam sub-source specifically and select the
                    # matching combo entry.
                    self._set_store_hint("")
                    _import_btn = next(
                        (_b for _b in getattr(self, "_runner_btns", [])
                         if _b.property("runnerValue") == "import"), None
                    )
                    if _import_btn is not None and _import_btn.isEnabled():
                        if _import_btn.isChecked():
                            # Already on Import — handler won't re-fire; switch
                            # sub-source manually.
                            self._on_import_source_picked("steam")
                        else:
                            _import_btn.setChecked(True)   # fires handler → import UI
                            self._on_import_source_picked("steam")  # force Steam sub-source
                    else:
                        # Import runner unavailable (Steam client not detected) —
                        # fall back to the combo/type_combo path so the entry is
                        # still selected even if the pills can't switch.
                        self._on_import_source_picked("steam")
                    self.steam_combo.setCurrentIndex(_match_idx)
                    self._on_steam_game_picked(_match_idx)
                    return True   # Steam takeover — caller should not run Proton follow-up
                # appid resolved but not in the user's library — Proton fallback.

        # Auto-fill name: prefer store-detected name, fall back to filename stem.
        # For new games (no id): always overwrite — switching type then browsing
        # a new file should update the name to reflect the new selection.
        # For existing games (edit flow): only fill if the field is empty so we
        # don't clobber a name the user intentionally set.
        _is_new = not (self.game and self.game.get("id"))
        if result["name"]:
            self.name_input.setPlainText(result["name"])
        elif _is_new or not self.name_input.toPlainText():
            self.name_input.setPlainText(Path(path).stem.replace("_", " ").title())

        if result["store"] == "gog":
            # Genuinely a separate, correctly-classified game_type in this
            # data model — drives the runner badge, _find_install_dir's
            # walk-up, and a future re-enabled protonfix GOG-ID lookup. Not
            # interchangeable with plain Proton the way Epic is (which has
            # no game_type of its own, just a store flag). So: save it as
            # "gog" for real — but WITHOUT the disruptive UI flip a
            # dedicated "GOG" button used to cause (that button doesn't
            # exist anymore; today's "Import" means "pick an already-
            # tracked Heroic/Lutris install", not "I browsed a raw exe").
            # type_combo is set with signals blocked so _on_type_change
            # never fires — the visible runner picker and exe_store_row
            # stay exactly as they were. gog_exe_input/_gog_mode are kept
            # in sync silently too, since _save() reads the exe path from
            # there once kind == "gog".
            if not self.game:
                self.type_combo.blockSignals(True)
                self.type_combo.setCurrentIndex(2)  # gog
                self.type_combo.blockSignals(False)
                self._gog_mode = "browse"
                self.gog_exe_input.setText(path)
                self._gog_browse_name = result["name"] or Path(path).stem.replace("_", " ").title()
            self._set_store_hint("✓ GOG install detected")
        elif result["store"] == "egs":
            # Epic: stay on Proton, set store combo
            self._select_store_combo("egs")
            self._set_store_hint("Epic Games Store install detected")
        else:
            # Neither store detected — clear a stale hint left over from a
            # previous browse (this was previously missing: re-browsing to a
            # plain exe after an Epic detection left the old hint stuck).
            self._set_store_hint("")

    def _save(self):
        name = self.name_input.toPlainText().strip()
        kind = self.type_combo.currentData()

        if kind == "steam":
            appid = self.steam_combo.currentData() or ""
            if not name or not appid:
                NAGOMessageBox.warning(self, "Missing Info",
                                    "Please pick a Steam game and provide a name.")
                return
            # We store the appid in exe_path for steam-type entries; launch handles it specially.
            exe_value = appid
        elif kind == "gog":
            if self._gog_mode == "browse":
                exe_value = self.gog_exe_input.text().strip()
            else:
                gog_data = self.gog_combo.currentData() or {}
                exe_value = gog_data.get("exe_path", "")
            if not name or not exe_value:
                NAGOMessageBox.warning(self, "Missing Info",
                                    "Please pick or browse a GOG game executable and provide a name.")
                return
        else:
            exe_value = self._active_exe_input().text().strip()
            if not name or not exe_value:
                NAGOMessageBox.warning(self, "Missing Info",
                                    "Please fill in name and executable path.")
                return

        # GOG and Steam both run through Proton/umu machinery
        is_proton_like = kind in ("proton", "gog")
        proton_path = self.proton_selector.selected_path() if is_proton_like else ""

        if is_proton_like:
            # Protonfix disabled (NAGO 04:20): never save a gameid. Store is purely
            # the origin label now — "gog" for GOG (drives the runner badge), "none"
            # for everything else (the store combo is hidden/disabled). No protonfix
            # combo precedence, no matcher read.
            final_store = "gog" if kind == "gog" else "none"
            umu_vals = {"enabled": True, "gameid": "", "store": final_store}
        else:
            umu_vals = {"enabled": False, "gameid": "", "store": "none"}

        # For DB storage, GOG is saved as game_type="proton" — same launch path,
        # just with store hardcoded to "gog".
        db_game_type = kind  # gog saved as "gog", not "proton"

        # ── Validate install_dir field (Add Game only) ───────────────────────
        if not self.game:
            if kind == "gog" and self._gog_mode == "browse":
                _id_chk = getattr(self, "_install_dir_input" if not self.game
                                  else "_gog_install_dir_input", None)
            elif kind not in ("steam", "gog"):
                _id_chk = getattr(self, "_install_dir_input", None)
            else:
                _id_chk = None
            if _id_chk is not None and _id_chk.isVisibleTo(self):
                _id_val = _id_chk.text().strip()
                if not _id_val or not Path(_id_val).is_dir():
                    NAGOMessageBox.warning(self, "Missing Info",
                                           "Please set a valid game install folder.")
                    return

        # ── Duplicate check (Add flow only — editing an existing game is exempt) ──
        if not self.game:
            con = None
            try:
                con = db_con()
                dupe = con.execute(
                    "SELECT id FROM games WHERE exe_path=?",
                    (exe_value,)
                ).fetchone()
            finally:
                if con is not None:
                    con.close()
            if dupe:
                NAGOMessageBox.warning(
                    self, "Duplicate Game",
                    f'A game with the path "{exe_value}" is already in your library.'
                )
                return

        _JP_VARS = "LANG=ja_JP.UTF-8 LC_ALL=ja_JP.UTF-8 LANGUAGE=ja_JP"
        _raw_env = self.env_vars_input.text().strip()
        # Strip any legacy JP locale tokens that were baked in by older versions
        for _tok in _JP_VARS.split():
            _raw_env = re.sub(r'(?:^|\s)' + re.escape(_tok) + r'(?=\s|$)', ' ', _raw_env).strip()
        _vn_jp_locale = 1 if (
            (hasattr(self, "_vn_jp_locale_cb") and self._vn_jp_locale_cb.isChecked())
            or (self._inst_jp_locale_cb is not None and self._inst_jp_locale_cb.isChecked())
        ) else 0
        _use_wined3d  = 1 if (hasattr(self, "_use_wined3d_cb") and
                               self._use_wined3d_cb.isChecked()) else 0
        _use_wow64    = 1 if (hasattr(self, "_use_wow64_cb") and
                               self._use_wow64_cb.isChecked()) else 0
        # Wayland: if AI upscaling force-disabled the box, the checkbox reads off even
        # though the user's preference may be on. Persist the real preference — the
        # launch-time XWayland override still wins at runtime, so saving 1 here is safe
        # and means the setting isn't lost when upscaling is later turned off.
        # Similarly, if HDR force-enabled the box, persist the real preference so that
        # disabling HDR later doesn't permanently leave Wayland checked.
        if hasattr(self, "_use_wayland_cb"):
            _kind_now = self.type_combo.currentData()
            _ups_now  = bool(getattr(self, "_upscale_cb", None) and self._upscale_cb.isChecked())
            _hdr_now  = bool(getattr(self, "_hdr_cb",    None) and self._hdr_cb.isChecked())
            _gs_now   = bool(getattr(self, "_gamescope_cb", None) and self._gamescope_cb.isChecked())
            if _kind_now in ("proton", "gog") and (_ups_now or (_hdr_now and not _gs_now)):
                _use_wayland = 1 if getattr(self, "_wayland_user_pref", False) else 0
            else:
                _use_wayland = 1 if self._use_wayland_cb.isChecked() else 0
        else:
            _use_wayland = 0
        _no_esync     = 1 if (hasattr(self, "_no_esync_cb") and
                               self._no_esync_cb.isChecked()) else 0
        _no_fsync     = 1 if (hasattr(self, "_no_fsync_cb") and
                               self._no_fsync_cb.isChecked()) else 0
        _no_ntsync    = 1 if (hasattr(self, "_no_ntsync_cb") and
                               self._no_ntsync_cb.isChecked()) else 0
        _legacy_mediaconv = 0  # deprecated — kept for DB compat, always 0 now
        _video_decode_mode = "winegstreamer" if (
            hasattr(self, "_use_gstreamer_cb") and self._use_gstreamer_cb.isChecked()
        ) else "default"

        # ── Resolve install_dir ───────────────────────────────────────────────
        # Steam: read installdir from appmanifest_APPID.acf via _resolve_game_folder.
        # GOG import mode: use install_path/install_dir from combo userData (Heroic/Lutris)
        #   if present, otherwise fall back to breadcrumb walk.
        # GOG browse, Proton, Native: read from field — if empty (user typed exe
        #   manually without Browse), auto-resolve now.
        if kind == "steam":
            _install_dir = _resolve_game_folder({"game_type": "steam", "exe_path": exe_value})
        elif kind == "gog" and not self.game and self._gog_mode != "browse":
            _gog_ud = self.gog_combo.currentData() or {}
            _install_dir = (
                _gog_ud.get("install_path") or
                _gog_ud.get("install_dir") or
                _find_install_dir(exe_value)
            )
        elif kind == "gog" and not self.game and self._gog_mode == "browse":
            _inp = getattr(self, "_install_dir_input", None)  # Add Game — same field as Native/Proton
            if _inp and not _inp.text().strip():
                self._auto_populate_install_dir(exe_value)
            _install_dir = _inp.text().strip() if _inp else _find_install_dir(exe_value)
        elif not self.game:
            # Native / Proton Add Game — read from field, auto-populate if empty
            _inp = getattr(self, "_install_dir_input", None)
            if _inp and not _inp.text().strip():
                self._auto_populate_install_dir(exe_value)
            _install_dir = _inp.text().strip() if _inp else _find_install_dir(exe_value)
        else:
            # Edit Game — field not shown, fallback only
            _install_dir = _find_install_dir(exe_value) if exe_value else ""

        self.result_data = {
            "name":                name,
            "exe_path":            exe_value,
            "game_type":           db_game_type,
            "proton_path":         proton_path,
            "umu_enabled":         1,  # unconditional for Proton
            "umu_gameid":          umu_vals["gameid"],
            "umu_store":           umu_vals["store"],
            "launch_args":         self.launch_args_input.text().strip(),
            "env_vars":            _raw_env,
            "vn_jp_locale":        _vn_jp_locale,
            "use_wined3d":         _use_wined3d,
            "use_wow64":           _use_wow64,
            "use_wayland":         _use_wayland,
            "no_esync":            _no_esync,
            "no_fsync":            _no_fsync,
            "no_ntsync":           _no_ntsync,
            "legacy_mediaconv":    _legacy_mediaconv,
            "video_decode_mode":   _video_decode_mode,
            "pre_launch_cmd":      self.pre_launch_input.text().strip(),
            "post_exit_cmd":       self.post_exit_input.text().strip(),
            "auto_backup":         1 if (hasattr(self, "_bk_auto_cb") and self._bk_auto_cb.isChecked()) else 0,
            # Steam games can't use any of HDR/gamescope/upscale — NAGO doesn't
            # own their launch path. If a user switched from Proton→Steam in the
            # dialog the checkboxes get hidden but their state would otherwise
            # leak through. Force-zero them here at the save boundary.
            #
            # Gamescope also has a "binary missing" path: when the dialog opens
            # with gamescope uninstalled we stash the DB value in
            # _gs_missing_pref and force the checkbox off. Honour that stash so
            # the user's preference isn't silently dropped on save.
            "gamescope_enabled":   0 if db_game_type == "steam" else (
                                   (1 if self._gs_missing_pref else 0)
                                   if hasattr(self, "_gs_missing_pref")
                                   else (
                                       (1 if getattr(self, "_gamescope_user_pref", False) else 0)
                                       if (bool(getattr(self, "_upscale_cb", None) and self._upscale_cb.isChecked()))
                                       else (1 if (hasattr(self, "_gamescope_cb") and self._gamescope_cb.isChecked()) else 0))),
            "pending_cover_path":  self._pending_cover_path,
            "upscale_enabled":     0 if db_game_type == "steam" else (
                                   1 if (hasattr(self, "_upscale_cb") and self._upscale_cb.isChecked()) else 0),
            "upscale_model":       (self._upscale_model_combo.currentData() if hasattr(self, "_upscale_model_combo") else "fast") or "fast",
            "hdr_enabled":         0 if db_game_type == "steam" else (
                                   (1 if getattr(self, "_hdr_user_pref", False) else 0)
                                   if (bool(getattr(self, "_upscale_cb", None) and self._upscale_cb.isChecked()))
                                   else (1 if (hasattr(self, "_hdr_cb") and self._hdr_cb.isChecked()) else 0)),
            "hdr_monitor":         "*",
            "fsr4_upgrade":        "" if db_game_type == "steam" else (
                                   self._fsr4_combo.currentData()
                                   if (hasattr(self, "_fsr4_cb") and self._fsr4_cb.isChecked()
                                       and hasattr(self, "_fsr4_combo"))
                                   else ""),
            "fsr4_indicator":      0,  # HUD checkbox removed; column retained, always 0
            "optiscaler_dll":      "" if db_game_type == "steam" else (
                                   self._opti_dll_combo.currentData()
                                   if (hasattr(self, "_opti_cb") and self._opti_cb.isChecked()
                                       and hasattr(self, "_opti_dll_combo"))
                                   else ""),
            "gog_id":              (scan_install_dir_for_store(exe_value).get("store_id", "")
                                    if db_game_type == "gog" and exe_value else ""),
            "tmp_prefix_path":     str(self._tmp_prefix_path) if self._tmp_prefix_path else "",
            "install_dir":         _install_dir,
        }

        # Commit pending cover to DB before accept()
        gid = self.game.get("id")
        if self._pending_cover_path:
            con = None
            try:
                con = db_con()
                if self._pending_cover_path == "__cleared__":
                    if gid:
                        # Delete old cover file from disk before clearing DB
                        old_cover = self.game.get("cover_path", "")
                        if old_cover:
                            try:
                                p = Path(old_cover)
                                if p.exists() and ART_PATH in p.parents:
                                    p.unlink()
                            except Exception as e:
                                _NAGOLog.session(f"[warn] GameDialog._save: failed to delete old cover {old_cover}: {e}")
                else:
                    p = Path(self._pending_cover_path)
                    if p.exists():
                        slug = slugify(self.game.get("name", "game") or
                                       self.name_input.toPlainText().strip() or "game")
                        final_id = gid or 0
                        final = ART_PATH / f"{slug}_{final_id}{p.suffix}"
                        if p != final:
                            p.rename(final)
                        if gid:
                            con.execute("UPDATE games SET cover_path=? WHERE id=?",
                                        (str(final), gid))
                        else:
                            # New game — _add_game will handle the DB write after insert
                            self.result_data["pending_cover_path"] = str(final)
                if gid:
                    con.commit()
            finally:
                if con is not None:
                    con.close()
            self._pending_cover_path = ""

        # If a cover download is still in flight, don't kill it — detach the
        # dialog's slot and hand the live worker to _add_game via result_data
        # so it can reconnect it once the new game ID is known.
        # If no download is in flight, teardown as normal.
        dw = self._dw
        try:
            still_running = dw is not None and dw.isRunning()
        except RuntimeError:
            # C++ object already deleted (worker finished and deleteLater fired)
            still_running = False
        if still_running:
            try:
                dw.cover_downloaded.disconnect(self._on_cover_downloaded)
            except (TypeError, RuntimeError):
                pass
            self.result_data["cover_worker"] = dw
            self._dw = None
        else:
            self._teardown_cover_worker()
        self.accept()

    def reject(self):
        """Clean up any pending cover — DB was never touched so nothing to restore.
        If a temporary prefix was created during Add Game, ask the user whether to keep it."""
        # Stop any in-flight cover-download worker first so it can't fire into the
        # dialog as it tears down.
        self._teardown_cover_worker()
        if self._pending_cover_path and self._pending_cover_path != "__cleared__":
            if Path(self._pending_cover_path).exists():
                Path(self._pending_cover_path).unlink(missing_ok=True)
        self._pending_cover_path = ""

        # Warn about orphaned tmp prefix
        if self._tmp_prefix_path and self._tmp_prefix_path.exists():
            box = NAGOMessageBox(
                "question",
                "Wine Prefix Created",
                f"A Wine prefix was created for this game but the game was not saved:\n\n"
                f"<code>{self._tmp_prefix_path}</code>\n\n"
                f"Delete it now, or keep it to reuse later?",
                parent=self,
                buttons=("Delete", "Keep"),
                default_button="Keep",
            )
            box.exec()
            if box.result_label() == "Delete":
                try:
                    shutil.rmtree(self._tmp_prefix_path, ignore_errors=True)
                except Exception as e:
                    _NAGOLog.session(f"[warn] GameDialog.reject: failed to delete tmp prefix {self._tmp_prefix_path}: {e}")
        self._tmp_prefix_path = None

        super().reject()


# ── VNDB Worker ───────────────────────────────────────────────────────────────
class VNDBWorker(_NAGOThread):
    """Searches VNDB for VN cover images. No API key required for reads.
    Returns a list of dicts with keys: title, url.
    Images with sexual rating > 1.0 are filtered out.
    """
    results_ready = pyqtSignal(list)
    error         = pyqtSignal(str)

    ENDPOINT = "https://api.vndb.org/kana/vn"

    def __init__(self, query: str):
        super().__init__()
        self.query = query

    def run(self):
        try:
            payload = {
                "filters":  ["search", "=", self.query],
                "fields":   "title, image.url, image.sexual, image.dims",
                "results":  10,
                "sort":     "searchrank",
            }
            r = _requests().post(
                self.ENDPOINT,
                json=payload,
                headers={"Content-Type": "application/json"},
                timeout=15,
            )
            if r.status_code != 200:
                self.error.emit(f"HTTP {r.status_code}")
                return
            data = r.json()
            covers = []
            for vn in data.get("results", []):
                img = vn.get("image")
                if not img or not img.get("url"):
                    continue
                # Skip sexually explicit images (rating scale 0-2; >1.0 = explicit)
                if (img.get("sexual") or 0) > 1.0:
                    continue
                dims = img.get("dims") or [0, 0]
                covers.append({
                    "title":  vn.get("title", ""),
                    "url":    img["url"],
                    "width":  dims[0],
                    "height": dims[1],
                })
            self.results_ready.emit(covers)
        except Exception as exc:
            self.error.emit(str(exc))


# ── Cover Picker Dialog ────────────────────────────────────────────────────────
class CoverPickerDialog(_NAGODialog):
    cover_selected = pyqtSignal(str)   # URL (remote)
    cover_local    = pyqtSignal(str)   # local file path chosen by user
    cover_cleared  = pyqtSignal()      # user explicitly chose "No Cover"

    SOURCE_SGDB = "sgdb"
    SOURCE_VNDB = "vndb"

    # Worker teardown is handled by _teardown_workers() → each worker's
    # stop_safely() (defined on the _NAGOThread base). A worker still mid-
    # request when the dialog closes gets parked in _NAGOThread._orphans so
    # it outlives the dialog and finishes detached, instead of being
    # destroyed while running — which is what aborted the process before.

    def __init__(self, api_key: str, game_name: str, parent=None):
        super().__init__(parent)
        self.api_key        = api_key
        self.game_name      = game_name
        self._source        = self.SOURCE_SGDB
        self.setWindowTitle("Pick Cover Art")
        self.setMinimumSize(700, 740)
        self.setWindowFlags(Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self._sgdb_results  = []
        self._cover_list    = []
        self._selected_url  = ""   # URL of last cover clicked (any source)
        self._selected_thumb = None  # CoverThumb widget of last selection
        self._search_gen    = 0    # incremented on each new search; stale results are discarded
        self._worker        = None  # active search worker; nulled by finished signal
        self._cworker       = None  # active cover fetch worker; nulled by finished signal
        self._build()
        self._has_api_key = bool(api_key.strip())
        self._search_started = False  # guard: auto-search fires once in showEvent

    def showEvent(self, event):
        super().showEvent(event)
        if not self._search_started:
            self._search_started = True
            self._do_search(self.game_name)

    def _build(self):
        outer = QVBoxLayout(self)
        outer.setContentsMargins(self._SHADOW, self._SHADOW, self._SHADOW, self._SHADOW)
        outer.setSpacing(0)
        root = QFrame()
        root.setObjectName("dialogRoot")
        outer.addWidget(root)

        layout = QVBoxLayout(root)
        layout.setContentsMargins(24, 24, 24, 24)
        layout.setSpacing(14)

        title = QLabel("Pick Cover Art")
        title.setObjectName("dlgTitle")
        layout.addWidget(title)

        # ── Search row ────────────────────────────────────────────────────
        row = QHBoxLayout()
        self.search_input = QLineEdit(self.game_name)
        self.search_input.setObjectName("search")
        self.search_input.returnPressed.connect(lambda: self._do_search(self.search_input.text()))
        search_btn = QPushButton("Search")
        search_btn.setObjectName("primary")
        search_btn.clicked.connect(lambda: self._do_search(self.search_input.text()))
        row.addWidget(self.search_input)
        row.addWidget(search_btn)
        layout.addLayout(row)

        # ── Source + game combo row ───────────────────────────────────────
        # "Source" label | [SteamGridDB] [VNDB] segmented toggle | game combo
        source_row = QHBoxLayout()
        source_row.setSpacing(8)

        source_lbl = QLabel("Source")
        source_lbl.setObjectName("dialogMuted")
        source_row.addWidget(source_lbl)
        source_row.setSpacing(6)

        # Segmented toggle — two QPushButtons inside a QFrame that looks like one control
        seg_frame = QFrame()
        seg_frame.setObjectName("sourceSegment")
        seg_layout = QHBoxLayout(seg_frame)
        seg_layout.setContentsMargins(6, 2, 6, 2)
        seg_layout.setSpacing(6)
        self._btn_sgdb = QPushButton("SGDB")
        self._btn_sgdb.setObjectName("segActive")
        self._btn_sgdb.setCheckable(True)
        self._btn_sgdb.setChecked(True)
        self._btn_sgdb.clicked.connect(lambda: self._set_source(self.SOURCE_SGDB))
        self._btn_vndb = QPushButton("VNDB")
        self._btn_vndb.setObjectName("segInactive")
        self._btn_vndb.setCheckable(True)
        self._btn_vndb.setChecked(False)
        self._btn_vndb.clicked.connect(lambda: self._set_source(self.SOURCE_VNDB))
        seg_layout.addWidget(self._btn_sgdb)
        seg_layout.addWidget(self._btn_vndb)
        source_row.addWidget(seg_frame)

        # Game combo — stretches to fill remaining row width
        self.game_combo = NAGOComboBox()
        self.game_combo.setObjectName("dlgCombo")
        self.game_combo.setPlaceholderText("Select game…")
        self.game_combo.currentIndexChanged.connect(self._on_game_selected)
        source_row.addWidget(self.game_combo, 1)

        layout.addLayout(source_row)

        # ── Status ────────────────────────────────────────────────────────
        self.status_lbl = QLabel("")
        self.status_lbl.setObjectName("dialogMuted")
        layout.addWidget(self.status_lbl)

        # ── Covers grid scroll ────────────────────────────────────────────
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.covers_container = QWidget()
        self.covers_grid = QGridLayout(self.covers_container)
        self.covers_grid.setSpacing(10)
        scroll.setWidget(self.covers_container)
        layout.addWidget(scroll)

        # ── Local file row ────────────────────────────────────────────────
        local_frame = QFrame()
        local_frame.setObjectName("settingsSection")
        lf = QHBoxLayout(local_frame)
        lf.setContentsMargins(12, 10, 12, 10)
        lf.setSpacing(8)
        local_lbl = QLabel("Local image:")
        local_lbl.setObjectName("dialogMuted")
        lf.addWidget(local_lbl)
        self.local_path_input = QLineEdit()
        self.local_path_input.setObjectName("dlgInput")
        self.local_path_input.setPlaceholderText("Browse or paste a path — takes priority over online sources")
        self.local_path_input.textChanged.connect(self._update_selection_label)
        local_browse_btn = QPushButton("Browse…")
        local_browse_btn.setObjectName("secondary")
        local_browse_btn.clicked.connect(self._browse_local)
        lf.addWidget(self.local_path_input, 1)
        lf.addWidget(local_browse_btn)
        layout.addWidget(local_frame)

        # ── Footer: selection status + action buttons ─────────────────────
        footer = QHBoxLayout()
        self.selection_lbl = QLabel("Nothing selected")
        self.selection_lbl.setObjectName("selectionStatus")
        footer.addWidget(self.selection_lbl, 1)
        no_cover_btn = QPushButton("No Cover")
        no_cover_btn.setObjectName("secondary")
        no_cover_btn.setToolTip("Remove the current cover and use no art")
        no_cover_btn.clicked.connect(self._clear_cover)
        footer.addWidget(no_cover_btn)
        cancel_btn = QPushButton("  Cancel")
        cancel_btn.setIcon(ph_icon("x", 22))
        cancel_btn.setObjectName("secondary")
        cancel_btn.clicked.connect(self.reject)
        footer.addWidget(cancel_btn)
        self.save_btn = QPushButton("  Save Cover")
        self.save_btn.setIcon(ph_icon("floppy-disk", 22, "#ffffff"))
        self.save_btn.setObjectName("primary")
        self.save_btn.setEnabled(False)
        self.save_btn.clicked.connect(self._commit_selection)
        footer.addWidget(self.save_btn)
        layout.addLayout(footer)

    def _browse_local(self):
        cfg = load_config()
        start_dir = cfg.get("last_browse_dir", str(Path.home()))
        path, _ = QFileDialog.getOpenFileName(
            self, "Select Cover Image", start_dir,
            "Images (*.png *.jpg *.jpeg *.webp *.bmp *.gif)"
        )
        if path:
            cfg["last_browse_dir"] = str(Path(path).parent)
            save_config(cfg)
            self.local_path_input.setText(path)

    def _update_selection_label(self):
        """Refresh the footer status label and Save button state."""
        local = self.local_path_input.text().strip()
        if local:
            name = Path(local).name
            self.selection_lbl.setText(f"📁  Local: {name}  (takes priority)")
            self.selection_lbl.setProperty("status", "ok")
            self.save_btn.setEnabled(True)
        elif self._selected_url:
            w = getattr(self._selected_thumb, "img_w", 0)
            h = getattr(self._selected_thumb, "img_h", 0)
            size_str = f"  \u00b7  {w}\u00d7{h}" if w and h else ""
            self.selection_lbl.setText(f"Selected{size_str}")
            self.selection_lbl.setProperty("status", "selected")
            self.save_btn.setEnabled(True)
        else:
            self.selection_lbl.setText("Nothing selected")
            self.selection_lbl.setProperty("status", "")
            self.save_btn.setEnabled(False)
        self.selection_lbl.style().unpolish(self.selection_lbl)
        self.selection_lbl.style().polish(self.selection_lbl)

    def _clear_cover(self):
        """Emit cover_cleared and close."""
        self.cover_cleared.emit()
        self.accept()

    def _commit_selection(self):
        """Save Cover clicked — local path wins over online source if both are set."""
        local = self.local_path_input.text().strip()
        if local:
            if not Path(local).exists():
                NAGOMessageBox.warning(self, "File Not Found", f"Could not find:\n{local}")
                return
            self.cover_local.emit(local)
        elif self._selected_url:
            self.cover_selected.emit(self._selected_url)
        self.accept()

    def _set_source(self, source: str):
        """Switch the active source, update button states, re-run the search."""
        self._source = source
        self._btn_sgdb.setChecked(source == self.SOURCE_SGDB)
        self._btn_vndb.setChecked(source == self.SOURCE_VNDB)
        self._btn_sgdb.setObjectName("segActive"   if source == self.SOURCE_SGDB else "segInactive")
        self._btn_vndb.setObjectName("segActive"   if source == self.SOURCE_VNDB else "segInactive")
        # Force stylesheet re-evaluation after objectName change
        self._btn_sgdb.style().unpolish(self._btn_sgdb)
        self._btn_sgdb.style().polish(self._btn_sgdb)
        self._btn_vndb.style().unpolish(self._btn_vndb)
        self._btn_vndb.style().polish(self._btn_vndb)
        self._selected_url = ""
        self._update_selection_label()
        self._do_search(self.search_input.text())

    def _do_search(self, query: str):
        if not query.strip():
            return
        self._search_gen += 1          # invalidate any in-flight results
        gen = self._search_gen
        self.game_combo.clear()
        self._clear_covers()
        self._selected_url = ""
        self._update_selection_label()
        if self._source == self.SOURCE_VNDB:
            self._do_search_vndb(query, gen)
        else:
            self._do_search_sgdb(query, gen)

    def _do_search_sgdb(self, query: str, gen: int):
        if not self._has_api_key:
            self.status_lbl.setText(
                "No SteamGridDB API key — add one in Settings, or use VNDB / a local image."
            )
            return
        # Stop any in-flight search worker before starting a new one
        if self._worker is not None:
            # stop_safely(): blocking network worker — quit()+deleteLater()
            # would destroy it mid-request and abort. Parks if still running.
            self._worker.stop_safely()
            self._worker = None
        self.status_lbl.setText("Searching SteamGridDB…")
        self._worker = SGDBWorker(self.api_key)
        self._worker.results_ready.connect(
            lambda results: self._on_sgdb_search_results(results, gen)
        )
        self._worker.error.connect(lambda e: self.status_lbl.setText(f"Error: {e}"))
        self._worker.finished.connect(self._worker.deleteLater)
        self._worker.finished.connect(lambda: setattr(self, "_worker", None))
        self._worker.search_game(query)

    def _do_search_vndb(self, query: str, gen: int):
        if self._worker is not None:
            self._worker.stop_safely()
            self._worker = None
        self.status_lbl.setText("Searching VNDB…")
        self.game_combo.setEnabled(False)
        self._worker = VNDBWorker(query)
        self._worker.results_ready.connect(lambda covers: self._on_vndb_results(covers, gen))
        self._worker.error.connect(lambda e: (
            self.status_lbl.setText(f"VNDB error: {e}"),
            self.game_combo.setEnabled(True),
        ))
        self._worker.finished.connect(self._worker.deleteLater)
        self._worker.finished.connect(lambda: setattr(self, "_worker", None))
        self._worker.start()

    def _on_sgdb_search_results(self, results, gen: int):
        if gen != self._search_gen:
            return   # stale — a newer search superseded this one
        self._sgdb_results = results
        self.game_combo.clear()
        self.game_combo.setEnabled(True)
        if not results:
            self.status_lbl.setText("No games found on SteamGridDB.")
            return
        for g in results:
            self.game_combo.addItem(g.get("name", ""), userData=g.get("id"))

        # Auto-pick the closest match.
        # Strategy: case-insensitive exact title match wins, then prefix match,
        # then substring match. Otherwise the first result (SGDB returns most-relevant first).
        query = self.search_input.text().strip().lower()
        best_idx = 0  # default to first/most-relevant result
        if query:
            exact_idx = -1
            prefix_idx = -1
            for i, g in enumerate(results):
                title = (g.get("name") or "").strip().lower()
                if title == query:
                    exact_idx = i
                    break
                if prefix_idx < 0 and title.startswith(query):
                    prefix_idx = i
            if exact_idx >= 0:
                best_idx = exact_idx
            elif prefix_idx >= 0:
                best_idx = prefix_idx

        match_label = results[best_idx].get("name", "")
        self.status_lbl.setText(
            f"Found {len(results)} game(s) on SteamGridDB. Auto-selected: {match_label}"
        )
        # Setting the index will fire _on_game_selected, which fetches the covers
        self.game_combo.setCurrentIndex(best_idx)

    def _on_vndb_results(self, covers, gen: int):
        """VNDB returns one cover per VN. Store them, populate the combo,
        then show the best-matching cover automatically."""
        if gen != self._search_gen:
            return   # stale — a newer search superseded this one
        self.game_combo.setEnabled(True)
        self._clear_covers()
        self._vndb_covers = covers
        if not covers:
            self.status_lbl.setText("No results found on VNDB.")
            return
        # Populate combo — selecting an entry shows that VN's single cover
        self.game_combo.blockSignals(True)
        self.game_combo.clear()
        for i, cover in enumerate(covers):
            self.game_combo.addItem(cover.get("title", f"Result {i+1}"), userData=i)
        self.game_combo.blockSignals(False)
        # Auto-select the closest title match, same strategy as SGDB
        query = self.search_input.text().strip().lower()
        best_idx = 0
        if query:
            for i, cover in enumerate(covers):
                title = (cover.get("title") or "").strip().lower()
                if title == query:
                    best_idx = i
                    break
                if title.startswith(query) and best_idx == 0:
                    best_idx = i
        self.game_combo.setCurrentIndex(best_idx)
        self._show_vndb_cover(best_idx)
        self.status_lbl.setText(
            f"Found {len(covers)} result(s) on VNDB. Auto-selected: {covers[best_idx].get('title', '')}"
        )

    def _show_vndb_cover(self, idx):
        """Display the single cover for the VNDB result at idx."""
        self._clear_covers()
        covers = getattr(self, "_vndb_covers", [])
        if idx < 0 or idx >= len(covers):
            return
        cover = covers[idx]
        thumb_lbl = CoverThumb(cover["url"], cover["url"],
                               cover.get("width", 0), cover.get("height", 0))
        thumb_lbl.selected.connect(self._cover_chosen)
        self.covers_grid.addWidget(thumb_lbl, 0, 0)

    def _on_game_selected(self, idx):
        if self._source == self.SOURCE_VNDB:
            self._show_vndb_cover(idx)
            return
        if idx < 0 or idx >= len(self._sgdb_results):
            return
        gid = self._sgdb_results[idx].get("id")
        if not gid:
            return
        self.status_lbl.setText("Fetching covers…")
        self._clear_covers()
        if self._cworker is not None:
            self._cworker.stop_safely()
            self._cworker = None
        self._cworker = SGDBWorker(self.api_key)
        self._cworker.covers_ready.connect(self._on_covers_ready)
        self._cworker.error.connect(lambda e: self.status_lbl.setText(f"Error: {e}"))
        self._cworker.finished.connect(self._cworker.deleteLater)
        self._cworker.finished.connect(lambda: setattr(self, "_cworker", None))
        self._cworker.fetch_covers(gid)

    def _on_covers_ready(self, covers):
        self._clear_covers()
        self._cover_list = covers
        if not covers:
            self.status_lbl.setText("No covers found.")
            return
        self.status_lbl.setText(f"{len(covers)} cover(s) available — click to select")
        cols = 4
        for i, cover in enumerate(covers):
            row, col = divmod(i, cols)
            thumb_lbl = CoverThumb(cover["thumb"], cover["url"],
                                     cover.get("width", 0), cover.get("height", 0))
            thumb_lbl.selected.connect(self._cover_chosen)
            self.covers_grid.addWidget(thumb_lbl, row, col)

    def _clear_covers(self):
        while self.covers_grid.count():
            item = self.covers_grid.takeAt(0)
            if item.widget():
                item.widget().deleteLater()

    def _cover_chosen(self, url: str):
        """Cover clicked (any source) — record it and update footer. Doesn't close yet."""
        self._selected_url = url
        self._selected_thumb = None
        # Find the thumb widget for dimension lookup
        for i in range(self.covers_grid.count()):
            w = self.covers_grid.itemAt(i).widget()
            if isinstance(w, CoverThumb):
                w.set_selected(w.full_url == url)
                if w.full_url == url:
                    self._selected_thumb = w
        self._update_selection_label()

    def _teardown_workers(self):
        """Stop both worker threads before the dialog is destroyed, via the
        base class's stop_safely() (disconnect + quit + brief wait, then park
        if still running). This is the guard that prevents the
        ~QThread-while-running fatal abort. Called from both done() (every
        accept/reject path) and closeEvent (window X)."""
        for attr in ("_worker", "_cworker"):
            w = getattr(self, attr, None)
            if w is None:
                continue
            setattr(self, attr, None)
            try:
                w.stop_safely()
            except Exception:
                pass

    def done(self, result):
        # done() is the single funnel both accept() and reject() pass through,
        # so overriding it here covers every close path — Cancel/Esc/X (reject),
        # a confirmed cover pick (accept, two call sites), and any programmatic
        # close — with one teardown, no duplicated guards.
        self._teardown_workers()
        super().done(result)

    def closeEvent(self, event):
        # Window-manager close (X) routes through closeEvent, which Qt then
        # turns into a reject()/done() — but tear down here too so the workers
        # are stopped even if a subclass/event-filter path reaches closeEvent
        # without going through done(). _teardown_workers() is idempotent
        # (nulls each attr as it goes), so running it twice is harmless.
        self._teardown_workers()
        super().closeEvent(event)


class CoverThumb(QLabel):
    selected = pyqtSignal(str)

    def __init__(self, thumb_url: str, full_url: str, img_w: int = 0, img_h: int = 0, parent=None):
        super().__init__(parent)
        self.full_url = full_url
        self.img_w = img_w
        self.img_h = img_h
        self._selected = False
        self._hover    = False
        self.setFixedSize(140, 200)
        self.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self._apply_border()
        self.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        self._load_thumb(thumb_url)

    def _accent(self) -> str:
        app = QApplication.instance()
        return (app.property("nagoAccent") or "#6366f1") if app else "#6366f1"

    def _apply_border(self):
        """Single source of truth for the border. Selected OR hover draws the
        accent; otherwise the muted default. Recomputed from state on every
        enter/leave/select, so leaving a selected thumb no longer wipes the
        selection indication (the old leaveEvent reset unconditionally)."""
        surf = _t('#2d2d32', '#f0f0f4')
        if self._selected or self._hover:
            self.setStyleSheet(f"background: {surf}; border-radius: 6px; border: 3px solid {self._accent()};")
        else:
            self.setStyleSheet(f"background: {surf}; border-radius: 6px; border: 2px solid {_t('#424248', '#d4d4d8')};")

    def _load_thumb(self, url):
        self._tw = _ThumbLoader(url)
        self._tw.loaded.connect(self._set_px)
        self._tw.finished.connect(self._tw.deleteLater)
        self._tw.start()

    def _set_px(self, px: QPixmap):
        scaled = px.scaled(140, 200,
                           Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                           Qt.TransformationMode.SmoothTransformation)
        x = (scaled.width()  - 140) // 2
        y = (scaled.height() - 200) // 2
        cropped = scaled.copy(x, y, 140, 200)
        self.setPixmap(cropped)

    def set_selected(self, selected: bool):
        self._selected = selected
        self._apply_border()
        self.update()   # repaint the corner check badge

    def mousePressEvent(self, event):
        self.selected.emit(self.full_url)

    def enterEvent(self, event):
        self._hover = True
        self._apply_border()

    def leaveEvent(self, event):
        self._hover = False
        self._apply_border()

    def paintEvent(self, event):
        # QLabel paints background, stylesheet border, and the pixmap first;
        # the selection badge is drawn on top so a selected cover stays
        # unmistakable even while the cursor hovers a different thumb (which
        # also shows an accent border — only the selected one gets the check).
        super().paintEvent(event)
        if not self._selected:
            return
        r  = 11.0
        cx = self.width() - r - 7.0
        cy = r + 7.0
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        # filled accent disc
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(QColor(self._accent())))
        p.drawEllipse(int(cx - r), int(cy - r), int(r * 2), int(r * 2))
        # white check mark
        path = QPainterPath()
        path.moveTo(cx - 5.0, cy + 0.5)
        path.lineTo(cx - 1.5, cy + 4.0)
        path.lineTo(cx + 5.0, cy - 4.5)
        pen = QPen(QColor("#ffffff"), 2.2)
        pen.setCapStyle(Qt.PenCapStyle.RoundCap)
        pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
        p.setPen(pen)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawPath(path)
        p.end()


class _ThumbLoader(_NAGOThread):
    _log_lifecycle = False   # spawns in bulk for every visible card — too noisy
    loaded = pyqtSignal(QPixmap)

    def __init__(self, url):
        super().__init__()
        self.url = url

    def run(self):
        try:
            r = _requests().get(self.url, timeout=15)
            img = _pil_image().open(io.BytesIO(r.content)).convert("RGB")
            buf = io.BytesIO()
            img.save(buf, "PNG")
            px = QPixmap()
            px.loadFromData(buf.getvalue())
            self.loaded.emit(px)
        except Exception as e:
            _NAGOLog.session(f"[warn] _ThumbLoader: failed to load thumbnail from {self.url}: {e}")
# segment under the active tab button, creating a seamless connected look.
class _IslandPanel(QWidget):
    """
    Contains:
      - A tab bar widget (QPushButtons) at the top
      - An island QFrame below it (content area, no QSS border)
    Draws the island border itself in paintEvent, skipping the segment
    directly under the active tab button.
    """
    RADIUS  = 12.0

    def __init__(self, parent=None):
        super().__init__(parent)
        self._active_idx  = 0
        self._tab_btns: list = []   # filled by SettingsPage
        self.setAttribute(Qt.WidgetAttribute.WA_OpaquePaintEvent, False)

    def _theme_colors(self):
        """Return (bg, border, page_bg) QColors appropriate for the current theme."""
        theme = _current_theme()
        if theme == "light":
            return (
                QColor("#ebebef"),   # island BG  — matches __T_SIDEBAR_BG__ light
                QColor("#d4d4d8"),   # border     — matches __T_BORDER__ light
                QColor("#f5f5f7"),   # page BG    — matches __T_BG__ light (erase color)
            )
        return (
            QColor("#2a2a30"),       # island BG  — original dark
            QColor("#3d3d43"),       # border     — original dark
            QColor("#1d1d20"),       # page BG    — original dark
        )

    # ── Layout ───────────────────────────────────────────────────────────────
    def setup(self, tab_bar: QWidget, island: QFrame):
        self._tab_bar = tab_bar
        self._island  = island
        tab_bar.setParent(self)
        island.setParent(self)
        # Strip all QSS styling — background and border are painted by us
        island.setObjectName("settingsIsland")
        island.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        island.setAutoFillBackground(False)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._do_layout()

    def _tab_bar_height(self) -> int:
        th = self._tab_bar.sizeHint().height()
        return th if th > 10 else 38

    def _do_layout(self):
        w  = self.width()
        h  = self.height()
        th = self._tab_bar_height()
        self._tab_bar.setGeometry(0, 0, w, th)
        # Island starts 1px into the tab bar so our painted border
        # sits exactly at the tab bar bottom edge
        self._island.setGeometry(1, th, w - 2, h - th - 1)
        self._tab_bar.raise_()
        self.update()   # repaint border

    def set_active_tab(self, idx: int):
        self._active_idx = idx
        self.update()

    # ── Paint ─────────────────────────────────────────────────────────────────
    def paintEvent(self, _event):
        if not hasattr(self, '_island'):
            return

        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)

        island_bg, border_col, page_bg = self._theme_colors()
        th = self._tab_bar_height()
        w  = self.width()
        h  = self.height()

        # The border rect — sits around the island area
        border_rect = QRectF(0.5, th - 0.5, w - 1, h - th - 0.5)

        # ── Draw rounded border — top-left flat when first tab is active ──────
        tl = 0.0 if self._active_idx == 0 else self.RADIUS
        path = QPainterPath()
        # Manually build path with per-corner radii
        r = border_rect
        path.moveTo(r.left() + tl, r.top())
        path.lineTo(r.right() - self.RADIUS, r.top())
        path.arcTo(QRectF(r.right() - self.RADIUS*2, r.top(), self.RADIUS*2, self.RADIUS*2), 90, -90)
        path.lineTo(r.right(), r.bottom() - self.RADIUS)
        path.arcTo(QRectF(r.right() - self.RADIUS*2, r.bottom() - self.RADIUS*2, self.RADIUS*2, self.RADIUS*2), 0, -90)
        path.lineTo(r.left() + self.RADIUS, r.bottom())
        path.arcTo(QRectF(r.left(), r.bottom() - self.RADIUS*2, self.RADIUS*2, self.RADIUS*2), 270, -90)
        path.lineTo(r.left(), r.top() + tl)
        if tl > 0:
            path.arcTo(QRectF(r.left(), r.top(), tl*2, tl*2), 180, -90)
        path.closeSubpath()
        # Fill background first, then stroke border on top
        p.setPen(Qt.PenStyle.NoPen)
        p.setBrush(QBrush(island_bg))
        p.drawPath(path)

        pen = QPen(border_col, 1.0)
        pen.setCosmetic(True)
        p.setPen(pen)
        p.setBrush(Qt.BrushStyle.NoBrush)
        p.drawPath(path)

        # ── Erase top border segment under active tab button ──────────────────
        # Find the active button's x extent in our coordinate space
        if self._tab_btns:
            try:
                btn, _ = self._tab_btns[self._active_idx]
                bx = btn.mapTo(self, QPoint(0, 0)).x()
                bw = btn.width()
                # Erase with page background color, no AA, 2px pen to fully
                # cover the 1px antialiased border line
                p.setRenderHint(QPainter.RenderHint.Antialiasing, False)
                erase_pen = QPen(page_bg, 2.0)
                erase_pen.setCosmetic(True)
                p.setPen(erase_pen)
                # +RADIUS on left to skip the rounded corner of the island,
                # but only when first tab is active (left edge)
                left_pad  = int(self.RADIUS) if self._active_idx == 0 else 2
                right_pad = 2
                p.drawLine(bx + left_pad, th - 1, bx + bw - right_pad, th - 1)
            except (IndexError, RuntimeError):
                pass

        p.end()


# ── Settings Page ──────────────────────────────────────────────────────────────
class SettingsPage(QWidget):
    config_saved = pyqtSignal(dict)

    def __init__(self, config: dict, parent=None):
        super().__init__(parent)
        self.config = config
        self._build()

    def _build(self):
        # ── Outer page padding ────────────────────────────────────────────────
        outer = QVBoxLayout(self)
        outer.setContentsMargins(24, 0, 24, 20)
        outer.setSpacing(0)

        # ── Island panel — owns tab bar + island, draws border in paintEvent ──
        self._panel = _IslandPanel()
        outer.addWidget(self._panel, 1)

        # ── Tab bar ───────────────────────────────────────────────────────────
        tab_bar_widget = QWidget()
        tab_bar_widget.setObjectName("settingsTabBar")
        tab_bar_layout = QHBoxLayout(tab_bar_widget)
        tab_bar_layout.setContentsMargins(0, 0, 4, 0)
        tab_bar_layout.setSpacing(2)

        # ── Island ────────────────────────────────────────────────────────────
        island = QFrame()
        island.setObjectName("settingsIsland")
        island.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        island_layout = QVBoxLayout(island)
        island_layout.setContentsMargins(0, 0, 0, 0)
        island_layout.setSpacing(0)

        self._panel.setup(tab_bar_widget, island)

        # ── Stacked pages ─────────────────────────────────────────────────────
        self._stack = QStackedWidget()
        island_layout.addWidget(self._stack, 1)

        # Build tab buttons + pages
        self._tab_btns = []   # list of (QPushButton, icon_name)

        def _add_tab(icon_name: str, label: str, page_widget: QWidget):
            idx = self._stack.count()
            self._stack.addWidget(page_widget)
            btn = QPushButton(f"  {label}")
            btn.setObjectName("settingsTabBtn")
            btn.setCheckable(True)
            btn.setIcon(ph_icon(icon_name, 15, "#7e7e88"))
            btn.setIconSize(QSize(15, 15))
            btn.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Fixed)
            btn.clicked.connect(lambda checked, i=idx: self._switch_tab(i))
            tab_bar_layout.addWidget(btn)
            self._tab_btns.append((btn, icon_name))

        # ── TAB 1: Appearance ─────────────────────────────────────────────────
        appearance_page = QWidget()
        ap = QVBoxLayout(appearance_page)
        ap.setContentsMargins(24, 14, 24, 20)
        ap.setSpacing(12)
        ap.setAlignment(Qt.AlignmentFlag.AlignTop)

        # ── Row 1: Accent Color (left) + Card Size (right) ───────────────────
        top_row = QHBoxLayout()
        top_row.setSpacing(12)

        # Accent color
        accent_frame = QFrame()
        accent_frame.setObjectName("settingsSection")
        accent_frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        accent_frame.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        av2 = QVBoxLayout(accent_frame)
        av2.setContentsMargins(12, 10, 12, 10)
        av2.setSpacing(10)
        av2.addWidget(self._section_label("Accent Color"))
        self._accent_color          = self.config.get("accent_color", DEFAULT_ACCENT)
        self._accent_color_original = self._accent_color
        self._accent_btns = []
        swatch_row = QHBoxLayout()
        swatch_row.setSpacing(8)
        swatch_row.setAlignment(Qt.AlignmentFlag.AlignLeft)
        _swatch_sel_brd = "#18181b" if self.config.get("theme", "dark") == "light" else "#ffffff"
        for hex_color in ACCENT_COLORS:
            sb = QPushButton()
            sb.setFixedSize(24, 24)
            sb.setStyleSheet(
                f"background:{hex_color}; border-radius:5px; border:2px solid "
                f"{_swatch_sel_brd if hex_color == self._accent_color else 'transparent'};")
            sb.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
            sb.clicked.connect(lambda checked, c=hex_color: self._pick_accent(c))
            swatch_row.addWidget(sb)
            self._accent_btns.append((hex_color, sb))
        swatch_row.addStretch()
        av2.addLayout(swatch_row)
        top_row.addWidget(accent_frame, 3)

        # Card size
        card_frame = QFrame()
        card_frame.setObjectName("settingsSection")
        card_frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        card_frame.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        cv = QVBoxLayout(card_frame)
        cv.setContentsMargins(12, 10, 12, 10)
        cv.setSpacing(10)
        cv.addWidget(self._section_label("Card Size"))
        self._card_size_slider = QSlider(Qt.Orientation.Horizontal)
        self._card_size_slider.setMinimum(140)
        self._card_size_slider.setMaximum(280)
        self._card_size_slider.setSingleStep(1)
        self._card_size_slider.setPageStep(10)
        self._card_size_slider.setValue(int(self.config.get("card_width", CARD_W)))
        self._card_size_slider.setTickPosition(QSlider.TickPosition.NoTicks)
        self._card_size_slider.setToolTip("Default: 185px")
        self._card_size_val = QLabel(f"{self._card_size_slider.value()}px")
        self._card_size_val.setObjectName("cardSizeVal")
        self._card_size_val.setFixedWidth(42)
        slider_row = QHBoxLayout()
        slider_row.setSpacing(10)
        slider_row.addWidget(self._card_size_slider, 1)
        slider_row.addWidget(self._card_size_val)
        cv.addLayout(slider_row)
        def _update_card_size_label(v: int):
            self._card_size_val.setText(f"{v}px")
            accent = self.config.get("accent_color", DEFAULT_ACCENT)
            if v == 185:
                self._card_size_val.setStyleSheet(f"color: {accent}; font-size: 12px; font-weight: 700;")
            else:
                self._card_size_val.setStyleSheet(f"color: {_t('#7e7e88', '#71717a')}; font-size: 12px; font-weight: 400;")
        def _on_card_size_changed(v: int):
            _update_card_size_label(v)
        self._card_size_slider.valueChanged.connect(_on_card_size_changed)
        _update_card_size_label(self._card_size_slider.value())
        top_row.addWidget(card_frame, 3)
        ap.addLayout(top_row)

        # ── Row 2: Default Proton ─────────────────────────────────────────────
        proton_frame = QFrame()
        proton_frame.setObjectName("settingsSection")
        proton_frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        proton_frame.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        pv = QVBoxLayout(proton_frame)
        pv.setSpacing(8)
        pv.setContentsMargins(12, 10, 12, 10)
        # Build the selector first so the count pill can read its install list —
        # single source of truth shared with _refresh_proton_count_pill.
        self.proton_selector = ProtonComboBox(self.config.get("default_proton", ""), horizontal=True, config=self.config)
        self.proton_selector.size_changed.connect(self._refresh_proton_count_pill)
        proton_title_row = QHBoxLayout()
        proton_title_row.setContentsMargins(0, 0, 0, 0)
        proton_title_row.setSpacing(8)
        proton_title_row.addWidget(self._section_label("Default Proton Version"))
        self._count_pill = self._make_count_pill_settings(len(self.proton_selector._installs))
        proton_title_row.addWidget(self._count_pill, 0, Qt.AlignmentFlag.AlignVCenter)
        proton_title_row.addStretch()
        pv.addLayout(proton_title_row)

        pv.addWidget(self.proton_selector)

        # ── Row 3: Wine Prefixes Location ─────────────────────────────────────
        prefix_frame = QFrame()
        prefix_frame.setObjectName("settingsSection")
        prefix_frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        prefix_frame.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        pfv = QVBoxLayout(prefix_frame)
        pfv.setSpacing(6)
        pfv.setContentsMargins(12, 10, 12, 10)
        pfv_hdr = QHBoxLayout()
        pfv_hdr.addWidget(self._section_label("Wine Prefixes Location"))
        pfv_hdr.addStretch()
        pfv_hint = QLabel("Empty = default inside NAGO folder")
        pfv_hint.setObjectName("fieldHint")
        pfv_hdr.addWidget(pfv_hint)
        pfv.addLayout(pfv_hdr)
        path_row = QHBoxLayout()
        path_row.setSpacing(6)
        self.prefix_path_input = QLineEdit(self.config.get("prefixes_path", ""))
        self.prefix_path_input.setObjectName("dlgInput")
        self.prefix_path_input.setPlaceholderText(str(PREFIXES_PATH))
        path_row.addWidget(self.prefix_path_input)
        browse_btn = QPushButton("Browse")
        browse_btn.setObjectName("secondary")
        browse_btn.setFixedWidth(80)
        browse_btn.clicked.connect(self._browse_prefix_path)
        path_row.addWidget(browse_btn)
        clear_btn = QPushButton("Reset")
        clear_btn.setObjectName("secondary")
        clear_btn.setFixedWidth(80)
        clear_btn.clicked.connect(lambda: self.prefix_path_input.setText(""))
        path_row.addWidget(clear_btn)
        pfv.addLayout(path_row)

        ap.addWidget(proton_frame)
        ap.addWidget(prefix_frame)
        _compat_btn_ss = "padding: 4px 10px;"

        def _vsep():
            s = QFrame()
            s.setFixedSize(1, 14)
            s.setObjectName("settingsSep")
            return s

        def _muted_lbl(text):
            l = QLabel(text)
            l.setObjectName("settingsMuted")
            return l

        def _pill_lbl(text="", width=110):
            l = QLabel(text)
            l.setObjectName("settingsPill")
            l.setAlignment(Qt.AlignmentFlag.AlignCenter)
            l.setFixedWidth(width)
            l.setFixedHeight(20)
            l.setContentsMargins(10, 2, 10, 2)
            return l

        # ── Tools row: System Tray card + Tools card side by side ────────────
        tools_row = QHBoxLayout()
        tools_row.setSpacing(8)
        tools_row.setContentsMargins(0, 0, 0, 0)

        # System Tray card
        tray_frame = QFrame()
        tray_frame.setObjectName("settingsSection")
        tray_frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        tray_frame.setSizePolicy(QSizePolicy.Policy.Fixed, QSizePolicy.Policy.Minimum)
        tv = QVBoxLayout(tray_frame)
        tv.setSpacing(0)
        tv.setContentsMargins(0, 0, 0, 0)

        tray_inner = QWidget()
        tray_inner.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        tr = QVBoxLayout(tray_inner)
        tr.setContentsMargins(12, 10, 12, 10)
        tr.setSpacing(8)
        tr.addWidget(self._section_label("System Tray"))
        self._tray_on_game_run = NAGOCheckBox("Send to tray on launch")
        self._tray_on_game_run.setChecked(bool(self.config.get("tray_on_game_run", False)))
        tr.addWidget(self._tray_on_game_run)
        self._tray_on_close = NAGOCheckBox("Send to tray on close")
        self._tray_on_close.setChecked(bool(self.config.get("tray_on_close", False)))
        tr.addWidget(self._tray_on_close)
        tv.addWidget(tray_inner)

        tools_row.addWidget(tray_frame, 0)

        # ── Tools card (umu-launcher + Winetricks grouped) ────────────────────
        tools_frame = QFrame()
        tools_frame.setObjectName("settingsSection")
        tools_frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        tools_frame.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Minimum)
        tools_layout = QVBoxLayout(tools_frame)
        tools_layout.setContentsMargins(0, 0, 0, 0)
        tools_layout.setSpacing(0)

        # umu-launcher row
        umu_row_w = QWidget()
        umu_row_w.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        umu_row = QHBoxLayout(umu_row_w)
        umu_row.setContentsMargins(12, 10, 12, 10)
        umu_row.setSpacing(10)
        umu_row.setAlignment(Qt.AlignmentFlag.AlignVCenter)
        _lbl = self._section_label("umu-launcher")
        _lbl.setFixedWidth(110)
        umu_row.addWidget(_lbl)
        umu_row.addWidget(_vsep(), 0, Qt.AlignmentFlag.AlignVCenter)
        umu_row.addWidget(_muted_lbl("Version"))
        self._umu_ver_pill = _pill_lbl(width=70)
        self._umu_ver_pill.setMinimumWidth(70)
        self._umu_ver_pill.setMaximumWidth(180)
        self._umu_ver_pill.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        umu_row.addWidget(self._umu_ver_pill)
        # Protonfix DB controls removed from the visible row (NAGO 04:20). The
        # protonfix database is no longer used. Pill kept constructed-but-hidden so
        # _refresh_umu_db_status() and other references stay valid (now no-op'd).
        self._umu_db_pill = _pill_lbl(width=88)
        self._umu_db_pill.setMinimumWidth(70)
        self._umu_db_pill.setMaximumWidth(160)
        self._umu_db_pill.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        self._umu_db_pill.hide()
        self._umu_db_age_lbl = QLabel()
        self._umu_db_age_lbl.hide()
        umu_row.addStretch()
        self._umu_install_btn = QPushButton()
        self._umu_install_btn.setIcon(ph_icon("upload-simple", 20))
        self._umu_install_btn.setObjectName("compatBtn")
        self._umu_install_btn.setFixedWidth(36)
        self._umu_install_btn.setToolTip("Update umu-launcher")
        self._umu_install_btn.clicked.connect(self._install_umu)
        umu_row.addWidget(self._umu_install_btn)
        self._umu_db_btn = QPushButton()
        self._umu_db_btn.setIcon(ph_icon("database", 22))
        self._umu_db_btn.setObjectName("compatBtn")
        self._umu_db_btn.setFixedWidth(36)
        self._umu_db_btn.setToolTip("Update Protonfix database")
        self._umu_db_btn.clicked.connect(self._update_umu_db)
        self._umu_db_btn.hide()  # protonfix disabled (NAGO 04:20) — not added to row
        self._umu_status_lbl = QLabel()
        self._umu_status_lbl.hide()
        self._umu_db_lbl = QLabel()
        self._umu_db_lbl.hide()
        tools_layout.addWidget(umu_row_w)

        # divider between rows
        _tools_sep = QFrame()
        _tools_sep.setFrameShape(QFrame.Shape.HLine)
        _tools_sep.setObjectName("settingsSep")
        _tools_sep.setFixedHeight(1)
        tools_layout.addWidget(_tools_sep)

        # Winetricks row
        wt_row_w = QWidget()
        wt_row_w.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        wt_row = QHBoxLayout(wt_row_w)
        wt_row.setContentsMargins(12, 10, 12, 10)
        wt_row.setSpacing(10)
        wt_row.setAlignment(Qt.AlignmentFlag.AlignVCenter)
        _lbl = self._section_label("Winetricks")
        _lbl.setFixedWidth(110)
        wt_row.addWidget(_lbl)
        wt_row.addWidget(_vsep(), 0, Qt.AlignmentFlag.AlignVCenter)
        wt_row.addWidget(_muted_lbl("Version"))
        self._wt_ver_pill = _pill_lbl(width=110)
        self._wt_ver_pill.setMinimumWidth(70)
        self._wt_ver_pill.setMaximumWidth(180)
        self._wt_ver_pill.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        wt_row.addWidget(self._wt_ver_pill)
        wt_row.addStretch()
        self._wt_install_btn = QPushButton()
        self._wt_install_btn.setIcon(ph_icon("upload-simple", 20))
        self._wt_install_btn.setObjectName("compatBtn")
        self._wt_install_btn.setFixedWidth(36)
        self._wt_install_btn.setToolTip("Update Winetricks")
        self._wt_install_btn.clicked.connect(self._install_winetricks)
        wt_row.addWidget(self._wt_install_btn)
        self._wt_status_lbl = QLabel()
        self._wt_status_lbl.hide()
        tools_layout.addWidget(wt_row_w)

        # divider before Ludusavi row
        _tools_sep2 = QFrame()
        _tools_sep2.setFrameShape(QFrame.Shape.HLine)
        _tools_sep2.setObjectName("settingsSep")
        _tools_sep2.setFixedHeight(1)
        tools_layout.addWidget(_tools_sep2)

        # Ludusavi row
        lud_row_w = QWidget()
        lud_row_w.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, False)
        lud_row = QHBoxLayout(lud_row_w)
        lud_row.setContentsMargins(12, 10, 12, 10)
        lud_row.setSpacing(10)
        lud_row.setAlignment(Qt.AlignmentFlag.AlignVCenter)
        _lbl = self._section_label("Ludusavi")
        _lbl.setFixedWidth(110)
        lud_row.addWidget(_lbl)
        lud_row.addWidget(_vsep(), 0, Qt.AlignmentFlag.AlignVCenter)
        lud_row.addWidget(_muted_lbl("Version"))
        self._lud_ver_pill = _pill_lbl(width=110)
        self._lud_ver_pill.setMinimumWidth(70)
        self._lud_ver_pill.setMaximumWidth(180)
        self._lud_ver_pill.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
        lud_row.addWidget(self._lud_ver_pill)
        lud_row.addStretch()
        self._lud_install_btn = QPushButton()
        self._lud_install_btn.setIcon(ph_icon("upload-simple", 20))
        self._lud_install_btn.setObjectName("compatBtn")
        self._lud_install_btn.setFixedWidth(36)
        self._lud_install_btn.setToolTip("Install Ludusavi")
        self._lud_install_btn.clicked.connect(self._install_ludusavi)
        lud_row.addWidget(self._lud_install_btn)
        # Update Database button — refreshes the manifest (game-save database),
        # separate from the binary update above. database-icon to distinguish it.
        self._lud_db_btn = QPushButton()
        self._lud_db_btn.setIcon(ph_icon("database", 20))
        self._lud_db_btn.setObjectName("compatBtn")
        self._lud_db_btn.setFixedWidth(36)
        self._lud_db_btn.setToolTip("Update Database")
        self._lud_db_btn.clicked.connect(self._update_ludusavi_db)
        lud_row.addWidget(self._lud_db_btn)
        self._lud_status_lbl = QLabel()
        self._lud_status_lbl.hide()
        tools_layout.addWidget(lud_row_w)

        tools_row.addWidget(tools_frame, 1)
        ap.addLayout(tools_row)

        # Steam Web API hidden — stub keeps _save/_load from crashing
        self.steam_key_input = QLineEdit(self.config.get("steam_api_key", ""))
        self.steam_key_input.hide()

        # checkboxes moved to footer save row
        self._show_play_btn_chk = NAGOCheckBox("Play button on hover")
        self._show_play_btn_chk.setChecked(bool(self.config.get("show_play_button", True)))
        self._light_theme_chk = NAGOCheckBox("Light theme")
        self._light_theme_chk.setChecked(self.config.get("theme", "dark") == "light")

        _add_tab("note-pencil", "General", appearance_page)

        # ── TAB 2: Compatibility (hidden — cards moved to General tab) ────────
        compat_page = QWidget()
        _add_tab("flask", "Compatibility", compat_page)
        # Hide the button but keep the page in the stack so Advanced = index 2
        self._tab_btns[-1][0].setVisible(False)

        # ── TAB 3: Advanced ───────────────────────────────────────────────────
        advanced_page = QWidget()
        advp = QVBoxLayout(advanced_page)
        advp.setContentsMargins(24, 14, 24, 20)
        advp.setSpacing(12)

        # ── API Keys (moved here from General tab) ────────────────────────────
        api_frame = QFrame()
        api_frame.setObjectName("settingsSection")
        api_frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        akv = QVBoxLayout(api_frame)
        akv.setSpacing(8)
        akv.setContentsMargins(12, 10, 12, 10)
        akv.addWidget(self._section_label("API Keys"))
        sgdb_row = QHBoxLayout()
        sgdb_lbl = QLabel("SteamGridDB")
        sgdb_lbl.setObjectName("fieldHintSm")
        sgdb_lbl.setFixedWidth(110)
        self.key_input = QLineEdit(self.config.get("sgdb_key", ""))
        self.key_input.setObjectName("dlgInput")
        self.key_input.setPlaceholderText("steamgriddb.com/api")
        self.key_input.setEchoMode(QLineEdit.EchoMode.Password)
        sgdb_show = QPushButton("")
        sgdb_show.setIcon(ph_icon("eye", 22))
        sgdb_show.setObjectName("secondary")
        sgdb_show.setFixedWidth(52)
        sgdb_show.setToolTip("Show / hide key")
        sgdb_show.clicked.connect(lambda: self._toggle_key_visibility(self.key_input, sgdb_show))
        sgdb_row.addWidget(sgdb_lbl)
        sgdb_row.addWidget(self.key_input)
        sgdb_row.addWidget(sgdb_show)
        akv.addLayout(sgdb_row)
        advp.addWidget(api_frame)

        _adv_sep = QFrame()
        _adv_sep.setFrameShape(QFrame.Shape.HLine)
        _adv_sep.setObjectName("settingsSep")
        _adv_sep.setFixedHeight(1)
        advp.addWidget(_adv_sep)

        # Global env vars
        env_frame = QFrame()
        env_frame.setObjectName("settingsSection")
        env_frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        env_frame.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Expanding)
        ev = QVBoxLayout(env_frame)
        ev.setSpacing(10)
        ev.setContentsMargins(12, 10, 12, 10)
        _genv_title = self._section_label("Global Environment Variables")
        _genv_title.setToolTip("Applied to every Proton/native game launch. Per-game variables override these.")
        ev.addWidget(_genv_title)
        self._global_env_grid = QWidget()
        self._global_env_grid.setObjectName("envGrid")
        self._global_env_grid.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self._global_env_grid.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Expanding)
        grid_outer = QVBoxLayout(self._global_env_grid)
        grid_outer.setContentsMargins(0, 0, 0, 0)
        grid_outer.setSpacing(0)
        hdr_frame = QFrame()
        hdr_frame.setObjectName("envGridHeader")
        hdr_layout = QHBoxLayout(hdr_frame)
        hdr_layout.setContentsMargins(10, 5, 10, 5)
        hdr_layout.setSpacing(8)
        self._env_hdr_key = QLabel("Variable")
        self._env_hdr_key.setObjectName("envHdrKey")
        self._env_hdr_val = QLabel("Value")
        self._env_hdr_val.setObjectName("envHdrVal")
        hdr_key = self._env_hdr_key
        hdr_val = self._env_hdr_val
        hdr_layout.addWidget(hdr_key, 3)
        hdr_layout.addWidget(hdr_val, 1)
        hdr_layout.addSpacing(28)
        grid_outer.addWidget(hdr_frame)
        self._env_rows_widget = QWidget()
        self._env_rows_layout = QVBoxLayout(self._env_rows_widget)
        self._env_rows_layout.setContentsMargins(0, 6, 0, 6)
        self._env_rows_layout.setSpacing(0)
        self._env_rows_layout.setAlignment(Qt.AlignmentFlag.AlignTop)
        env_scroll = QScrollArea()
        env_scroll.setWidgetResizable(True)
        env_scroll.setWidget(self._env_rows_widget)
        env_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        env_scroll.setMinimumHeight(120)
        env_scroll.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Expanding)
        env_scroll.setFrameShape(QFrame.Shape.NoFrame)
        grid_outer.addWidget(env_scroll, 1)
        ev.addWidget(self._global_env_grid, 1)
        saved_global = self.config.get("global_env", "")
        saved_pairs = []
        for line in saved_global.splitlines():
            line = line.strip()
            if "=" in line:
                k, _, v = line.partition("=")
                saved_pairs.append((k.strip(), v.strip()))
        if not saved_pairs:
            saved_pairs = [("", "")]
        for k, v in saved_pairs:
            self._add_env_row(k, v)
        add_row_btn = QPushButton("  Add Variable")
        add_row_btn.setIcon(ph_icon("plus", 22))
        add_row_btn.setObjectName("secondary")
        add_row_btn.clicked.connect(lambda: self._add_env_row("", ""))
        ev.addWidget(add_row_btn, 0, Qt.AlignmentFlag.AlignLeft)
        advp.addWidget(env_frame, 1)

        _add_tab("list", "Advanced", advanced_page)

        tab_bar_layout.addStretch()

        # ── Save footer ───────────────────────────────────────────────────────
        save_div = QFrame()
        save_div.setObjectName("settingsTabDivider")
        save_div.setFixedHeight(1)
        island_layout.addWidget(save_div)

        save_row = QHBoxLayout()
        save_row.setContentsMargins(24, 12, 24, 12)
        save_row.setSpacing(24)
        save_row.addWidget(self._show_play_btn_chk)
        save_row.addWidget(self._light_theme_chk)
        save_row.addStretch()
        save_btn = QPushButton("  Save Settings")
        save_btn.setIcon(ph_icon("floppy-disk", 22, "#ffffff"))
        save_btn.setObjectName("primary")
        save_btn.setFixedWidth(180)
        save_btn.clicked.connect(self._save)
        save_row.addWidget(save_btn)
        island_layout.addLayout(save_row)

        # Wire panel's tab button list for paintEvent erase calculation
        self._panel._tab_btns = self._tab_btns

        # Activate first tab
        self._switch_tab(0)

        self._refresh_umu_status()
        self._refresh_umu_db_status()
        self._refresh_winetricks_status()
        self._refresh_ludusavi_status()

    def _switch_tab(self, idx: int):
        """Activate tab at idx, update button icon colors."""
        accent = self.config.get("accent_color", DEFAULT_ACCENT)
        for i, (btn, icon_name) in enumerate(self._tab_btns):
            active = (i == idx)
            btn.setChecked(active)
            btn.setIcon(ph_icon(icon_name, 15, accent if active else "#7e7e88"))
        self._stack.setCurrentIndex(idx)
        self._panel.set_active_tab(idx)

    def _section_label(self, text: str) -> QLabel:
        lbl = QLabel(text)
        lbl.setObjectName("cardTitle")
        return lbl

    def _set_pill(self, pill: QLabel, text: str, state: str):
        """Set a status pill's text + pillState and force a style repolish.
        Centralizes the setText/setProperty/unpolish/polish/setFixedHeight
        incantation that was duplicated across every status refresher."""
        pill.setText(text)
        pill.setProperty("pillState", state)
        pill.style().unpolish(pill)
        pill.style().polish(pill)
        pill.setFixedHeight(20)

    def _refresh_swatch_borders(self):
        """Re-apply the accent swatch selection rings. The ring color depends on
        the active theme, so this must run after a theme switch — otherwise the
        selected swatch keeps a stale (e.g. white-on-light) border."""
        sel_brd = "#18181b" if self.config.get("theme", "dark") == "light" else "#ffffff"
        for hex_color, btn in self._accent_btns:
            selected = (hex_color == self._accent_color)
            btn.setStyleSheet(
                f"background:{hex_color}; border-radius:5px; border:2px solid "
                f"{sel_brd if selected else 'transparent'};"
            )

    def _toggle_key_visibility(self, field: QLineEdit, btn: QPushButton):
        if field.echoMode() == QLineEdit.EchoMode.Password:
            field.setEchoMode(QLineEdit.EchoMode.Normal)
            btn.setIcon(ph_icon("eye-slash", 22))
            btn.setText("")
        else:
            field.setEchoMode(QLineEdit.EchoMode.Password)
            btn.setIcon(ph_icon("eye", 22))
            btn.setText("")

    def _add_env_row(self, key: str = "", value: str = ""):
        """Add one KEY / VALUE row to the global env grid."""
        row_widget = QWidget()
        row_widget.setObjectName("envGridRow")
        rl = QHBoxLayout(row_widget)
        rl.setContentsMargins(6, 3, 6, 3)
        rl.setSpacing(8)
        key_input = QLineEdit(key)
        key_input.setObjectName("dlgInputMono")
        key_input.setPlaceholderText("KEY")
        val_input = QLineEdit(value)
        val_input.setObjectName("dlgInputMono")
        val_input.setPlaceholderText("value")
        del_btn = QPushButton()
        del_btn.setIcon(ph_icon("trash-simple", 22))
        del_btn.setObjectName("envDelBtn")
        del_btn.setFixedWidth(28)
        del_btn.setFixedHeight(28)
        del_btn.setToolTip("Remove variable")
        del_btn.clicked.connect(lambda: self._remove_env_row(row_widget))
        rl.addWidget(key_input, 13)
        rl.addWidget(val_input, 7)
        rl.addWidget(del_btn)
        self._env_rows_layout.addWidget(row_widget)

    def _remove_env_row(self, row_widget: QWidget):
        self._env_rows_layout.removeWidget(row_widget)
        row_widget.deleteLater()

    def _collect_global_env(self) -> str:
        """Collect all KEY=VALUE rows from the grid into a newline-separated string."""
        lines = []
        for i in range(self._env_rows_layout.count()):
            w = self._env_rows_layout.itemAt(i).widget()
            if w is None:
                continue
            inputs = w.findChildren(QLineEdit)
            if len(inputs) < 2:
                continue
            k = inputs[0].text().strip()
            v = inputs[1].text().strip()
            if k:
                lines.append(f"{k}={v}")
        return "\n".join(lines)

    def revert(self):
        """Reset all fields to the last saved config values. Called when navigating
        away from Settings without saving."""
        cfg = self.config

        # API keys
        self.key_input.setText(cfg.get("sgdb_key", ""))
        self.steam_key_input.setText(cfg.get("steam_api_key", ""))

        # Proton selector
        self.proton_selector._set_current(cfg.get("default_proton", ""))

        # umu default toggle removed — umu is unconditional for Proton

        # Prefix path
        self.prefix_path_input.setText(cfg.get("prefixes_path", ""))

        # Card size slider
        self._card_size_slider.setValue(int(cfg.get("card_width", CARD_W)))

        # Global env grid — clear all rows and rebuild from saved config
        while self._env_rows_layout.count():
            item = self._env_rows_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
        saved_env = cfg.get("global_env", "")
        pairs = []
        for line in saved_env.splitlines():
            line = line.strip()
            if "=" in line:
                k, _, v = line.partition("=")
                pairs.append((k.strip(), v.strip()))
        if not pairs:
            pairs = [("", "")]
        for k, v in pairs:
            self._add_env_row(k, v)

        # Accent color
        saved_accent = cfg.get("accent_color", DEFAULT_ACCENT)
        live_accent  = self._accent_color          # capture before overwrite
        self._accent_color = saved_accent
        self._accent_color_original = saved_accent
        self._refresh_swatch_borders()
        # Only reparse the stylesheet if the live preview actually differed from saved
        if live_accent != saved_accent:
            _apply_stylesheet(QApplication.instance(), {**cfg, "accent_color": saved_accent})

        # Tray / appearance checkboxes
        self._tray_on_game_run.setChecked(bool(cfg.get("tray_on_game_run", False)))
        self._tray_on_close.setChecked(bool(cfg.get("tray_on_close", False)))
        self._show_play_btn_chk.setChecked(bool(cfg.get("show_play_button", True)))
        self._light_theme_chk.setChecked(cfg.get("theme", "dark") == "light")

    def _pick_accent(self, color: str):
        """Apply accent immediately — persisted only when Save is clicked."""
        self._accent_color = color
        self._refresh_swatch_borders()
        # Debounce: cancel any pending stylesheet application and restart the
        # timer. Only the final click in a rapid sequence triggers the full
        # app.setStyleSheet() call, which is expensive on large libraries.
        if not hasattr(self, "_accent_timer"):
            self._accent_timer = QTimer(self)
            self._accent_timer.setSingleShot(True)
            self._accent_timer.timeout.connect(
                lambda: _apply_stylesheet(
                    QApplication.instance(),
                    {**self.config, "accent_color": self._accent_color}
                )
            )
        self._accent_timer.start(80)

    def _make_count_pill_settings(self, count: int) -> QLabel:
        lbl = QLabel(f"{count} found" if count else "none found")
        lbl.setObjectName("settingsPill")
        lbl.setProperty("pillState", "ok" if count else "error")
        lbl.style().unpolish(lbl)
        lbl.style().polish(lbl)
        lbl.setFixedHeight(20)
        return lbl

    def _refresh_proton_count_pill(self):
        count = len(self.proton_selector._installs)
        self._set_pill(self._count_pill, f"{count} found" if count else "none found",
                       "ok" if count else "error")

    def _refresh_count_pill_theme(self):
        """Re-apply count pill colors after a theme change."""
        count = len(self.proton_selector._installs)
        self._set_pill(self._count_pill, f"{count} found" if count else "none found",
                       "ok" if count else "error")

    def _validate_prefix_path(self, path: str):
        """Return (ok, error_message) for the Wine prefixes location.
        Empty is always valid (= NAGO's default folder). A non-empty path must
        either be an existing writable directory, or be creatable — i.e. its
        nearest existing ancestor is a writable directory."""
        if not path:
            return True, ""
        p = Path(path).expanduser()
        if p.exists():
            if not p.is_dir():
                return False, "That path points to a file, not a folder.\n\nPick a directory for the Wine prefixes."
            if not os.access(p, os.W_OK):
                return False, "That folder isn't writable.\n\nNAGO needs write access to create per-game prefixes there."
            return True, ""
        # Doesn't exist yet — walk up to the nearest existing ancestor.
        ancestor = p.parent
        while not ancestor.exists() and ancestor != ancestor.parent:
            ancestor = ancestor.parent
        if not ancestor.exists() or not ancestor.is_dir():
            return False, "That path is invalid — the parent folder doesn't exist."
        if not os.access(ancestor, os.W_OK):
            return False, "NAGO can't create the prefixes folder there — the location isn't writable."
        return True, ""

    def _save(self):
        # Validate the prefixes path up front. If it's bad, abort the whole save
        # before touching anything so a single bad field can't half-persist.
        prefix_path = self.prefix_path_input.text().strip()
        ok, err = self._validate_prefix_path(prefix_path)
        if not ok:
            NAGOMessageBox.warning(self, "Invalid Prefixes Location", err)
            self._switch_tab(0)
            self.prefix_path_input.setFocus()
            self.prefix_path_input.selectAll()
            return
        # Cancel any pending accent debounce — _on_config_saved will apply
        # the stylesheet once, no need for a second application right after.
        if hasattr(self, "_accent_timer"):
            self._accent_timer.stop()
        # Pull in any keys other parts of the app may have written since we loaded
        # (e.g. umu_version written by the install worker), so we don't clobber them.
        on_disk = load_config()
        on_disk.update(self.config)
        self.config = on_disk

        self.config["sgdb_key"]            = self.key_input.text().strip().strip('"').strip("'")
        self.config["steam_api_key"]       = self.steam_key_input.text().strip().strip('"').strip("'")
        self.config["default_proton"]      = self.proton_selector.selected_path()
        self.config["prefixes_path"]       = prefix_path
        self.config["global_env"]          = self._collect_global_env()
        self.config["accent_color"]        = self._accent_color
        self._accent_color_original        = self._accent_color   # new baseline
        self.config["card_width"]           = self._card_size_slider.value()
        self.config["show_play_button"]     = self._show_play_btn_chk.isChecked()
        self.config["theme"]                = "light" if self._light_theme_chk.isChecked() else "dark"
        self.config["tray_on_game_run"]     = self._tray_on_game_run.isChecked()
        self.config["tray_on_close"]        = self._tray_on_close.isChecked()
        save_config(self.config)
        self.config_saved.emit(self.config)

    def _browse_prefix_path(self):
        start = self.prefix_path_input.text().strip() or str(Path.home())
        path = QFileDialog.getExistingDirectory(self, "Select Prefixes Folder", start)
        if path:
            self.prefix_path_input.setText(path)

    def _refresh_umu_status(self):
        kind = umu_install_kind()
        version = get_umu_version()
        active_path = find_umu_run()

        if kind == "system":
            display_version = version or "…"
            self._set_pill(self._umu_ver_pill, display_version, "ok")
            self._umu_ver_pill.show()
            self._umu_install_btn.setToolTip("Reinstall umu-launcher")
            self._umu_install_btn.setIcon(ph_icon("upload-simple", 20))
            if not version:
                self._start_version_subprocess_worker(active_path)
        elif kind == "managed":
            self._set_pill(self._umu_ver_pill, version or "…", "ok")
            self._umu_ver_pill.show()
            self._umu_install_btn.setToolTip("Update umu-launcher")
            self._umu_install_btn.setIcon(ph_icon("upload-simple", 20))
        else:
            self._set_pill(self._umu_ver_pill, "Not installed", "error")
            self._umu_ver_pill.show()
            self._umu_install_btn.setToolTip("Install umu-launcher")
            self._umu_install_btn.setIcon(ph_icon("upload-simple", 20))
        self._umu_install_btn.setEnabled(True)

        # Async upstream-latest check (only when a managed install exists)
        if kind == "managed":
            # Cancel any in-flight previous check before starting a new one
            old = getattr(self, "_umu_check_worker", None)
            if old is not None:
                try:
                    old.got_version.disconnect()
                except Exception:
                    pass
                if old.isRunning():
                    old.quit()
                    old.wait(1000)

            self._umu_check_current = version  # store outside the lambda
            self._umu_check_worker = UmuLatestVersionWorker()
            self._umu_check_worker.got_version.connect(self._on_umu_version_check)
            self._umu_check_worker.finished.connect(self._umu_check_worker.deleteLater)
            self._umu_check_worker.finished.connect(
                lambda: setattr(self, "_umu_check_worker", None))
            self._umu_check_worker.start()

    def _start_version_subprocess_worker(self, active_path: str):
        """Run umu-run --version in background and update the status label."""
        old = getattr(self, "_umu_ver_worker", None)
        if old is not None and old.isRunning():
            return  # already in flight
        self._umu_ver_worker = UmuVersionSubprocessWorker()
        def _on_ver(ver: str):
            try:
                global _umu_version_cache
                _umu_version_cache = ver or "installed"
                self._set_pill(self._umu_ver_pill, _umu_version_cache, "ok")
            except RuntimeError:
                pass
        self._umu_ver_worker.got_version.connect(_on_ver)
        self._umu_ver_worker.finished.connect(self._umu_ver_worker.deleteLater)
        self._umu_ver_worker.finished.connect(
            lambda: setattr(self, "_umu_ver_worker", None))
        self._umu_ver_worker.start()

    def _on_umu_version_check(self, latest: str):
        # Bail out gracefully if the widget was destroyed while the worker was running
        try:
            current = getattr(self, "_umu_check_current", "")
            self._on_latest_umu_version(current, latest)
        except RuntimeError:
            # The C++ widget has been deleted — nothing to update
            return

    def _on_latest_umu_version(self, current: str, latest: str):
        if not latest:
            return

        cur_clean = current.lstrip("v").strip()
        lat_clean = latest.lstrip("v").strip()
        try:
            if cur_clean == lat_clean:
                self._set_pill(self._umu_ver_pill, current, "ok")
            else:
                self._set_pill(self._umu_ver_pill, f"{current} → {latest}", "warn")
        except RuntimeError:
            pass

    def _install_umu(self):
        action = "Update" if UMU_BIN.exists() else "Install"

        self._umu_install_btn.setEnabled(False)
        self._set_pill(self._umu_ver_pill, "…", "pending")

        self._umu_worker = UmuInstallWorker()
        self._umu_worker.progress.connect(
            lambda msg: self._umu_ver_pill.setText(msg)
        )
        self._umu_worker.finished_ok.connect(self._on_umu_installed)
        self._umu_worker.failed.connect(self._on_umu_install_failed)
        self._umu_worker.finished.connect(self._umu_worker.deleteLater)
        self._umu_worker.start()

    def _on_umu_installed(self, version: str):
        # The worker wrote umu_version to disk — invalidate the module-level
        # cache so _refresh_umu_status() picks up the freshly installed version.
        _invalidate_umu_version_cache()
        self.config = load_config()
        self._refresh_umu_status()
        self._umu_install_btn.clearFocus()

    def _on_umu_install_failed(self, error: str):
        _invalidate_umu_version_cache()
        self._refresh_umu_status()
        self._umu_install_btn.clearFocus()
        NAGOMessageBox.critical(self, "Install Failed", error)

    def _refresh_umu_db_status(self):
        # Protonfix disabled (NAGO 04:20): DB pill is hidden and the protonfix
        # database is no longer loaded. Early-return so opening Settings never
        # touches/parses the CSV. Body below preserved (dormant) for re-enable.
        return
        if not UMU_DB_CSV.exists():
            self._set_pill(self._umu_db_pill, "No DB", "error")
            self._umu_db_btn.setToolTip("Download Protonfix database")
        else:
            try:
                import datetime as _dt
                mtime = UMU_DB_CSV.stat().st_mtime
                age_days = (time.time() - mtime) / 86400
                stamp = _fmt_date(_dt.datetime.fromtimestamp(mtime))
                entries = len(UmuDatabase.load())
                if age_days < 1:
                    age_str = "today"
                elif age_days < 2:
                    age_str = "yesterday"
                else:
                    age_str = f"{int(age_days)} days ago"
                self._set_pill(self._umu_db_pill, f"{entries} entries", "ok")
                self._umu_db_btn.setToolTip(f"Update Protonfix database\nLast updated {age_str} ({stamp})")
            except Exception:
                self._set_pill(self._umu_db_pill, "loaded", "ok")
                self._umu_db_btn.setToolTip("Update Protonfix database")
        self._umu_db_btn.setIcon(ph_icon("database", 22))
        self._umu_db_btn.setEnabled(True)

    def _update_umu_db(self):
        self._umu_db_btn.setEnabled(False)
        self._umu_db_pill.setText("…")

        self._umu_db_worker = UmuDatabaseDownloadWorker()
        self._umu_db_worker.finished_ok.connect(self._on_umu_db_done)
        self._umu_db_worker.failed.connect(self._on_umu_db_failed)
        self._umu_db_worker.finished.connect(self._umu_db_worker.deleteLater)
        self._umu_db_worker.start()

    def _on_umu_db_done(self):
        # Invalidate the cached parsed entries so any open widgets re-read on next search
        UmuDatabase._entries = []
        self._refresh_umu_db_status()
        self._umu_db_btn.clearFocus()

    def _on_umu_db_failed(self, error: str):
        self._refresh_umu_db_status()
        self._umu_db_btn.clearFocus()
        NAGOMessageBox.warning(self, "Update Failed",
                            f"Couldn't download the umu protonfix database.\n\n{error}")

    # ── Winetricks ────────────────────────────────────────────────────────────

    def _refresh_winetricks_status(self):
        kind    = winetricks_install_kind()
        version = get_winetricks_version()

        if kind == "managed":
            self._set_pill(self._wt_ver_pill, version or "…", "ok")
            self._wt_install_btn.setToolTip("Update Winetricks")
        elif kind == "system":
            self._set_pill(self._wt_ver_pill, version or "…", "ok")
            self._wt_install_btn.setToolTip("Fetch Winetricks (system install detected)")
        else:
            self._set_pill(self._wt_ver_pill, "Not installed", "error")
            self._wt_install_btn.setToolTip("Install Winetricks")
        self._wt_install_btn.setIcon(ph_icon("upload-simple", 20))
        self._wt_install_btn.setEnabled(True)

    def _install_winetricks(self):
        self._wt_install_btn.setEnabled(False)
        self._wt_status_lbl.setText("<span style='color:#7e7e88;'>Downloading winetricks…</span>")
        self._set_pill(self._wt_ver_pill, "…", "pending")

        self._wt_worker = WinetricksInstallWorker()
        self._wt_worker.progress.connect(self._wt_status_lbl.setText)
        self._wt_worker.finished_ok.connect(self._on_winetricks_installed)
        self._wt_worker.failed.connect(self._on_winetricks_install_failed)
        self._wt_worker.finished.connect(self._wt_worker.deleteLater)
        self._wt_worker.start()

    def _on_winetricks_installed(self, version: str):
        _invalidate_winetricks_version_cache()
        self._refresh_winetricks_status()
        self._wt_install_btn.clearFocus()

    def _on_winetricks_install_failed(self, error: str):
        self._refresh_winetricks_status()
        self._wt_install_btn.clearFocus()
        NAGOMessageBox.warning(self, "Install Failed",
                            f"Couldn't download winetricks.\n\n{error}")

    # ── Ludusavi ──────────────────────────────────────────────────────────────
    def _refresh_ludusavi_status(self):
        kind    = ludusavi_install_kind()
        version = get_ludusavi_version()

        if kind == "managed":
            self._set_pill(self._lud_ver_pill, version or "…", "ok")
            self._lud_install_btn.setToolTip("Update Ludusavi")
        elif kind == "system":
            self._set_pill(self._lud_ver_pill, version or "…", "ok")
            self._lud_install_btn.setToolTip("Fetch Ludusavi (system install detected)")
        else:
            self._set_pill(self._lud_ver_pill, "Not installed", "error")
            self._lud_install_btn.setToolTip("Install Ludusavi")
        self._lud_install_btn.setIcon(ph_icon("upload-simple", 20))
        self._lud_install_btn.setEnabled(True)
        # DB update only makes sense once a binary exists to run it.
        _lud_present = (kind in ("managed", "system"))
        if hasattr(self, "_lud_db_btn"):
            self._lud_db_btn.setEnabled(_lud_present)
            self._lud_db_btn.setToolTip(
                "Update Database" if _lud_present
                else "Install Ludusavi first"
            )

    def _install_ludusavi(self):
        # Version check is fired here (button press) only — never on Settings open.
        self._lud_install_btn.setEnabled(False)
        self._set_pill(self._lud_ver_pill, "…", "pending")

        self._lud_worker = LudusaviInstallWorker()
        self._lud_worker.progress.connect(
            lambda msg: self._lud_ver_pill.setText(msg)
        )
        self._lud_worker.finished_ok.connect(self._on_ludusavi_installed)
        self._lud_worker.failed.connect(self._on_ludusavi_install_failed)
        self._lud_worker.finished.connect(self._lud_worker.deleteLater)
        self._lud_worker.start()

    def _on_ludusavi_installed(self, version: str):
        _invalidate_ludusavi_version_cache()
        self.config = load_config()
        self._refresh_ludusavi_status()
        self._lud_install_btn.clearFocus()

    def _on_ludusavi_install_failed(self, error: str):
        _invalidate_ludusavi_version_cache()
        self._refresh_ludusavi_status()
        self._lud_install_btn.clearFocus()
        NAGOMessageBox.warning(self, "Install Failed",
                            f"Couldn't download Ludusavi.\n\n{error}")

    def _update_ludusavi_db(self):
        # Refresh the manifest (game-save database). Separate from the binary
        # update — different source, different cadence. No-op safe if ludusavi
        # isn't installed (worker reports it).
        if not LUDUSAVI_BIN.exists() and not shutil.which("ludusavi"):
            NAGOMessageBox.warning(self, "Ludusavi Not Installed",
                "Install Ludusavi first using the update button to its left.")
            return
        self._lud_db_btn.setEnabled(False)
        self._set_pill(self._lud_ver_pill, "…", "pending")
        self._lud_db_worker = LudusaviManifestUpdateWorker()
        self._lud_db_worker.progress.connect(
            lambda msg: self._lud_ver_pill.setText(msg)
        )
        self._lud_db_worker.finished_ok.connect(self._on_ludusavi_db_done)
        self._lud_db_worker.failed.connect(self._on_ludusavi_db_failed)
        self._lud_db_worker.finished.connect(self._lud_db_worker.deleteLater)
        self._lud_db_worker.start()

    def _on_ludusavi_db_done(self, status: str):
        self._lud_db_btn.setEnabled(True)
        self._refresh_ludusavi_status()
        self._lud_db_btn.clearFocus()

    def _on_ludusavi_db_failed(self, error: str):
        self._lud_db_btn.setEnabled(True)
        self._refresh_ludusavi_status()
        self._lud_db_btn.clearFocus()
        NAGOMessageBox.warning(self, "Database Update Failed",
                            f"Couldn't update the Ludusavi game database.\n\n{error}")


# ── Library Page ───────────────────────────────────────────────────────────────
class LibraryPage(QWidget):
    status_message = pyqtSignal(str)
    game_launched  = pyqtSignal(str)   # emitted after a game process starts, carries log path

    def __init__(self, config: dict, parent=None):
        super().__init__(parent)
        self.config = config
        self._all_games: list[dict] = []   # master list — full DB, never filtered
        self._game_cats: dict[int, set] = {}  # game_id -> set of category_ids
        self._games: list[dict] = []       # current visible ordered subset
        self._cards = {}
        self._current_filter_text: str = ""
        self._current_category_id = None
        self._show_hidden: bool = False        # toggled by the eye button in toolbar
        self._empty_lbl_e = None
        self._empty_lbl_h = None
        # Track which games are currently running.
        # Maps game_id -> (subprocess.Popen, post_exit_cmd_string).
        # A QTimer polls every 2 seconds to clean up entries whose process exited
        # and to fire the post-exit hook command.
        self._running_games: dict[int, tuple] = {}
        # Maps game_id -> _RunInPrefixWorker for right-click "Run File in Prefix"
        # runs kicked off from the card menu. Separate from _running_games (the
        # actual game launches) — a tool/installer can run in a game's prefix
        # independently of whether the game itself is running.
        self._prefix_run_workers: dict[int, "_RunInPrefixWorker"] = {}
        self._auto_bk_workers: dict[int, list] = {}  # gid → [worker, ...] kept alive until done
        # Track Steam-type games separately. Popen exits immediately after handing
        # off the steam:// URL, so we watch registry.vdf instead.
        # Maps appid_str -> (game_id, post_exit_cmd_string, launched_at_monotonic).
        self._steam_watched: dict[str, tuple] = {}
        # Maps game_id -> monotonic start time for playtime tracking.
        # Populated on launch, consumed on process exit to accumulate minutes.
        self._session_starts: dict[int, float] = {}
        # Maps game_id -> upscaler subprocess.Popen (killed when game exits).
        self._upscale_procs: dict[int, object] = {}
        self._upscaler_worker = None   # _UpscalerLaunchWorker, if one is running
        self._single_cover_workers: set = set()  # keeps refs alive until threads finish
        self._steam_exit_workers: set = set()    # keeps per-exit Steam playtime workers alive until done
        self._poll_timer = QTimer(self)
        self._poll_timer.setInterval(2000)
        self._poll_timer.timeout.connect(self._poll_running_games)
        self._poll_timer.start()
        self._build()
        # Defer the initial reload so the window can paint its first frame before
        # we hit SQLite, build cards, and start ThumbnailWorker.  Result: window
        # appears in ~100 ms; cards populate ~200–400 ms later.
        QTimer.singleShot(0, self.reload)
        # Sync Steam playtime once at startup in a background thread.
        # No key = no-op. On success, _apply_steam_playtime() writes DB and
        # updates any already-rendered cards in-place via update_playtime().
        QTimer.singleShot(500, self._startup_steam_sync)

    def _build(self):
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        self.scroll = QScrollArea()
        self.scroll.setObjectName("libraryScroll")
        self.scroll.setWidgetResizable(True)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.container = _LibraryGrid()
        self.container.setObjectName("libraryGrid")
        self.container.set_accent(self.config.get("accent_color", DEFAULT_ACCENT))
        self.container.reorder_requested.connect(self._reorder_games)
        self.scroll.setObjectName("libraryScroll")
        self.scroll.viewport().setObjectName("libraryViewport")
        self.scroll.setWidget(self.container)
        layout.addWidget(self.scroll)

    def update_config(self, cfg: dict):
        self.config = cfg

    def _reflow(self):
        """Re-position all visible cards using the container's flow layout."""
        ordered = [self._cards[g["id"]] for g in self._games if g["id"] in self._cards]
        self.container.reflow(ordered, self.scroll.viewport().width())

    def resizeEvent(self, event):
        super().resizeEvent(event)
        QTimer.singleShot(0, self._reflow)

    def reload(self, filter_text: str = None, category_id: int = None):
        """Full rebuild — destroys and recreates all cards from DB.
        Call only when the game list itself changes: startup, add, delete,
        card-width change. For view switches and search use _apply_filter().
        When called with no args, preserves the current filter/category state."""
        # Preserve existing view state if no explicit args given
        if filter_text is None:
            filter_text = self._current_filter_text
        if category_id is None:
            category_id = self._current_category_id

        self.container.setUpdatesEnabled(False)
        try:
            self._full_rebuild()
            self._apply_filter(filter_text, category_id, _reflow=True)
        finally:
            self.container.setUpdatesEnabled(True)

    def _full_rebuild(self):
        """Load all games from DB, create all cards, load all covers.
        Does NOT show/hide — call _apply_filter() after."""
        # Tear down existing cards — hide and reparent to None so Qt destroys them
        for card in list(self._cards.values()):
            card.hide()
            card.setParent(None)
            card.deleteLater()
        self._cards.clear()
        # Null out empty-state label refs — their C++ objects are now deleted
        if self._empty_lbl_e is not None:
            self._empty_lbl_e.setParent(None)
            self._empty_lbl_e.deleteLater()
            self._empty_lbl_e = None
        if self._empty_lbl_h is not None:
            self._empty_lbl_h.setParent(None)
            self._empty_lbl_h.deleteLater()
            self._empty_lbl_h = None

        # Load all games (no filter — master list)
        con = db_con()
        try:
            cur = con.execute("SELECT * FROM games ORDER BY sort_pos, name COLLATE NOCASE")
            cols_desc = [d[0] for d in cur.description]
            self._all_games = [dict(zip(cols_desc, row)) for row in cur.fetchall()]

            # Bulk-load category memberships in one query
            cat_rows = con.execute(
                "SELECT game_id, category_id FROM game_categories"
            ).fetchall()
        finally:
            con.close()
        self._game_cats = {}
        for gid, cid in cat_rows:
            self._game_cats.setdefault(gid, set()).add(cid)

        # Create a card for every game — all hidden until _apply_filter positions them
        for game in self._all_games:
            card = GameCard(game, accent_color=self.config.get("accent_color", DEFAULT_ACCENT))
            card.launch_requested.connect(self._launch_game)
            card.edit_requested.connect(self._edit_game)
            card.delete_requested.connect(self._delete_game)
            card.cover_requested.connect(self.pick_cover)
            card.categories_requested.connect(self._assign_categories)
            card.show_log_requested.connect(self._show_game_log)
            card.delete_prefix_requested.connect(self._delete_prefix)
            card.force_terminate_requested.connect(self._force_terminate_game)
            card.run_in_prefix_requested.connect(self._run_file_in_prefix)
            card.stop_prefix_run_requested.connect(self._stop_prefix_run)
            card.hide_requested.connect(self._toggle_hide_game)
            card.setVisible(False)
            self._cards[game["id"]] = card
            if game["id"] in self._running_games:
                card.set_running(True)

        # Kick off cover loading for all games
        tasks = [
            (g["id"], g["cover_path"])
            for g in self._all_games
            if g.get("cover_path") and Path(g["cover_path"]).exists()
        ]
        if tasks:
            self._tw = ThumbnailWorker(tasks)
            self._tw.loaded.connect(self._on_thumb_loaded)
            self._tw.finished.connect(self._tw.deleteLater)
            self._tw.start()

    def _apply_filter(self, filter_text: str = "", category_id: int = None,
                      _reflow: bool = True):
        """Show/hide existing cards to match the current view + search.
        No DB access, no widget creation. Safe to call on every keystroke."""
        self._current_category_id = category_id
        self._current_filter_text = filter_text

        ft = filter_text.lower()

        if category_id is not None:
            con = db_con()
            rows = con.execute(
                "SELECT game_id, sort_pos FROM game_categories WHERE category_id=?",
                (category_id,)
            ).fetchall()
            con.close()
            cat_sort = {gid: pos for gid, pos in rows}
            visible = [
                g for g in self._all_games
                if g["id"] in cat_sort
                and (not ft or ft in g["name"].lower())
                and (self._show_hidden == bool(g.get("hidden", 0)))
            ]
            visible.sort(key=lambda g: (cat_sort[g["id"]], g["name"].lower()))
        else:
            visible = [
                g for g in self._all_games
                if (not ft or ft in g["name"].lower())
                and (self._show_hidden == bool(g.get("hidden", 0)))
            ]

        self._games = visible

        self.container.setUpdatesEnabled(False)
        try:
            # Hide all cards first
            for card in self._cards.values():
                card.setVisible(False)

            if not visible:
                # Empty state labels — positioned absolutely in the container
                if self._show_hidden:
                    empty_msg = "No hidden games"
                    hint_msg  = "Hide games via right-click → Hide"
                elif category_id is None:
                    empty_msg = "No games yet"
                    hint_msg  = "Add a game with the + button above"
                else:
                    empty_msg = "No games in this category"
                    hint_msg  = "Right-click any game card → Assign Categories"
                if self._empty_lbl_e is None:
                    self._empty_lbl_e = QLabel(self.container)
                    self._empty_lbl_e.setObjectName("emptyTitle")
                    self._empty_lbl_e.setAlignment(Qt.AlignmentFlag.AlignCenter)
                    self._empty_lbl_h = QLabel(self.container)
                    self._empty_lbl_h.setObjectName("emptyHint")
                    self._empty_lbl_h.setAlignment(Qt.AlignmentFlag.AlignCenter)
                self._empty_lbl_e.setText(empty_msg)
                self._empty_lbl_h.setText(hint_msg)
                self._empty_lbl_e.setVisible(True)
                self._empty_lbl_h.setVisible(True)
                # Centre in the scroll viewport
                vw = self.scroll.viewport().width()
                self._empty_lbl_e.setFixedWidth(vw)
                self._empty_lbl_h.setFixedWidth(vw)
                self._empty_lbl_e.move(0, 80)
                self._empty_lbl_h.move(0, 120)
                self.container.setFixedHeight(200)
                self.container._ordered = []
            else:
                if self._empty_lbl_e is not None:
                    self._empty_lbl_e.setVisible(False)
                    self._empty_lbl_h.setVisible(False)
                # Reparent new cards to container (first time they appear)
                for game in visible:
                    card = self._cards.get(game["id"])
                    if card and card.parent() is not self.container:
                        card.setParent(self.container)
                ordered = [self._cards[g["id"]] for g in visible if g["id"] in self._cards]
                self.container.reflow(ordered, self.scroll.viewport().width())
        finally:
            self.container.setUpdatesEnabled(True)

    def _startup_steam_sync(self):
        """Launch a background Steam playtime fetch. Called once at startup."""
        key = self.config.get("steam_api_key", "").strip()
        if not key:
            return
        self._steam_pt_worker = SteamPlaytimeWorker(key)
        self._steam_pt_worker.done.connect(self._apply_steam_playtime)
        self._steam_pt_worker.finished.connect(self._steam_pt_worker.deleteLater)
        self._steam_pt_worker.start()

    def _apply_steam_playtime(self, bulk: dict):
        """Write fresher Steam playtime to DB and update visible cards in-place.
        Called from SteamPlaytimeWorker.done — always runs on the main thread."""
        if not bulk:
            return
        steam_games = [g for g in self._all_games if g.get("game_type") == "steam"]
        if not steam_games:
            return
        con = db_con()
        try:
            for g in steam_games:
                appid = (g.get("exe_path") or "").strip()
                if not appid:
                    continue
                fresh = bulk.get(appid, 0)
                if fresh > 0 and fresh > (g.get("playtime_minutes") or 0):
                    con.execute(
                        "UPDATE games SET playtime_minutes=? WHERE id=?",
                        (fresh, g["id"])
                    )
                    g["playtime_minutes"] = fresh
                    card = self._cards.get(g["id"])
                    if card:
                        try:
                            card.update_playtime(fresh)
                        except RuntimeError:
                            pass
            con.commit()
        finally:
            con.close()

    def _assign_categories(self, game: dict):
        current = db_get_game_categories(game["id"])
        dlg = CategoryAssignDialog(current, self.parent())
        if dlg.exec() == QDialog.DialogCode.Accepted:
            new_ids = dlg.selected_ids()
            db_set_game_categories(game["id"], new_ids)
            # Keep in-memory category map in sync so _apply_filter is correct
            self._game_cats[game["id"]] = set(new_ids)
            self.status_message.emit(f"Categories updated for {game['name']}")

    def _on_thumb_loaded(self, gid: int, px: QPixmap):
        if gid in self._cards:
            card = self._cards[gid]
            card.set_cover(px)

    def _launch_game(self, game: dict):
        log_file = None  # initialised here so the except handler can close it on crash
        # Prevent launching a game that's already running — same game_id check covers
        # both native/proton (in _running_games) and Steam (in _steam_watched).
        gid = game.get("id")
        if gid in self._running_games or any(e[0] == gid for e in self._steam_watched.values()):
            return
        try:
            # Pre-launch hook (runs before any other launch logic). Failures are
            # logged but never block the launch — fail-soft by design.
            pre_cmd = (game.get("pre_launch_cmd") or "").strip()

            # Precompute HDR launch state ONCE — this same data is needed in
            # three places (pre-cmd build, post-cmd build, launch log). Without
            # caching, each call hits _hdr_capable_connectors which spawns a
            # subprocess (up to 3s timeout each). Computed only when HDR will
            # actually fire — otherwise an empty list and the rest is no-op.
            _hdr_will_fire = (bool(game.get("hdr_enabled"))
                              and bool(game.get("hdr_monitor"))
                              and not bool(game.get("upscale_enabled"))
                              and game.get("game_type") != "steam")
            _hdr_capable_list: list[str] = []
            _hdr_tool_used = ""
            if _hdr_will_fire:
                _use_ksd, _use_gdct = _hdr_tool_choice()
                _hdr_tool_used = ("kscreen-doctor" if _use_ksd
                                  else "gdctl" if _use_gdct else "")
                if _hdr_tool_used:
                    _hdr_capable_list = _hdr_capable_connectors()

            # HDR enable — runs as its own subprocess BEFORE the user pre_cmd so
            # neither command can block the other. Steam-type games are excluded
            # entirely: NAGO doesn't own the Steam launch lifetime, so flipping
            # HDR on the host display from here would leak state into Steam's
            # own launcher.
            _hdr_post_cmd = ""
            if _hdr_will_fire and _hdr_capable_list:
                _hdr_pre, _hdr_post_cmd = _hdr_commands(game["hdr_monitor"], connectors=_hdr_capable_list)
                if _hdr_pre:
                    try:
                        subprocess.run(_hdr_pre, shell=True, timeout=15,
                                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                    except subprocess.TimeoutExpired:
                        _NAGOLog.launch("[warn] HDR enable timed out (15s)")
                    except Exception as e:
                        _NAGOLog.launch(f"[warn] HDR enable failed: {e}")

            if pre_cmd:
                try:
                    subprocess.run(pre_cmd, shell=True, timeout=30,
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                except subprocess.TimeoutExpired:
                    self.status_message.emit("Pre-launch command timed out (30s)")
                    _NAGOLog.launch(f"[warn] Pre-launch command timed out (30s): {pre_cmd}")
                except Exception as e:
                    self.status_message.emit(f"Pre-launch command failed: {e}")
                    _NAGOLog.launch(f"[error] Pre-launch command failed: {e}  cmd={pre_cmd}")

            # Per-game extras applied to all launch types
            launch_args = self._parse_launch_args(game.get("launch_args", ""))
            extra_env   = self._parse_env_vars(game.get("env_vars", ""))

            # Resolve gamescope binary once here — used both for env var gating
            # (HDR path selection) and for cmd building below. Avoids the case
            # where env vars assume gamescope is active but the binary isn't found.
            _gamescope_active = (
                bool(game.get("gamescope_enabled", 0))
                and game["game_type"] != "steam"
                and bool(shutil.which("gamescope"))
            )
            # Japanese locale — stored separately, injected at launch only.
            # Proton recommends HOST_LC_ALL over a raw LC_ALL (Proton sets its own
            # LC_ALL internally and only honours HOST_LC_ALL for host-side overrides),
            # so a bare LC_ALL can be silently dropped. JP locale is gated to
            # Proton/GOG, so HOST_LC_ALL is always the right target here.
            if game.get("vn_jp_locale"):
                extra_env.update({
                    "LANG":        "ja_JP.UTF-8",
                    "HOST_LC_ALL": "ja_JP.UTF-8",
                    "LANGUAGE":    "ja_JP",
                })
            # Proton toggles
            _is_proton_runtime = game["game_type"] in ("proton", "gog")
            if game.get("use_wined3d"):
                extra_env["PROTON_USE_WINED3D"] = "1"
            if game.get("use_wow64"):
                extra_env["PROTON_USE_WOW64"] = "1"
            # PROTON_ENABLE_WAYLAND only does anything inside the Proton runtime.
            # Native games ignore it but it'd still get logged as an "added" env
            # var — cleaner to not set it at all unless the runtime can read it.
            if (game.get("use_wayland")
                and not game.get("upscale_enabled")
                and not _gamescope_active
                and _is_proton_runtime):
                extra_env["PROTON_ENABLE_WAYLAND"] = "1"
            if game.get("hdr_enabled") and not game.get("upscale_enabled"):
                if _gamescope_active:
                    # Gamescope owns the HDR pipeline — inject DXVK_HDR=1 only;
                    # PROTON_ENABLE_WAYLAND/HDR are not needed and would conflict.
                    # DXVK_HDR is only meaningful for DXVK (Proton/GOG); native
                    # games don't use DXVK, so don't pollute their env either.
                    if _is_proton_runtime:
                        extra_env["DXVK_HDR"] = "1"
                elif _is_proton_runtime:
                    # PROTON_ENABLE_HDR/WAYLAND are Proton-only. For native HDR
                    # the kscreen-doctor mode flip (run as the pre-cmd above)
                    # is the only thing actually needed.
                    extra_env["PROTON_ENABLE_WAYLAND"] = "1"
                    extra_env["PROTON_ENABLE_HDR"] = "1"
            # FSR4 Upgrade — replace the game's bundled FSR 3.1 DLL
            if _is_proton_runtime:
                _fsr4_upgrade = (game.get("fsr4_upgrade") or "").strip()
                if _fsr4_upgrade:
                    extra_env["PROTON_FSR4_UPGRADE"] = _fsr4_upgrade
                # HUD checkbox removed (NAGO 07:25): fsr4_indicator column is now
                # always 0, so this branch is dormant. Kept for re-enable; use the
                # per-game env vars field (PROTON_FSR4_INDICATOR=1) for the overlay.
                if _fsr4_upgrade and game.get("fsr4_indicator"):
                    extra_env["PROTON_FSR4_INDICATOR"] = "1"
                _optiscaler_dll = (game.get("optiscaler_dll") or "").strip()
                if _optiscaler_dll:
                    extra_env["PROTON_USE_OPTISCALER"] = "1"
                    extra_env["PROTON_OPTISCALER_NAME"] = _optiscaler_dll
            # Esync/fsync/ntsync — always emit explicit 1/0 rather than only
            # setting on disable. Verified against the actual GE-Proton wrapper
            # script (check_environment()'s nonzero() parser, not presence-only):
            # explicit "0" correctly forces the script's else-branch (sync ON),
            # identical outcome to omitting the var, on every current build.
            # No functional change vs. the old conditional-only behavior — this
            # exists so the launch-env dump in Logs is self-documenting instead
            # of requiring the reader to know the script's default branch.
            #
            # ntsync gets both PROTON_NO_NTSYNC and PROTON_USE_NTSYNC, inverted
            # against each other, because two conventions are genuinely live in
            # the wild: GE-Proton10-10+/official Proton 11/current CachyOS read
            # PROTON_NO_NTSYNC (opt-out, default-on); GE-Proton10-9 reads
            # PROTON_USE_NTSYNC (opt-in, default-off) and was confirmed (grep)
            # to not read PROTON_NO_NTSYNC at all — and vice versa, 10-10 was
            # confirmed to not read PROTON_USE_NTSYNC. Each var is inert noise
            # on the build that doesn't read it, so sending both is safe on
            # every build checked, with no Proton-version detection needed.
            # esync/fsync have only ever had the disable-only flag — no "USE_"
            # variant exists or has existed for either, confirmed via source
            # and web search — so they don't get this treatment.
            if _is_proton_runtime:
                extra_env["PROTON_NO_ESYNC"]   = "1" if game.get("no_esync")  else "0"
                extra_env["PROTON_NO_FSYNC"]   = "1" if game.get("no_fsync")  else "0"
                _no_ntsync = bool(game.get("no_ntsync"))
                extra_env["PROTON_NO_NTSYNC"]  = "1" if _no_ntsync else "0"
                extra_env["PROTON_USE_NTSYNC"] = "0" if _no_ntsync else "1"
            # Video decode mode
            _vdm = game.get("video_decode_mode", "default") or "default"
            if _vdm == "winegstreamer":
                extra_env["PROTON_MEDIA_USE_GST"] = "1"

            # Global env vars — loaded from config, applied before per-game vars
            # so per-game always wins. Parse newline-separated KEY=VALUE pairs.
            global_env_raw = self.config.get("global_env", "")
            global_env = {}
            for _line in global_env_raw.splitlines():
                _line = _line.strip()
                if "=" in _line:
                    _k, _, _v = _line.partition("=")
                    _k = _k.strip()
                    if _k:
                        global_env[_k] = _v.strip()

            if game["game_type"] == "steam":
                appid = (game.get("exe_path") or "").strip()
                if not appid:
                    NAGOMessageBox.warning(None, "No Steam Game",
                                        "This entry has no Steam appid stored. Edit the game and pick one.")
                    return
                # Use the steam:// URL — Steam handles Proton, runtime, cloud saves, etc.
                # Try `steam` command first; fall back to xdg-open which respects the protocol handler.
                steam_url = f"steam://rungameid/{appid}"
                steam_bin = shutil.which("steam") or shutil.which("steam-runtime")
                if steam_bin:
                    cmd = [steam_bin, steam_url]
                elif shutil.which("xdg-open"):
                    cmd = ["xdg-open", steam_url]
                else:
                    NAGOMessageBox.warning(None, "Steam Not Found",
                                        "Couldn't find the steam command on your PATH. "
                                        "Make sure Steam is installed and accessible.")
                    return
                env = os.environ.copy()
                # Note: launch_args are intentionally NOT appended for Steam-type games —
                # Steam manages per-game launch options through its own UI.
            elif game["game_type"] == "native":
                cmd = [game["exe_path"], *launch_args]
                env = os.environ.copy()
            else:
                # umu is unconditional for all Proton games

                # Use archived prefix override if set and exists, else scan for
                # an existing prefix folder matching *_<id>, else derive a new one.
                # Persisted on first use so game renames never break the path.
                _pfx_override = (game.get("prefix_path") or "").strip()
                if _pfx_override and Path(_pfx_override).exists():
                    pfx = _pfx_override
                else:
                    # Scan prefixes root for any folder ending in _<game_id>
                    # — catches pre-fix prefixes created before prefix_path was persisted
                    _gid_str = str(game["id"])
                    _found_pfx = None
                    try:
                        for _entry in get_prefixes_root().iterdir():
                            if _entry.is_dir() and _entry.name.endswith(f"_{_gid_str}"):
                                _found_pfx = str(_entry)
                                break
                    except Exception:
                        pass

                    if _found_pfx:
                        pfx = _found_pfx
                    else:
                        pfx = str(get_game_prefix(game["id"], game.get("name", "")))

                    # Persist so future launches and renames always use this path
                    _pcon = None
                    try:
                        _pcon = db_con()
                        _pcon.execute("UPDATE games SET prefix_path=? WHERE id=?",
                                      (pfx, game["id"]))
                        _pcon.commit()
                        game["prefix_path"] = pfx
                    except Exception as _pe:
                        _NAGOLog.session(f"[warn] failed to persist prefix_path for game {game.get('id')}: {_pe}")
                    finally:
                        if _pcon is not None:
                            try:
                                _pcon.close()
                            except Exception:
                                pass

                proton = game.get("proton_path") or self.config.get("default_proton", "")

                umu_bin = find_umu_run()
                if not umu_bin:
                    NAGOMessageBox.warning(
                        None, "umu-launcher Not Found",
                        "umu-launcher is required to launch Proton games but 'umu-run' isn't installed.\n\n"
                        "Install it from Settings → umu-launcher."
                    )
                    return

                # umu's PROTONPATH expects a Proton DIRECTORY, not the proton script inside it.
                # find_proton_installations() returns paths to the script (e.g. .../Proton - Experimental/proton),
                # so strip the trailing /proton if it's a file, leaving the parent dir.
                proton_arg = ""
                if proton in (UMU_DEFAULT_SENTINEL, "GE-Proton"):
                    # Auto options: pass through untouched; build_umu_env interprets the
                    # sentinel as "no PROTONPATH" (UMU-Proton default) and "GE-Proton" as
                    # the latest-GE codename.
                    proton_arg = proton
                elif proton:
                    p = Path(proton).resolve()
                    if p.is_file() and p.name == "proton":
                        proton_arg = str(p.parent)
                    elif p.is_dir():
                        proton_arg = str(p)
                    else:
                        # Path doesn't exist or is something else — treat as a codename like "GE-Proton"
                        proton_arg = proton
                if not proton_arg:
                    # No selection at all → tell umu to fetch the latest GE-Proton automatically
                    proton_arg = "GE-Proton"

                # Protonfix disabled (NAGO 04:20): never pass GAMEID or STORE to
                # umu. The per-game protonfix matcher was applying the wrong game's
                # fix (loose matcher), and GE-Proton already bundles the common
                # fixes. Empty game_id → build_umu_env omits GAMEID → umu falls back
                # to umu-default and applies no specific fix. Empty store → no STORE.
                # Games launch identically; only the per-game fix injection stops.
                game_id = ""
                store   = ""

                env = build_umu_env(os.environ.copy(),
                                    wineprefix=pfx, proton_path=proton_arg,
                                    game_id=game_id, store=store,
                                    extra_share_paths=[game.get("exe_path", "")])
                cmd = [umu_bin, game["exe_path"], *launch_args]

            # Set the working directory to the game's folder so it can find its own
            # data files (configs/assets sitting next to the exe).
            # Fallback chain — never leave a Proton/GOG game running in NAGO's own cwd:
            #   1. exe's parent dir if the exe resolves as a real file (the normal case)
            #   2. exe's parent dir if that directory exists, even when the exe file
            #      check is flaky (e.g. a drive mounted just after a path was saved,
            #      or a path with odd casing) — the data files live there regardless
            #   3. the Wine prefix dir as a last resort, so the game at least starts
            #      inside its own sandbox rather than NAGO's install dir
            # Native/Steam games are launched directly and keep cwd=None (correct).
            cwd = None
            if game["game_type"] != "steam":
                exe_path = Path(game.get("exe_path") or "")
                parent   = exe_path.parent
                if exe_path.exists() and exe_path.is_file():
                    cwd = str(parent)
                elif str(parent) not in ("", ".") and parent.is_dir():
                    cwd = str(parent)
                    _NAGOLog.launch(f"cwd fallback     exe not resolved as file; using parent dir: {cwd}")
                else:
                    _pfx_dir = locals().get("pfx")
                    if _pfx_dir and Path(_pfx_dir).is_dir():
                        cwd = str(_pfx_dir)
                        _NAGOLog.launch(f"cwd fallback     exe dir unavailable; using prefix dir: {cwd}")
                    else:
                        _NAGOLog.launch("cwd fallback     no valid dir found; launching with NAGO's cwd")

            # Apply environment variables: global first, then per-game on top.
            # Per-game always wins — it's applied second and overwrites globals.
            # Both layers respect NAGO_MANAGED_ENV — those vars are NAGO's domain
            # and cannot be overridden from either layer.
            NAGO_MANAGED_ENV = {
                "WINEPREFIX",
                "STEAM_COMPAT_DATA_PATH",
                "STEAM_COMPAT_CLIENT_INSTALL_PATH",
                "STEAM_COMPAT_INSTALL_PATH",
                "STEAM_COMPAT_LIBRARY_PATHS",
                "PROTONPATH",
                "GAMEID",
                "STORE",
            }
            # Layer 1: global env vars (lowest priority)
            for key, value in global_env.items():
                if key not in NAGO_MANAGED_ENV:
                    env[key] = value
            # Layer 2: per-game env vars (overrides globals)
            if extra_env:
                blocked = []
                for key, value in extra_env.items():
                    if key in NAGO_MANAGED_ENV:
                        blocked.append(key)
                        continue
                    env[key] = value
                if blocked:
                    self.status_message.emit(
                        f"Ignored {len(blocked)} reserved env var(s): {', '.join(blocked)}"
                    )

            # AI upscaler forces XWayland (PROTON_ENABLE_WAYLAND=0) on Proton/GOG so it can
            # capture the game window. Apply it to env HERE — before the launch log is
            # written below — so the logged env-diff reflects what the game actually
            # receives, not the pre-override state. The full UPSCALER section further down
            # handles the capture worker/timer and its own logging.
            _upscale_enabled = bool(game.get("upscale_enabled", 0))
            _upscale_bin = (shutil.which("upscale")
                            if (_upscale_enabled and game["game_type"] != "steam") else "")
            if _upscale_bin and game["game_type"] in ("proton", "gog"):
                env["PROTON_ENABLE_WAYLAND"] = "0"

            # Gamescope — wrap the launch command when active.
            # Applied before the log write so the logged CMD shows the full command.
            # Resolution is read from kscreen-doctor (physical pixels, correct under
            # fractional scaling). Falls back to 1920x1080 if detection fails.
            # When HDR is also on: adds --hdr-enabled if the installed gamescope
            # supports it (v3.13+). Older builds get a warning in the log and
            # the flag is dropped so they don't crash on launch.
            if _gamescope_active:
                _gs_bin = shutil.which("gamescope")  # already confirmed truthy via _gamescope_active
                _gs_w, _gs_h, _gs_r = _gamescope_resolution()
                _gs_cmd = [_gs_bin, "-W", str(_gs_w), "-H", str(_gs_h), "-r", str(_gs_r), "-f"]
                if game.get("hdr_enabled") and not game.get("upscale_enabled"):
                    if _gamescope_supports_hdr():
                        _gs_cmd.append("--hdr-enabled")
                    else:
                        _NAGOLog.launch("[warn] installed gamescope doesn't support --hdr-enabled; HDR signalling skipped (upgrade to v3.13+)")
                _gs_cmd.append("--")
                cmd = _gs_cmd + cmd

            # Write stdout/stderr to a per-game log so users can debug failed launches.
            # Rotate so the last 3 launches are preserved (current + .1 + .2).
            log_path = self._game_log_path(game)
            log_path.parent.mkdir(parents=True, exist_ok=True)
            self._rotate_log(log_path, keep=3)
            log_file = open(log_path, "w")

            # Write launch context to the top of the log: command, cwd, and every
            # env var that differs from the base system environment.  This makes it
            # easy to verify that per-game env vars (MANGOHUD, DXVK_HUD, etc.) are
            # actually being passed correctly, and to debug launch failures.
            log_file.write(f"=== NAGO launch: {game['name']} ===\n")
            log_file.write(f"CMD : {' '.join(str(a) for a in cmd)}\n")
            log_file.write(f"CWD : {cwd}\n")
            log_file.write("ENV (overrides / additions vs system environment):\n")
            for k, v in sorted(env.items()):
                if os.environ.get(k) != v:
                    log_file.write(f"  {k}={v}\n")
            log_file.write("=" * 40 + "\n\n")
            log_file.flush()

            # Write NAGO verbose launch log (in-memory, viewable in Logs page)
            _env_diff      = {k: v for k, v in env.items() if os.environ.get(k) != v}
            _launch_proton = game.get("proton_path") or self.config.get("default_proton", "")
            _launch_prefix = locals().get("pfx", "")
            _launch_umu    = (locals().get("umu_bin", "") or "") if game["game_type"] not in ("native", "steam") else ""
            _launch_fix    = env.get("PROTONDB_FIX", "") or env.get("UMU_PROTONFIX", "")
            _log_launch(game, cmd, _env_diff, _launch_prefix,
                        _launch_umu, _launch_fix, _launch_proton,
                        gamescope_active=_gamescope_active,
                        gamescope_res=(_gs_w, _gs_h, _gs_r) if _gamescope_active else None,
                        hdr_tool=_hdr_tool_used,
                        hdr_capable=_hdr_capable_list,
                        share_paths=env.get("STEAM_COMPAT_LIBRARY_PATHS", ""))

            # ── AI Upscaler ────────────────────────────────────────────────
            # When enabled: inject PROTON_ENABLE_WAYLAND=0 for Proton/GOG games
            # (forces XWayland so the upscaler can capture the window), then fire
            # `upscale -t <window_title> -m <model>` in parallel.
            #
            # Window title detection: after the initial delay, query xprop to find
            # the actual window title belonging to the game's PID. This handles games
            # where the exe stem doesn't match the window title (e.g. utaware-voice.exe
            # but the window is titled "Utawarerumono").
            # Falls back to exe stem if xprop finds nothing after retries.
            _upscale_enabled = bool(game.get("upscale_enabled", 0))
            if _upscale_enabled and game["game_type"] != "steam":
                _NAGOLog.launch("-" * 64)
                _NAGOLog.launch("UPSCALER")
                _NAGOLog.launch(f"  enabled        yes")
                _NAGOLog.launch(f"  binary         {_upscale_bin or '(not found)'}")
                if _upscale_bin:
                    # XWayland was already forced (PROTON_ENABLE_WAYLAND=0) above, before
                    # the launch log — upscaler can't capture native Wayland windows.
                    if game["game_type"] in ("proton", "gog"):
                        _NAGOLog.launch(f"  wayland        PROTON_ENABLE_WAYLAND=0 injected (XWayland forced)")
                    else:
                        _NAGOLog.launch(f"  wayland        not injected (native game)")
                    _exe_stem    = Path(game.get("exe_path", "")).stem or game["name"]
                    _upscale_model = game.get("upscale_model", "fast") or "fast"
                    _NAGOLog.launch(f"  exe stem       {_exe_stem!r} (fallback title)")
                    _NAGOLog.launch(f"  model          {_upscale_model}")
                    _NAGOLog.launch(f"  delay          4s (waiting for Wine window to appear)")
                    _NAGOLog.launch(f"  status         timer started (fires in 4s, then probes xprop)")

                    def _on_upscaler_ready(
                        _bin: str, _title: str, _model: str, _gid: int, _log_msg: str,
                        _self=self,
                    ):
                        if _log_msg:
                            _NAGOLog.launch(_log_msg)
                        _cmd = [_bin, "-t", _title, "-m", _model, "--quiet"]
                        _NAGOLog.launch(f"  command        {' '.join(_cmd)}")
                        try:
                            _up_proc = subprocess.Popen(
                                _cmd,
                                stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL,
                                preexec_fn=_set_pdeathsig_sigterm,
                            )
                            _self._upscale_procs[_gid] = _up_proc
                            _NAGOLog.launch(f"  upscaler pid   {_up_proc.pid}")
                        except Exception as _e:
                            _NAGOLog.launch(f"  upscaler error {_e}")
                        _self._upscaler_worker = None

                    _upscaler_worker = _UpscalerLaunchWorker(
                        _upscale_bin, _upscale_model, game, _exe_stem,
                        initial_delay=4.0, parent=self,
                    )
                    _upscaler_worker.ready.connect(_on_upscaler_ready)
                    _upscaler_worker.finished.connect(_upscaler_worker.deleteLater)
                    _upscaler_worker.start()
                    self._upscaler_worker = _upscaler_worker
                else:
                    _NAGOLog.launch(f"  status         SKIPPED — 'upscale' not found on PATH")
                    _NAGOLog.launch(f"                 install: pip install linux-rt-upscaler")

            # start_new_session=True puts this process (and everything gamescope/
            # umu/Proton/wine spawns under it, unless they explicitly detach like
            # wineserver does) into its own process group, separate from NAGO's.
            # Required for Force Terminate to safely killpg() the whole launch
            # tree — without this, the child shares NAGO's own process group and
            # a group-kill would take NAGO down with it.
            proc = subprocess.Popen(cmd, env=env, cwd=cwd,
                                    stdout=log_file, stderr=subprocess.STDOUT,
                                    start_new_session=True)
            # Close our copy of the handle now that the child has its own dup'd fd.
            # The child keeps writing to the file fine; this just stops NAGO from
            # leaking a parent-side handle on every launch.
            try:
                log_file.close()
            except Exception:
                pass
            log_file = None  # mark as closed so the except handler skips it
            # Track only types where Popen represents the actual game lifetime.
            # The Steam-type Popen exits as soon as steam:// is handed off to Steam,
            # so we register it in _steam_watched and use registry.vdf polling instead.
            # HDR disable — appended to user post_exit_cmd with `;` (not `&&`)
            # so HDR is restored to SDR even when the user's post-exit command
            # returns non-zero. Steam-type games are excluded (matches the pre
            # path; NAGO doesn't own the Steam launch lifetime). Reuses the
            # connector list computed at the top of _launch_game.
            _post_cmd_base = (game.get("post_exit_cmd") or "").strip()

            # HDR disable — appended with `;` (not `&&`) so HDR is restored to SDR
            # even when the user's post-exit command returns non-zero (or is empty).
            # NAGO never turns HDR off otherwise, so without this the kscreen-doctor
            # mode flip applied at launch persists until the next manual change.
            # Steam is already excluded upstream (_hdr_will_fire is False for steam).
            if _hdr_post_cmd:
                _post_cmd_base = (f"{_post_cmd_base} ; {_hdr_post_cmd}"
                                  if _post_cmd_base else _hdr_post_cmd)
            if game["game_type"] == "steam":
                appid = (game.get("exe_path") or "").strip()
                if appid:
                    # HDR-disable is computed at EXIT time, not here — see
                    # _fire_steam_exit_post_cmd_async() at the Steam
                    # exit-cleanup site. NAGO never enables HDR for Steam
                    # games (see the pre-cmd exclusion above), and Steam
                    # games never expose an HDR toggle in NAGO's UI, so
                    # there's no per-game "did NAGO turn HDR on" state to
                    # check here at launch — the only meaningful check is
                    # "is HDR on right now, at the moment the game exits."
                    self._steam_watched[appid] = (
                        game["id"],
                        _post_cmd_base,
                        time.monotonic(),
                    )
                    self._session_starts[game["id"]] = time.monotonic()
                    # Don't set_running yet — /proc scan will confirm when up.
            else:
                self._running_games[game["id"]] = (proc, _post_cmd_base, bool(game.get("auto_backup")))
                self._session_starts[game["id"]] = time.monotonic()
                if game["id"] in self._cards:
                    try:
                        self._cards[game["id"]].set_running(True)
                    except RuntimeError:
                        pass

            self.status_message.emit(f"Launched: {game['name']}  (log: {log_path.name})")
            self.game_launched.emit(str(log_path))

            # Update last played
            con = None
            try:
                con = db_con()
                con.execute("UPDATE games SET last_played = datetime('now') WHERE id = ?", (game["id"],))
                con.commit()
            finally:
                if con is not None:
                    try:
                        con.close()
                    except Exception:
                        pass
        except Exception as e:
            import traceback as _tb
            _tb_str = _tb.format_exc()
            _game_name = game.get("name", "?") if isinstance(game, dict) else "?"
            _NAGOLog.launch("=" * 64)
            _NAGOLog.launch(f"LAUNCH ERROR  game={_game_name!r}")
            _NAGOLog.launch(f"  {e}")
            _NAGOLog.launch(_tb_str.strip())
            _NAGOLog.launch("=" * 64)
            # Also write to the per-game log file if it was opened before the crash
            _lf = locals().get("log_file")
            if _lf is not None:
                try:
                    _lf.write("\n[NAGO] Launch error: " + str(e) + "\n" + _tb_str)
                    _lf.flush()
                    _lf.close()
                except Exception:
                    pass
            NAGOMessageBox.critical(None, "Launch Error",
                str(e) + "\n\nSee Game Log for details.")

    def _auto_backup_game(self, gid: int) -> None:
        """
        Run find→backup silently after game exit.
        Shows a pill on the GameCard: "Backing up…" → "Saved ✓" or "Backup failed".
        No dialogs; no blocking the UI.
        """
        if not (LUDUSAVI_BIN.exists() or shutil.which("ludusavi")):
            _NAGOLog.session(f"[auto-backup] skipped game {gid}: ludusavi not found")
            return

        # Read the game row from DB so we have a fresh copy with all fields.
        con = None
        game = None
        try:
            con = db_con()
            cur = con.execute("SELECT * FROM games WHERE id=?", (gid,))
            row = cur.fetchone()
            if row:
                cols = [d[0] for d in cur.description]
                game = dict(zip(cols, row))
        except Exception as e:
            _NAGOLog.session(f"[auto-backup] DB read failed for game {gid}: {e}")
            return
        finally:
            if con:
                try: con.close()
                except Exception: pass

        if not game:
            return

        def _set_pill(state: str) -> None:
            card = self._cards.get(gid)
            if card:
                try:
                    card.show_backup_pill(state)
                except RuntimeError:
                    pass

        def _cleanup(worker) -> None:
            workers = self._auto_bk_workers.get(gid, [])
            if worker in workers:
                workers.remove(worker)
            if not workers:
                self._auto_bk_workers.pop(gid, None)

        _set_pill("running")
        _NAGOLog.session(f"[auto-backup] starting for game {gid} '{game.get('name','')}'")

        stored_title = (game.get("ludusavi_title") or "").strip()
        game_for_find = dict(game, ludusavi_title=stored_title)

        find_worker = LudusaviFindWorker(game_for_find)

        def _on_resolved(titles: list) -> None:
            if not titles:
                _set_pill("failed")
                _NAGOLog.session(f"[auto-backup] no title resolved for game {gid}")
                return
            title = titles[0]
            bk_worker = LudusaviBackupWorker(game, title,
                                             backup_root=str(LUDUSAVI_AUTO_BACKUPS))

            def _on_done(summary: dict) -> None:
                _write_auto_backup_db(gid, title, summary)
                _set_pill("success")
                _mb = summary.get("totalBytes", 0) / (1024 * 1024)
                _NAGOLog.session(
                    f"[auto-backup] success  game {gid} '{game.get('name','')}'  "
                    f"title='{title}'  "
                    f"files={summary.get('fileCount', 0)}  size={_mb:.2f} MB  "
                    f"path='{str(LUDUSAVI_AUTO_BACKUPS)}'"
                )
                _cleanup(bk_worker)

            def _on_bk_failed(msg: str) -> None:
                _set_pill("failed")
                _NAGOLog.session(f"[auto-backup] backup failed game {gid}: {msg}")
                _cleanup(bk_worker)

            bk_worker.done.connect(_on_done)
            bk_worker.failed.connect(_on_bk_failed)
            bk_worker.finished.connect(bk_worker.deleteLater)
            bk_worker.start()
            self._auto_bk_workers.setdefault(gid, []).append(bk_worker)
            _cleanup(find_worker)

        def _on_candidates(titles: list) -> None:
            # Ambiguous title — can't show picker during auto-backup, fail silently.
            _set_pill("failed")
            _NAGOLog.session(f"[auto-backup] ambiguous title for game {gid}: {titles}")
            _cleanup(find_worker)

        def _on_find_failed(msg: str) -> None:
            _set_pill("failed")
            _NAGOLog.session(f"[auto-backup] find failed game {gid}: {msg}")
            _cleanup(find_worker)

        find_worker.resolved.connect(_on_resolved)
        find_worker.candidates.connect(_on_candidates)
        find_worker.failed.connect(_on_find_failed)
        find_worker.finished.connect(find_worker.deleteLater)
        find_worker.start()
        self._auto_bk_workers.setdefault(gid, []).append(find_worker)

    def _poll_running_games(self):
        """Detect games that have exited and clean up trackers + UI.
        Runs the per-game post-exit command if one is configured.

        Two tracking paths:
          • _running_games  — native/proton games tracked via Popen.poll()
          • _steam_watched  — Steam games tracked via registry.vdf RunningAppID
        """

        # ── Native / Proton: Popen-based tracking ─────────────────────────
        if self._running_games:
            exited = []
            for gid, (proc, post_cmd, do_auto_bk) in self._running_games.items():
                try:
                    if proc.poll() is not None:
                        # Capture returncode here while proc is still in hand —
                        # gid is popped below, so re-fetching it later is too late.
                        exited.append((gid, post_cmd, do_auto_bk, proc.returncode))
                except Exception:
                    exited.append((gid, post_cmd, do_auto_bk, None))
            for gid, post_cmd, do_auto_bk, _exit_code in exited:
                self._running_games.pop(gid, None)
                # ── Accumulate playtime ───────────────────────────────────
                start = self._session_starts.pop(gid, None)
                elapsed_min = 0
                if start is not None:
                    elapsed_min = int((time.monotonic() - start) / 60)
                    if elapsed_min > 0:
                        con = None
                        try:
                            con = db_con()
                            row = con.execute(
                                "SELECT playtime_minutes FROM games WHERE id=?", (gid,)
                            ).fetchone()
                            prev = int(row[0]) if row and row[0] else 0
                            new_total = prev + elapsed_min
                            con.execute(
                                "UPDATE games SET playtime_minutes=?, last_session_minutes=? WHERE id=?",
                                (new_total, elapsed_min, gid)
                            )
                            con.commit()
                            if gid in self._cards:
                                try:
                                    self._cards[gid].update_playtime(new_total)
                                except RuntimeError:
                                    pass
                        except Exception as e:
                            _NAGOLog.session(f"[warn] playtime update failed for game {gid}: {e}")
                        finally:
                            if con is not None:
                                try:
                                    con.close()
                                except Exception:
                                    pass
                _NAGOLog.launch("-" * 64)
                _NAGOLog.launch(f"EXIT  game_id={gid}")
                _exit_hint = ""
                if _exit_code is not None and _exit_code != 0:
                    _exit_hint = {
                        1:   " (general error)",
                        127: " (command not found)",
                        134: " (abort/assert)",
                        137: " (killed — OOM or SIGKILL)",
                        139: " (segfault)",
                        143: " (SIGTERM)",
                    }.get(_exit_code, " (non-zero)")
                _NAGOLog.launch(f"Exit code      {_exit_code if _exit_code is not None else '(unknown)'}{_exit_hint}")
                if start is not None:
                    _NAGOLog.launch(f"Session time   {elapsed_min} min")
                # Resolved Proton: read the build umu actually used back from the
                # per-game log (umu prints it at startup). This is the only place
                # the real build/path is known for the auto options, where NAGO
                # set no PROTONPATH and let umu resolve/download at runtime.
                con = None
                try:
                    con = db_con()
                    _row = con.execute(
                        "SELECT name, game_type FROM games WHERE id=?", (gid,)
                    ).fetchone()
                    if _row and (_row[1] in ("proton", "gog")):
                        _glog = NAGO_HOME / "logs" / f"{slugify(_row[0])}_{gid}.log"
                        _build, _channel = _resolve_proton_from_umu_log(_glog)
                        if _build or _channel:
                            _via = f"  via {_channel}" if _channel else ""
                            _NAGOLog.launch(f"Proton resolved {_build or '(unknown build)'}{_via}")
                            _install = _find_proton_install_dir(_channel, _build)
                            if _install:
                                _NAGOLog.launch(f"Proton dir     {_install}")
                            else:
                                _NAGOLog.launch("Proton dir     (umu-managed — not found on disk)")
                except Exception as e:
                    _NAGOLog.session(f"[warn] resolved-Proton read failed for game {gid}: {e}")
                finally:
                    if con is not None:
                        try:
                            con.close()
                        except Exception:
                            pass
                # ─────────────────────────────────────────────────────────
                if gid in self._cards:
                    try:
                        self._cards[gid].set_running(False)
                    except RuntimeError:
                        pass
                # Auto-backup — runs silently; pill on card shows result
                if do_auto_bk:
                    self._auto_backup_game(gid)
                if post_cmd:
                    try:
                        subprocess.Popen(post_cmd, shell=True,
                                         stdout=subprocess.DEVNULL,
                                         stderr=subprocess.DEVNULL)
                        _NAGOLog.launch(f"Post-exit cmd  started: {post_cmd}")
                    except Exception as e:
                        self.status_message.emit(f"Post-exit command failed: {e}")
                        _NAGOLog.launch(f"[error] Post-exit command failed: {e}  cmd={post_cmd}")
                # Kill upscaler if one was started for this game
                _up = self._upscale_procs.pop(gid, None)
                if _up is not None:
                    try:
                        _up.terminate()
                        _NAGOLog.launch(f"Upscaler terminated  pid={_up.pid}  game_id={gid}")
                    except Exception:
                        pass

        # ── Steam: /proc-based tracking ───────────────────────────────────
        if not self._steam_watched:
            return

        running_appids = get_running_steam_appids()
        STEAM_LAUNCH_GRACE = 90.0

        for appid, entry in list(self._steam_watched.items()):
            gid         = entry[0]
            post_cmd    = entry[1]
            launched_at = entry[2] if len(entry) > 2 else time.monotonic()
            card = self._cards.get(gid)
            currently_running = (appid in running_appids)

            if currently_running:
                if card:
                    try:
                        card.set_running(True)
                    except RuntimeError:
                        pass
            else:
                was_running = card.is_running if card else False
                if was_running:
                    self._steam_watched.pop(appid, None)
                    # ── Steam exit: apply LOCAL session time first ───────────
                    # The Steam Web API is authoritative but (a) needs an API
                    # key and (b) lags minutes behind exit, so on its own it
                    # often records nothing. Add the locally-timed session like
                    # native/proton games do; the API sync below will overwrite
                    # with the true total when it can (it only updates if its
                    # value is higher, so it can't shrink a fresh local bump).
                    _start = self._session_starts.pop(gid, None)
                    if _start is not None:
                        _elapsed_min = int((time.monotonic() - _start) / 60)
                        if _elapsed_min > 0:
                            _con = None
                            try:
                                _con = db_con()
                                _row = _con.execute(
                                    "SELECT playtime_minutes FROM games WHERE id=?", (gid,)
                                ).fetchone()
                                _prev = int(_row[0]) if _row and _row[0] else 0
                                _new_total = _prev + _elapsed_min
                                _con.execute(
                                    "UPDATE games SET playtime_minutes=?, last_session_minutes=? WHERE id=?",
                                    (_new_total, _elapsed_min, gid)
                                )
                                _con.commit()
                                _c = self._cards.get(gid)
                                if _c:
                                    try:
                                        _c.update_playtime(_new_total)
                                    except RuntimeError:
                                        pass
                            except Exception as e:
                                _NAGOLog.session(f"[warn] Steam local playtime update failed for game {gid}: {e}")
                            finally:
                                if _con is not None:
                                    try:
                                        _con.close()
                                    except Exception:
                                        pass
                    # ── Steam exit: sync authoritative playtime (background) ─
                    _key = self.config.get("steam_api_key", "")
                    if _key:
                        _w = SteamPlaytimeWorker(_key)
                        def _on_exit_pt(bulk, _gid=gid, _appid=appid):
                            fresh = bulk.get(_appid, 0)
                            if fresh <= 0:
                                return
                            con = None
                            try:
                                con = db_con()
                                row = con.execute(
                                    "SELECT playtime_minutes FROM games WHERE id=?",
                                    (_gid,)
                                ).fetchone()
                                prev = int(row[0]) if row and row[0] else 0
                                if fresh > prev:
                                    con.execute(
                                        "UPDATE games SET playtime_minutes=? WHERE id=?",
                                        (fresh, _gid)
                                    )
                                    con.commit()
                                    _card = self._cards.get(_gid)
                                    if _card:
                                        try:
                                            _card.update_playtime(fresh)
                                        except RuntimeError:
                                            pass
                            except Exception as e:
                                _NAGOLog.session(f"[warn] Steam playtime update failed for game {_gid}: {e}")
                            finally:
                                if con is not None:
                                    try:
                                        con.close()
                                    except Exception:
                                        pass
                        _w.done.connect(_on_exit_pt)
                        # Keep a strong ref until the thread finishes — a bare local
                        # gets GC'd mid-run and Qt aborts ("Destroyed while thread is
                        # still running"). Same pattern as _single_cover_workers.
                        _w.finished.connect(lambda w=_w: self._steam_exit_workers.discard(w))
                        _w.finished.connect(_w.deleteLater)
                        self._steam_exit_workers.add(_w)
                        _w.start()
                    # ─────────────────────────────────────────────────────────
                    if card:
                        try:
                            card.set_running(False)
                        except RuntimeError:
                            pass
                    # Always fires — even with no user post-exit command, the
                    # HDR-disable still needs to run. Computed fresh on a
                    # background thread inside the helper itself, so this
                    # never blocks the poll-loop/UI thread.
                    _fire_steam_exit_post_cmd_async(post_cmd, identifier=appid)
                else:
                    if time.monotonic() - launched_at > STEAM_LAUNCH_GRACE:
                        self._steam_watched.pop(appid, None)
                        self._session_starts.pop(gid, None)
                        self.status_message.emit(
                            f"Steam game {appid} did not start within {int(STEAM_LAUNCH_GRACE)}s."
                        )

    def _game_log_path(self, game: dict) -> Path:
        """Compute the per-game log file path."""
        return NAGO_HOME / "logs" / f"{slugify(game['name'])}_{game['id']}.log"

    @staticmethod
    def _parse_launch_args(raw: str) -> list[str]:
        """Split a launch-arguments string into argv tokens.
        Uses shell-style splitting so quotes work: `-foo "bar baz"` → ['-foo', 'bar baz'].
        Returns [] for empty/None input. Falls back to whitespace split if shlex chokes
        (e.g. on unbalanced quotes in user input)."""
        s = (raw or "").strip()
        if not s:
            return []
        try:
            return shlex.split(s)
        except ValueError:
            return s.split()

    @staticmethod
    def _parse_env_vars(raw: str) -> dict:
        """Parse a string of `KEY=VALUE` pairs separated by whitespace into a dict.
        Uses shell-style splitting so values with spaces work when quoted:
        `FOO=bar BAZ="hello world"` → {'FOO': 'bar', 'BAZ': 'hello world'}.
        Tokens without '=' are skipped silently."""
        s = (raw or "").strip()
        if not s:
            return {}
        try:
            tokens = shlex.split(s)
        except ValueError:
            tokens = s.split()
        out: dict[str, str] = {}
        for tok in tokens:
            if "=" not in tok:
                continue
            key, _, value = tok.partition("=")
            key = key.strip()
            if key:
                out[key] = value
        return out

    def _rotate_log(self, log_path: Path, keep: int = 3):
        """Rotate logs: log → log.1 → log.2 → … → log.<keep-1>; oldest is dropped."""
        if not log_path.exists():
            return
        try:
            # Drop the oldest by going from highest down: e.g. log.2 → log.3 (gone), log.1 → log.2, log → log.1
            for i in range(keep - 1, 0, -1):
                older = log_path.with_suffix(log_path.suffix + f".{i}")
                newer = log_path.with_suffix(log_path.suffix + f".{i+1}")
                if older.exists():
                    if i + 1 >= keep:
                        older.unlink(missing_ok=True)
                    else:
                        older.rename(newer)
            log_path.rename(log_path.with_suffix(log_path.suffix + ".1"))
        except Exception as e:
            print(f"[log] rotation failed for {log_path}: {e}")

    def _show_game_log(self, game: dict):
        """Open the most recent log file for a game in the system default editor."""
        log_path = self._game_log_path(game)
        if not log_path.exists():
            self.status_message.emit(f"No log yet for '{game['name']}' — launch it once first")
            return
        try:
            # Cross-DE way to open with the system's default editor for text files
            subprocess.Popen(["xdg-open", str(log_path)],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            self.status_message.emit(f"Opened log: {log_path.name}")
        except Exception as e:
            self.status_message.emit(f"Couldn't open log: {e}")

    def _edit_game(self, game: dict):
        # Always re-read cover_path from DB so the dialog shows the current cover
        con = db_con()
        row = con.execute("SELECT cover_path FROM games WHERE id=?",
                          (game["id"],)).fetchone()
        con.close()
        if row:
            game["cover_path"] = row[0] or ""
        dlg = GameDialog(self.config, game, self.parent())
        if dlg.exec() == QDialog.DialogCode.Accepted:
            d = dlg.result_data
            con = db_con()
            con.execute("""
                UPDATE games SET name=?, exe_path=?, game_type=?, proton_path=?,
                                 umu_enabled=?, umu_gameid=?, umu_store=?,
                                 launch_args=?, env_vars=?, vn_jp_locale=?,
                                 use_wined3d=?, use_wow64=?, use_wayland=?,
                                 no_esync=?, no_fsync=?, no_ntsync=?,
                                 legacy_mediaconv=?, video_decode_mode=?,
                                 pre_launch_cmd=?, post_exit_cmd=?,
                                 auto_backup=?,
                                 gamescope_enabled=?,
                                 upscale_enabled=?, upscale_model=?,
                                 hdr_enabled=?, hdr_monitor=?, gog_id=?,
                                 fsr4_upgrade=?, optiscaler_dll=?, fsr4_indicator=?
                WHERE id=?
            """, (d["name"], d["exe_path"], d["game_type"], d["proton_path"],
                  d["umu_enabled"], d["umu_gameid"], d["umu_store"],
                  d["launch_args"], d["env_vars"], d.get("vn_jp_locale", 0),
                  d.get("use_wined3d", 0), d.get("use_wow64", 0), d.get("use_wayland", 0),
                  d.get("no_esync", 0), d.get("no_fsync", 0), d.get("no_ntsync", 0),
                  d.get("legacy_mediaconv", 0), d.get("video_decode_mode", "default"),
                  d["pre_launch_cmd"], d["post_exit_cmd"],
                  d.get("auto_backup", 0),
                  d.get("gamescope_enabled", 0),
                  d.get("upscale_enabled", 0), d.get("upscale_model", "fast"),
                  d.get("hdr_enabled", 0), d.get("hdr_monitor", ""), d.get("gog_id", ""),
                  d.get("fsr4_upgrade", ""), d.get("optiscaler_dll", ""), d.get("fsr4_indicator", 0),
                  game["id"]))
            con.commit()
            con.close()
            # Update the card in-place — no full rebuild, no flash.
            card = self._cards.get(game["id"])
            if card:
                card.update_game_data(d)
            # Refresh cover if it changed — re-read from DB to get the committed path
            con2 = db_con()
            try:
                cover_row = con2.execute("SELECT cover_path FROM games WHERE id=?",
                                         (game["id"],)).fetchone()
            finally:
                con2.close()
            new_cover = cover_row[0] if cover_row else ""
            if new_cover and Path(new_cover).exists():
                self._refresh_single_cover(game["id"], new_cover)
            elif card and not new_cover:
                card._set_placeholder()
            # Keep master game list in sync for DnD / sort order
            for g in self._all_games:
                if g["id"] == game["id"]:
                    g.update(d)
                    g["cover_path"] = new_cover
                    break

    def _delete_game(self, gid: int):
        reply = NAGOMessageBox.question(
            self, "Remove Game",
            "Remove this game from your library?\n(The game files won't be deleted.)"
        )
        if reply == QMessageBox.StandardButton.Yes:
            con = db_con()
            row = con.execute(
                "SELECT cover_path, name, exe_path, game_type, umu_store, "
                "playtime_minutes, last_session_minutes, last_played, prefix_path, gog_id, "
                "launch_args, env_vars, pre_launch_cmd, post_exit_cmd, auto_backup, "
                "ludusavi_title, gamescope_enabled, upscale_enabled, upscale_model, "
                "hdr_enabled, fsr4_upgrade, optiscaler_dll, "
                "use_wined3d, use_wow64, use_wayland, no_esync, no_fsync, no_ntsync, "
                "legacy_mediaconv, video_decode_mode, vn_jp_locale, added_at "
                "FROM games WHERE id=?",
                (gid,)).fetchone()
            # Always archive on delete — captures prefix path even if never played
            if row:
                _name, _exe, _gtype, _store, _pt, _ls, _lp, _pfx_override, _gog_id = (
                    row[1], row[2], row[3], row[4], row[5] or 0, row[6] or 0, row[7], row[8] or "", row[9] or "")
                # Config fields
                (_launch_args, _env_vars, _pre_cmd, _post_cmd, _auto_backup,
                 _ludusavi_title, _gamescope, _upscale, _upscale_model,
                 _hdr, _fsr4, _optiscaler,
                 _wined3d, _wow64, _wayland, _no_esync, _no_fsync, _no_ntsync,
                 _legacy_mc, _video_decode, _vn_jp) = (
                    row[10] or "", row[11] or "", row[12] or "", row[13] or "", row[14] or 0,
                    row[15] or "", row[16] or 0, row[17] or 0, row[18] or "fast",
                    row[19] or 0, row[20] or "", row[21] or "",
                    row[22] or 0, row[23] or 0, row[24] or 0, row[25] or 0, row[26] or 0, row[27] or 0,
                    row[28] or 0, row[29] or "default", row[30] or 0)
                _added_at_orig = row[31] or ""
                _exe_filename = Path(_exe).name if _exe else ""
                # store_key must be a unique identifier per game:
                #   Steam  → AppID (exe_path); umu_store is just "steam", useless as key
                #   GOG    → gog_id (numeric GOG game ID); umu_store is just "gog", same for all GOG games
                #   Others → umu_store (may be empty for native/proton, keyed by exe_filename instead)
                if _gtype == "steam":
                    _store_key = _exe.strip() if _exe else ""
                elif _gtype == "gog":
                    _store_key = _gog_id.strip() if _gog_id else ""
                else:
                    _store_key = _store or ""
                # Resolve the actual prefix path on disk — do NOT call get_game_prefix()
                # because that function creates the directory as a side-effect, which
                # would cause an empty folder to be archived and "restored" later.
                _pfx_override_stripped = _pfx_override.strip()
                if _pfx_override_stripped:
                    _pfx_path = _pfx_override_stripped
                else:
                    _pfx_path = str(get_prefixes_root() / f"{slugify(_name)}_{gid}")
                # Only archive the prefix path if the folder actually exists on disk.
                # An empty/nonexistent path is useless to restore.
                if not Path(_pfx_path).exists():
                    _pfx_path = ""
                # Fetch category names for this game before deletion
                _cat_rows = con.execute(
                    "SELECT c.name FROM categories c "
                    "JOIN game_categories gc ON gc.category_id = c.id "
                    "WHERE gc.game_id=? ORDER BY c.name", (gid,)
                ).fetchall()
                _cat_names = ",".join(r[0] for r in _cat_rows) if _cat_rows else ""

                if _exe_filename or _store_key:
                    con.execute("""
                        INSERT INTO playtime_archive
                            (exe_filename, game_type, store_key, game_name,
                             playtime_minutes, last_session_minutes, last_played, archived_at, prefix_path,
                             launch_args, env_vars, pre_launch_cmd, post_exit_cmd, auto_backup,
                             ludusavi_title, gamescope_enabled, upscale_enabled, upscale_model,
                             hdr_enabled, fsr4_upgrade, optiscaler_dll,
                             use_wined3d, use_wow64, use_wayland, no_esync, no_fsync, no_ntsync,
                             legacy_mediaconv, video_decode_mode, vn_jp_locale, added_at, category_names)
                        VALUES (?, ?, ?, ?, ?, ?, ?, datetime('now'), ?,
                                ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                                ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, (_exe_filename, _gtype, _store_key, _name, _pt, _ls, _lp or "", _pfx_path,
                          _launch_args, _env_vars, _pre_cmd, _post_cmd, _auto_backup,
                          _ludusavi_title, _gamescope, _upscale, _upscale_model,
                          _hdr, _fsr4, _optiscaler,
                          _wined3d, _wow64, _wayland, _no_esync, _no_fsync, _no_ntsync,
                          _legacy_mc, _video_decode, _vn_jp, _added_at_orig, _cat_names))
            con.execute("DELETE FROM games WHERE id=?", (gid,))
            con.commit()
            con.close()
            # Delete cover file if it's in NAGO's artwork folder
            if row and row[0]:
                try:
                    p = Path(row[0])
                    if p.exists() and ART_PATH in p.parents:
                        p.unlink()
                except Exception as e:
                    _NAGOLog.session(f"[warn] _delete_game: failed to delete cover for game {gid}: {e}")
            # we no longer have a card to display its state on.
            self._running_games.pop(gid, None)
            to_remove = [appid for appid, entry in self._steam_watched.items()
                         if entry[0] == gid]
            for appid in to_remove:
                self._steam_watched.pop(appid, None)
            # Remove card in-place — no full rebuild, no flash.
            # _delete_game lives on LibraryPage, so self IS the library page.
            self._all_games = [g for g in self._all_games if g["id"] != gid]
            self._game_cats.pop(gid, None)
            card = self._cards.pop(gid, None)
            if card:
                card.hide()
                card.setParent(None)
                card.deleteLater()
            self._apply_filter(self._current_filter_text, self._current_category_id)

    def _toggle_hide_game(self, game: dict):
        """Toggle the hidden flag for a game, then remove its card from the current view."""
        gid        = game["id"]
        new_hidden = 0 if game.get("hidden", 0) else 1
        try:
            con = db_con()
            con.execute("UPDATE games SET hidden=? WHERE id=?", (new_hidden, gid))
            con.commit()
            con.close()
        except Exception as e:
            _NAGOLog.session(f"[warn] _toggle_hide_game: DB update failed for game {gid}: {e}")
            return
        # Update in-memory record so the context menu label is correct next time
        for g in self._all_games:
            if g["id"] == gid:
                g["hidden"] = new_hidden
                break
        # The card no longer belongs in this view — re-filter in-place
        self._apply_filter(self._current_filter_text, self._current_category_id)

    def _force_terminate_game(self, game: dict):
        """Force-kill a running game and everything it spawned (gamescope,
        umu, Proton, wine, and that prefix's wineserver). Steam games are
        handled separately via _kill_steam_appid_processes() since NAGO
        doesn't own that process — it only hands off a steam:// URL.

        After the kill, _poll_running_games() picks up the dead process on
        its next 2-second tick and runs the usual exit cleanup (playtime,
        post-exit command, auto-backup, card UI, upscaler teardown) — no
        need to duplicate any of that here."""
        gid   = game["id"]
        gname = game.get("name", "Game")
        gtype = game.get("game_type", "native")

        box = NAGOMessageBox(
            "warning",
            "Force Terminate",
            f"Force-terminate <b>{gname}</b>?<br><br>"
            f"This kills the game and everything it spawned immediately — "
            f"any unsaved progress will be lost.",
            parent=self,
            buttons=("Force Terminate", "Cancel"),
            default_button="Cancel",
        )
        box.exec()
        if box.result_label() != "Force Terminate":
            return

        if gtype == "steam":
            appid = (game.get("exe_path") or "").strip()
            if appid:
                killed = _kill_steam_appid_processes(appid)
                _NAGOLog.launch(f"[force-terminate] steam appid={appid}  killed={killed} processes")
                self.status_message.emit(f"Force-terminated {gname}")
            return

        entry = self._running_games.get(gid)
        if not entry:
            return
        proc = entry[0]
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except Exception:
            try:
                proc.kill()
            except Exception:
                pass

        if gtype in ("proton", "gog"):
            _pfx_override = (game.get("prefix_path") or "").strip()
            pfx = _pfx_override if (_pfx_override and Path(_pfx_override).exists()) \
                else str(get_game_prefix(gid, gname))
            # Runs on a daemon thread, not inline — this is a Qt slot on the
            # UI thread, and wineserver -k has a 5-second timeout that would
            # otherwise freeze the window while it waits. game_name is baked
            # into the log line (not left bare) because this fires async —
            # if another game launches before this completes, clear_launch()
            # will have wiped the buffer this is writing into, and without
            # attribution the kill-count line would read as belonging to
            # whatever's currently on top.
            _kill_wineserver_for_prefix_async(
                pfx, log_fn=lambda msg, _g=gname: _NAGOLog.launch(f"[force-terminate] {_g}: {msg}")
            )

        # Upscaler runs as its own separate Popen (no start_new_session), so
        # it's outside the process group killpg() above just targeted. The
        # normal exit path only sends it a polite .terminate() (SIGTERM) —
        # not good enough for a force-kill, since a stuck process (exactly
        # what this feature exists for) can ignore that. Kill it directly.
        _up = self._upscale_procs.pop(gid, None)
        if _up is not None:
            try:
                _up.kill()
                _NAGOLog.launch(f"[force-terminate] upscaler killed  pid={_up.pid}  game_id={gid}")
            except Exception:
                pass

        _NAGOLog.launch(f"[force-terminate] game_id={gid}  pid={proc.pid}")
        self.status_message.emit(f"Force-terminated {gname}")

    def _delete_prefix(self, game: dict):
        """Delete the WINEPREFIX for a Proton/GOG game after confirmation."""
        import shutil
        gid   = game["id"]
        gname = game.get("name", "Game")
        # Use prefix_path override if set, else derive from game id/name
        _pfx_override = (game.get("prefix_path") or "").strip()
        pfx = Path(_pfx_override) if _pfx_override else (
            get_prefixes_root() / f"{slugify(gname)}_{gid}")

        # Confirmation dialog with red save-game warning
        box = NAGOMessageBox(
            "warning",
            "Delete Prefix",
            f"Delete the Wine prefix for <b>{gname}</b>?<br><br>"
            f"This will permanently remove all Wine configuration, "
            f"installed runtime files, and any "
            f"<span style='color:#ef4444;font-weight:600;'>save files</span> "
            f"stored inside the prefix.<br><br>"
            f"<code>{pfx}</code><br><br>"
            f"<b>This cannot be undone.</b>",
            parent=self,
            buttons=("Delete", "Cancel"),
            default_button="Cancel",
        )
        box.exec()
        if box.result_label() != "Delete":
            return

        try:
            shutil.rmtree(pfx)
            self.status_message.emit(f"Prefix deleted: {gname}")
        except Exception as e:
            NAGOMessageBox(
                "critical", "Delete Failed",
                f"Could not delete prefix:<br><code>{e}</code>",
                parent=self,
            ).exec()

    def _run_file_in_prefix(self, game: dict):
        """Right-click 'Run File in Prefix' — same engine as the Edit Game
        dialog's button (_RunInPrefixWorker, shared at module scope), just
        triggered straight from the card instead of requiring the dialog
        to be open first.

        Mirrors the dialog button's prefix resolution exactly (override-or-
        get_game_prefix(), no rename-scan) on purpose — see session notes:
        the contextMenuEvent method that built this very menu already ran
        its own rename-safe resolution before the menu was shown, and wrote
        any correction into this same `game` dict and the DB. So even this
        simple override-or-derive lookup is reading an already-corrected
        value when one was needed. Adding a second resolution here would
        just be redundant, not safer.

        Proton/env come from the saved DB values (game.get("proton_path"),
        game.get("env_vars")) since there's no open dialog to read a live
        unsaved selection from — same pattern the main launch path uses.
        """
        gid   = game["id"]
        gname = game.get("name", "Game")

        if gid in self._prefix_run_workers:
            # Already running — menu would have shown Stop instead, but
            # guard anyway in case of a stale click.
            return

        umu_bin = find_umu_run()
        if not umu_bin:
            NAGOMessageBox.warning(
                self, "umu-launcher Not Found",
                "umu-launcher is required to run executables in a Proton prefix.\n\n"
                "Install it from Settings → umu-launcher."
            )
            return

        downloads = Path.home() / "Downloads"
        fallback_dir = str(downloads) if downloads.exists() else str(Path.home())
        start_dir = self.config.get("last_browse_dir", fallback_dir)
        exe_path, _ = QFileDialog.getOpenFileName(
            self, "Select File to Run in Prefix", start_dir,
            "Windows files (*.exe *.msi *.bat *.cmd);;All files (*)"
        )
        if not exe_path:
            return
        self.config["last_browse_dir"] = str(Path(exe_path).parent)

        # Prefix resolution — override-or-derive, same as the dialog button.
        # get_game_prefix() creates the directory if it doesn't exist yet
        # (umu/Proton bootstraps a fresh prefix on first run inside it,
        # same as a normal first launch would) — but that mkdir only
        # happens here, at click time, not while the menu was open.
        _pfx_override = (game.get("prefix_path") or "").strip()
        pfx = _pfx_override if (_pfx_override and Path(_pfx_override).exists()) \
            else str(get_game_prefix(gid, gname))

        proton = game.get("proton_path") or self.config.get("default_proton", "")
        proton_arg = ""
        if proton in (UMU_DEFAULT_SENTINEL, "GE-Proton"):
            proton_arg = proton
        elif proton:
            p = Path(proton).resolve()
            if p.is_file() and p.name == "proton":
                proton_arg = str(p.parent)
            elif p.is_dir():
                proton_arg = str(p)
            else:
                proton_arg = proton
        if not proton_arg:
            proton_arg = "GE-Proton"

        env = build_umu_env(
            os.environ.copy(),
            wineprefix=pfx,
            proton_path=proton_arg,
            game_id="umu-default",
            store="",
            extra_share_paths=[exe_path],
        )
        raw_env = (game.get("env_vars") or "").strip()
        if raw_env:
            for key, value in LibraryPage._parse_env_vars(raw_env).items():
                env[key] = value

        cwd = str(Path(exe_path).parent)
        worker = _RunInPrefixWorker(umu_bin, exe_path, env, cwd)
        exe_name = Path(exe_path).name
        card = self._cards.get(gid)

        def _clear_running():
            self._prefix_run_workers.pop(gid, None)
            if card is not None:
                card.set_prefix_running(False)

        def _on_done():
            _clear_running()
            self.status_message.emit(f"Finished running {exe_name} in {gname}'s prefix")
            _prefix_run_log_footer(gname, "finished ok")

        def _on_failed(err: str):
            _clear_running()
            NAGOMessageBox.warning(self, "Run in Prefix Failed", f"Failed to run {exe_name}:\n{err}")
            _prefix_run_log_footer(gname, f"failed: {err}")

        def _on_cancelled():
            _clear_running()
            self.status_message.emit(f"Force-terminated {exe_name} in {gname}'s prefix")
            _prefix_run_log_footer(gname, "force-terminated")

        worker.finished_ok.connect(_on_done)
        worker.failed.connect(_on_failed)
        worker.cancelled.connect(_on_cancelled)
        worker.finished.connect(worker.deleteLater)
        worker.start()
        self._prefix_run_workers[gid] = worker
        if card is not None:
            card.set_prefix_running(True)

        self.status_message.emit(f"Running {exe_name} in {gname}'s prefix…")
        _NAGOLog.launch(f"[run-in-prefix] {exe_name} → prefix={pfx}  proton={proton_arg}  umu={umu_bin}  game_id={gid}")
        _prefix_run_log_header(gname, exe_path, pfx, proton_arg, umu_bin, raw_env,
                                share_paths=env.get("STEAM_COMPAT_LIBRARY_PATHS", ""))

    def _stop_prefix_run(self, game: dict):
        """Right-click 'Stop Run in Prefix' — force-terminate the worker
        started by _run_file_in_prefix() for this game. Same killpg +
        wineserver cleanup the worker's terminate_now() already does for
        the dialog button's Stop path."""
        gid = game["id"]
        worker = self._prefix_run_workers.get(gid)
        if worker is not None:
            worker.terminate_now()

    def _reorder_games(self, src_id: int, target_id: int):
        """Move src_id to just before target_id in the sort order.
        target_id == -1 means append at end.
        Persists sort_pos as clean contiguous integers."""
        if src_id == target_id:
            return
        cat_id = getattr(self, "_current_category_id", None)
        ids = [g["id"] for g in self._games]
        if src_id not in ids:
            return
        if target_id != -1 and target_id not in ids:
            return

        new_order = [gid for gid in ids if gid != src_id]
        if target_id == -1:
            new_order.append(src_id)
        else:
            tgt_idx = new_order.index(target_id)
            new_order.insert(tgt_idx, src_id)

        con = db_con()
        try:
            if cat_id is None:
                for pos, gid in enumerate(new_order):
                    con.execute("UPDATE games SET sort_pos=? WHERE id=?", (pos, gid))
            else:
                for pos, gid in enumerate(new_order):
                    con.execute(
                        "UPDATE game_categories SET sort_pos=? WHERE game_id=? AND category_id=?",
                        (pos, gid, cat_id)
                    )
            con.commit()
        finally:
            con.close()

        # Update in-memory order
        id_to_game = {g["id"]: g for g in self._games}
        self._games[:] = [id_to_game[gid] for gid in new_order]

        if cat_id is None:
            id_to_all = {g["id"]: g for g in self._all_games}
            for pos, gid in enumerate(new_order):
                if gid in id_to_all:
                    id_to_all[gid]["sort_pos"] = pos
            self._all_games.sort(key=lambda g: g.get("sort_pos", 0))

        # Reflow positions without destroying widgets
        self._reflow()

    def pick_cover(self, game: dict):
        key = self.config.get("sgdb_key", "").strip().strip('"').strip("'")
        # Open the dialog even without an API key — the local image section works without one.
        # If there's no key the SGDB search section will show a notice instead of results.
        dlg = CoverPickerDialog(key, game["name"], self.parent())
        dlg.cover_selected.connect(lambda url: self._download_cover(url, game))
        dlg.cover_local.connect(lambda path: self._use_local_cover(path, game))
        dlg.cover_cleared.connect(lambda: self._clear_cover_art(game))
        dlg.exec()

    def _download_cover(self, url: str, game: dict):
        self.status_message.emit("Downloading cover…")
        if hasattr(self, "_dw") and self._dw is not None:
            # Old code did quit()+deleteLater() here — broken for this worker:
            # SGDBWorker.run() blocks inside requests.get (up to a 30s cover
            # download), so quit() (which only stops a Qt event loop) does
            # nothing, and deleteLater() then destroys a still-running thread,
            # which Qt turns into a fatal abort. stop_safely() disconnects,
            # waits briefly, and parks it to finish detached if it's still
            # mid-download — the same crash-proof teardown every worker now
            # has from the _NAGOThread base.
            self._dw.stop_safely()
            self._dw = None
        self._dw = SGDBWorker(self.config.get("sgdb_key", ""))
        self._dw.cover_downloaded.connect(self._on_cover_downloaded)
        self._dw.error.connect(lambda e: (
            self.status_message.emit(f"Cover error: {e}"),
            _NAGOLog.session(f"[warn] Auto cover fetch failed: {e}"),
        ))
        self._dw.finished.connect(self._dw.deleteLater)
        self._dw.download_cover(url, game["id"], game.get("name", ""))

    def _refresh_single_cover(self, gid: int, path: str):
        """Load and display a cover on a single card without a full reload."""
        if gid not in self._cards:
            return
        tw = ThumbnailWorker([(gid, path)])
        tw.loaded.connect(self._on_thumb_loaded)
        # Remove from the live-workers list only after the thread is fully done,
        # then let deleteLater clean up the Qt object.  Storing in a list (not a
        # single slot) prevents a second call from GC-ing a still-running thread.
        tw.finished.connect(lambda: self._single_cover_workers.discard(tw))
        tw.finished.connect(tw.deleteLater)
        self._single_cover_workers.add(tw)
        tw.start()

    def _on_cover_downloaded(self, gid: int, path: str):
        con = db_con()
        # Delete old cover file if different from the new one
        row = con.execute("SELECT cover_path FROM games WHERE id=?", (gid,)).fetchone()
        if row and row[0] and row[0] != path:
            try:
                p = Path(row[0])
                if p.exists() and ART_PATH in p.parents:
                    p.unlink()
            except Exception as e:
                _NAGOLog.session(f"[warn] _on_cover_downloaded: failed to delete old cover for game {gid}: {e}")
        con.commit()
        con.close()
        for g in self._all_games:
            if g["id"] == gid:
                g["cover_path"] = path
                break
        self.status_message.emit("Cover saved!")
        self._refresh_single_cover(gid, path)

    def _use_local_cover(self, src_path: str, game: dict):
        """Copy a local image into the NAGO artwork folder and update the DB."""
        try:
            ART_PATH.mkdir(parents=True, exist_ok=True)
            slug = slugify(game.get("name", "game"))
            filename = f"{slug}_{game['id']}.png"
            out_path = ART_PATH / filename
            img = _pil_image().open(src_path).convert("RGBA")
            img.save(str(out_path), "PNG")
            con = db_con()
            # Delete old cover if different
            old = game.get("cover_path", "")
            if old and old != str(out_path):
                try:
                    p = Path(old)
                    if p.exists() and ART_PATH in p.parents:
                        p.unlink()
                except Exception as e:
                    _NAGOLog.session(f"[warn] _use_local_cover: failed to delete old cover for game {game.get('id')}: {e}")
            con.commit()
            con.close()
            for g in self._all_games:
                if g["id"] == game["id"]:
                    g["cover_path"] = str(out_path)
                    break
            self.status_message.emit("Cover saved!")
            self._refresh_single_cover(game["id"], str(out_path))
        except Exception as e:
            self.status_message.emit(f"Cover error: {e}")


    def _clear_cover_art(self, game: dict):
        """Remove cover art — clear DB and delete file if it's in NAGO's artwork folder."""
        old_path = game.get("cover_path", "")
        con = db_con()
        con.execute("UPDATE games SET cover_path='' WHERE id=?", (game["id"],))
        con.commit()
        con.close()
        if old_path:
            try:
                p = Path(old_path)
                if p.exists() and ART_PATH in p.parents:
                    p.unlink()
            except Exception as e:
                _NAGOLog.session(f"[warn] _clear_cover_art: failed to delete cover for game {game.get('id')}: {e}")
        gid = game["id"]
        for g in self._all_games:
            if g["id"] == gid:
                g["cover_path"] = ""
                break
        if gid in self._cards:
            self._cards[gid]._has_cover = False
            self._cards[gid]._set_placeholder()


# ── Category Assign Dialog (shown when editing/adding a game) ─────────────────
class CategoryAssignDialog(_NAGODialog):
    """Checkboxes for all categories; used inside GameDialog."""
    def __init__(self, selected_ids: list[int], parent=None):
        super().__init__(parent)
        self.setWindowFlags(Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        self.setMinimumWidth(320 + self._SHADOW * 2)
        self._checks: dict[int, NAGOCheckBox] = {}

        outer = QVBoxLayout(self)
        outer.setContentsMargins(self._SHADOW, self._SHADOW, self._SHADOW, self._SHADOW)
        outer.setSpacing(0)
        root = QFrame()
        root.setObjectName("dialogRoot")
        outer.addWidget(root)

        layout = QVBoxLayout(root)
        layout.setContentsMargins(24, 24, 24, 24)
        layout.setSpacing(10)

        title = QLabel("Assign Categories")
        title.setObjectName("dlgTitle")
        layout.addWidget(title)

        cats = db_get_categories()
        if cats:
            for cat in cats:
                cb = NAGOCheckBox(cat["name"])
                cb.setChecked(cat["id"] in selected_ids)
                self._checks[cat["id"]] = cb
                layout.addWidget(cb)
        else:
            layout.addWidget(QLabel("No categories yet — add some in the sidebar."))

        layout.addSpacing(8)
        btn_row = QHBoxLayout()
        cancel = QPushButton("  Cancel"); cancel.setObjectName("secondary")
        cancel.setIcon(ph_icon("x", 22))
        cancel.clicked.connect(self.reject)
        ok = QPushButton("Done"); ok.setObjectName("primary")
        ok.clicked.connect(self.accept)
        btn_row.addWidget(cancel); btn_row.addStretch(); btn_row.addWidget(ok)
        layout.addLayout(btn_row)

    def selected_ids(self) -> list[int]:
        return [cid for cid, cb in self._checks.items() if cb.isChecked()]


# ── Drag-bar widget for frameless window movement ─────────────────────────────
class DragBar(QWidget):
    """Topbar that drags the window using the window manager."""
    def __init__(self, main_window, parent=None):
        super().__init__(parent)
        self._win = main_window
        self.setMouseTracking(True)

    def _is_interactive_child(self, pos) -> bool:
        child = self.childAt(pos)
        while child is not None and child is not self:
            if isinstance(child, (QPushButton, QLineEdit, QComboBox)):
                return True
            child = child.parentWidget()
        return False

    def mouseMoveEvent(self, event):
        if self._is_interactive_child(event.position().toPoint()):
            event.ignore()
        else:
            super().mouseMoveEvent(event)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            if not self._is_interactive_child(event.position().toPoint()):
                # Use the system window manager to move the window
                handle = self._win.windowHandle()
                if handle is not None:
                    handle.startSystemMove()
                    event.accept()
                    return
        super().mousePressEvent(event)

    def mouseDoubleClickEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            if not self._is_interactive_child(event.position().toPoint()):
                self._win._toggle_max()
                event.accept()
                return
        super().mouseDoubleClickEvent(event)



# ── Toast Notification ─────────────────────────────────────────────────────────
class _ToastNotification(QWidget):
    """Floating toast that fades in/out at the bottom-right of the parent."""

    _PADDING_H = 24
    _PADDING_V = 12
    _RADIUS    = 10

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setAttribute(Qt.WidgetAttribute.WA_TransparentForMouseEvents)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self._msg = ""
        self._opacity = 0.0

        self._opacity_effect = QGraphicsOpacityEffect(self)
        self.setGraphicsEffect(self._opacity_effect)
        self._opacity_effect.setOpacity(0)

        self._fade_in = QPropertyAnimation(self._opacity_effect, b"opacity")
        self._fade_in.setDuration(180)
        self._fade_in.setEasingCurve(QEasingCurve.Type.OutCubic)
        self._fade_in.setStartValue(0.0)
        self._fade_in.setEndValue(1.0)

        self._fade_out = QPropertyAnimation(self._opacity_effect, b"opacity")
        self._fade_out.setDuration(350)
        self._fade_out.setEasingCurve(QEasingCurve.Type.InCubic)
        self._fade_out.setStartValue(1.0)
        self._fade_out.setEndValue(0.0)
        self._fade_out.finished.connect(self.hide)

        self._hide_timer = QTimer(self)
        self._hide_timer.setSingleShot(True)
        self._hide_timer.timeout.connect(self._fade_out.start)

        self.hide()

    def show_message(self, msg: str, duration: int = 3000):
        self._hide_timer.stop()
        self._fade_out.stop()
        self._msg = msg
        self._resize_to_text()
        self._reposition()
        self.show()
        self.raise_()
        self._fade_in.start()
        self._hide_timer.start(duration)

    def _resize_to_text(self):
        fm = QFontMetrics(QFont("Segoe UI", 11, QFont.Weight.Medium.value))
        tw = fm.horizontalAdvance(self._msg)
        th = fm.height()
        # Add shadow room: 16px extra on each side
        shadow_pad = 16
        w = tw + self._PADDING_H * 2 + shadow_pad * 2
        h = th + self._PADDING_V * 2 + shadow_pad * 2
        self.setFixedSize(w, h)

    def _reposition(self):
        parent = self.parent()
        if parent is None:
            return
        # Use the central widget's geometry if parent is a QMainWindow
        # to avoid coordinate offset from the window frame/titlebar
        cw = parent.centralWidget() if hasattr(parent, "centralWidget") else None
        if cw:
            geo = cw.geometry()
            pw = geo.width()
            ph = geo.height()
            ox = geo.x()
            oy = geo.y()
        else:
            pw = parent.width()
            ph = parent.height()
            ox, oy = 0, 0
        margin = 24
        x = ox + pw - self.width()  - margin
        y = oy + ph - self.height() - margin
        self.move(x, y)

    def paintEvent(self, event):
        p = QPainter(self)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        p.setRenderHint(QPainter.RenderHint.TextAntialiasing)

        shadow_pad = 16
        rect = QRectF(
            shadow_pad, shadow_pad,
            self.width()  - shadow_pad * 2,
            self.height() - shadow_pad * 2
        )

        # Drop shadow — multiple passes with decreasing opacity
        for i in range(8, 0, -1):
            sr = rect.adjusted(-i * 0.5, -i * 0.5, i * 0.5, i * 0.5 + i)
            alpha = int(40 * (i / 8))
            p.setPen(Qt.PenStyle.NoPen)
            p.setBrush(QColor(0, 0, 0, alpha))
            p.drawRoundedRect(sr, self._RADIUS + 2, self._RADIUS + 2)

        # Background
        p.setPen(QPen(QColor("#44444e"), 1))
        p.setBrush(QColor("#2d2d34"))
        p.drawRoundedRect(rect, self._RADIUS, self._RADIUS)

        # Text
        font = QFont("Segoe UI", 11, QFont.Weight.Medium.value)
        p.setFont(font)
        p.setPen(QColor("#e4e4e7"))
        p.drawText(rect, Qt.AlignmentFlag.AlignCenter, self._msg)

        p.end()

    def resizeEvent(self, event):
        super().resizeEvent(event)


# ── NAGO Logger ────────────────────────────────────────────────────────────────
# Global in-memory log store. Two sections: session (startup) and last launch.
# Written once at startup for session info, overwritten on every game launch.

class _NAGOLog:
    """Singleton in-memory log store shared across the app."""
    _session_lines:    "collections.deque[str]" = None   # initialised below
    _launch_lines:     "collections.deque[str]" = None
    _winetricks_lines: "collections.deque[str]" = None
    _prefix_lines:     "collections.deque[str]" = None

    @classmethod
    def _ts(cls) -> str:
        return _fmt_stamp(datetime.datetime.now())

    @classmethod
    def session(cls, line: str):
        stamped = f"[{cls._ts()}]  {line}"
        cls._session_lines.append(stamped)
        if "[warn]" in line:
            print(stamped, file=sys.stderr)

    @classmethod
    def launch(cls, line: str):
        cls._launch_lines.append(f"[{cls._ts()}]  {line}")

    @classmethod
    def winetricks(cls, line: str):
        cls._winetricks_lines.append(f"[{cls._ts()}]  {line}")

    @classmethod
    def prefix_run(cls, line: str):
        cls._prefix_lines.append(line)

    @classmethod
    def clear_launch(cls):
        cls._launch_lines.clear()

    @classmethod
    def clear_winetricks(cls):
        cls._winetricks_lines.clear()

    @classmethod
    def clear_prefix_run(cls):
        cls._prefix_lines.clear()

    @classmethod
    def session_text(cls) -> str:
        return "\n".join(cls._session_lines) if cls._session_lines else "(no session data yet)"

    @classmethod
    def launch_text(cls) -> str:
        return "\n".join(cls._launch_lines) if cls._launch_lines else "(no launch recorded yet)"

    @classmethod
    def winetricks_text(cls) -> str:
        return "\n".join(cls._winetricks_lines) if cls._winetricks_lines else "(no winetricks run yet)"

    @classmethod
    def prefix_run_text(cls) -> str:
        return "\n".join(cls._prefix_lines) if cls._prefix_lines else "(no installer run yet)"


# Initialise deques after class definition so maxlen cap is always enforced.
_NAGOLog._session_lines    = collections.deque(maxlen=2000)
_NAGOLog._launch_lines     = collections.deque(maxlen=2000)
_NAGOLog._winetricks_lines = collections.deque(maxlen=2000)
_NAGOLog._prefix_lines     = collections.deque(maxlen=5000)


# ── Module-level signal bridge ─────────────────────────────────────────────────
# Allows background workers (e.g. _RunInPrefixWorker inside GameDialog) to push
# log lines to LogsPage without holding a direct widget reference.
class _PrefixRunBridge(QObject):
    line_ready = pyqtSignal(str)   # emitted per stdout/stderr line

_prefix_run_bridge = _PrefixRunBridge()


class _WinetricksBridge(QObject):
    line_ready = pyqtSignal(str)   # emitted per stdout/stderr line

_winetricks_bridge = _WinetricksBridge()


def _log_session_info(config: dict):
    """Write verbose NAGO session info to the log at startup."""
    from PyQt6.QtCore import QT_VERSION_STR, PYQT_VERSION_STR
    _NAGOLog.session("=" * 64)
    _NAGOLog.session(f"NAGO Launcher  build {BUILD}  /  version {VERSION}")
    _NAGOLog.session(f"Python         {sys.version}")
    _NAGOLog.session(f"Qt             {QT_VERSION_STR}  (PyQt6 {PYQT_VERSION_STR})")
    _NAGOLog.session(f"Platform       {platform.system()} {platform.release()} "
                     f"({platform.machine()})")
    _NAGOLog.session("-" * 64)
    _NAGOLog.session(f"Config path    {CFG_PATH}")
    _NAGOLog.session(f"DB path        {DB_PATH}")
    _NAGOLog.session(f"Art path       {ART_PATH}")
    _NAGOLog.session(f"Prefixes path  {config.get('prefixes_path') or PREFIXES_PATH}")
    _NAGOLog.session(f"Logs path      {NAGO_HOME / 'logs'}")
    _NAGOLog.session("-" * 64)
    # Proton
    default_proton = config.get("default_proton", "")
    if default_proton:
        pver = _proton_version_str(default_proton)
        _NAGOLog.session(f"Default Proton {default_proton}")
        _NAGOLog.session(f"Proton version {pver or '(could not determine)'}")
    else:
        _NAGOLog.session("Default Proton (not set)")
    # umu
    umu_path = find_umu_run() or "(not found)"
    umu_ver  = get_umu_version() or "(unknown)"
    _NAGOLog.session(f"umu-run path   {umu_path}")
    _NAGOLog.session(f"umu version    {umu_ver}")
    _NAGOLog.session(f"umu always-on for Proton")
    _NAGOLog.session("-" * 64)
    # Screen
    screen = QApplication.primaryScreen()
    if screen:
        geo = screen.geometry()
        dpr = screen.devicePixelRatio()
        _NAGOLog.session(f"Screen         {geo.width()}×{geo.height()} logical  /  DPR={dpr}")
    _NAGOLog.session(f"Accent color   {config.get('accent_color', DEFAULT_ACCENT)}")
    _NAGOLog.session(f"Card width     {config.get('card_width', CARD_W)}px")
    _NAGOLog.session("=" * 64)


def _proton_version_str(proton_path: str) -> str:
    """Try to read the Proton version from a proton_path executable.
    proton_path points to the 'proton' executable inside the Proton directory,
    so all lookups use .parent to get the containing directory."""
    if not proton_path:
        return ""
    # Auto-managed selections have no real path — report them by name.
    if proton_path == UMU_DEFAULT_SENTINEL:
        return "UMU-Proton (auto)"
    if proton_path == "GE-Proton":
        return "GE-Proton (auto)"
    try:
        proton_dir = Path(proton_path).parent
        ver_file = proton_dir / "version"
        if ver_file.exists():
            return ver_file.read_text().strip().split()[-1]
        # Some Proton builds put it in files/version
        ver_file2 = proton_dir / "files" / "version"
        if ver_file2.exists():
            return ver_file2.read_text().strip().split()[-1]
        # Fall back to directory name
        return proton_dir.name
    except Exception:
        return Path(proton_path).parent.name


# umu prints its resolved Proton as it starts up, e.g.:
#   INFO: Using UMU-Latest
#   INFO: Running 'UMU-Proton-10.0-4' using runtime 'sniper'
# We read those back from the per-game log after the run to report the EXACT
# build umu chose for the auto options (where NAGO never set a PROTONPATH and so
# can't know the path pre-launch).
_UMU_CHANNEL_RE = re.compile(r"INFO:\s*Using\s+(.+?)\s*$")
_UMU_BUILD_RE   = re.compile(r"INFO:\s*Running\s+'([^']+)'\s+using\s+runtime")


def _resolve_proton_from_umu_log(log_path: Path) -> tuple[str, str]:
    """Parse a per-game launch log for umu's resolved Proton build and channel.

    Returns (build, channel) — e.g. ("UMU-Proton-10.0-4", "UMU-Latest").
    Either field may be "" if the corresponding line isn't present (game failed
    to start before umu logged, killed instantly, or a future umu changes the
    format). Fails safe: an unparseable log yields ("", "").
    """
    build = ""
    channel = ""
    try:
        with open(log_path, "r", encoding="utf-8", errors="replace") as f:
            for line in f:
                if not channel:
                    m = _UMU_CHANNEL_RE.search(line)
                    if m:
                        channel = m.group(1).strip()
                if not build:
                    m = _UMU_BUILD_RE.search(line)
                    if m:
                        build = m.group(1).strip()
                if build and channel:
                    break
    except Exception:
        pass
    return build, channel


def _find_proton_install_dir(channel: str, build: str) -> str:
    """Locate the on-disk directory of the Proton umu resolved to.

    Looks at real directories only — never guesses. Checks, in order:
      • umu's managed channel dir   (~/.local/share/umu/<channel>, e.g. UMU-Latest)
      • compatibilitytools.d dirs   (named <channel> or <build>)
    Returns the resolved (symlinks followed) absolute path, or "" if nothing on
    disk matches — in which case the caller reports the build name alone.
    """
    candidates = []
    umu_data = XDG_DATA / "umu"
    for name in (channel, build):
        if name:
            # umu keeps its managed builds under compatibilitytools/ (e.g.
            # UMU-Latest); older/other layouts put them directly under umu/.
            candidates.append(umu_data / "compatibilitytools" / name)
            candidates.append(umu_data / name)
    compat_roots = [
        Path.home() / ".steam" / "root" / "compatibilitytools.d",
        XDG_DATA / "Steam" / "compatibilitytools.d",
        Path.home() / ".var" / "app" / "com.valvesoftware.Steam" /
            "data" / "Steam" / "compatibilitytools.d",
    ]
    for root in compat_roots:
        for name in (build, channel):
            if name:
                candidates.append(root / name)
    for c in candidates:
        try:
            if c.exists():
                return os.path.realpath(c)
        except Exception:
            continue
    return ""


def _log_launch(game: dict, cmd: list, env_diff: dict, prefix_path: str,
                umu_path: str, umu_fix: str, proton_path: str,
                gamescope_active: bool = False,
                gamescope_res: tuple | None = None,
                hdr_tool: str = "",
                hdr_capable: list[str] | None = None,
                share_paths: str = ""):
    """Write a verbose launch record. Called just before exec."""
    _NAGOLog.clear_launch()
    gt = game.get("game_type", "?")
    _NAGOLog.launch("=" * 64)
    _NAGOLog.launch(f"LAUNCH  {game.get('name', '?')}  (id={game.get('id', '?')})")
    _NAGOLog.launch(f"Type           {gt}")
    _NAGOLog.launch("-" * 64)
    # Executable
    _NAGOLog.launch(f"Executable     {game.get('exe_path', '(none)')}")
    if game.get('launch_args'):
        _NAGOLog.launch(f"Launch args    {game['launch_args']}")
    # Full command
    _NAGOLog.launch(f"Full command    {' '.join(str(c) for c in cmd)}")
    _NAGOLog.launch("-" * 64)
    # Proton / Wine
    if gt in ("proton", "gog") and proton_path:
        pver = _proton_version_str(proton_path)
        # The two auto options carry an internal marker, not a real path. umu
        # resolves (and may download) the actual build at runtime, so we can't
        # know the path here — print a readable description instead of the marker.
        # The exact resolved build + path is appended to the EXIT block, read
        # back from umu's own output once the game has started.
        if proton_path == UMU_DEFAULT_SENTINEL:
            _NAGOLog.launch("Proton path    (umu default — UMU-Proton, resolved at launch)")
        elif proton_path == "GE-Proton":
            _NAGOLog.launch("Proton path    (GE-Proton auto — resolved at launch)")
        else:
            _NAGOLog.launch(f"Proton path    {proton_path}")
        _NAGOLog.launch(f"Proton version {pver or '(could not determine)'}")
        # Readable summary above the raw env diff below — the diff alone would
        # bury esync/fsync as two extra alphabetized lines among everything
        # else, and ntsync now carries two vars in opposite polarity (see the
        # injection comment in _launch_game), which isn't obvious to eyeball
        # from raw 0/1 values without re-deriving which var means what.
        _sync_e = "off" if game.get("no_esync")  else "on"
        _sync_f = "off" if game.get("no_fsync")  else "on"
        _sync_n = "off" if game.get("no_ntsync") else "on"
        _NAGOLog.launch(f"Sync           esync={_sync_e}  fsync={_sync_f}  ntsync={_sync_n}")
    # Prefix
    if prefix_path:
        _NAGOLog.launch(f"Prefix path    {prefix_path}")
        pf_exists = Path(prefix_path).exists()
        _NAGOLog.launch(f"Prefix exists  {pf_exists}")
    # Sandbox share paths — see _filesystem_share_root for why this exists:
    # without it, paths outside $HOME (a second drive/mount) can read as
    # silently missing inside umu's pressure-vessel sandbox even though
    # they're really there. Only printed when non-empty so unaffected
    # launches (everything under $HOME) don't get a noise line.
    if share_paths:
        _NAGOLog.launch(f"Share paths    {share_paths}  (outside $HOME, exposed to sandbox)")
    # umu
    if game.get("umu_enabled"):
        _NAGOLog.launch("-" * 64)
        _NAGOLog.launch(f"umu-run path   {umu_path or '(not found)'}")
        umu_ver = get_umu_version() or "(unknown)"
        _NAGOLog.launch(f"umu version    {umu_ver}")
        _NAGOLog.launch(f"umu GameID     {game.get('umu_gameid') or '(auto)'}")
        _NAGOLog.launch(f"umu store      {game.get('umu_store') or '(none)'}")
        _NAGOLog.launch(f"Protonfix      {umu_fix or '(none applied)'}")
    # Japanese locale
    if game.get("vn_jp_locale"):
        _NAGOLog.launch("-" * 64)
        _NAGOLog.launch("Japanese locale  ON  (LANG=ja_JP.UTF-8  HOST_LC_ALL=ja_JP.UTF-8)")
    # Video decode mode
    _vdm = game.get("video_decode_mode", "default") or "default"
    if _vdm != "default":
        _NAGOLog.launch("-" * 64)
        _NAGOLog.launch(f"Video decode     {_vdm}  ({'PROTON_MEDIA_USE_GST=1' if _vdm == 'winegstreamer' else 'default winedmo backend'})")
    # Pre/post hooks + gamescope
    if game.get("gamescope_enabled"):
        if gamescope_active:
            # Only claim --hdr-enabled when it was actually appended (requires
            # gamescope v3.13+). DXVK_HDR=1 may or may not be set depending on
            # game_type — gated on _is_proton_runtime upstream.
            if game.get("hdr_enabled") and not game.get("upscale_enabled") and _gamescope_supports_hdr():
                _gs_note = "  + --hdr-enabled"
                if game.get("game_type") in ("proton", "gog"):
                    _gs_note += "  DXVK_HDR=1"
            else:
                _gs_note = ""
            _NAGOLog.launch("-" * 64)
            _gs_res_str = (f"{gamescope_res[0]}x{gamescope_res[1]}@{gamescope_res[2]}Hz"
                           if gamescope_res else "(resolution unavailable)")
            _NAGOLog.launch(f"Gamescope        on  ({_gs_res_str}{_gs_note})")
        else:
            # `_gamescope_active` is False for three reasons. Report the actual
            # one instead of always blaming the binary — Steam games and the
            # AI-upscale conflict both produce the same surface symptom.
            if game.get("game_type") == "steam":
                _gs_reason = "not applied to Steam-type games"
            elif not shutil.which("gamescope"):
                _gs_reason = "binary not found on PATH"
            elif game.get("upscale_enabled"):
                _gs_reason = "conflicts with AI upscaling (forced off)"
            else:
                _gs_reason = "skipped"
            _NAGOLog.launch("-" * 64)
            _NAGOLog.launch(f"Gamescope        SKIPPED — {_gs_reason}")
    # HDR — mirror the gamescope reporting so the user can confirm in the log
    # whether HDR actually fired or got skipped (silent skip before now).
    # State is precomputed in _launch_game and passed in — re-running the
    # detection here would mean a second subprocess call per HDR-enabled launch.
    if game.get("hdr_enabled"):
        _NAGOLog.launch("-" * 64)
        if game.get("game_type") == "steam":
            _NAGOLog.launch("HDR              SKIPPED — not applied to Steam-type games")
        elif game.get("upscale_enabled"):
            _NAGOLog.launch("HDR              SKIPPED — conflicts with AI upscaling (forced off)")
        elif not hdr_tool:
            _NAGOLog.launch("HDR              SKIPPED — no compatible tool (need kscreen-doctor or gdctl)")
        elif not hdr_capable:
            _NAGOLog.launch("HDR              SKIPPED — no HDR-capable monitors detected")
        else:
            _NAGOLog.launch(f"HDR              on  (tool={hdr_tool}, monitors={', '.join(hdr_capable)})")
    if game.get("pre_launch_cmd"):
        _NAGOLog.launch("-" * 64)
        _NAGOLog.launch(f"Pre-launch cmd {game['pre_launch_cmd']}")
    if game.get("post_exit_cmd"):
        _NAGOLog.launch(f"Post-exit cmd  {game['post_exit_cmd']}")
    # Env diff
    _NAGOLog.launch("-" * 64)
    if env_diff:
        _NAGOLog.launch("Env overrides  (NAGO-set, diff from system):")
        for k, v in sorted(env_diff.items()):
            _NAGOLog.launch(f"  {k}={v}")
    else:
        _NAGOLog.launch("Env overrides  (none)")
    _NAGOLog.launch("=" * 64)


def _resolve_window_title_via_xprop(game_name: str, fallback: str) -> str:
    """
    Use xprop to find the best-matching window title for this game.
    Gets all visible X11 window titles, then fuzzy-matches against
    the game name (case-insensitive word overlap).
    No PID matching — works regardless of Wine process tree depth.
    Returns the exact window title string, or fallback if nothing matches.
    """
    xprop_bin = shutil.which("xprop")
    if not xprop_bin:
        return fallback

    try:
        r = subprocess.run(
            [xprop_bin, "-root", "_NET_CLIENT_LIST"],
            capture_output=True, text=True, timeout=5
        )
        wid_matches = re.findall(r'0x[0-9a-fA-F]+', r.stdout)
    except Exception:
        return fallback

    titles = []
    for wid in wid_matches:
        try:
            r2 = subprocess.run(
                [xprop_bin, "-id", wid, "WM_NAME"],
                capture_output=True, text=True, timeout=3
            )
            title_match = re.search(r'WM_NAME\(\w+\)\s*=\s*"(.+)"', r2.stdout)
            if title_match:
                titles.append(title_match.group(1))
        except Exception:
            continue

    if not titles:
        return fallback

    name_words = [w.lower() for w in re.split(r'\W+', game_name) if len(w) > 2]
    if not name_words:
        return fallback

    best_title = None
    best_score = 0
    for title in titles:
        title_lower = title.lower()
        score = sum(1 for w in name_words if w in title_lower)
        if score > best_score:
            best_score = score
            best_title = title

    if best_score > 0 and best_title:
        return best_title
    return fallback


# ── Upscaler launch worker ─────────────────────────────────────────────────────
class _UpscalerLaunchWorker(_NAGOThread):
    """
    Waits for a game window to appear, resolves its title via xprop, then
    launches the upscaler process.  Replaces the threading.Timer approach so
    all Qt-touching code (NAGOLog, _upscale_procs) is called via a signal on
    the main thread rather than from a raw Python thread.
    """
    ready = pyqtSignal(str, str, str, int, str)  # bin, title, model, game_id, log_msg

    def __init__(self, upscale_bin: str, upscale_model: str,
                 game: dict, exe_stem: str,
                 initial_delay: float = 4.0, parent=None):
        super().__init__(parent)
        self._bin           = upscale_bin
        self._model         = upscale_model
        self._game          = game
        self._exe_stem      = exe_stem
        self._initial_delay = initial_delay

    def run(self):
        time.sleep(self._initial_delay)
        game_name = self._game.get("name", self._exe_stem)
        title = None
        log_msg = ""
        for attempt in range(5):
            found = _resolve_window_title_via_xprop(game_name, "")
            if found:
                title = found
                log_msg = (f"  xprop          matched title {title!r} "
                           f"(attempt {attempt + 1})")
                break
            if attempt < 4:
                time.sleep(2)
        if not title:
            title = self._exe_stem
            log_msg = (f"  xprop          no match for {game_name!r} — "
                       f"falling back to exe stem {title!r}")
        self.ready.emit(self._bin, title, self._model, self._game["id"], log_msg)


# ── Logs Page ──────────────────────────────────────────────────────────────────
class LogsPage(QWidget):
    """Read-only log viewer — Session info, Last Launch, and Game Log tabs."""

    TAB_SESSION    = 0
    TAB_LAUNCH     = 1
    TAB_GAMELOG    = 2
    TAB_WINETRICKS = 3
    TAB_PREFIX_RUN = 4

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("logsPage")
        self._log_file_path: str = ""
        self._gamelog_offset: int = 0   # bytes of the log already shown (tail tracking)
        self._watcher = None
        self._build()

    def _build(self):
        layout = QVBoxLayout(self)
        layout.setContentsMargins(32, 24, 32, 24)
        layout.setSpacing(14)

        # Header
        header_row = QHBoxLayout()
        title = QLabel("Logs")
        title.setObjectName("settingsTitle")
        header_row.addWidget(title)
        header_row.addStretch()

        copy_btn = QPushButton("  Copy to Clipboard")
        copy_btn.setObjectName("secondary")
        copy_btn.setIcon(ph_icon("copy", 22))
        copy_btn.setFixedHeight(32)
        copy_btn.clicked.connect(self._copy_current)
        header_row.addWidget(copy_btn)

        self._clear_btn = QPushButton("  Clear Log")
        self._clear_btn.setObjectName("secondary")
        self._clear_btn.setIcon(ph_icon("eraser", 22))
        self._clear_btn.setFixedHeight(32)
        self._clear_btn.clicked.connect(self._clear_current)
        header_row.addWidget(self._clear_btn)

        layout.addLayout(header_row)

        # Tabs
        self._tabs = QTabWidget()
        self._tabs.setObjectName("dlgTabs")
        layout.addWidget(self._tabs, 1)

        # Session tab
        self._session_edit = self._make_text_edit()
        self._tabs.addTab(self._session_edit, "Session")

        # Last Launch tab
        self._launch_edit = self._make_text_edit()
        self._tabs.addTab(self._launch_edit, "Last Launch")

        # Game Log tab
        self._gamelog_edit = self._make_text_edit()
        self._tabs.addTab(self._gamelog_edit, "Game Log")

        # Winetricks tab
        self._winetricks_edit = self._make_text_edit()
        self._tabs.addTab(self._winetricks_edit, "Winetricks")

        # Run in Prefix tab
        self._prefix_edit = self._make_text_edit()
        self._tabs.addTab(self._prefix_edit, "Run in Prefix")

        self._tabs.currentChanged.connect(self._on_tab_changed)
        # Initial state — Session tab is active, clear not applicable
        self._clear_btn.setVisible(False)

    def _make_text_edit(self) -> QTextEdit:
        te = QTextEdit()
        te.setReadOnly(True)
        te.setObjectName("logView")
        return te

    def set_log_file(self, path: str):
        """Called when a new game is launched — update the watched log file."""
        self._log_file_path = path
        self._gamelog_offset = 0   # new file — read from the top next time
        # If Game Log tab is active, switch watcher to new file immediately
        if self._tabs.currentIndex() == self.TAB_GAMELOG:
            self._start_watcher()
            self._read_gamelog(full=True)

    def _on_tab_changed(self, idx: int):
        if idx == self.TAB_GAMELOG:
            self._start_watcher()
            self._read_gamelog(full=True)
        else:
            self._stop_watcher()
            self._refresh_current(idx)
        # Update clear button label and enabled state
        if idx == self.TAB_SESSION:
            self._clear_btn.setVisible(False)
        elif idx == self.TAB_LAUNCH:
            self._clear_btn.setText("  Clear Launch Log")
            self._clear_btn.setIcon(ph_icon("eraser", 22))
            self._clear_btn.setVisible(True)
        elif idx == self.TAB_GAMELOG:
            self._clear_btn.setText("  Clear View")
            self._clear_btn.setIcon(ph_icon("eraser", 22))
            self._clear_btn.setVisible(True)
        elif idx == self.TAB_WINETRICKS:
            self._clear_btn.setText("  Clear Winetricks Log")
            self._clear_btn.setIcon(ph_icon("eraser", 22))
            self._clear_btn.setVisible(True)
        else:  # TAB_PREFIX_RUN
            self._clear_btn.setText("  Clear Log")
            self._clear_btn.setIcon(ph_icon("eraser", 22))
            self._clear_btn.setVisible(True)

    def _start_watcher(self):
        """Start watching the current log file for changes."""
        self._stop_watcher()
        if not self._log_file_path or not Path(self._log_file_path).exists():
            return
        from PyQt6.QtCore import QFileSystemWatcher
        self._watcher = QFileSystemWatcher([self._log_file_path])
        self._watcher.fileChanged.connect(self._on_log_changed)

    def _stop_watcher(self):
        if self._watcher:
            self._watcher.fileChanged.disconnect()
            self._watcher = None

    def _on_log_changed(self, path: str):
        """File changed — append only the new bytes."""
        self._read_gamelog()

    def _read_gamelog(self, full: bool = False):
        if not self._log_file_path:
            self._gamelog_edit.setPlainText("(no game launched yet)")
            self._gamelog_offset = 0
            return
        p = Path(self._log_file_path)
        if not p.exists():
            self._gamelog_edit.setPlainText(f"(log file not found: {p.name})")
            self._gamelog_offset = 0
            return
        try:
            size = p.stat().st_size
            # Full rebuild: caller asked for it, or the file shrank (rotated /
            # truncated) so our byte offset is no longer valid.
            if full or size < self._gamelog_offset:
                data = p.read_bytes()
                self._gamelog_offset = len(data)
                self._gamelog_edit.setPlainText(data.decode(errors="replace"))
                sb = self._gamelog_edit.verticalScrollBar()
                sb.setValue(sb.maximum())
                return
            if size == self._gamelog_offset:
                return  # nothing new since last read
            # Incremental: read only the bytes appended since last time and
            # tack them onto the end without rebuilding the whole view.
            with open(p, "rb") as f:
                f.seek(self._gamelog_offset)
                chunk = f.read()
            self._gamelog_offset += len(chunk)
            if not chunk:
                return
            sb = self._gamelog_edit.verticalScrollBar()
            # Only follow the tail if the user was already at the bottom; a small
            # tolerance absorbs rounding so "near bottom" still counts.
            at_bottom = sb.value() >= sb.maximum() - 4
            cursor = self._gamelog_edit.textCursor()
            cursor.movePosition(cursor.MoveOperation.End)
            cursor.insertText(chunk.decode(errors="replace"))
            if at_bottom:
                sb.setValue(sb.maximum())
        except Exception as e:
            self._gamelog_edit.setPlainText(f"(error reading log: {e})")
            self._gamelog_offset = 0

    def refresh(self):
        """Refresh whichever tab is active."""
        self._on_tab_changed(self._tabs.currentIndex())

    def _refresh_current(self, idx: int):
        if idx == self.TAB_SESSION:
            self._session_edit.setPlainText(_NAGOLog.session_text())
            self._session_edit.moveCursor(self._session_edit.textCursor().MoveOperation.Start)
        elif idx == self.TAB_LAUNCH:
            self._launch_edit.setPlainText(_NAGOLog.launch_text())
            sb = self._launch_edit.verticalScrollBar()
            sb.setValue(sb.maximum())
        elif idx == self.TAB_WINETRICKS:
            self._winetricks_edit.setPlainText(_NAGOLog.winetricks_text())
            sb = self._winetricks_edit.verticalScrollBar()
            sb.setValue(sb.maximum())
        elif idx == self.TAB_PREFIX_RUN:
            self._prefix_edit.setPlainText(_NAGOLog.prefix_run_text())
            sb = self._prefix_edit.verticalScrollBar()
            sb.setValue(sb.maximum())

    def append_prefix_line(self, line: str):
        """Append a single line to the Run in Prefix tab in real time."""
        # Drop the placeholder before the first real line, else it gets glued on
        # (e.g. "(no installer run yet)installer line 1"). The deque stays clean,
        # so this only matters for the live view.
        if self._prefix_edit.toPlainText() == "(no installer run yet)":
            self._prefix_edit.clear()
        self._prefix_edit.moveCursor(self._prefix_edit.textCursor().MoveOperation.End)
        self._prefix_edit.insertPlainText(line + "\n")
        sb = self._prefix_edit.verticalScrollBar()
        sb.setValue(sb.maximum())

    def append_winetricks_line(self, line: str):
        """Append a single line to the Winetricks tab in real time."""
        if self._winetricks_edit.toPlainText() == "(no winetricks run yet)":
            self._winetricks_edit.clear()
        self._winetricks_edit.moveCursor(self._winetricks_edit.textCursor().MoveOperation.End)
        self._winetricks_edit.insertPlainText(line + "\n")
        sb = self._winetricks_edit.verticalScrollBar()
        sb.setValue(sb.maximum())

    def _copy_current(self):
        idx = self._tabs.currentIndex()
        if idx == self.TAB_SESSION:
            text = _NAGOLog.session_text()
        elif idx == self.TAB_LAUNCH:
            text = _NAGOLog.launch_text()
        elif idx == self.TAB_WINETRICKS:
            text = _NAGOLog.winetricks_text()
        elif idx == self.TAB_PREFIX_RUN:
            text = _NAGOLog.prefix_run_text()
        else:
            text = self._gamelog_edit.toPlainText()
        QApplication.clipboard().setText(text)

    def _clear_current(self):
        idx = self._tabs.currentIndex()
        if idx == self.TAB_LAUNCH:
            _NAGOLog.clear_launch()
            self._launch_edit.setPlainText(_NAGOLog.launch_text())
        elif idx == self.TAB_GAMELOG:
            self._gamelog_edit.clear()
        elif idx == self.TAB_WINETRICKS:
            _NAGOLog.clear_winetricks()
            self._winetricks_edit.setPlainText(_NAGOLog.winetricks_text())
        elif idx == self.TAB_PREFIX_RUN:
            _NAGOLog.clear_prefix_run()
            self._prefix_edit.clear()


# ── Main Window ────────────────────────────────────────────────────────────────

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.config = load_config()
        init_db()
        # Defer session logging until after window shows — get_umu_version()
        # runs a subprocess and would block startup if called synchronously
        QTimer.singleShot(0, lambda: _log_session_info(self.config))
        self.setWindowTitle(APP_NAME)
        # Use the bundled NAGO logo as the window icon (taskbar / dock / Alt-Tab)
        if LOGO_PATH.exists():
            self.setWindowIcon(QIcon(str(LOGO_PATH)))
        # Minimum size of 1025x750 in logical points. Clamp to the available
        # screen size so the window stays usable on small / high-DPI displays
        # (e.g. 1920x1080 at 200% scale = 960x540 logical points).
        screen = QApplication.primaryScreen()
        if screen is not None:
            avail = screen.availableGeometry()
            min_w = min(1065, max(640, avail.width()  - 40))
            min_h = min(715,  max(480, avail.height() - 80))
        else:
            min_w, min_h = 1065, 715
        self.setMinimumSize(min_w, min_h)
        # Restore saved window geometry, or use defaults. Wrapped in try/except so a
        # corrupted config.json (non-numeric width/height/x/y from a hand-edit or a
        # partial write) can never lock the user out — we silently fall back to defaults.
        win_cfg = self.config.get("window", {})
        try:
            w = max(int(win_cfg.get("width",  1280)), min_w)
            h = max(int(win_cfg.get("height", 800)),  min_h)
            self.resize(w, h)
            if "x" in win_cfg and "y" in win_cfg:
                self.move(int(win_cfg["x"]), int(win_cfg["y"]))
        except (ValueError, TypeError) as e:
            _NAGOLog.session(f"[warn] bad window geometry in config, using defaults: {e}")
            self.resize(1280, 800)
        if win_cfg.get("maximized"):
            QTimer.singleShot(0, self.showMaximized)
        # Frameless window with custom controls
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.Window)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        # Drag / resize state
        self._drag_offset = QPoint(0, 0)
        self._resize_dir = ""
        self._resize_start_geo = None
        self._resize_start_pos = None
        self._resize_margin = 6
        self._force_quit = False   # set by _tray_quit to bypass tray-intercept in closeEvent
        self._confirmed_quit = False  # set when user clicks "Quit Anyway" in running-games dialog
        self.setMouseTracking(True)
        self._build()
        self._restore_last_view()
        self._install_edge_filter()
        self._setup_tray()

    def _setup_tray(self):
        """Create system tray icon. Used by both tray-on-close and tray-on-game-run."""
        self._tray = QSystemTrayIcon(self)
        if LOGO_PATH.exists():
            self._tray.setIcon(QIcon(str(LOGO_PATH)))
        else:
            self._tray.setIcon(self.windowIcon())
        self._tray.setToolTip(APP_NAME)

        # Structure: [recent games] | sep | Show NAGO | Quit
        # Recent games are inserted at the top on demand via aboutToShow.
        tray_menu = QMenu()
        show_act = tray_menu.addAction("Show NAGO")
        show_act.triggered.connect(self._tray_restore)
        quit_act = tray_menu.addAction("Quit")
        quit_act.triggered.connect(self._tray_quit)

        self._tray_menu = tray_menu
        self._tray_recent_actions = []
        tray_menu.aboutToShow.connect(self._populate_tray_recent)
        self._tray.setContextMenu(tray_menu)
        self._tray.activated.connect(self._on_tray_activated)

    def _raise_window(self):
        """Bring window to front — called when a second instance is launched."""
        if self.isHidden():
            self._tray_restore()
        else:
            self.showNormal()
            self.activateWindow()
            self.raise_()

    def _tray_restore(self):
        self._tray.hide()
        self.showNormal()
        self.activateWindow()
        self.raise_()

    def _tray_quit(self):
        # _force_quit bypasses the tray-intercept in closeEvent but NOT the
        # running-games guard — that check ignores _force_quit intentionally.
        self._force_quit = True
        self._tray.hide()
        self.close()

    def _on_tray_activated(self, reason):
        if reason in (QSystemTrayIcon.ActivationReason.Trigger,
                      QSystemTrayIcon.ActivationReason.DoubleClick):
            self._tray_restore()

    def _populate_tray_recent(self):
        """Rebuild the 5 most-recently-played game entries in the tray menu.
        Separator is added dynamically so it only appears when there are games."""
        # Remove previous recent actions + separator
        for act in self._tray_recent_actions:
            self._tray_menu.removeAction(act)
        self._tray_recent_actions = []

        try:
            con = db_con()
            cols_desc = [d[0] for d in con.execute("SELECT * FROM games LIMIT 0").description]
            rows = con.execute(
                "SELECT * FROM games WHERE last_played IS NOT NULL "
                "ORDER BY last_played DESC LIMIT 5"
            ).fetchall()
            con.close()
        except Exception as e:
            _NAGOLog.session(f"[warn] _populate_tray_recent: DB read failed: {e}")
            return
        # Find Show NAGO action to insert before it.
        show_act = next((a for a in self._tray_menu.actions()
                         if a.text() == "Show NAGO"), None)
        if show_act is None:
            return

        # Insert separator first (will sit just above Show NAGO)
        sep = QAction(self._tray_menu)
        sep.setSeparator(True)
        self._tray_menu.insertAction(show_act, sep)
        self._tray_recent_actions.append(sep)

        # Insert recent games above the separator, newest first
        for row in rows:
            game = dict(zip(cols_desc, row))
            act = QAction(game["name"], self._tray_menu)
            act.triggered.connect(lambda checked, g=game: self._tray_launch(g))
            self._tray_menu.insertAction(sep, act)
            self._tray_recent_actions.insert(0, act)

    def _on_game_launched(self, log_path: str):
        """Called when a game process starts."""
        self.logs_page.set_log_file(log_path)
        if self.config.get("tray_on_game_run", False):
            self.hide()
            self._tray.show()

    def _tray_launch(self, game: dict):
        """Launch a game from the tray menu using the existing launch path.
        Only restore the window if tray_on_game_run is off — otherwise stay
        minimized, the launch hook will keep the tray visible."""
        if not self.config.get("tray_on_game_run", False):
            self._tray_restore()
        self.library_page._launch_game(game)

    def closeEvent(self, event):
        # ── Running games guard ───────────────────────────────────────────────
        # Collect names of any games currently tracked as running.
        running_names = []
        lp = self.library_page
        for gid in lp._running_games:
            card = lp._cards.get(gid)
            name = card.game["name"] if card else f"Game #{gid}"
            running_names.append(name)
        for appid, entry in lp._steam_watched.items():
            gid  = entry[0]
            card = lp._cards.get(gid)
            name = card.game["name"] if card else f"Steam #{appid}"
            if name not in running_names:
                running_names.append(name)

        if running_names and not self._confirmed_quit \
                and not (self.config.get("tray_on_close", False) and not self._force_quit):
            game_list = "\n".join(f"  • {n}" for n in running_names)
            plural = "a game is" if len(running_names) == 1 else "games are"
            msg = (f"The following {plural} still running:\n\n"
                   f"{game_list}\n\n"
                   f"Quitting now will stop playtime tracking and "
                   f"skip post-exit commands.")
            dlg = NAGOMessageBox(
                "warning", "Game still running", msg, self,
                buttons=("Cancel", "Quit Anyway"), default_button="Cancel"
            )
            dlg.exec()
            if dlg.result_label() != "Quit Anyway":
                self._force_quit = False   # reset so next close attempt works normally
                # If we came from the tray, restore the icon — it was hidden in _tray_quit
                if self._tray and not self._tray.isVisible():
                    self._tray.show()
                event.ignore()
                return
            self._confirmed_quit = True

        # ── Tray on close ─────────────────────────────────────────────────────
        # _force_quit is set by _tray_quit — skip tray intercept so save runs.
        if self.config.get("tray_on_close", False) and not self._force_quit:
            event.ignore()
            self.hide()
            self._tray.show()
            return

        # ── 1. Stop all timers unconditionally ────────────────────────────────
        for owner in (self, self.library_page, self.settings_page):
            for attr in ("_poll_timer",):
                t = getattr(owner, attr, None)
                if t is not None:
                    try:
                        t.stop()
                    except Exception:
                        pass

        # Stop the Logs page file watcher so a late fileChanged can't fire into
        # a widget mid-teardown (same SIP use-after-free class as the workers).
        try:
            self.logs_page._stop_watcher()
        except Exception:
            pass

        # ── 2. Disconnect + stop all background QThreads ──────────────────────
        # This prevents signals firing into widgets that are being deleted,
        # which is a primary cause of SIP use-after-free crashes on shutdown.
        all_worker_attrs = (
            "_umu_check_worker", "_umu_worker", "_umu_db_worker",
            "_dbw", "_worker", "_cworker", "_dw", "_tw", "_steam_pt_worker",
            "_umu_ver_worker", "_wt_worker", "_lud_worker", "_preset_worker",
            "_upscaler_worker", "_winetricks_worker", "_run_in_prefix_worker",
        )
        for owner in (self.settings_page, self.library_page):
            for attr in all_worker_attrs:
                w = getattr(owner, attr, None)
                if w is None:
                    continue
                try:
                    w.disconnect()
                except Exception:
                    pass
                try:
                    if w.isRunning():
                        w.quit()
                        if not w.wait(800):
                            w.terminate()
                            w.wait(200)
                except Exception:
                    pass

        # Pull in any keys other parts of the app may have written (umu_version, etc.)
        # so we don't overwrite them with our stale in-memory copy.
        on_disk = load_config()
        on_disk.update(self.config)
        self.config = on_disk

        # Persist window geometry
        was_max = self.isMaximized()
        # When maximized, save the *normal* geometry so restore works on next launch
        geo = self.normalGeometry() if was_max else self.geometry()
        self.config["window"] = {
            "x":             geo.x(),
            "y":             geo.y(),
            "width":         geo.width(),
            "height":        geo.height(),
            "maximized":     was_max,
            "sidebar_width": self._sidebar.width(),
        }
        save_config(self.config)
        super().closeEvent(event)

    def _build(self):
        # Outer wrapper for translucent rounded window
        outer = QWidget()
        outer.setMouseTracking(True)
        outer_layout = QVBoxLayout(outer)
        outer_layout.setContentsMargins(0, 0, 0, 0)
        outer_layout.setSpacing(0)
        self.setCentralWidget(outer)

        root = QWidget()
        root.setObjectName("root")
        root.setMouseTracking(True)
        outer_layout.addWidget(root)
        main_h = QHBoxLayout(root)
        main_h.setContentsMargins(0, 0, 0, 0)
        main_h.setSpacing(0)

        # ── Sidebar ──────────────────────────────────────────────────────────
        sidebar = QWidget()
        sidebar.setObjectName("sidebar")
        self._sidebar = sidebar
        # SIDEBAR WIDTH LOCKED — do not touch until resizable sidebar is re-enabled.
        # Feature code (_SidebarHandle class + save/restore logic) is intact — just disabled here.
        # To re-enable: remove setFixedWidth(200) and restore the three commented lines below.
        #   _saved_sw = self.config.get("window", {}).get("sidebar_width", 210)
        #   _sidebar_w = max(_SidebarHandle._MIN_W, min(_SidebarHandle._MAX_W, int(_saved_sw)))
        #   sidebar.setFixedWidth(_sidebar_w)
        sidebar.setFixedWidth(180)
        self._sidebar_layout = QVBoxLayout(sidebar)
        self._sidebar_layout.setContentsMargins(0, 8, 10, 20)
        self._sidebar_layout.setSpacing(2)

        # Logo: bundled NAGO logo image + "Launcher" text beside it.
        # HiDPI-aware: render at device-pixel size (logical * DPR), then mark the
        # resulting pixmap with setDevicePixelRatio so Qt knows the bitmap is
        # already at the screen's pixel density and skips the upscale that would
        # otherwise blur it on fractional-scale displays (e.g. 1.25x, 1.5x).
        logo_row = QWidget()
        lr = QHBoxLayout(logo_row)
        lr.setContentsMargins(14, 10, 0, 16)
        lr.setSpacing(10)
        if LOGO_PATH.exists():
            # Resolve DPR from the screen if available; fall back to 1.0.
            _screen = QApplication.primaryScreen()
            _dpr = _screen.devicePixelRatio() if _screen is not None else 1.0
            logo_pix = QPixmap(str(LOGO_PATH))
            scaled = logo_pix.scaled(
                int(48 * _dpr), int(48 * _dpr),
                Qt.AspectRatioMode.KeepAspectRatio,
                Qt.TransformationMode.SmoothTransformation
            )
            scaled.setDevicePixelRatio(_dpr)
            logo_img = QLabel()
            logo_img.setPixmap(scaled)
            logo_img.setFixedSize(56, 56)
            logo_img.setAlignment(Qt.AlignmentFlag.AlignCenter)
            logo_img.setObjectName("transparentBg")
            lr.addWidget(logo_img)
        logo_text_col = QWidget()
        logo_text_col.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)
        logo_text_v = QVBoxLayout(logo_text_col)
        logo_text_v.setContentsMargins(0, 0, 0, 0)
        logo_text_v.setSpacing(0)
        self._logo_nago = QLabel("NAGO")
        self._logo_nago.setObjectName("logoNago")
        self._logo_sub = QLabel("Launcher")
        self._logo_sub.setObjectName("logoSub")
        logo_nago = self._logo_nago
        logo_sub  = self._logo_sub
        logo_text_v.addWidget(logo_nago)
        logo_text_v.addWidget(logo_sub)
        lr.addWidget(logo_text_col, 0, Qt.AlignmentFlag.AlignBottom)
        lr.addStretch()
        self._sidebar_layout.addWidget(logo_row)

        # Nav container: restores 10px left indent for all items below the logo.
        # sidebar_layout left margin is 0 so the logo can sit at 6px; nav content
        # stays visually unchanged at 10px from the sidebar edge.
        _nav_w = QWidget()
        _nav_w.setObjectName("transparentBg")
        _nav_layout = QVBoxLayout(_nav_w)
        _nav_layout.setContentsMargins(10, 0, 0, 0)
        _nav_layout.setSpacing(2)

        # ── Navigation section ────────────────────────────────────────────────
        # setAutoExclusive groups sibling checkable buttons into a radio-style
        # cluster — clicking a checked button no longer un-checks it (Qt's
        # default), which prevents the flicker from click→uncheck→handler-recheck.
        self.btn_library  = self._sidebar_btn("Library")
        self.btn_library.setIcon(ph_icon("stack", 20))
        self.btn_library.setCheckable(True)
        self.btn_library.setAutoExclusive(True)
        _nav_layout.addWidget(self.btn_library)
        self.btn_library.clicked.connect(self._show_library)

        # Settings parent button — toggles sub-menu, doesn't navigate directly
        self.btn_settings = self._sidebar_btn("Settings")
        self.btn_settings.setIcon(ph_icon("gear", 20))
        self.btn_settings.setCheckable(True)
        self.btn_settings.setAutoExclusive(True)
        _nav_layout.addWidget(self.btn_settings)
        self.btn_settings.clicked.connect(self._toggle_settings_tree)

        # Sub-buttons container with animated height
        self._settings_sub = QWidget()
        self._settings_sub.setObjectName("transparentBg")
        sub_layout = QVBoxLayout(self._settings_sub)
        sub_layout.setContentsMargins(0, 0, 0, 0)
        sub_layout.setSpacing(1)

        self.btn_settings_general = QPushButton("   General")
        self.btn_settings_general.setObjectName("sideSubBtn")
        self.btn_settings_general.setCheckable(True)
        self.btn_settings_general.setAutoExclusive(True)
        self.btn_settings_general.setIcon(ph_icon("sliders", 22))
        self.btn_settings_general.clicked.connect(self._show_settings)

        self.btn_settings_logs = QPushButton("   Logs")
        self.btn_settings_logs.setObjectName("sideSubBtn")
        self.btn_settings_logs.setCheckable(True)
        self.btn_settings_logs.setAutoExclusive(True)
        self.btn_settings_logs.setIcon(ph_icon("article", 22))
        self.btn_settings_logs.clicked.connect(self._show_logs)

        # Unicode dot prefix — swapped in/out on toggle to indicate active sub-page.
        # Relies on __ACCENT2__ color from QSS:checked to tint the whole button text.
        def _sync_sub_labels():
            self.btn_settings_general.setText(
                "● General" if self.btn_settings_general.isChecked() else "   General")
            self.btn_settings_logs.setText(
                "● Logs" if self.btn_settings_logs.isChecked() else "   Logs")

        self.btn_settings_general.toggled.connect(lambda _: _sync_sub_labels())
        self.btn_settings_logs.toggled.connect(lambda _: _sync_sub_labels())

        sub_layout.addWidget(self.btn_settings_general)
        sub_layout.addWidget(self.btn_settings_logs)

        # Measure the natural height of the sub-menu (rather than hardcoding
        # 38*2+2, which assumed default button metrics).  adjustSize is required
        # so sizeHint reflects the just-added children.  We re-measure lazily on
        # first expand in case the font/DPI changes — see _measure_settings_sub_h.
        self._settings_sub.adjustSize()
        self._settings_sub_full_h = self._settings_sub.sizeHint().height()
        self._settings_sub.setMaximumHeight(0)
        self._settings_sub_expanded = False
        _nav_layout.addWidget(self._settings_sub)

        # Animation for expand/collapse
        self._sub_anim = QPropertyAnimation(self._settings_sub, b"maximumHeight")
        self._sub_anim.setDuration(150)
        self._sub_anim.setEasingCurve(QEasingCurve.Type.OutCubic)

        # ── Separator ────────────────────────────────────────────────────────
        sep = QFrame()
        sep.setObjectName("sideSeparator")
        _nav_layout.addWidget(sep)

        # ── Categories section ────────────────────────────────────────────────
        # Scroll area for category buttons (in case there are many)
        self._cat_scroll = QScrollArea()
        self._cat_scroll.setWidgetResizable(True)
        self._cat_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self._cat_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self._cat_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self._cat_scroll.setObjectName("transparentBg")
        self._cat_container = _CatDropContainer()
        self._cat_container.setObjectName("transparentBg")
        self._cat_container.set_accent(self.config.get("accent_color", DEFAULT_ACCENT))
        self._cat_container.reorder_requested.connect(self._reorder_categories)
        self._cat_vbox = QVBoxLayout(self._cat_container)
        self._cat_vbox.setContentsMargins(0, 0, 0, 0)
        self._cat_vbox.setSpacing(2)
        self._cat_scroll.setWidget(self._cat_container)
        _nav_layout.addWidget(self._cat_scroll, 1)

        # Add Category button
        self._add_cat_btn = QPushButton("  New Category")
        self._add_cat_btn.setIcon(ph_icon("tag-chevron", 22))
        self._add_cat_btn.setObjectName("addCatBtn")
        self._add_cat_btn.clicked.connect(self._add_category)
        _nav_layout.addWidget(self._add_cat_btn)

        # Version — two lines (version on top, build below) so it can't clip
        # against the 190px usable sidebar width regardless of font/locale.
        # WordWrap is also enabled as a belt-and-braces fallback.
        self._ver_lbl = QLabel(f"v{VERSION}\n{BUILD}")
        self._ver_lbl.setObjectName("sidebarVersion")
        self._ver_lbl.setWordWrap(True)
        self._ver_lbl.setAlignment(Qt.AlignmentFlag.AlignHCenter)
        ver = self._ver_lbl
        _nav_layout.addWidget(ver)
        self._sidebar_layout.addWidget(_nav_w, 1)

        main_h.addWidget(sidebar)
        # SIDEBAR HANDLE DISABLED — re-enable alongside the width lock above.
        self._sidebar_handle = _SidebarHandle(sidebar, root)
        self._sidebar_handle.setFixedWidth(0)
        self._sidebar_handle.hide()
        main_h.addWidget(self._sidebar_handle)

        # Track which category button is active
        self._cat_buttons: dict[int, QPushButton] = {}
        self._active_cat_id: int = None

        # Populate categories
        self._rebuild_cat_buttons()

        # ── Right side ────────────────────────────────────────────────────────
        right = QWidget()
        rv = QVBoxLayout(right)
        rv.setContentsMargins(0, 0, 0, 0)
        rv.setSpacing(0)

        # Top bar (also acts as title bar / drag handle)
        topbar = DragBar(self)
        topbar.setObjectName("topbar")
        topbar.setFixedHeight(60)
        self._topbar = topbar
        tbl = QHBoxLayout(topbar)
        tbl.setContentsMargins(24, 0, 12, 0)
        tbl.setSpacing(20)  # padding between title / search / buttons

        # ── Left section (title) ─────────────────────────────────────────
        # Hugs its text and sits at the left edge.
        left_section = QWidget()
        left_section.setObjectName("transparentBg")
        ls = QHBoxLayout(left_section)
        ls.setContentsMargins(0, 0, 0, 0)
        ls.setSpacing(12)
        self.page_title = QLabel("Library")
        self.page_title.setObjectName("pageTitle")
        ls.addWidget(self.page_title)
        left_section.setSizePolicy(QSizePolicy.Policy.Maximum, QSizePolicy.Policy.Preferred)
        tbl.addWidget(left_section, 0)

        # Stretch absorbs leftover space on the left side of the search box
        tbl.addStretch(1)

        # ── Search box (flexible width with sane bounds) ─────────────────
        self.search_box = QLineEdit()
        self.search_box.setObjectName("search")
        self.search_box.setPlaceholderText("Search games…")
        self.search_box.setMinimumWidth(220)
        self.search_box.setMaximumWidth(560)
        self.search_box.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        self.search_box.textChanged.connect(self._on_search)
        tbl.addWidget(self.search_box, 2)

        # ── Show hidden toggle (eye-slash icon, lights up when active) ───
        self._show_hidden_btn = QPushButton()
        self._show_hidden_btn.setIcon(ph_icon("eye-slash", 20))
        self._show_hidden_btn.setCheckable(True)
        self._show_hidden_btn.setChecked(False)
        self._show_hidden_btn.setFixedSize(36, 36)
        self._show_hidden_btn.setObjectName("iconBtn")
        self._show_hidden_btn.setToolTip("Show hidden games")
        self._show_hidden_btn.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        self._show_hidden_btn.toggled.connect(self._on_toggle_show_hidden)
        self._apply_hidden_btn_style(self.config.get("accent_color", DEFAULT_ACCENT))
        tbl.addWidget(self._show_hidden_btn)

        # Stretch absorbs leftover space on the right side of the search box
        tbl.addStretch(1)

        # ── Right section (add/cover + window controls) ──────────────────
        right_section = QWidget()
        right_section.setObjectName("rightSection")
        rs = QHBoxLayout(right_section)
        rs.setContentsMargins(0, 0, 0, 0)
        rs.setSpacing(4)

        self.add_btn = QPushButton("  Add Game")
        self.add_btn.setIcon(ph_icon("sparkle", 22))
        self.add_btn.setObjectName("addGameBtn")
        self.add_btn.setAttribute(Qt.WidgetAttribute.WA_Hover, True)
        self.add_btn.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        self.add_btn.clicked.connect(self._add_game)
        rs.addWidget(self.add_btn)

        # Window controls
        rs.addSpacing(8)
        self._min_btn   = self._make_win_btn("─", lambda: self.showMinimized())
        self._max_btn   = self._make_win_btn("☐", self._toggle_max)
        self._close_btn = self._make_win_btn("✕", self.close, danger=True)
        rs.addWidget(self._min_btn)
        rs.addWidget(self._max_btn)
        rs.addWidget(self._close_btn)

        right_section.setSizePolicy(QSizePolicy.Policy.Maximum, QSizePolicy.Policy.Preferred)
        tbl.addWidget(right_section, 0)

        rv.addWidget(topbar)

        # Stacked pages
        self.stack = QStackedWidget()
        self.library_page  = LibraryPage(self.config)
        self.settings_page = SettingsPage(self.config)
        self.logs_page     = LogsPage()
        self.library_page.status_message.connect(self._set_status)
        self.library_page.game_launched.connect(self._on_game_launched)
        self.settings_page.config_saved.connect(self._on_config_saved)
        # Wire prefix run bridge → live append in Run in Prefix log tab
        _prefix_run_bridge.line_ready.connect(self.logs_page.append_prefix_line)
        # Wire winetricks bridge → live append in Winetricks log tab
        _winetricks_bridge.line_ready.connect(self.logs_page.append_winetricks_line)
        self.stack.addWidget(self.library_page)
        self.stack.addWidget(self.settings_page)
        self.stack.addWidget(self.logs_page)
        _stack_wrapper = QWidget()
        _sw = QHBoxLayout(_stack_wrapper)
        # 4px right margin keeps the scrollbar clear of the window border and
        # the 6px resize zone — without it the resize cursor fires before the
        # scrollbar is reachable. Status bar and topbar are outside this wrapper
        # so they still extend edge to edge.
        _sw.setContentsMargins(0, 0, 4, 0)
        _sw.setSpacing(0)
        _sw.addWidget(self.stack)
        rv.addWidget(_stack_wrapper)

        self._right = right
        # Status bar
        self.status_lbl = QLabel("  Ready")
        self.status_lbl.setObjectName("statusBar")
        self.status_lbl.setFixedHeight(32)
        rv.addWidget(self.status_lbl)

        main_h.addWidget(right)

    def _sidebar_btn(self, text: str) -> QPushButton:
        btn = QPushButton(f"  {text}")
        btn.setObjectName("sideBtn")
        btn.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        # Match category button height (40) so the sidebar reads as a single
        # consistent column.  Visual hierarchy between primary nav and
        # categories comes from QSS (font weight / object name), not height.
        btn.setFixedHeight(40)
        return btn

    # ── Category sidebar helpers ──────────────────────────────────────────────

    def _rebuild_cat_buttons(self):
        # Suspend updates on BOTH the container and the enclosing scroll area.
        # Disabling updates on the container alone isn't enough: when we clear
        # the layout, the container's height briefly collapses to ~0, and the
        # scroll area — still painting — sees "content fits" and hides the
        # vertical scrollbar.  That widens the viewport by ~12px, expanding the
        # buttons (Expanding sizePolicy).  As soon as the new buttons are added
        # the scrollbar comes back and the buttons snap narrower.  Result: a
        # visible width-flicker on every add/rename/delete when the list is
        # long enough to scroll.  Suspending updates on the scroll area too
        # keeps the scrollbar (and therefore the viewport width) stable until
        # the rebuild is fully committed.
        self._cat_container.setUpdatesEnabled(False)
        self._cat_scroll.setUpdatesEnabled(False)
        try:
            # Fully clear the layout (widgets, spacers, stretches)
            while self._cat_vbox.count():
                item = self._cat_vbox.takeAt(0)
                w = item.widget()
                if w is not None:
                    w.deleteLater()
            self._cat_buttons.clear()

            cats = db_get_categories()
            for cat in cats:
                btn = self._make_cat_btn(cat)
                self._cat_vbox.addWidget(btn)
                self._cat_buttons[cat["id"]] = btn

            self._cat_vbox.addStretch()

            # Restore active selection if still valid
            if self._active_cat_id and self._active_cat_id in self._cat_buttons:
                self._cat_buttons[self._active_cat_id].setChecked(True)
        finally:
            self._cat_scroll.setUpdatesEnabled(True)
            self._cat_container.setUpdatesEnabled(True)

    def _make_cat_btn(self, cat: dict) -> QPushButton:
        btn = DraggableCategoryButton(cat['name'], cat["id"])
        btn.setObjectName("catBtn")
        btn.setCheckable(True)
        # Auto-exclusive within _cat_container so clicking the already-active
        # category doesn't un-check it (which would cause a visible flicker
        # before _show_category re-checks it).  Cross-group de-selection
        # (Library/Settings ↔ categories) is still handled explicitly in the
        # show methods, since those buttons live in a different parent widget.
        btn.setAutoExclusive(True)
        btn.setFixedHeight(40)
        btn.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        cid = cat["id"]
        btn.clicked.connect(lambda checked, c=cid, n=cat["name"]: self._show_category(c, n))
        btn.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        btn.customContextMenuRequested.connect(
            lambda pos, c=cid, b=btn: self._cat_context_menu(pos, c, b))
        # Delete / F2 keyboard shortcuts — routed through the same handlers as
        # the right-click menu so confirmation dialogs and rename UI stay
        # identical between mouse and keyboard paths.
        btn.delete_requested.connect(self._delete_category)
        btn.rename_requested.connect(lambda c=cid, b=btn: self._rename_category(c, b))
        return btn

    def _reorder_categories(self, src_id: int, target_id: int):
        """Move src_id to just before target_id in the sidebar sort order.
        target_id == -1 means append at end.
        Re-numbers sort_pos as clean contiguous integers."""
        if src_id == target_id:
            return
        ids = list(self._cat_buttons.keys())
        if src_id not in ids:
            return
        if target_id != -1 and target_id not in ids:
            return

        new_order = [cid for cid in ids if cid != src_id]
        if target_id == -1:
            new_order.append(src_id)
        else:
            tgt_idx = new_order.index(target_id)
            new_order.insert(tgt_idx, src_id)

        con = db_con()
        try:
            for pos, cid in enumerate(new_order):
                con.execute("UPDATE categories SET sort_pos=? WHERE id=?", (pos, cid))
            con.commit()
        finally:
            con.close()
        self._rebuild_cat_buttons()

    def _show_category(self, cat_id: int, cat_name: str):
        self._revert_unsaved_accent()
        self._collapse_settings_tree()
        # Deselect nav buttons
        self.btn_library.setChecked(False)
        self.btn_settings.setChecked(False)
        # Deselect other cat buttons
        for cid, b in self._cat_buttons.items():
            b.setChecked(cid == cat_id)
        self._active_cat_id = cat_id
        self.stack.setCurrentWidget(self.library_page)
        self.page_title.setText(cat_name)
        self.search_box.setVisible(True)
        self.add_btn.setVisible(True)
        self._show_hidden_btn.setVisible(True)
        self.library_page._apply_filter(
            self.library_page._current_filter_text, cat_id)
        # Persist for next launch
        self.config["last_view"] = "category"
        self.config["last_category_id"] = cat_id

    def _cat_context_menu(self, pos, cat_id: int, btn: QPushButton):
        menu = QMenu(self)
        menu.setWindowFlags(menu.windowFlags()
                            | Qt.WindowType.FramelessWindowHint
                            | Qt.WindowType.NoDropShadowWindowHint)
        menu.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        menu.setStyleSheet(_menu_stylesheet())

        rename_act, _ = _make_menu_row(menu, "pencil-simple", "Rename")
        menu.addAction(rename_act)
        menu.addSeparator()
        delete_act, _ = _make_menu_row(menu, "trash", "Delete Category")
        menu.addAction(delete_act)

        action = menu.exec(btn.mapToGlobal(pos))
        if action == rename_act:
            self._rename_category(cat_id, btn)
        elif action == delete_act:
            self._delete_category(cat_id)

    def _add_category(self):
        name, ok = self._input_dialog("New Category", "Category name:")
        if ok and name.strip():
            name = name.strip()
            try:
                db_add_category(name)
                self._rebuild_cat_buttons()
                self._set_status(f"Category '{name}' added")
            except Exception:
                NAGOMessageBox.warning(self, "Duplicate", f"A category named '{name}' already exists.")

    def _rename_category(self, cat_id: int, btn: QPushButton):
        current = btn.text().strip()
        name, ok = self._input_dialog("Rename Category", "New name:", current)
        if ok and name.strip():
            name = name.strip()
            try:
                db_rename_category(cat_id, name)
                self._rebuild_cat_buttons()
                # Update page title if this category is active
                if self._active_cat_id == cat_id:
                    self.page_title.setText(name)
                self._set_status(f"Renamed to '{name}'")
            except Exception:
                NAGOMessageBox.warning(self, "Duplicate", f"A category named '{name}' already exists.")

    def _delete_category(self, cat_id: int):
        reply = NAGOMessageBox.question(
            self, "Delete Category",
            "Delete this category?\nGames in it won't be deleted."
        )
        if reply == QMessageBox.StandardButton.Yes:
            db_delete_category(cat_id)
            if self._active_cat_id == cat_id:
                self._active_cat_id = None
                self._show_library()
            self._rebuild_cat_buttons()
            self._set_status("Category deleted")

    def _input_dialog(self, title: str, label: str, default: str = "") -> tuple[str, bool]:
        """Simple inline input dialog styled to match the app."""
        dlg = _NAGODialog(self)
        dlg.setWindowTitle(title)
        dlg.setWindowFlags(Qt.WindowType.Dialog | Qt.WindowType.FramelessWindowHint)
        dlg.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        dlg.setMinimumWidth(340 + dlg._SHADOW * 2)
        _outer = QVBoxLayout(dlg)
        _outer.setContentsMargins(dlg._SHADOW, dlg._SHADOW, dlg._SHADOW, dlg._SHADOW)
        _outer.setSpacing(0)
        _root = QFrame()
        _root.setObjectName("dialogRoot")
        _outer.addWidget(_root)
        lv = QVBoxLayout(_root)
        lv.setContentsMargins(24, 24, 24, 24)
        lv.setSpacing(12)
        t = QLabel(title); t.setObjectName("dlgTitle"); lv.addWidget(t)
        lbl = QLabel(label); lbl.setObjectName("sectionLabel"); lv.addWidget(lbl)
        inp = QLineEdit(default); inp.setObjectName("dlgInput"); lv.addWidget(inp)
        inp.selectAll()
        row = QHBoxLayout()
        cancel = QPushButton("  Cancel"); cancel.setObjectName("secondary")
        cancel.setIcon(ph_icon("x", 22))
        cancel.clicked.connect(dlg.reject)
        ok = QPushButton("OK"); ok.setObjectName("primary")
        ok.clicked.connect(dlg.accept)
        inp.returnPressed.connect(dlg.accept)
        row.addWidget(cancel); row.addStretch(); row.addWidget(ok)
        lv.addLayout(row)
        result = dlg.exec()
        return inp.text(), result == QDialog.DialogCode.Accepted

    def _revert_unsaved_accent(self):
        """Revert all unsaved settings page changes if currently on settings."""
        if self.stack.currentWidget() is not self.settings_page:
            return
        self.settings_page.revert()

    def _measure_settings_sub_h(self) -> int:
        """Return the current natural height of the Settings sub-menu.
        Re-measured on demand so font/DPI changes are picked up automatically
        instead of being baked in at construction time."""
        # Temporarily lift the max so sizeHint reflects the children, not the
        # collapsed cap.  We restore the cap before returning.
        prev_cap = self._settings_sub.maximumHeight()
        self._settings_sub.setMaximumHeight(16777215)  # Qt's QWIDGETSIZE_MAX
        self._settings_sub.adjustSize()
        h = self._settings_sub.sizeHint().height()
        self._settings_sub.setMaximumHeight(prev_cap)
        if h > 0:
            self._settings_sub_full_h = h
        return self._settings_sub_full_h

    def _animate_sub(self, target_h: int):
        """Run the sub-menu animation toward target_h, starting from whatever
        height it's at right now.  Stops any in-flight animation first so rapid
        clicks don't cause the height to snap to a stale start value."""
        self._sub_anim.stop()
        self._sub_anim.setStartValue(self._settings_sub.maximumHeight())
        self._sub_anim.setEndValue(target_h)
        self._sub_anim.start()

    def _collapse_settings_tree(self):
        """Collapse the Settings sub-menu if expanded."""
        if self._settings_sub_expanded:
            self._animate_sub(0)
            self._settings_sub_expanded = False
            self.btn_settings.setChecked(False)
            self.btn_settings_general.setChecked(False)
            self.btn_settings_logs.setChecked(False)

    def _show_library(self):
        self._revert_unsaved_accent()
        self._collapse_settings_tree()
        self._active_cat_id = None
        # Auto-exclusive blocks programmatic setChecked(False) — toggle off, uncheck, restore.
        for b in self._cat_buttons.values():
            b.setAutoExclusive(False)
            b.setChecked(False)
            b.setAutoExclusive(True)
        self.stack.setCurrentWidget(self.library_page)
        self.btn_library.setChecked(True)
        self.btn_settings.setChecked(False)
        self.btn_settings_general.setChecked(False)
        self.btn_settings_logs.setChecked(False)
        self.page_title.setText("Library")
        self.search_box.setVisible(True)
        self.add_btn.setVisible(True)
        self._show_hidden_btn.setVisible(True)
        self.library_page._apply_filter(
            self.library_page._current_filter_text, None)
        self.config["last_view"] = "library"
        self.config["last_category_id"] = None

    def _toggle_settings_tree(self):
        """Expand or collapse the Settings sub-menu."""
        if self._settings_sub_expanded:
            # Collapse
            self._animate_sub(0)
            self._settings_sub_expanded = False
            # If currently on a settings sub-page, go to library
            if self.stack.currentWidget() in (self.settings_page, self.logs_page):
                self._show_library()
            else:
                self.btn_settings.setChecked(False)
        else:
            # Re-measure in case font/DPI changed since construction, then expand.
            self._measure_settings_sub_h()
            self._animate_sub(self._settings_sub_full_h)
            self._settings_sub_expanded = True
            self._show_settings()

    def _show_settings(self):
        self._active_cat_id = None
        # Auto-exclusive blocks programmatic setChecked(False) — toggle off, uncheck, restore.
        for b in self._cat_buttons.values():
            b.setAutoExclusive(False)
            b.setChecked(False)
            b.setAutoExclusive(True)
        self.stack.setCurrentWidget(self.settings_page)
        self.btn_library.setChecked(False)
        self.btn_settings.setChecked(True)
        self.btn_settings_general.setChecked(True)
        self.btn_settings_logs.setChecked(False)
        self.page_title.setText("Settings")
        self.search_box.setVisible(False)
        self.add_btn.setVisible(False)
        self._show_hidden_btn.setVisible(False)

    def _show_logs(self):
        self._active_cat_id = None
        for b in self._cat_buttons.values():
            b.setChecked(False)
        self.logs_page.refresh()
        self.stack.setCurrentWidget(self.logs_page)
        self.btn_library.setChecked(False)
        self.btn_settings.setChecked(True)
        self.btn_settings_general.setChecked(False)
        self.btn_settings_logs.setChecked(True)
        self.page_title.setText("Logs")
        self.search_box.setVisible(False)
        self.add_btn.setVisible(False)
        self._show_hidden_btn.setVisible(False)

    def _restore_last_view(self):
        """Restore the view the user had open last time. Falls back to Library."""
        last_view = self.config.get("last_view", "library")
        last_cat  = self.config.get("last_category_id")
        if last_view == "category" and last_cat is not None:
            # Look up the category's current name (names can be renamed but ids are stable)
            try:
                con = db_con()
                cur = con.execute("SELECT id, name FROM categories WHERE id = ?", (int(last_cat),))
                row = cur.fetchone()
                con.close()
            except Exception:
                row = None
            if row:
                self._show_category(row[0], row[1])
                return
        # Default — also covers the "settings was the last view" case
        self._show_library()

    def _on_search(self, text: str):
        if not hasattr(self, "_search_timer"):
            self._search_timer = QTimer(self)
            self._search_timer.setSingleShot(True)
            self._search_timer.timeout.connect(
                lambda: self.library_page._apply_filter(
                    self.search_box.text(), self._active_cat_id))
        self._search_timer.start(150)

    def _apply_hidden_btn_style(self, accent: str):
        """Build the eye-button stylesheet using the current accent color and theme."""
        ac = QColor(accent)
        is_light = _current_theme() == "light"
        if is_light:
            icon_col   = "#52525b"
            bg_hover   = "#e4e4e8"
            hover_col  = "#18181b"
            bg_active  = QColor(
                ac.red()   + (255 - ac.red())   * 7 // 8,
                ac.green() + (255 - ac.green()) * 7 // 8,
                ac.blue()  + (255 - ac.blue())  * 7 // 8,
            ).name()
        else:
            icon_col   = "#71717a"
            bg_hover   = "#3d3d42"
            hover_col  = "#f4f4f5"
            bg_active  = QColor(ac.red() // 5, ac.green() // 5, ac.blue() // 5).name()

        # Re-render icon with correct color for current theme
        checked = self._show_hidden_btn.isChecked()
        icon_name = "eye" if checked else "eye-slash"
        self._show_hidden_btn.setIcon(ph_icon(icon_name, 20, accent if checked else icon_col))

        if checked:
            bg_active = QColor(ac.red() // 5, ac.green() // 5, ac.blue() // 5).name()
            self._show_hidden_btn.setStyleSheet(
                f"QPushButton#iconBtn:checked {{ background: {bg_active}; border: 1px solid {accent}; color: {accent}; }}"
                f"QPushButton#iconBtn:checked:hover {{ background: {bg_hover}; border: 1px solid {accent}; color: {accent}; }}"
            )
        else:
            self._show_hidden_btn.setStyleSheet("")

    def _on_toggle_show_hidden(self, checked: bool):
        """Toggle the library between normal and hidden-games view."""
        self.library_page._show_hidden = checked
        if checked:
            self._show_hidden_btn.setIcon(ph_icon("eye", 20))
            self._show_hidden_btn.setToolTip("Back to library")
            self.search_box.setPlaceholderText("Search hidden games…")
        else:
            self._show_hidden_btn.setIcon(ph_icon("eye-slash", 20))
            self._show_hidden_btn.setToolTip("Show hidden games")
            self.search_box.setPlaceholderText("Search games…")
        self.library_page._apply_filter(self.search_box.text(), self._active_cat_id)

    def _add_game(self):
        dlg = GameDialog(self.config, parent=self)
        if dlg.exec() == QDialog.DialogCode.Accepted:
            d = dlg.result_data
            con = db_con()
            try:
                con.execute("""
                    INSERT INTO games (name, exe_path, game_type, proton_path,
                                       umu_enabled, umu_gameid, umu_store,
                                       launch_args, env_vars, vn_jp_locale,
                                       use_wined3d, use_wow64, use_wayland,
                                       no_esync, no_fsync, no_ntsync,
                                       legacy_mediaconv, video_decode_mode,
                                       pre_launch_cmd, post_exit_cmd,
                                       auto_backup,
                                       gamescope_enabled,
                                       upscale_enabled, upscale_model,
                                       hdr_enabled, hdr_monitor,
                                       gog_id,
                                       fsr4_upgrade, optiscaler_dll, fsr4_indicator,
                                       install_dir,
                                       sort_pos, added_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?,
                            ?,
                            (SELECT COALESCE(MAX(sort_pos), 0) + 1 FROM games),
                            datetime('now'))
                """, (d["name"], d["exe_path"], d["game_type"], d["proton_path"],
                      d["umu_enabled"], d["umu_gameid"], d["umu_store"],
                      d["launch_args"], d["env_vars"], d.get("vn_jp_locale", 0),
                      d.get("use_wined3d", 0), d.get("use_wow64", 0), d.get("use_wayland", 0),
                      d.get("no_esync", 0), d.get("no_fsync", 0), d.get("no_ntsync", 0),
                      d.get("legacy_mediaconv", 0), d.get("video_decode_mode", "default"),
                      d["pre_launch_cmd"], d["post_exit_cmd"],
                      d.get("auto_backup", 0),
                      d.get("gamescope_enabled", 0),
                      d.get("upscale_enabled", 0), d.get("upscale_model", "fast"),
                      d.get("hdr_enabled", 0), d.get("hdr_monitor", ""),
                      d.get("gog_id", ""),
                      d.get("fsr4_upgrade", ""), d.get("optiscaler_dll", ""), d.get("fsr4_indicator", 0),
                      d.get("install_dir", "")))
                con.commit()
                new_id = con.execute("SELECT last_insert_rowid()").fetchone()[0]
                _NAGOLog.session(
                    f'[add-game] "{d["name"]}"'
                )
                _NAGOLog.session(
                    f'  exe={d["exe_path"]}'
                )
                _NAGOLog.session(
                    f'  install_dir={d.get("install_dir", "") or "(none)"}'
                )

                # If a cover was picked before saving, rename it from _0 to _<real_id>
                pending = d.get("pending_cover_path", "")
                if pending and Path(pending).exists():
                    name   = d["name"]
                    slug   = slugify(name)
                    ext    = Path(pending).suffix or ".png"
                    final  = ART_PATH / f"{slug}_{new_id}{ext}"
                    Path(pending).rename(final)
                    con.execute("UPDATE games SET cover_path=? WHERE id=?",
                                (str(final), new_id))
                    con.commit()

                # If a cover download was still in flight when Save was pressed,
                # reconnect the live worker to apply the cover once it finishes.
                cover_worker = d.get("cover_worker")
                if cover_worker is not None:
                    _slug = slugify(d["name"])
                    _nid  = new_id
                    def _bg_cover_done(_gid_ignored: int, path: str,
                                       slug=_slug, nid=_nid, wref=cover_worker):
                        try:
                            ART_PATH.mkdir(parents=True, exist_ok=True)
                            ext   = Path(path).suffix or ".png"
                            final = ART_PATH / f"{slug}_{nid}{ext}"
                            if Path(path).exists() and Path(path) != final:
                                Path(path).rename(final)
                            _con = db_con()
                            _con.execute("UPDATE games SET cover_path=? WHERE id=?",
                                         (str(final), nid))
                            _con.commit()
                            _con.close()
                            for g in self._all_games:
                                if g["id"] == nid:
                                    g["cover_path"] = str(final)
                                    break
                            self._refresh_single_cover(nid, str(final))
                            self.status_message.emit("Cover saved!")
                        except Exception as e:
                            _NAGOLog.session(f"[warn] _add_game bg cover: {e}")
                        finally:
                            self._single_cover_workers.discard(wref)
                    cover_worker.cover_downloaded.connect(_bg_cover_done)
                    cover_worker.finished.connect(cover_worker.deleteLater)
                    self._single_cover_workers.add(cover_worker)

                # If a tmp prefix was created via Run in Prefix before saving,
                # rename it to the canonical slug_id path and persist it.
                # _installed_pfx tracks the resulting path so the prefix restore
                # block below knows a fresh install prefix already exists.
                _installed_pfx = ""
                tmp_pfx = d.get("tmp_prefix_path", "")
                if tmp_pfx and Path(tmp_pfx).exists():
                    slug     = slugify(d["name"])
                    real_pfx = get_prefixes_root() / f"{slug}_{new_id}"
                    try:
                        Path(tmp_pfx).rename(real_pfx)
                        con.execute("UPDATE games SET prefix_path=? WHERE id=?",
                                    (str(real_pfx), new_id))
                        con.commit()
                        _installed_pfx = str(real_pfx)
                        _NAGOLog.session(f"[add-game] tmp prefix renamed: {tmp_pfx} → {real_pfx}")
                    except Exception as e:
                        # Rename failed (e.g. cross-device) — keep tmp path as-is
                        con.execute("UPDATE games SET prefix_path=? WHERE id=?",
                                    (tmp_pfx, new_id))
                        con.commit()
                        _installed_pfx = tmp_pfx
                        _NAGOLog.session(f"[warn] _add_game: prefix rename failed, keeping tmp path {tmp_pfx}: {e}")

                # Import Steam playtime immediately for Steam-type games
                if d["game_type"] == "steam" and d.get("exe_path"):
                    minutes = steam_playtime_for_appid(
                        d["exe_path"].strip(),
                        api_key=self.config.get("steam_api_key", "")
                    )
                    if minutes > 0:
                        con.execute("UPDATE games SET playtime_minutes=? WHERE id=?",
                                    (minutes, new_id))
                        con.commit()

                # ── Playtime archive restore ───────────────────────────────────
                _gt      = d["game_type"]
                _exe     = d.get("exe_path", "")
                _store   = d.get("umu_store", "") or ""
                _gname   = d["name"]

                # Build the lookup key depending on game type.
                # All types restore silently — playtime, last session, and last
                # played are all restored. No prompt: removing and re-adding a
                # game is unambiguous intent to restore its history.
                if _gt == "steam":
                    # Steam: keyed by AppID (store_key) — silent full restore
                    arc = con.execute("""
                        SELECT id, game_name, playtime_minutes, last_session_minutes, last_played,
                               launch_args, env_vars, pre_launch_cmd, post_exit_cmd, auto_backup, ludusavi_title, gamescope_enabled, upscale_enabled, upscale_model, hdr_enabled, fsr4_upgrade, optiscaler_dll, use_wined3d, use_wow64, use_wayland, no_esync, no_fsync, no_ntsync, legacy_mediaconv, video_decode_mode, vn_jp_locale, added_at, category_names
                        FROM playtime_archive
                        WHERE game_type='steam' AND store_key=?
                        ORDER BY archived_at DESC LIMIT 1
                    """, (_exe.strip(),)).fetchone()
                    if arc:
                        con.execute(
                            "UPDATE games SET playtime_minutes=?, last_session_minutes=?, last_played=?, "
                            "launch_args=?, env_vars=?, pre_launch_cmd=?, post_exit_cmd=?, auto_backup=?, ludusavi_title=?, gamescope_enabled=?, upscale_enabled=?, upscale_model=?, hdr_enabled=?, fsr4_upgrade=?, optiscaler_dll=?, use_wined3d=?, use_wow64=?, use_wayland=?, no_esync=?, no_fsync=?, no_ntsync=?, legacy_mediaconv=?, video_decode_mode=?, vn_jp_locale=?, added_at=? WHERE id=?",
                            (arc[2], arc[3], arc[4],
                             arc[5], arc[6], arc[7], arc[8], arc[9], arc[10], arc[11], arc[12], arc[13], arc[14], arc[15], arc[16], arc[17], arc[18], arc[19], arc[20], arc[21], arc[22], arc[23], arc[24], arc[25], arc[26],
                             new_id))
                        con.commit()
                        self._set_status(f"Restored playtime and settings for {_gname}")
                        # Restore categories — match by name, skip any that no longer exist
                        _arc_cats = (arc[27] or "").strip()
                        if _arc_cats:
                            _cat_names_to_restore = [c.strip() for c in _arc_cats.split(",") if c.strip()]
                            if _cat_names_to_restore:
                                _existing_cats = {c["name"]: c["id"] for c in db_get_categories()}
                                _restore_ids = [_existing_cats[n] for n in _cat_names_to_restore if n in _existing_cats]
                                if _restore_ids:
                                    db_set_game_categories(new_id, _restore_ids)

                elif _gt in ("gog",) or (_gt == "proton" and _store == "gog"):
                    # GOG: keyed by gog_id — silent full restore
                    _gog_id_restore = (d.get("gog_id") or "").strip()
                    if _gog_id_restore:
                        arc = con.execute("""
                            SELECT id, game_name, playtime_minutes, last_session_minutes, last_played,
                                   launch_args, env_vars, pre_launch_cmd, post_exit_cmd, auto_backup, ludusavi_title, gamescope_enabled, upscale_enabled, upscale_model, hdr_enabled, fsr4_upgrade, optiscaler_dll, use_wined3d, use_wow64, use_wayland, no_esync, no_fsync, no_ntsync, legacy_mediaconv, video_decode_mode, vn_jp_locale, added_at, category_names
                            FROM playtime_archive
                            WHERE game_type=? AND store_key=? AND store_key != ''
                            ORDER BY archived_at DESC LIMIT 1
                        """, (_gt, _gog_id_restore)).fetchone()
                        if arc:
                            con.execute(
                                "UPDATE games SET playtime_minutes=?, last_session_minutes=?, last_played=?, "
                                "launch_args=?, env_vars=?, pre_launch_cmd=?, post_exit_cmd=?, auto_backup=?, ludusavi_title=?, gamescope_enabled=?, upscale_enabled=?, upscale_model=?, hdr_enabled=?, fsr4_upgrade=?, optiscaler_dll=?, use_wined3d=?, use_wow64=?, use_wayland=?, no_esync=?, no_fsync=?, no_ntsync=?, legacy_mediaconv=?, video_decode_mode=?, vn_jp_locale=?, added_at=? WHERE id=?",
                                (arc[2], arc[3], arc[4],
                                 arc[5], arc[6], arc[7], arc[8], arc[9], arc[10], arc[11], arc[12], arc[13], arc[14], arc[15], arc[16], arc[17], arc[18], arc[19], arc[20], arc[21], arc[22], arc[23], arc[24], arc[25], arc[26],
                                 new_id))
                            con.commit()
                            self._set_status(f"Restored playtime and settings for {_gname}")
                            # Restore categories — match by name, skip any that no longer exist
                            _arc_cats = (arc[27] or "").strip()
                            if _arc_cats:
                                _cat_names_to_restore = [c.strip() for c in _arc_cats.split(",") if c.strip()]
                                if _cat_names_to_restore:
                                    _existing_cats = {c["name"]: c["id"] for c in db_get_categories()}
                                    _restore_ids = [_existing_cats[n] for n in _cat_names_to_restore if n in _existing_cats]
                                    if _restore_ids:
                                        db_set_game_categories(new_id, _restore_ids)

                else:
                    # Native / Proton: keyed by exe filename.
                    # Match is ambiguous (exe names can collide) so we prompt
                    # once for both playtime and config together.
                    _exe_filename = Path(_exe).name if _exe else ""
                    if _exe_filename:
                        arc = con.execute("""
                            SELECT id, game_name, playtime_minutes, last_session_minutes, last_played,
                                   launch_args, env_vars, pre_launch_cmd, post_exit_cmd, auto_backup, ludusavi_title, gamescope_enabled, upscale_enabled, upscale_model, hdr_enabled, fsr4_upgrade, optiscaler_dll, use_wined3d, use_wow64, use_wayland, no_esync, no_fsync, no_ntsync, legacy_mediaconv, video_decode_mode, vn_jp_locale, added_at, category_names
                            FROM playtime_archive
                            WHERE exe_filename=? AND game_type=?
                            ORDER BY archived_at DESC LIMIT 1
                        """, (_exe_filename, _gt)).fetchone()
                        if arc:
                            # Silent restore — no prompt for Native/Proton config/playtime.
                            # Only the prefix conflict (handled below) prompts the user.
                            con.execute(
                                "UPDATE games SET playtime_minutes=?, last_session_minutes=?, last_played=?, "
                                "launch_args=?, env_vars=?, pre_launch_cmd=?, post_exit_cmd=?, auto_backup=?, ludusavi_title=?, gamescope_enabled=?, upscale_enabled=?, upscale_model=?, hdr_enabled=?, fsr4_upgrade=?, optiscaler_dll=?, use_wined3d=?, use_wow64=?, use_wayland=?, no_esync=?, no_fsync=?, no_ntsync=?, legacy_mediaconv=?, video_decode_mode=?, vn_jp_locale=?, added_at=? WHERE id=?",
                                (arc[2], arc[3], arc[4],
                                 arc[5], arc[6], arc[7], arc[8], arc[9], arc[10], arc[11], arc[12], arc[13], arc[14], arc[15], arc[16], arc[17], arc[18], arc[19], arc[20], arc[21], arc[22], arc[23], arc[24], arc[25], arc[26],
                                 new_id))
                            con.commit()
                            self._set_status(f"Restored playtime and settings for {_gname}")
                            # Restore categories — match by name, skip any that no longer exist
                            _arc_cats = (arc[27] or "").strip()
                            if _arc_cats:
                                _cat_names_to_restore = [c.strip() for c in _arc_cats.split(",") if c.strip()]
                                if _cat_names_to_restore:
                                    _existing_cats = {c["name"]: c["id"] for c in db_get_categories()}
                                    _restore_ids = [_existing_cats[n] for n in _cat_names_to_restore if n in _existing_cats]
                                    if _restore_ids:
                                        db_set_game_categories(new_id, _restore_ids)

                # ── Prefix restore ─────────────────────────────────────────────
                _prefix_restore_msg = ""
                # For Proton/GOG games, try to match an archived prefix.
                # Matching strategy:
                #   Proton: match on exe_filename + game_type (exe always set)
                #   GOG:    match on store_key + game_type (GOG has no exe path)
                # Stage 1: strip articles, slugify, exact name compare → silent restore
                #          EXCEPTION: if an installer prefix also exists, show conflict
                #          dialog instead of silently restoring (see below).
                # Stage 2: fuzzy ratio >= 0.85 → prompt user
                if _gt in ("proton", "gog"):
                    import difflib, re as _re

                    def _norm(s: str) -> str:
                        s = _re.sub(r"^(the|a|an)\s+", "", s.strip().lower())
                        return slugify(s).lower()

                    _norm_new = _norm(_gname)
                    _exe_filename = Path(_exe).name if _exe else ""
                    _store_key_new = (_store or "").strip()

                    _candidates = []
                    if _exe_filename:
                        _candidates = con.execute("""
                            SELECT game_name, prefix_path FROM playtime_archive
                            WHERE exe_filename=? AND game_type=? AND prefix_path != ''
                            ORDER BY archived_at DESC
                        """, (_exe_filename, _gt)).fetchall()
                    elif _store_key_new:
                        _candidates = con.execute("""
                            SELECT game_name, prefix_path FROM playtime_archive
                            WHERE store_key=? AND game_type=? AND prefix_path != ''
                            ORDER BY archived_at DESC
                        """, (_store_key_new, _gt)).fetchall()

                    # Initialised here so the filesystem fallback below can read
                    # them even when _candidates is empty.
                    _arc_match_path = ""
                    _arc_match_name = ""
                    if _candidates:
                        # Find the best matching archived prefix that exists on disk

                        # Stage 1 — exact slug match
                        for _cname, _cpath in _candidates:
                            if not Path(_cpath).exists():
                                continue
                            if _norm(_cname) == _norm_new:
                                _arc_match_path = _cpath
                                _arc_match_name = _cname
                                break

                        # Stage 2 — fuzzy fallback (ratio >= 0.85)
                        if not _arc_match_path:
                            for _cname, _cpath in _candidates:
                                if not Path(_cpath).exists():
                                    continue
                                _ratio = difflib.SequenceMatcher(
                                    None, _norm(_cname), _norm_new).ratio()
                                if _ratio >= 0.85:
                                    _arc_match_path = _cpath
                                    _arc_match_name = _cname
                                    break

                        if _arc_match_path:
                            # ── Conflict: installer prefix + archived prefix both exist ──
                            # The user just ran the installer (fresh game install lives in
                            # _installed_pfx) AND there is an old prefix with potential
                            # saves. We cannot merge — prompt the user to pick one.
                            # The unchosen prefix is deleted immediately.
                            if _installed_pfx and Path(_installed_pfx).exists() \
                                    and _arc_match_path != _installed_pfx:
                                _box = NAGOMessageBox(
                                    "warning",
                                    "Two Prefixes Found",
                                    f"<b>{_gname}</b> has two Wine prefixes:<br><br>"
                                    f"<b>New</b> — fresh install (game files):<br>"
                                    f"<code>{_installed_pfx}</code><br><br>"
                                    f"<b>Old</b> — previous data (may contain saves):<br>"
                                    f"<code>{_arc_match_path}</code><br><br>"
                                    f"Keeping one will <b>permanently delete</b> the other.",
                                    parent=self,
                                    buttons=("Use New", "Use Old"),
                                    default_button="Use New",
                                )
                                _box.exec()
                                if _box.result_label() == "Use Old":
                                    # Keep old prefix — delete the new install prefix
                                    try:
                                        shutil.rmtree(_installed_pfx, ignore_errors=True)
                                        _NAGOLog.session(
                                            f"[add-game] conflict: user chose old prefix, "
                                            f"deleted new: {_installed_pfx}"
                                        )
                                    except Exception as _e:
                                        _NAGOLog.session(
                                            f"[warn] _add_game: failed to delete new prefix "
                                            f"{_installed_pfx}: {_e}"
                                        )
                                    con.execute("UPDATE games SET prefix_path=? WHERE id=?",
                                                (_arc_match_path, new_id))
                                    con.commit()
                                    _prefix_restore_msg = f"Kept old prefix for {_gname}"
                                else:
                                    # Keep new install prefix — delete the old one
                                    try:
                                        shutil.rmtree(_arc_match_path, ignore_errors=True)
                                        _NAGOLog.session(
                                            f"[add-game] conflict: user chose new prefix, "
                                            f"deleted old: {_arc_match_path}"
                                        )
                                    except Exception as _e:
                                        _NAGOLog.session(
                                            f"[warn] _add_game: failed to delete old prefix "
                                            f"{_arc_match_path}: {_e}"
                                        )
                                    # prefix_path already set to _installed_pfx — no DB update needed
                                    _prefix_restore_msg = f"Kept new prefix for {_gname}"
                                    # Restore archived playtime if the earlier pass didn't write it
                                    _cur_pt = con.execute(
                                        "SELECT playtime_minutes FROM games WHERE id=?",
                                        (new_id,)).fetchone()
                                    if not _cur_pt or (_cur_pt[0] or 0) == 0:
                                        _arc_pt = con.execute("""
                                            SELECT playtime_minutes, last_played
                                            FROM playtime_archive
                                            WHERE (exe_filename=? OR (store_key != '' AND store_key=?))
                                              AND game_type=?
                                            ORDER BY archived_at DESC LIMIT 1
                                        """, (_exe_filename or "", _store_key_new or "", _gt)).fetchone()
                                        if _arc_pt and (_arc_pt[0] or 0) > 0:
                                            con.execute(
                                                "UPDATE games SET playtime_minutes=?, last_played=? WHERE id=?",
                                                (_arc_pt[0], _arc_pt[1], new_id))
                                            con.commit()
                                            _NAGOLog.session(
                                                f"[add-game] conflict: restored playtime "
                                                f"{_arc_pt[0]}m for {_gname}"
                                            )

                            else:
                                # No installer prefix — normal silent/prompted restore
                                if _arc_match_path == _installed_pfx:
                                    # Archive points at same path we just renamed to — already correct
                                    _prefix_restore_msg = f"Prefix restored for {_gname}"
                                else:
                                    # Determine if this was a stage-1 (exact) or stage-2 (fuzzy) match
                                    _is_exact = any(
                                        _norm(c[0]) == _norm_new and c[1] == _arc_match_path
                                        for c in _candidates
                                    )
                                    if _is_exact:
                                        con.execute("UPDATE games SET prefix_path=? WHERE id=?",
                                                    (_arc_match_path, new_id))
                                        con.commit()
                                        _prefix_restore_msg = f"Prefix restored for {_gname}"
                                    else:
                                        # Fuzzy — prompt user
                                        _box = NAGOMessageBox(
                                            "question",
                                            "Restore Prefix?",
                                            f"Found a prefix that might belong to <b>{_gname}</b>:<br><br>"
                                            f"Previous name: <b>{_arc_match_name}</b><br>"
                                            f"<code>{_arc_match_path}</code><br><br>"
                                            f"Restore it for this game?",
                                            parent=self,
                                            buttons=("Restore", "Skip"),
                                            default_button="Skip",
                                        )
                                        _box.exec()
                                        if _box.result_label() == "Restore":
                                            con.execute("UPDATE games SET prefix_path=? WHERE id=?",
                                                        (_arc_match_path, new_id))
                                            con.commit()
                                            _prefix_restore_msg = f"Prefix restored for {_gname}"

                    # ── Prefix name scan ─────────────────────────────────────────────
                    # Always runs for proton/gog games on Add-Game Save.
                    # Scans the prefixes directory for any dir whose name starts with
                    # "{slug}_", excluding paths already handled above (_installed_pfx
                    # and _arc_match_path).  Two outcomes:
                    #   • New prefix exists (_installed_pfx set) + orphan found
                    #     → conflict dialog: user picks one, the other is deleted.
                    #   • No new prefix (_installed_pfx empty) + orphan found
                    #     → silent restore: point the new game at the existing prefix.
                    _pfx_root    = get_prefixes_root()
                    _slug_new_fs = slugify(_gname).lower()
                    _already_handled = {p for p in [_installed_pfx, _arc_match_path] if p}
                    try:
                        _disk_orphans = sorted(
                            [_p for _p in _pfx_root.iterdir()
                             if _p.is_dir()
                             and _p.name.lower().startswith(_slug_new_fs + "_")
                             and str(_p) not in _already_handled],
                            key=lambda _p: _p.stat().st_mtime,
                            reverse=True,   # most-recently-modified first
                        )
                    except OSError:
                        _disk_orphans = []
                    if _disk_orphans:
                        _disk_old = str(_disk_orphans[0])
                        if _installed_pfx and Path(_installed_pfx).exists():
                            # Two prefixes on disk — user must pick one
                            _box = NAGOMessageBox(
                                "warning",
                                "Two Prefixes Found",
                                f"<b>{_gname}</b> has two Wine prefixes:<br><br>"
                                f"<b>New</b> — fresh install (game files):<br>"
                                f"<code>{_installed_pfx}</code><br><br>"
                                f"<b>Old</b> — previous data (may contain saves):<br>"
                                f"<code>{_disk_old}</code><br><br>"
                                f"Keeping one will <b>permanently delete</b> the other.",
                                parent=self,
                                buttons=("Use New", "Use Old"),
                                default_button="Use New",
                            )
                            _box.exec()
                            if _box.result_label() == "Use Old":
                                try:
                                    shutil.rmtree(_installed_pfx, ignore_errors=True)
                                    _NAGOLog.session(
                                        f"[add-game] pfx-scan: chose old prefix, "
                                        f"deleted new: {_installed_pfx}"
                                    )
                                except Exception as _e:
                                    _NAGOLog.session(
                                        f"[warn] _add_game: failed to delete new prefix "
                                        f"{_installed_pfx}: {_e}"
                                    )
                                con.execute("UPDATE games SET prefix_path=? WHERE id=?",
                                            (_disk_old, new_id))
                                con.commit()
                                _prefix_restore_msg = f"Kept old prefix for {_gname}"
                            else:
                                # Keep new — delete all orphan slug matches
                                for _old_p in _disk_orphans:
                                    try:
                                        shutil.rmtree(str(_old_p), ignore_errors=True)
                                        _NAGOLog.session(
                                            f"[add-game] pfx-scan: chose new prefix, "
                                            f"deleted old: {_old_p}"
                                        )
                                    except Exception as _e:
                                        _NAGOLog.session(
                                            f"[warn] _add_game: failed to delete old prefix "
                                            f"{_old_p}: {_e}"
                                        )
                                _prefix_restore_msg = f"Kept new prefix for {_gname}"
                                # Restore archived playtime if the earlier pass didn't write it
                                _cur_pt = con.execute(
                                    "SELECT playtime_minutes FROM games WHERE id=?",
                                    (new_id,)).fetchone()
                                if not _cur_pt or (_cur_pt[0] or 0) == 0:
                                    _arc_pt = con.execute("""
                                        SELECT playtime_minutes, last_played
                                        FROM playtime_archive
                                        WHERE (exe_filename=? OR (store_key != '' AND store_key=?))
                                          AND game_type=?
                                        ORDER BY archived_at DESC LIMIT 1
                                    """, (_exe_filename or "", _store_key_new or "", _gt)).fetchone()
                                    if _arc_pt and (_arc_pt[0] or 0) > 0:
                                        con.execute(
                                            "UPDATE games SET playtime_minutes=?, last_played=? WHERE id=?",
                                            (_arc_pt[0], _arc_pt[1], new_id))
                                        con.commit()
                                        _NAGOLog.session(
                                            f"[add-game] pfx-scan: restored playtime "
                                            f"{_arc_pt[0]}m for {_gname}"
                                        )
                        else:
                            # No new install prefix — silently restore the existing one.
                            # Skip if the DB-based restore already matched and handled
                            # a prefix (_arc_match_path set); the orphan is a secondary
                            # stale dir that isn't needed.
                            if not _arc_match_path:
                                con.execute("UPDATE games SET prefix_path=? WHERE id=?",
                                            (_disk_old, new_id))
                                con.commit()
                                _NAGOLog.session(
                                    f"[add-game] pfx-scan: restored orphan prefix "
                                    f"for {_gname}: {_disk_old}"
                                )
                                _prefix_restore_msg = f"Prefix restored for {_gname}"

            finally:
                con.close()
            # Insert the new card in-place — no full rebuild, no flash.
            # Re-query the saved row so we get DB-generated fields (added_at, sort_pos).
            _con2 = db_con()
            _row = _con2.execute("SELECT * FROM games WHERE id=?", (new_id,)).fetchone()
            _cols = [desc[0] for desc in _con2.execute("SELECT * FROM games LIMIT 0").description]
            _con2.close()
            if _row:
                new_game = dict(zip(_cols, _row))
                lp = self.library_page
                lp._all_games.append(new_game)
                lp._game_cats[new_id] = set()
                card = GameCard(new_game,
                                accent_color=self.config.get("accent_color", DEFAULT_ACCENT))
                card.launch_requested.connect(lp._launch_game)
                card.edit_requested.connect(lp._edit_game)
                card.delete_requested.connect(lp._delete_game)
                card.cover_requested.connect(lp.pick_cover)
                card.categories_requested.connect(lp._assign_categories)
                card.show_log_requested.connect(lp._show_game_log)
                card.hide_requested.connect(lp._toggle_hide_game)
                card.delete_prefix_requested.connect(lp._delete_prefix)
                card.force_terminate_requested.connect(lp._force_terminate_game)
                card.run_in_prefix_requested.connect(lp._run_file_in_prefix)
                card.stop_prefix_run_requested.connect(lp._stop_prefix_run)
                card.setVisible(False)
                lp._cards[new_id] = card
                # Load cover if one was saved (pending cover already renamed above)
                cover = new_game.get("cover_path", "")
                if cover and Path(cover).exists():
                    lp._refresh_single_cover(new_id, cover)
            # Switch to library view — _show_library calls _apply_filter which
            # reflows the grid and makes the new card visible. No rebuild needed.
            self._show_library()
            if _prefix_restore_msg:
                self._set_status(_prefix_restore_msg)
            else:
                self._set_status(f"Added: {d['name']}")

    def _on_config_saved(self, cfg: dict):
        old_width  = self.config.get("card_width",   CARD_W)
        old_accent = self.config.get("accent_color", DEFAULT_ACCENT)
        old_theme  = self.config.get("theme", "dark")
        self.config = cfg
        self.library_page.update_config(cfg)

        width_changed  = cfg.get("card_width",   CARD_W)          != old_width
        accent_changed = cfg.get("accent_color", DEFAULT_ACCENT)  != old_accent
        theme_changed  = cfg.get("theme", "dark")                 != old_theme

        if width_changed or accent_changed or theme_changed:
            # _apply_stylesheet also calls _apply_palette — handles theme switch
            _apply_stylesheet(QApplication.instance(), cfg)
            # Proton count pill uses pillState property — refresh it
            self.settings_page._refresh_count_pill_theme()
            # Accent swatch rings depend on theme — re-style so the selected
            # swatch doesn't keep a stale border color after a theme switch.
            self.settings_page._refresh_swatch_borders()


        if (accent_changed or theme_changed) and not width_changed:
            # Update hover overlay accent on all existing cards without rebuilding
            new_accent = cfg.get("accent_color", DEFAULT_ACCENT)
            for card in self.library_page._cards.values():
                card.update_accent(new_accent)
            self._apply_hidden_btn_style(new_accent)
            # Propagate accent to drop containers so indicator lines stay in sync
            self.library_page.container.set_accent(new_accent)
            self._cat_container.set_accent(new_accent)


        # Apply play button visibility to all cards immediately
        show_play = bool(cfg.get("show_play_button", True))
        for card in self.library_page._cards.values():
            card.update_play_button(show_play)

        if width_changed:
            # Cards must be rebuilt at the new size
            self.library_page.reload(category_id=self._active_cat_id)

        self._set_status("Settings saved")

    def _set_status(self, msg: str):
        self.status_lbl.setText(f"  {msg}")
        QTimer.singleShot(4000, lambda: self.status_lbl.setText("  Ready"))

    # ── Frameless window helpers ──────────────────────────────────────────────

    def _make_win_btn(self, text: str, on_click, danger: bool = False) -> QPushButton:
        btn = QPushButton(text)
        btn.setObjectName("winCloseBtn" if danger else "winBtn")
        btn.setFixedSize(32, 36)
        btn.setCursor(QCursor(Qt.CursorShape.PointingHandCursor))
        btn.clicked.connect(on_click)
        return btn

    def _toggle_max(self):
        if self.isMaximized():
            self.showNormal()
            self._max_btn.setText("☐")
        else:
            self.showMaximized()
            self._max_btn.setText("❐")

    def changeEvent(self, event):
        super().changeEvent(event)
        from PyQt6.QtCore import QEvent as _QEvent
        if event.type() == _QEvent.Type.WindowStateChange:
            maximized = self.isMaximized()
            self._max_btn.setText("❐" if maximized else "☐")
            if maximized:
                # Remove translucency so the compositor clips to a plain rectangle,
                # eliminating the rounded-corner ghost outline at screen edges.
                self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, False)
                self.setStyleSheet("""
                    QMainWindow, QWidget#root {
                        border-radius: 0px; background: #1d1d20; border: none;
                    }
                    QWidget#sidebar {
                        border-top-left-radius: 0px;
                        border-bottom-left-radius: 0px;
                    }
                    QWidget#topbar {
                        border-top-right-radius: 0px;
                    }
                    QLabel#statusBar {
                        border-bottom-right-radius: 0px;
                    }
                """)
            else:
                # Restore translucency and rounded corners for windowed mode.
                self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
                self.setStyleSheet("")   # let the app stylesheet take over again

    # ── Resize from window edges ──────────────────────────────────────────────

    def _install_edge_filter(self):
        """Install event filter on the app to catch mouse events anywhere in window for edge resize."""
        QApplication.instance().installEventFilter(self)

    def eventFilter(self, obj, event):
        # Only handle mouse events on QWidgets that belong to this window
        if not isinstance(obj, QWidget):
            return super().eventFilter(obj, event)
        if not isinstance(event, QMouseEvent):
            return super().eventFilter(obj, event)
        if obj is not self and not self.isAncestorOf(obj):
            return super().eventFilter(obj, event)
        if self.isMaximized():
            return super().eventFilter(obj, event)

        et = event.type()
        if et == QEvent.Type.MouseMove:
            global_pos = event.globalPosition().toPoint()
            local = self.mapFromGlobal(global_pos)
            d = self._edge_at(local)
            if not event.buttons():
                self._set_resize_cursor(d)
        elif et == QEvent.Type.MouseButtonPress and event.button() == Qt.MouseButton.LeftButton:
            global_pos = event.globalPosition().toPoint()
            local = self.mapFromGlobal(global_pos)
            d = self._edge_at(local)
            if d:
                # Don't trigger resize on interactive widgets that need the click
                if isinstance(obj, (QPushButton, QLineEdit, QComboBox, NAGOCheckBox)):
                    return super().eventFilter(obj, event)
                edge = self._dir_to_edge(d)
                handle = self.windowHandle()
                if handle is not None:
                    handle.startSystemResize(edge)
                    event.accept()
                    return True
        return super().eventFilter(obj, event)

    def _edge_at(self, pos) -> str:
        m = self._resize_margin
        w, h = self.width(), self.height()
        x, y = pos.x(), pos.y()
        # Only consider edge if the position is inside the window
        if x < 0 or y < 0 or x > w or y > h:
            return ""
        left   = x <= m
        right  = x >= w - m
        top    = y <= m
        bottom = y >= h - m
        if top and left:    return "tl"
        if top and right:   return "tr"
        if bottom and left: return "bl"
        if bottom and right:return "br"
        if left:            return "l"
        if right:           return "r"
        if top:             return "t"
        if bottom:          return "b"
        return ""

    def _dir_to_edge(self, d: str):
        E = Qt.Edge
        m = {
            "l":  E.LeftEdge,
            "r":  E.RightEdge,
            "t":  E.TopEdge,
            "b":  E.BottomEdge,
            "tl": E.TopEdge    | E.LeftEdge,
            "tr": E.TopEdge    | E.RightEdge,
            "bl": E.BottomEdge | E.LeftEdge,
            "br": E.BottomEdge | E.RightEdge,
        }
        return m.get(d, E.RightEdge)

    def _set_resize_cursor(self, d: str):
        cursors = {
            "l":  Qt.CursorShape.SizeHorCursor,  "r":  Qt.CursorShape.SizeHorCursor,
            "t":  Qt.CursorShape.SizeVerCursor,  "b":  Qt.CursorShape.SizeVerCursor,
            "tl": Qt.CursorShape.SizeFDiagCursor,"br": Qt.CursorShape.SizeFDiagCursor,
            "tr": Qt.CursorShape.SizeBDiagCursor,"bl": Qt.CursorShape.SizeBDiagCursor,
        }
        if d:
            self.setCursor(QCursor(cursors[d]))
        else:
            self.unsetCursor()


# ── Entry point ────────────────────────────────────────────────────────────────
# ── Single-instance lock ──────────────────────────────────────────────────────
# Uses a Unix domain socket in /tmp. First instance creates and listens.
# Second instance connects, sends "raise", and exits immediately.
# Stale socket (from a crash) is detected via "connection refused" and replaced.
_INSTANCE_SOCKET = Path("/tmp/nago-launcher.sock")

class _RaiseSignalEmitter(QObject):
    """Tiny QObject that lives on the main thread and emits raise_window."""
    raise_window = pyqtSignal()

class _InstanceListener(threading.Thread):
    """Background thread that listens for second-instance connections."""
    def __init__(self, sock: socket.socket, emitter: _RaiseSignalEmitter):
        super().__init__(daemon=True, name="nago-instance-listener")
        self._sock = sock
        self._emitter = emitter

    def run(self):
        while True:
            try:
                conn, _ = self._sock.accept()
                with conn:
                    try:
                        msg = conn.recv(16).decode("utf-8", errors="ignore").strip()
                        if msg == "raise":
                            self._emitter.raise_window.emit()
                    except Exception:
                        pass
            except Exception:
                break  # socket closed — app is shutting down


def _acquire_instance_lock() -> "_InstanceListener | None":
    """Try to become the first instance.
    Returns a running _InstanceListener if we are the first instance.
    Returns None and exits the process if another instance is already running."""
    # Try connecting first — if it succeeds, a first instance is running.
    try:
        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        s.settimeout(0.5)
        s.connect(str(_INSTANCE_SOCKET))
        s.sendall(b"raise")
        s.close()
        sys.exit(0)  # second instance — exit silently
    except (ConnectionRefusedError, FileNotFoundError):
        pass  # no listener — we are the first instance
    except OSError:
        pass

    # Clean up stale socket file if present
    try:
        _INSTANCE_SOCKET.unlink()
    except FileNotFoundError:
        pass

    # Create listening socket
    srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    srv.bind(str(_INSTANCE_SOCKET))
    srv.listen(1)

    emitter = _RaiseSignalEmitter()
    listener = _InstanceListener(srv, emitter)
    listener.start()
    return listener, emitter, srv
def main():
    # Single-instance check — exits here if another instance is running
    _lock_result = _acquire_instance_lock()

    # Force Fusion style BEFORE QApplication so file dialogs inherit dark palette
    os.environ.setdefault("QT_QPA_PLATFORMTHEME", "")
    # NAGOStyle (installed in _run_app) wraps Fusion — no need to pre-set it here.

    # _safe_excepthook is already installed at module level above.

    # Top-level guard: if anything raises before or after app.exec(), we catch it
    # here so the exception is never alive during interpreter shutdown.  Python 3.14
    # changed how it cleans up exception state on exit; a live traceback that holds
    # a reference to a QApplication or QWidget (via local variables in stack frames)
    # causes SIP to try to access an already-destroyed C++ object → SIGSEGV.
    # NOTE: BaseException (not Exception) so SystemExit / KeyboardInterrupt are
    # also caught and don't escape to Python's internal _PyErr_PrintEx path.
    _listener, _emitter, _srv = _lock_result
    _exit_code = 0
    try:
        _exit_code = _run_app(_emitter)
    except BaseException:  # noqa: BLE001
        import traceback as _tb
        _tb.print_exc()
        _exit_code = 1
    finally:
        # Scrub all exception/traceback state from the interpreter before shutdown.
        # Python 3.14 + SIP 13.11 will SEGV if any live traceback frame holds a
        # reference to a Qt wrapper object when QApplication is being deallocated.
        # _run_app() already called `del win; del app` so Qt is fully shut down;
        # wiping sys.last_* and the current exception chain ensures no stale frame
        # survives into GC teardown.
        for _attr in ("last_exc", "last_traceback", "last_value", "last_type"):
            try:
                setattr(sys, _attr, None)
            except AttributeError:
                pass
        sys.excepthook = sys.__excepthook__

    # os._exit() bypasses Python's GC entirely — safe here because Qt has already
    # been torn down inside _run_app() via `del win; del app`.  This is the
    # recommended workaround for PyQt6 + Python 3.12+ where GC dealloc order can
    # trigger SIP use-after-free on wrapped QObjects during interpreter shutdown.
    try:
        _srv.close()
        _INSTANCE_SOCKET.unlink()
    except Exception:
        pass
    os._exit(_exit_code)


def _run_app(_emitter: "_RaiseSignalEmitter") -> int:
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setApplicationVersion(VERSION)
    # Tell KDE/GNOME the desktop file name so startup-notification is dismissed
    # as soon as the window appears, stopping the bouncing cursor immediately.
    app.setDesktopFileName("nago-launcher")
    # App-wide icon (used by file dialogs, message boxes, splash, etc.)
    if LOGO_PATH.exists():
        app.setWindowIcon(QIcon(str(LOGO_PATH)))

    # Load the Phosphor icon font before any widgets are built
    _load_phosphor_font()

    # Apply palette (dark or light) based on saved theme preference.
    # _apply_stylesheet (called below) also calls _apply_palette, but doing it
    # here first ensures file dialogs and message boxes that Qt creates before
    # MainWindow inherit the correct palette from the start.
    _apply_palette(app, load_config())

    # Install NAGO's custom style proxy — draws checkboxes using Phosphor icons.
    app.setStyle(NAGOStyle("Fusion"))

    # Load and apply stylesheet with accent color from config.
    _apply_stylesheet(app, load_config())

    win = MainWindow()
    _emitter.raise_window.connect(win._raise_window)
    win.show()

    # Keyboard shortcuts
    from PyQt6.QtGui import QShortcut, QKeySequence
    QShortcut(QKeySequence("Ctrl+N"), win, activated=win._add_game)
    QShortcut(QKeySequence("Ctrl+F"), win, activated=lambda: win.search_box.setFocus())
    QShortcut(QKeySequence("Escape"), win,
              activated=lambda: (win.search_box.clear(), win.search_box.clearFocus()))

    exit_code = app.exec()

    # Explicit cleanup order matters on Python 3.14+ with PyQt6/SIP.
    # Wrap the entire teardown in try/except BaseException so that if anything
    # raises during widget destruction (e.g. a timer callback firing into a
    # half-deleted widget), we catch it and scrub exception state immediately —
    # before Python's GC has a chance to walk the traceback chain and call
    # SIP's cleanup_qobject on already-freed C++ objects.
    try:
        app.processEvents()          # flush pending signal deliveries / paint events
        gc.collect()                 # collect Python-side circular refs before Qt teardown
        del win
        app.processEvents()          # drain events queued during widget teardown
        del app
    except BaseException:
        # Scrub exception chain immediately — don't let any frame ref survive
        import sys as _sys
        _ex = _sys.exc_info()[1]
        _next = None
        while _ex is not None:
            try:
                _ex.__traceback__ = None
            except Exception:
                pass
            _next = getattr(_ex, "__context__", None) or getattr(_ex, "__cause__", None)
            if _next is _ex:
                break
            _ex = _next
        del _ex, _next

    return exit_code


if __name__ == "__main__":
    main()
