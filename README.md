# NAGO Launcher

Smooth to use, good looking GUI, light and compact, and above all, works without any issues.

A Linux game launcher for Native, Proton, GOG, and Steam games. Built with Python and PyQt6. In active development.

![NAGO Launcher](icons/nago-logo.png)

---

## Features

- **Multiple game types** — Native Linux, Proton (via umu-launcher), GOG, and Steam
- **Cover art** — automatic fetching from SteamGridDB and VNDB
- **Import** — import games from Steam, Heroic, and Lutris libraries
- **Extended GOG support** — breadcrumb-based install detection, Heroic and Lutris GOG import
- **Extended Visual Novel support** — Japanese and Western VNs, VNDB cover search
- **AI upscaling** — per-game AI upscale toggle with model selection, powered by [linux-rt-upscaler](https://github.com/baronsmv/linux-rt-upscaler)
- **Per-game Wine prefixes** — each game gets its own isolated prefix
- **Save backups** — [ludusavi](https://github.com/mtkennerly/ludusavi) integration for backup and restore
- **In-game upscaler detection** — detects FSR 4, FSR 3.1, FSR 2, DLSS, and XeSS DLLs in game directories
- **Proton management** — auto-detects all installed Proton versions (GE-Proton, CachyOS Proton, Steam Proton, system-installed)
- **umu-launcher integration** — all Proton/GOG games run through umu unconditionally; auto-installs on first run
- **Sync support** — esync, fsync, and ntsync per game
- **FSR 4 / OptiScaler** — per-game FSR environment variable controls
- **Custom launch options** — pre/post launch commands, environment variable overrides
- **Categories** — organize your library with custom categories
- **Drag and drop** — reorder game cards by dragging
- **Light/Dark theme** — toggle between themes
- **Dark themed UI** — custom Qt stylesheet, Phosphor icon font
- Built primarily for **KDE Wayland**, but should work on all desktop environments (more testing needed)
- No direct installer yet

---

## Requirements

### System packages

| Package | Purpose |
|---|---|
| `python` 3.10+ | Runtime |
| `qt6-wayland` | Native Wayland support (Hyprland, Sway, KDE Wayland, etc.) |

Install on Arch:
```bash
sudo pacman -S python qt6-wayland
```

Install on Fedora:
```bash
sudo dnf install python3 qt6-qtwayland
```

### Python packages

```bash
pip install PyQt6 requests Pillow
```

> If you use a virtual environment, create it with `--system-site-packages` if system Python packages are already installed, to avoid duplicating them.

### Runtime tools (auto-installed on first run)

NAGO will download and install these automatically to `~/.local/share/nago-launcher/tools/`:

- [umu-launcher](https://github.com/Open-Wine-Components/umu-launcher) — Proton/GOG game runner
- [ludusavi](https://github.com/mtkennerly/ludusavi) — save backup and restore
- [winetricks](https://github.com/Winetricks/winetricks) — Wine runtime installer

### Proton

NAGO does not bundle Proton. Install at least one:

- **GE-Proton** (recommended) — [Releases](https://github.com/GloriousEggroll/proton-ge-custom/releases) or AUR: `proton-ge-custom`
- **CachyOS Proton** — `sudo pacman -S proton-cachyos` (CachyOS only)
- **Steam Proton** — installed automatically if Steam is present

---

## Installation

1. Clone or download this repository
2. Place all files in a directory of your choice, e.g. `~/nago-launcher/`
3. Make sure the `icons/` folder is present alongside `nago-launcher.py`
4. Run:

```bash
python nago-launcher.py
```

### Optional: Desktop entry

To add NAGO to your application launcher:

```bash
cp nago-launcher.desktop ~/.local/share/applications/
```

Edit the `Exec=` and `Icon=` lines in the `.desktop` file to point to your install location.

---

## Notes

- All game data, prefixes, covers, and logs are stored under `~/.local/share/nago-launcher/`
- No hardcoded paths — NAGO respects `XDG_DATA_HOME` and runs from any location
- Tested on Fedora (KDE Wayland) and Arch Linux (Hyprland)

---

## License

WIP
