#!/usr/bin/env python3
"""NAGO launcher stub.

Running `python nago-launcher.py` directly recompiles all ~22k lines of
source on EVERY launch — Python only caches bytecode (__pycache__/*.pyc)
for IMPORTED modules, never for scripts. This stub imports nago-launcher.py
through the import machinery, so the compiled bytecode is written once and
reused on every launch after the first (saves a few hundred ms per start;
the cache auto-invalidates whenever nago-launcher.py changes).

Launch via:   python3 nago.py        (or point your .desktop Exec here)
Direct launch (`python nago-launcher.py`) still works unchanged — this
stub is an optional fast path, not a requirement.

This file is write-once. All development happens in nago-launcher.py.
"""
import importlib.util
import sys
from pathlib import Path

_src = Path(__file__).resolve().parent / "nago-launcher.py"
_spec = importlib.util.spec_from_file_location("nago_launcher", _src)
_mod = importlib.util.module_from_spec(_spec)
# Register before exec so anything looking up sys.modules mid-import finds it.
sys.modules["nago_launcher"] = _mod
_spec.loader.exec_module(_mod)
# __name__ is "nago_launcher" here, not "__main__" — the guard at the bottom
# of nago-launcher.py doesn't fire, so call main() explicitly.
_mod.main()
