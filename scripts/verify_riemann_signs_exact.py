#!/usr/bin/env python3
"""Replay the sweep-free exact certificate for q, F2, and C4.

The maintained algebraic core lives beside this launcher. This launcher forces
SymPy's pure-Python rational domain and rejects every attempted FLINT import,
so a successful replay also checks the stated dependency boundary.
"""

from __future__ import annotations

import importlib.abc
import os
from pathlib import Path
import runpy
import sys


class _RejectFlint(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        if fullname == "flint" or fullname.startswith("flint."):
            raise ImportError(f"FLINT import forbidden by exact certificate: {fullname}")
        return None


ROOT = Path(__file__).resolve().parents[1]
VERIFIER = (
    ROOT
    / "scripts"
    / "verify_riemann_signs_core.py"
)

if not VERIFIER.is_file():
    raise SystemExit(f"missing promoted verifier artifact: {VERIFIER}")

os.environ["SYMPY_GROUND_TYPES"] = "python"
sys.meta_path.insert(0, _RejectFlint())
import sympy as sp


def check_pf3_slope_identity() -> None:
    t, a, b, z = sp.symbols("t a b z", positive=True)
    ell = sp.Function("ell")
    s = lambda value: sp.diff(ell(z), z).subs(z, value)
    q = lambda value: -sp.diff(ell(z), z, 2).subs(z, value)
    log_ratio = (
        ell(t - b)
        - ell(t + a)
        + sp.log(s(t - b) - s(t))
        - sp.log(s(t) - s(t + a))
    )
    slope = (
        s(t - b)
        - s(t + a)
        + (q(t) - q(t - b)) / (s(t - b) - s(t))
        - (q(t + a) - q(t)) / (s(t) - s(t + a))
    )
    if sp.simplify(sp.diff(log_ratio, t) - slope) != 0:
        raise AssertionError("PF3 logarithmic slope identity failed")


check_pf3_slope_identity()
print("PASS exact generic PF3 logarithmic slope identity")
runpy.run_path(str(VERIFIER), run_name="__main__")
print("PASS certificate launcher rejected FLINT imports")
print("status=sweep-free exact global q,F2,C4 certificate passed")
