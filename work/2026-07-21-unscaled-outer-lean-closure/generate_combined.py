#!/usr/bin/env python3
"""Compose the checked compact replay with the unscaled outer body."""
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SOURCES = [
    ROOT / "work/2026-07-21-robust-three-mode-closure/RobustThreeModeClosureCombined.lean",
    ROOT / "work/2026-07-21-global-kernel-jet-identification/GlobalKernelJetIdentification.lean",
    HERE / "C4OuterMarginData.lean",
    HERE / "UnscaledOuterClosureBody.lean",
]
OUT = HERE / "UnscaledOuterClosureCombined.lean"
def without_imports(text):
    return "\n".join(line for line in text.splitlines()
                     if not line.startswith("import "))
header = """import PF4.KernelAnalytic
import PF4.ClearedJetCertificateBridge
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic

set_option linter.style.header false
"""
OUT.write_text(header + "\n\n" + "\n\n".join(
    without_imports(path.read_text()) for path in SOURCES) + "\n")
