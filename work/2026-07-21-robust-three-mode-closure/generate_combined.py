#!/usr/bin/env python3
"""Compose prior checked advancement modules with the current closure body."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCES = [
    ROOT / "work/2026-07-21-infinite-tail-theorem-refactor/RelativeTailRefactor.lean",
    ROOT / "work/2026-07-21-cert12-lean-inequalities/CERT12FiniteMargins.lean",
    ROOT / "work/2026-07-21-cert12-lean-inequalities/CERT12PerturbationBounds.lean",
    Path(__file__).with_name("C4MidCertificates.lean"),
    Path(__file__).with_name("RobustThreeModeClosureBody.lean"),
]
OUT = Path(__file__).with_name("RobustThreeModeClosureCombined.lean")


def without_imports(text: str) -> str:
    return "\n".join(line for line in text.splitlines() if not line.startswith("import "))


header = """import PF4.ClearedJetCertificateBridge
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic

set_option linter.style.header false

/-! Generated all-in-one replay for the robust three-mode closure round. -/
"""

OUT.write_text(
    header + "\n\n" + "\n\n".join(without_imports(path.read_text()) for path in SOURCES)
    + "\n"
)
