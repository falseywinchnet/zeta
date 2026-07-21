#!/usr/bin/env python3
"""Promote the exact generated CERT12 tables without copying draft semantics."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "work" / "2026-07-21-cert12-lean-inequalities"
TARGET = ROOT / "proof" / "formal" / "PF4"


def after_second(text: str, marker: str) -> str:
    first = text.index(marker)
    return text[text.index(marker, first + len(marker)) :]


finite = (SOURCE / "CERT12FiniteMargins.lean").read_text()
finite_body = after_second(finite, "namespace PF4.CERT12Inequalities\n")
finite_body = finite_body.replace(
    " / i !", " / (Nat.factorial i : ℝ)"
)
finite_body = finite_body.replace(
    "(Real.exp_pos 1).le Real.exp_one_lt_d9 (by omega)",
    "Real.exp_one_lt_d9 (Real.exp_pos 1).le (by omega)",
)
finite_body = finite_body.replace(
    "  intro i hi j hj\n  interval_cases",
    "  intro i hi j hj\n  simp only [Finset.mem_range] at hi hj\n  interval_cases",
)
finite_body = finite_body.replace(
    "  intro j hj k hk\n  interval_cases",
    "  intro j hj k hk\n  simp only [Finset.mem_range] at hj hk\n  interval_cases",
)
finite_body = finite_body.replace(
    "  intro j hj\n  interval_cases",
    "  intro j hj\n  simp only [Finset.mem_range] at hj\n  interval_cases",
)
finite_body = finite_body.replace(
    "bernsteinBasis_eq, Nat.choose]",
    "bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]",
)
def between(text: str, start: str, end: str) -> str:
    return text[text.index(start) : text.index(end)]


q_body = between(
    finite_body,
    "noncomputable def qCorePolynomial",
    "noncomputable def f2CorePolynomial",
)
q_margin_body = between(
    finite_body,
    "noncomputable def qMarginCorePolynomial",
    "noncomputable def f2MarginCorePolynomial",
)
q_combined = (q_body + q_margin_body).replace("<;> ring", "<;> ring_nf")
(TARGET / "CERT12QMargins.lean").write_text(
    "import PF4.CERT12Bernstein\n"
    "import Mathlib.Tactic\n\n"
    "set_option linter.style.header false\n"
    "set_option linter.style.longLine false\n"
    "set_option linter.style.setOption false\n"
    "set_option linter.unnecessarySeqFocus false\n"
    "set_option maxHeartbeats 2000000\n"
    "set_option maxRecDepth 100000\n\n"
    "/-! Independently checked q continuum margins from the CERT12 tables. -/\n\n"
    "namespace PF4.CERT12Inequalities.Generated\n\n"
    + q_combined
    + "end PF4.CERT12Inequalities.Generated\n"
)

perturbation = (SOURCE / "CERT12PerturbationBounds.lean").read_text()
marker = "namespace PF4.CERT12Inequalities.Perturbation.Generated\n"
perturbation_body = perturbation[perturbation.index(marker) :]
perturbation_body = perturbation_body.replace("; powers :=", ", powers :=")
perturbation_body = perturbation_body.replace(
    "def coreE : Fin 7 → ℝ", "noncomputable def coreE : Fin 7 → ℝ"
)
perturbation_body = perturbation_body.replace(
    "def outerE : Fin 7 → ℝ", "noncomputable def outerE : Fin 7 → ℝ"
)
perturbation_body = perturbation_body.replace(
    "Fin.prod_univ_succ]",
    "prod_fin7_erase, Matrix.cons_val_two, Matrix.cons_val_three, "
    "Matrix.cons_val_four, Fin.prod_univ_succ]",
)
perturbation_body = perturbation_body.replace(
    "  norm_num [",
    "  norm_num (config := { maxSteps := 10000000 }) [",
)
(TARGET / "CERT12PerturbationBounds.lean").write_text(
    "import PF4.CERT12Perturbation\n"
    "import Mathlib.Tactic\n\n"
    "set_option linter.style.header false\n\n"
    "set_option linter.style.longLine false\n"
    "set_option linter.style.setOption false\n\n"
    "set_option maxHeartbeats 2000000\n\n"
    "set_option maxRecDepth 100000\n\n"
    "/-! Exact generated perturbation budgets; promoted from the replayable "
    "CERT12 artifact. -/\n\n"
    + perturbation_body
)
