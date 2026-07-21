#!/usr/bin/env python3
"""Promote the remaining CERT12 continuum tables into narrow Lean modules."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = (
    ROOT
    / "work"
    / "2026-07-21-cert12-lean-inequalities"
    / "CERT12FiniteMargins.lean"
)
TARGET = ROOT / "proof" / "formal" / "PF4"


def after_second(text: str, marker: str) -> str:
    first = text.index(marker)
    return text[text.index(marker, first + len(marker)) :]


def between(text: str, start: str, end: str) -> str:
    return text[text.index(start) : text.index(end)]


def repair(text: str) -> str:
    text = text.replace(
        "  intro i hi j hj\n  interval_cases",
        "  intro i hi j hj\n"
        "  simp only [Finset.mem_range] at hi hj\n"
        "  interval_cases",
    )
    text = text.replace(
        "bernsteinBasis_eq, Nat.choose]",
        "bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]",
    )
    return text.replace("<;> ring", "<;> ring_nf")


def write_module(name: str, description: str, body: str) -> None:
    (TARGET / f"{name}.lean").write_text(
        "import PF4.CERT12Bernstein\n"
        "import Mathlib.Tactic\n\n"
        "set_option linter.style.header false\n"
        "set_option linter.style.longLine false\n"
        "set_option linter.style.setOption false\n"
        "set_option linter.unnecessarySeqFocus false\n"
        "set_option maxHeartbeats 2000000\n"
        "set_option maxRecDepth 100000\n\n"
        f"/-! {description} -/\n\n"
        "namespace PF4.CERT12Inequalities.Generated\n\n"
        + repair(body)
        + "end PF4.CERT12Inequalities.Generated\n"
    )


source = SOURCE.read_text()
body = after_second(source, "namespace PF4.CERT12Inequalities\n")

write_module(
    "CERT12F2Margins",
    "Independently checked F2 continuum margins from the CERT12 tables.",
    between(
        body,
        "noncomputable def f2CorePolynomial",
        "noncomputable def c4CorePolynomial",
    )
    + between(
        body,
        "noncomputable def f2MarginCorePolynomial",
        "noncomputable def c4MarginCorePolynomial",
    ),
)

write_module(
    "CERT12C4Margins",
    "Independently checked C4 continuum margins from the CERT12 tables.",
    between(
        body,
        "noncomputable def c4CorePolynomial",
        "noncomputable def qMarginCorePolynomial",
    )
    + between(
        body,
        "noncomputable def c4MarginCorePolynomial",
        "noncomputable def base0UpperPolynomial",
    ),
)

write_module(
    "CERT12BaseBounds",
    "Seven independently checked compact three-mode jet coordinate bounds.",
    between(
        body,
        "noncomputable def base0UpperPolynomial",
        "noncomputable def f2OuterPolynomial",
    ),
)
