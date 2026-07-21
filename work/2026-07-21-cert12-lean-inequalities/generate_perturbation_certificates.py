#!/usr/bin/env python3
"""Generate Lean-checkable cleared-polynomial perturbation budgets."""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path

os.environ["SYMPY_GROUND_TYPES"] = "python"

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "cert12_core", ROOT / "scripts" / "verify_riemann_signs_core.py"
)
core = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(core)
sp = core.sp


def rat(value) -> str:
    value = sp.Rational(value)
    if value.q == 1:
        return str(value.p)
    return f"({value.p} / {value.q} : ℚ)"


def real_rat(value) -> str:
    value = sp.Rational(value)
    if value.q == 1:
        return str(value.p)
    return f"({value.p} / {value.q} : ℝ)"


def vector(values, render) -> str:
    return "![" + ", ".join(render(v) for v in values) + "]"


def terms_definition(name: str, poly) -> tuple[str, int]:
    terms = sp.Poly(poly, core.RAW).terms()
    entries = []
    for powers, coefficient in terms:
        entries.append(
            "{ coeff := " + rat(coefficient) +
            "; powers := " + vector(powers, str) + " }"
        )
    return (
        f"def {name} : Fin {len(entries)} → Monomial 7 :=\n  "
        + vector(entries, lambda x: x),
        len(entries),
    )


polys = {
    "q": core.raw_q,
    "f2": core.raw_f2,
    "c4": core.raw_h4,
}
margins = {"q": 10, "f2": 1000, "c4": 50_000_000}
core_B = list(map(sp.Rational, core.CORE_BASE))
core_E = [sp.Rational(v.numerator, v.denominator) for v in core.CORE_TAIL]
outer_B = [sp.Rational(2 * core.ENVELOPE[j] * 5**j) for j in range(7)]
outer_E = [
    sp.Rational(core.ENVELOPE[j] * 5**j * 3**(2*j+4), 10**17)
    for j in range(7)
]

source = (HERE / "PerturbationCertificate.lean").read_text()
out = [source, "\nnamespace PF4.CERT12Inequalities.Perturbation.Generated\n",
       "open PF4.CERT12Inequalities.Perturbation\n"]

out.append("def coreB : Fin 7 → ℝ := " + vector(core_B, real_rat))
out.append("def coreE : Fin 7 → ℝ := " + vector(core_E, real_rat))
out.append("def outerB : Fin 7 → ℝ := " + vector(outer_B, real_rat))
out.append("def outerE : Fin 7 → ℝ := " + vector(outer_E, real_rat))

for name, poly in polys.items():
    term_def, count = terms_definition(f"{name}Terms", poly)
    out.append(term_def)
    cleared = {"q": "clearedQ", "f2": "clearedF2", "c4": "clearedC4"}[name]
    args = " ".join(f"(a {i})" for i in range({"q": 3, "f2": 5, "c4": 7}[name]))
    out.append(
        f"theorem {name}Terms_value (a : Fin 7 → ℝ) :\n"
        f"    polynomialValue {name}Terms a =\n"
        f"      PF4.ClearedJetCertificateBridge.{cleared} {args} := by\n"
        f"  simp [polynomialValue, {name}Terms, monomialValue, Fin.sum_univ_succ, "
        f"Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.{cleared}]\n"
        f"  ring\n"
    )
    for region in ("core", "outer"):
        cap = region.capitalize()
        B, E = f"{region}B", f"{region}E"
        out.append(
            f"theorem {name}{cap}Budget_lt :\n"
            f"    polynomialErrorBudget {name}Terms {B} {E} < {margins[name]} := by\n"
            f"  norm_num [polynomialErrorBudget, monomialErrorBudget, {name}Terms, "
            f"{B}, {E}, Fin.sum_univ_succ, Fin.prod_univ_succ]\n"
        )
        out.append(
            f"theorem abs_{name}_perturbation_lt_{region}\n"
            f"    (a e : Fin 7 → ℝ)\n"
            f"    (ha : ∀ i, |a i| ≤ {B} i) (he : ∀ i, |e i| ≤ {E} i) :\n"
            f"    |PF4.ClearedJetCertificateBridge.{cleared} "
            + " ".join(f"(a {i} + e {i})" for i in range({"q": 3, "f2": 5, "c4": 7}[name]))
            + f" - PF4.ClearedJetCertificateBridge.{cleared} {args}| < {margins[name]} := by\n"
            f"  have h := abs_polynomialValue_add_sub_le {name}Terms a e {B} {E}\n"
            f"    (by intro i; fin_cases i <;> norm_num [{B}])\n"
            f"    (by intro i; fin_cases i <;> norm_num [{E}]) ha he\n"
            f"  rw [{name}Terms_value, {name}Terms_value] at h\n"
            f"  exact h.trans_lt {name}{cap}Budget_lt\n"
        )

out.append(r'''
theorem clearedQ_pos_of_base_margin_and_core_error
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i)
    (hbase : 10 < PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2)) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) := by
  have h := abs_q_perturbation_lt_core a e ha he
  rw [abs_lt] at h
  linarith

theorem clearedF2_pos_of_base_margin_and_core_error
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i)
    (hbase : 1000 < PF4.ClearedJetCertificateBridge.clearedF2
      (a 0) (a 1) (a 2) (a 3) (a 4)) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) := by
  have h := abs_f2_perturbation_lt_core a e ha he
  rw [abs_lt] at h
  linarith

theorem clearedC4_pos_of_base_margin_and_core_error
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i)
    (hbase : 50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3)
      (a 4 + e 4) (a 5 + e 5) (a 6 + e 6) := by
  have h := abs_c4_perturbation_lt_core a e ha he
  rw [abs_lt] at h
  linarith
''')

out.append("end PF4.CERT12Inequalities.Perturbation.Generated\n")
(HERE / "CERT12PerturbationBounds.lean").write_text("\n".join(out))
print(f"generated {HERE / 'CERT12PerturbationBounds.lean'}")
