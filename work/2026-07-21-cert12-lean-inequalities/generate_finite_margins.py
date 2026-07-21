#!/usr/bin/env python3
"""Generate Lean source for the finite Bernstein parts of CERT12.

The output repeats the checked generic semantics from BernsteinCertificate.lean
and appends exact polynomial identities plus rational coefficient tables.  It
is generated data, not a trusted proof: Lean rechecks every table bound and
every polynomial identity.
"""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path

os.environ["SYMPY_GROUND_TYPES"] = "python"

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CORE = ROOT / "scripts" / "verify_riemann_signs_core.py"

spec = importlib.util.spec_from_file_location("cert12_core", CORE)
core = importlib.util.module_from_spec(spec)
assert spec.loader is not None
spec.loader.exec_module(core)
sp = core.sp


def lean_rat(value) -> str:
    value = sp.Rational(value)
    if value.q == 1:
        return str(value.p)
    return f"({value.p} / {value.q} : ℚ)"


def lean_real_rat(value) -> str:
    value = sp.Rational(value)
    if value.q == 1:
        return f"({value.p} : ℝ)"
    return f"(({value.p} : ℝ) / {value.q})"


def lean_expr(expr, variables: dict) -> str:
    expr = sp.expand(expr)
    if expr.is_Integer or expr.is_Rational:
        return lean_real_rat(expr)
    if expr.is_Symbol:
        return variables[expr]
    if expr.is_Add:
        return "(" + " + ".join(lean_expr(a, variables) for a in expr.args) + ")"
    if expr.is_Mul:
        return "(" + " * ".join(lean_expr(a, variables) for a in expr.args) + ")"
    if expr.is_Pow and expr.exp.is_Integer and expr.exp >= 0:
        return f"({lean_expr(expr.base, variables)} ^ {expr.exp})"
    raise TypeError(f"unsupported expression: {expr!r}")


def bernstein_coefficients(poly, xlo, xhi, ylo, yhi):
    transformed = sp.Poly(sp.expand(poly.subs({
        core.x: xlo + (xhi - xlo) * core.w,
        core.y: ylo + (yhi - ylo) * core.v,
    })), core.w, core.v)
    dx, dy = transformed.degree(core.w), transformed.degree(core.v)
    power = {(i, j): transformed.coeff_monomial(core.w**i * core.v**j)
             for i in range(dx + 1) for j in range(dy + 1)}
    coeff = {}
    for k in range(dx + 1):
        for ell in range(dy + 1):
            coeff[k, ell] = sp.factor(sum(
                power[i, j]
                * sp.binomial(k, i) / sp.binomial(dx, i)
                * sp.binomial(ell, j) / sp.binomial(dy, j)
                for i in range(k + 1) for j in range(ell + 1)
            ))
            assert coeff[k, ell] > 0
    return dx, dy, coeff


def coeff_definition(name: str, coeff: dict) -> str:
    lines = [f"def {name} (i j : ℕ) : ℚ :=", "  match i, j with"]
    for (i, j), value in sorted(coeff.items()):
        lines.append(f"  | {i}, {j} => {lean_rat(value)}")
    lines.append("  | _, _ => 0")
    return "\n".join(lines)


normalized = [
    sp.cancel((p + 4 * core.y * p.subs(core.x, 4 * core.x)) / (2 * core.x - 3))
    for p in core.P
]
substitution = dict(zip(core.RAW, normalized))
raw_normalized = {
    "q": sp.cancel(core.raw_q.subs(substitution)),
    "f2": sp.cancel(core.raw_f2.subs(substitution)),
    "c4": sp.cancel(core.raw_h4.subs(substitution)),
}
direct = {name: core.numerator(value) for name, value in raw_normalized.items()}
margin = {
    "q": core.numerator(sp.cancel(raw_normalized["q"] - 10)),
    "f2": core.numerator(sp.cancel(raw_normalized["f2"] - 1000)),
    "c4": core.numerator(sp.cancel(raw_normalized["c4"] - 50_000_000)),
}

certificates = [
    ("qCore", direct["q"], core.X_LO, core.X_SPLIT,
     sp.Rational(0), sp.Rational(1, 12000)),
    ("qMid", direct["q"], core.X_SPLIT, sp.Integer(5),
     sp.Rational(0), sp.Rational(1, 22000)),
    ("f2Core", direct["f2"], core.X_LO, core.X_SPLIT,
     sp.Rational(0), sp.Rational(1, 12000)),
    ("f2Mid", direct["f2"], core.X_SPLIT, sp.Integer(5),
     sp.Rational(0), sp.Rational(1, 22000)),
    ("c4Core", direct["c4"], core.X_LO, core.X_SPLIT,
     sp.Rational(0), sp.Rational(1, 12000)),
    ("qMarginCore", margin["q"], core.X_LO, core.X_SPLIT,
     sp.Rational(0), sp.Rational(1, 12000)),
    ("qMarginMid", margin["q"], core.X_SPLIT, sp.Integer(5),
     sp.Rational(0), sp.Rational(1, 22000)),
    ("f2MarginCore", margin["f2"], core.X_LO, core.X_SPLIT,
     sp.Rational(1, 23000), sp.Rational(1, 12000)),
    ("f2MarginMid", margin["f2"], core.X_SPLIT, sp.Integer(5),
     sp.Rational(0), sp.Rational(1, 22000)),
    ("c4MarginCore", margin["c4"], core.X_LO, core.X_SPLIT,
     sp.Rational(0), sp.Rational(1, 12000)),
]

# Coordinate bounds for the exact two-mode normalized jet on x in [157/50,5].
base_bound_names = []
for j, polynomial in enumerate(core.P):
    raw = sp.expand(polynomial + 4 * core.y * polynomial.subs(core.x, 4 * core.x))
    denominator = 2 * core.x - 3
    for label, sign in (("Upper", -1), ("Lower", 1)):
        name = f"base{j}{label}"
        bound_poly = sp.expand(core.CORE_BASE[j] * denominator + sign * raw)
        certificates.append((name, bound_poly, core.X_LO, sp.Integer(5),
            sp.Rational(0), sp.Rational(1, 12000)))
        base_bound_names.append((j, label, name))

semantics = (HERE / "BernsteinCertificate.lean").read_text()
exp_bounds = "\n".join(
    line for line in (HERE / "ExpBounds.lean").read_text().splitlines()
    if not line.startswith("import ")
)
out = [semantics, exp_bounds, "\nnamespace PF4.CERT12Inequalities.Generated\n"]

for name, poly, xlo, xhi, ylo, yhi in certificates:
    dx, dy, coeff = bernstein_coefficients(poly, xlo, xhi, ylo, yhi)
    floor = min(coeff.values())
    # The direct polynomials are repeated per region deliberately; their exact
    # equality is checked by the generated representation theorem.
    out.append(f"noncomputable def {name}Polynomial (x y : ℝ) : ℝ :=\n  "
               + lean_expr(poly, {core.x: "x", core.y: "y"}) + "\n")
    out.append(coeff_definition(f"{name}Coeff", coeff) + "\n")
    out.append(
        f"theorem {name}Coeff_floor : ∀ i ∈ Finset.range ({dx} + 1), "
        f"∀ j ∈ Finset.range ({dy} + 1), {lean_rat(floor)} ≤ {name}Coeff i j := by\n"
        f"  intro i hi j hj\n"
        f"  interval_cases i <;> interval_cases j <;> norm_num [{name}Coeff]\n"
    )
    affine_x = f"({lean_real_rat(xlo)} + ({lean_real_rat(xhi - xlo)}) * u)"
    affine_y = f"({lean_real_rat(ylo)} + ({lean_real_rat(yhi - ylo)}) * v)"
    out.append(
        f"theorem {name}_representation (u v : ℝ) :\n"
        f"    {name}Polynomial {affine_x} {affine_y} =\n"
        f"      bernsteinBoxEval {dx} {dy} {name}Coeff u v := by\n"
        f"  norm_num [{name}Polynomial, bernsteinBoxEval, {name}Coeff, "
        f"bernsteinBasis_eq, Nat.choose]\n"
        f"  ring\n"
    )
    out.append(
        f"theorem {name}_pos {{u v : ℝ}} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) "
        f"(hv0 : 0 ≤ v) (hv1 : v ≤ 1) :\n"
        f"    0 < {name}Polynomial {affine_x} {affine_y} := by\n"
        f"  rw [{name}_representation]\n"
        f"  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < {lean_rat(floor)}) "
        f"hu0 hu1 hv0 hv1 {name}Coeff_floor\n"
    )
    out.append(
        f"theorem {name}_box_pos {{x y : ℝ}}\n"
        f"    (hx0 : {lean_real_rat(xlo)} ≤ x) (hx1 : x ≤ {lean_real_rat(xhi)})\n"
        f"    (hy0 : {lean_real_rat(ylo)} ≤ y) (hy1 : y ≤ {lean_real_rat(yhi)}) :\n"
        f"    0 < {name}Polynomial x y := by\n"
        f"  let u := (x - {lean_real_rat(xlo)}) / {lean_real_rat(xhi - xlo)}\n"
        f"  let v := (y - {lean_real_rat(ylo)}) / {lean_real_rat(yhi - ylo)}\n"
        f"  have hu0 : 0 ≤ u := by dsimp [u]; positivity\n"
        f"  have hu1 : u ≤ 1 := by\n"
        f"    dsimp [u]\n"
        f"    rw [div_le_one (by norm_num : (0 : ℝ) < {lean_real_rat(xhi - xlo)})]\n"
        f"    linarith\n"
        f"  have hv0 : 0 ≤ v := by dsimp [v]; positivity\n"
        f"  have hv1 : v ≤ 1 := by\n"
        f"    dsimp [v]\n"
        f"    rw [div_le_one (by norm_num : (0 : ℝ) < {lean_real_rat(yhi - ylo)})]\n"
        f"    linarith\n"
        f"  have h := {name}_pos hu0 hu1 hv0 hv1\n"
        f"  dsimp [u, v] at h\n"
        f"  convert h using 1 <;> field_simp <;> ring\n"
    )

def append_halfstrip(name: str, half_poly) -> None:
    transformed = sp.Poly(sp.expand(half_poly.subs({
        core.x: core.z + 5,
        core.y: core.v / sp.Integer(3_000_000),
    })), core.v)
    nv = transformed.degree(core.v)
    power = [transformed.coeff_monomial(core.v**j) for j in range(nv + 1)]
    half_coeff = {}
    nz = 0
    for j in range(nv + 1):
        bpoly = sp.Poly(sp.expand(sum(
            power[k] * sp.binomial(j, k) / sp.binomial(nv, k)
            for k in range(j + 1)
        )), core.z)
        nz = max(nz, bpoly.degree())
        for k in range(bpoly.degree() + 1):
            half_coeff[j, k] = bpoly.coeff_monomial(core.z**k)
            assert half_coeff[j, k] >= 0
    for j in range(nv + 1):
        for k in range(nz + 1):
            half_coeff.setdefault((j, k), sp.Integer(0))
    half_floor = min(half_coeff[j, 0] for j in range(nv + 1))
    assert half_floor > 0
    out.append(f"noncomputable def {name}Polynomial (x y : ℝ) : ℝ :=\n  "
               + lean_expr(half_poly, {core.x: "x", core.y: "y"}) + "\n")
    out.append(coeff_definition(f"{name}Coeff", half_coeff) + "\n")
    out.append(
        f"theorem {name}Coeff_const_floor : ∀ j ∈ Finset.range ({nv} + 1), "
        f"{lean_rat(half_floor)} ≤ {name}Coeff j 0 := by\n"
        f"  intro j hj\n"
        f"  interval_cases j <;> norm_num [{name}Coeff]\n")
    out.append(
        f"theorem {name}Coeff_nonneg : ∀ j ∈ Finset.range ({nv} + 1), "
        f"∀ k ∈ Finset.range ({nz} + 1), 0 ≤ {name}Coeff j k := by\n"
        f"  intro j hj k hk\n"
        f"  interval_cases j <;> interval_cases k <;> norm_num [{name}Coeff]\n")
    out.append(
        f"theorem {name}_representation (v z : ℝ) :\n"
        f"    {name}Polynomial (z + 5) (v / 3000000) =\n"
        f"      bernsteinHalfstripEval {nv} {nz} {name}Coeff v z := by\n"
        f"  norm_num [{name}Polynomial, bernsteinHalfstripEval, {name}Coeff, "
        f"bernsteinBasis_eq, Nat.choose]\n"
        f"  ring\n")
    out.append(
        f"theorem {name}_pos {{v z : ℝ}} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) "
        f"(hz : 0 ≤ z) :\n"
        f"    0 < {name}Polynomial (z + 5) (v / 3000000) := by\n"
        f"  rw [{name}_representation]\n"
        f"  exact bernsteinHalfstripEval_pos "
        f"(by norm_num : (0 : ℚ) < {lean_rat(half_floor)}) hv0 hv1 hz "
        f"{name}Coeff_const_floor {name}Coeff_nonneg\n")
    out.append(
        f"theorem {name}_region_pos {{x y : ℝ}}\n"
        f"    (hx : (5 : ℝ) ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 3000000) :\n"
        f"    0 < {name}Polynomial x y := by\n"
        f"  let v := y / (1 / 3000000)\n"
        f"  let z := x - 5\n"
        f"  have hv0 : 0 ≤ v := by dsimp [v]; positivity\n"
        f"  have hv1 : v ≤ 1 := by\n"
        f"    dsimp [v]\n"
        f"    rw [div_le_one (by norm_num : (0 : ℝ) < 1 / 3000000)]\n"
        f"    exact hy1\n"
        f"  have hz : 0 ≤ z := by dsimp [z]; linarith\n"
        f"  have h := {name}_pos hv0 hv1 hz\n"
        f"  dsimp [v, z] at h\n"
        f"  convert h using 1 <;> field_simp <;> ring\n")


append_halfstrip("f2Outer", direct["f2"])
append_halfstrip("f2MarginOuter", margin["f2"])

out.append(r'''
/-! ## Natural exponential curve and exact two-mode jet -/

theorem qTwoModeNumerator_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < qCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact qCore_box_pos hx0 hsplit (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    have h := qMid_box_pos hlow hx5 (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_22000 hlow).le
    simpa [qCorePolynomial, qMidPolynomial] using h

theorem f2TwoModeNumerator_pos {x : ℝ} (hx0 : (157 / 50 : ℝ) ≤ x) :
    0 < f2CorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact f2Core_box_pos hx0 hsplit (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    by_cases hfive : x ≤ (5 : ℝ)
    · have h := f2Mid_box_pos hlow hfive (Real.exp_pos _).le
        (exp_neg_three_mul_lt_inv_22000 hlow).le
      simpa [f2CorePolynomial, f2MidPolynomial] using h
    · have h5low : (5 : ℝ) ≤ x := (lt_of_not_ge hfive).le
      have h := f2Outer_region_pos h5low (Real.exp_pos _).le
        (exp_neg_three_mul_lt_inv_3000000 h5low).le
      simpa [f2CorePolynomial, f2OuterPolynomial] using h

theorem c4TwoModeNumerator_pos_core {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx1 : x ≤ 10 / 3) :
    0 < c4CorePolynomial x (Real.exp (-3 * x)) :=
  c4Core_box_pos hx0 hx1 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le

noncomputable def twoModeNormalizedJet (j : ℕ) (x y : ℝ) : ℝ :=
  ((PF4.certPoly j).eval x + 4 * y * (PF4.certPoly j).eval (4 * x)) /
    (2 * x - 3)

theorem clearedQ_twoModeNormalizedJet (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedQ
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) =
      qCorePolynomial x y / (2 * x - 3) ^ 2 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedQ, qCorePolynomial]
  field_simp [hx]
  ring

theorem clearedF2_twoModeNormalizedJet (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedF2
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) (twoModeNormalizedJet 3 x y)
        (twoModeNormalizedJet 4 x y) =
      f2CorePolynomial x y / (2 * x - 3) ^ 6 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedF2, f2CorePolynomial]
  field_simp [hx]
  ring

theorem clearedC4_twoModeNormalizedJet (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedC4
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) (twoModeNormalizedJet 3 x y)
        (twoModeNormalizedJet 4 x y) (twoModeNormalizedJet 5 x y)
        (twoModeNormalizedJet 6 x y) =
      c4CorePolynomial x y / (2 * x - 3) ^ 4 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedC4, c4CorePolynomial]
  field_simp [hx]
  ring

theorem two_mul_sub_three_pos {x : ℝ} (hx : (157 / 50 : ℝ) ≤ x) :
    0 < 2 * x - 3 := by linarith

theorem clearedQ_twoMode_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x))) := by
  rw [clearedQ_twoModeNormalizedJet _ _ (two_mul_sub_three_pos hx0).ne']
  exact div_pos (qTwoModeNumerator_pos_to_five hx0 hx5)
    (pow_pos (two_mul_sub_three_pos hx0) 2)

theorem clearedF2_twoMode_pos {x : ℝ} (hx0 : (157 / 50 : ℝ) ≤ x) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x))) := by
  rw [clearedF2_twoModeNormalizedJet _ _ (two_mul_sub_three_pos hx0).ne']
  exact div_pos (f2TwoModeNumerator_pos hx0)
    (pow_pos (two_mul_sub_three_pos hx0) 6)

theorem clearedC4_twoMode_pos_core {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx1 : x ≤ 10 / 3) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 5 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 6 x (Real.exp (-3 * x))) := by
  rw [clearedC4_twoModeNormalizedJet _ _ (two_mul_sub_three_pos hx0).ne']
  exact div_pos (c4TwoModeNumerator_pos_core hx0 hx1)
    (pow_pos (two_mul_sub_three_pos hx0) 4)

/-! ## Certified quantitative two-mode margins -/

theorem qTwoModeMarginNumerator_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < qMarginCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact qMarginCore_box_pos hx0 hsplit (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    have h := qMarginMid_box_pos hlow hx5 (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_22000 hlow).le
    simpa [qMarginCorePolynomial, qMarginMidPolynomial] using h

theorem f2TwoModeMarginNumerator_pos {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) :
    0 < f2MarginCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact f2MarginCore_box_pos hx0 hsplit
      (inv_23000_lt_exp_neg_three_mul hsplit).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    by_cases hfive : x ≤ (5 : ℝ)
    · have h := f2MarginMid_box_pos hlow hfive (Real.exp_pos _).le
        (exp_neg_three_mul_lt_inv_22000 hlow).le
      simpa [f2MarginCorePolynomial, f2MarginMidPolynomial] using h
    · have h5low : (5 : ℝ) ≤ x := (lt_of_not_ge hfive).le
      have h := f2MarginOuter_region_pos h5low (Real.exp_pos _).le
        (exp_neg_three_mul_lt_inv_3000000 h5low).le
      simpa [f2MarginCorePolynomial, f2MarginOuterPolynomial] using h

theorem c4TwoModeMarginNumerator_pos_core {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx1 : x ≤ 10 / 3) :
    0 < c4MarginCorePolynomial x (Real.exp (-3 * x)) :=
  c4MarginCore_box_pos hx0 hx1 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le

theorem clearedQ_twoMode_sub_ten (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedQ
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) - 10 =
      qMarginCorePolynomial x y / (2 * x - 3) ^ 2 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedQ, qMarginCorePolynomial]
  field_simp [hx]
  ring

theorem clearedF2_twoMode_sub_thousand (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedF2
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) (twoModeNormalizedJet 3 x y)
        (twoModeNormalizedJet 4 x y) - 1000 =
      f2MarginCorePolynomial x y / (2 * x - 3) ^ 6 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedF2, f2MarginCorePolynomial]
  field_simp [hx]
  ring

theorem clearedC4_twoMode_sub_margin (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedC4
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) (twoModeNormalizedJet 3 x y)
        (twoModeNormalizedJet 4 x y) (twoModeNormalizedJet 5 x y)
        (twoModeNormalizedJet 6 x y) - 50000000 =
      c4MarginCorePolynomial x y / (2 * x - 3) ^ 4 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedC4, c4MarginCorePolynomial]
  field_simp [hx]
  ring

theorem clearedQ_twoMode_gt_ten_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    10 < PF4.ClearedJetCertificateBridge.clearedQ
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x))) := by
  rw [← sub_pos, clearedQ_twoMode_sub_ten _ _ (two_mul_sub_three_pos hx0).ne']
  exact div_pos (qTwoModeMarginNumerator_pos_to_five hx0 hx5)
    (pow_pos (two_mul_sub_three_pos hx0) 2)

theorem clearedF2_twoMode_gt_thousand {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) :
    1000 < PF4.ClearedJetCertificateBridge.clearedF2
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x))) := by
  rw [← sub_pos, clearedF2_twoMode_sub_thousand _ _
    (two_mul_sub_three_pos hx0).ne']
  exact div_pos (f2TwoModeMarginNumerator_pos hx0)
    (pow_pos (two_mul_sub_three_pos hx0) 6)

theorem clearedC4_twoMode_gt_margin_core {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx1 : x ≤ 10 / 3) :
    50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 5 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 6 x (Real.exp (-3 * x))) := by
  rw [← sub_pos, clearedC4_twoMode_sub_margin _ _
    (two_mul_sub_three_pos hx0).ne']
  exact div_pos (c4TwoModeMarginNumerator_pos_core hx0 hx1)
    (pow_pos (two_mul_sub_three_pos hx0) 4)
''')

for j in range(7):
    B = core.CORE_BASE[j]
    out.append(
        f"theorem abs_twoModeNormalizedJet_{j}_le_coreBase {{x : ℝ}}\n"
        f"    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :\n"
        f"    |twoModeNormalizedJet {j} x (Real.exp (-3 * x))| ≤ {B} := by\n"
        f"  have hupper := base{j}Upper_box_pos hx0 hx5 (Real.exp_pos _).le\n"
        f"    (exp_neg_three_mul_lt_inv_12000 hx0).le\n"
        f"  have hlower := base{j}Lower_box_pos hx0 hx5 (Real.exp_pos _).le\n"
        f"    (exp_neg_three_mul_lt_inv_12000 hx0).le\n"
        f"  rw [abs_le]\n"
        f"  constructor\n"
        f"  · rw [twoModeNormalizedJet]\n"
        f"    have hden := two_mul_sub_three_pos hx0\n"
        f"    rw [le_div_iff₀ hden]\n"
        f"    simpa [base{j}LowerPolynomial, PF4.certPoly] using hlower.le\n"
        f"  · rw [twoModeNormalizedJet]\n"
        f"    have hden := two_mul_sub_three_pos hx0\n"
        f"    rw [div_le_iff₀ hden]\n"
        f"    simpa [base{j}UpperPolynomial, PF4.certPoly] using hupper.le\n"
    )

out.append("end PF4.CERT12Inequalities.Generated\n")
(HERE / "CERT12FiniteMargins.lean").write_text("\n".join(out))
print(f"generated {HERE / 'CERT12FiniteMargins.lean'}")
