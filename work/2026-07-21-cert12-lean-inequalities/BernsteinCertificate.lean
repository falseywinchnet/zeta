import PF4.ClearedJetCertificateBridge
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Executable Bernstein-box certificate semantics

The external certificate converts exact rational polynomials to tensor-product
Bernstein form.  This file gives that data a small mathematical meaning in
Lean: a checked coefficient floor implies a pointwise lower bound on the unit
square.  No numerical approximation or process result enters the theorem.
-/

namespace PF4.CERT12Inequalities

open Finset Polynomial

/-- Evaluation of the ordinary Bernstein basis polynomial. -/
noncomputable def bernsteinBasis (n i : ℕ) (x : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ n i).eval x

theorem bernsteinBasis_eq (n i : ℕ) (x : ℝ) :
    bernsteinBasis n i x =
      (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i) := by
  simp [bernsteinBasis, bernsteinPolynomial]

theorem bernsteinBasis_nonneg {n i : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinBasis n i x := by
  rw [bernsteinBasis_eq]
  have hsub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  positivity

theorem sum_bernsteinBasis (n : ℕ) (x : ℝ) :
    ∑ i ∈ range (n + 1), bernsteinBasis n i x = 1 := by
  rw [← Polynomial.eval_finset_sum]
  simp only [bernsteinBasis]
  rw [bernsteinPolynomial.sum]
  simp

/-- Tensor-product Bernstein evaluation for a rational coefficient table. -/
noncomputable def bernsteinBoxEval
    (nx ny : ℕ) (c : ℕ → ℕ → ℚ) (x y : ℝ) : ℝ :=
  ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
    (c i j : ℝ) * bernsteinBasis nx i x * bernsteinBasis ny j y

/-- A rational coefficient floor is a complete positivity certificate for the
corresponding Bernstein form on the closed unit square. -/
theorem bernsteinBoxEval_lower_bound
    {nx ny : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc : ∀ i ∈ range (nx + 1), ∀ j ∈ range (ny + 1), ε ≤ c i j) :
    (ε : ℝ) ≤ bernsteinBoxEval nx ny c x y := by
  have hxsum := sum_bernsteinBasis nx x
  have hysum := sum_bernsteinBasis ny y
  rw [bernsteinBoxEval]
  calc
    (ε : ℝ) = (ε : ℝ) *
        (∑ i ∈ range (nx + 1), bernsteinBasis nx i x) *
        (∑ j ∈ range (ny + 1), bernsteinBasis ny j y) := by
      rw [hxsum, hysum]
      ring
    _ = ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
          (ε : ℝ) * bernsteinBasis nx i x * bernsteinBasis ny j y := by
      rw [mul_sum, mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [sum_mul]
    _ ≤ ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
          (c i j : ℝ) * bernsteinBasis nx i x * bernsteinBasis ny j y := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      gcongr
      · exact_mod_cast hc i hi j hj
      · exact bernsteinBasis_nonneg hx0 hx1
      · exact bernsteinBasis_nonneg hy0 hy1

theorem bernsteinBoxEval_pos
    {nx ny : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {x y : ℝ}
    (hε : 0 < ε)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc : ∀ i ∈ range (nx + 1), ∀ j ∈ range (ny + 1), ε ≤ c i j) :
    0 < bernsteinBoxEval nx ny c x y := by
  exact_mod_cast hε.trans_le
    (bernsteinBoxEval_lower_bound hx0 hx1 hy0 hy1 hc)

/-- Bernstein in the bounded coordinate and the ordinary nonnegative power
basis in an unbounded coordinate. -/
noncomputable def bernsteinHalfstripEval
    (nv nz : ℕ) (c : ℕ → ℕ → ℚ) (v z : ℝ) : ℝ :=
  ∑ j ∈ range (nv + 1), ∑ k ∈ range (nz + 1),
    (c j k : ℝ) * bernsteinBasis nv j v * z ^ k

theorem bernsteinHalfstripEval_lower_bound
    {nv nz : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {v z : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hz : 0 ≤ z)
    (hc0 : ∀ j ∈ range (nv + 1), ε ≤ c j 0)
    (hc : ∀ j ∈ range (nv + 1), ∀ k ∈ range (nz + 1), 0 ≤ c j k) :
    (ε : ℝ) ≤ bernsteinHalfstripEval nv nz c v z := by
  have hvsum := sum_bernsteinBasis nv v
  rw [bernsteinHalfstripEval]
  calc
    (ε : ℝ) = ∑ j ∈ range (nv + 1),
        (ε : ℝ) * bernsteinBasis nv j v := by
      rw [← mul_sum, hvsum, mul_one]
    _ ≤ ∑ j ∈ range (nv + 1), ∑ k ∈ range (nz + 1),
          (c j k : ℝ) * bernsteinBasis nv j v * z ^ k := by
      apply sum_le_sum
      intro j hj
      calc
        (ε : ℝ) * bernsteinBasis nv j v ≤
            (c j 0 : ℝ) * bernsteinBasis nv j v := by
          gcongr
          exact_mod_cast hc0 j hj
        _ = (c j 0 : ℝ) * bernsteinBasis nv j v * z ^ 0 := by simp
        _ ≤ ∑ k ∈ range (nz + 1),
            (c j k : ℝ) * bernsteinBasis nv j v * z ^ k := by
          apply single_le_sum
          · intro k hk
            exact mul_nonneg
              (mul_nonneg (by exact_mod_cast hc j hj k hk)
                (bernsteinBasis_nonneg hv0 hv1))
              (pow_nonneg hz k)
          · simp

theorem bernsteinHalfstripEval_pos
    {nv nz : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {v z : ℝ}
    (hε : 0 < ε) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hz : 0 ≤ z)
    (hc0 : ∀ j ∈ range (nv + 1), ε ≤ c j 0)
    (hc : ∀ j ∈ range (nv + 1), ∀ k ∈ range (nz + 1), 0 ≤ c j k) :
    0 < bernsteinHalfstripEval nv nz c v z := by
  exact_mod_cast hε.trans_le
    (bernsteinHalfstripEval_lower_bound hv0 hv1 hz hc0 hc)

end PF4.CERT12Inequalities
