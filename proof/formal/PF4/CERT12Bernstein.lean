import PF4.ClearedJetCertificateBridge
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact Bernstein continuum-certificate semantics

A finite rational coefficient table proves a pointwise inequality on an entire
closed box or half-strip.  The table is finite; the theorem's domain is not.
-/

namespace PF4.CERT12Inequalities

open Finset Polynomial

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
  change (∑ i ∈ range (n + 1), (bernsteinPolynomial ℝ n i).eval x) = 1
  rw [← Polynomial.eval_finsetSum]
  rw [bernsteinPolynomial.sum]
  simp

noncomputable def bernsteinBoxEval
    (nx ny : ℕ) (c : ℕ → ℕ → ℚ) (x y : ℝ) : ℝ :=
  ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
    (c i j : ℝ) * bernsteinBasis nx i x * bernsteinBasis ny j y

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
    _ = (∑ i ∈ range (nx + 1),
          (ε : ℝ) * bernsteinBasis nx i x) *
          (∑ j ∈ range (ny + 1), bernsteinBasis ny j y) := by
      congr 1
      exact Finset.mul_sum (range (nx + 1))
        (fun i => bernsteinBasis nx i x) (ε : ℝ)
    _ = ∑ i ∈ range (nx + 1),
          ((ε : ℝ) * bernsteinBasis nx i x) *
          (∑ j ∈ range (ny + 1), bernsteinBasis ny j y) := by
      exact Finset.sum_mul (range (nx + 1))
        (fun i => (ε : ℝ) * bernsteinBasis nx i x)
        (∑ j ∈ range (ny + 1), bernsteinBasis ny j y)
    _ = ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
          (ε : ℝ) * bernsteinBasis nx i x * bernsteinBasis ny j y := by
      apply sum_congr rfl
      intro i hi
      exact Finset.mul_sum (range (ny + 1))
        (fun j => bernsteinBasis ny j y)
        ((ε : ℝ) * bernsteinBasis nx i x)
    _ ≤ ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
          (c i j : ℝ) * bernsteinBasis nx i x * bernsteinBasis ny j y := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hcR : (ε : ℝ) ≤ (c i j : ℝ) := by
        exact_mod_cast hc i hi j hj
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcR
          (bernsteinBasis_nonneg hx0 hx1))
        (bernsteinBasis_nonneg hy0 hy1)

theorem bernsteinBoxEval_pos
    {nx ny : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {x y : ℝ}
    (hε : 0 < ε)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc : ∀ i ∈ range (nx + 1), ∀ j ∈ range (ny + 1), ε ≤ c i j) :
    0 < bernsteinBoxEval nx ny c x y := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  exact hεR.trans_le
    (bernsteinBoxEval_lower_bound hx0 hx1 hy0 hy1 hc)

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
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hc0 j hj
          · exact bernsteinBasis_nonneg hv0 hv1
        _ = (c j 0 : ℝ) * bernsteinBasis nv j v * z ^ 0 := by simp
        _ ≤ ∑ k ∈ range (nz + 1),
            (c j k : ℝ) * bernsteinBasis nv j v * z ^ k := by
          have hterm : ∀ k ∈ range (nz + 1),
              0 ≤ (c j k : ℝ) * bernsteinBasis nv j v * z ^ k := by
            intro k hk
            exact mul_nonneg
              (mul_nonneg (by exact_mod_cast hc j hj k hk)
                (bernsteinBasis_nonneg hv0 hv1))
              (pow_nonneg hz k)
          simpa using single_le_sum hterm
            (show 0 ∈ range (nz + 1) by simp)

theorem bernsteinHalfstripEval_pos
    {nv nz : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {v z : ℝ}
    (hε : 0 < ε) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hz : 0 ≤ z)
    (hc0 : ∀ j ∈ range (nv + 1), ε ≤ c j 0)
    (hc : ∀ j ∈ range (nv + 1), ∀ k ∈ range (nz + 1), 0 ≤ c j k) :
    0 < bernsteinHalfstripEval nv nz c v z := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  exact hεR.trans_le
    (bernsteinHalfstripEval_lower_bound hv0 hv1 hz hc0 hc)

end PF4.CERT12Inequalities
