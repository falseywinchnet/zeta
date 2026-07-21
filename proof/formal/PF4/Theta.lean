/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option linter.style.header false

/-!
# The real theta normalization

This file fixes the paper's theta normalization directly as a real integer
exponential sum. It proves only elementary summability and splitting facts.
No complex-valued object, Fourier transform, or Poisson-summation theorem
occurs in the project-level definitions or proofs.
-/

namespace PF4

open Real

/-- The paper's real theta function as its literal integer exponential sum. -/
noncomputable def riemannTheta (x : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi * x * (n : ℝ) ^ 2)

/-- The global theta-normalized function to which the kernel operator is
applied. -/
noncomputable def riemannH (t : ℝ) : ℝ :=
  Real.exp (t / 2) * riemannTheta (Real.exp (2 * t))

/-- The positive integer represented by a zero-based natural index. -/
def modeN (k : ℕ) : ℝ := (k + 1 : ℕ)

theorem modeN_pos (k : ℕ) : 0 < modeN k := by
  unfold modeN
  exact_mod_cast Nat.succ_pos k

theorem modeN_one_le (k : ℕ) : 1 ≤ modeN k := by
  unfold modeN
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)

/-- One strictly positive-index term of the real integer theta sum. -/
noncomputable def positiveThetaTerm (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-Real.pi * x * modeN k ^ 2)

theorem summable_nat_thetaTerms {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ ↦ Real.exp (-Real.pi * x * (n : ℝ) ^ 2)) := by
  have hr : 0 < Real.pi * x := mul_pos Real.pi_pos hx
  have hlinear : Summable (fun n : ℕ ↦ Real.exp (-(Real.pi * x) * (n : ℝ))) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hr))
  exact hlinear.of_nonneg_of_le (fun _ ↦ Real.exp_nonneg _) fun n ↦ by
    apply Real.exp_monotone
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hn_sq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      cases n with
      | zero => norm_num
      | succ n =>
          have hn_one : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          nlinarith [sq_nonneg ((n + 1 : ℕ) : ℝ)]
    nlinarith

theorem summable_int_thetaTerms {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℤ ↦ Real.exp (-Real.pi * x * (n : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor <;> simpa using summable_nat_thetaTerms hx

/-- The integer theta sum is one plus twice its strictly positive half. -/
theorem riemannTheta_eq_one_add_two_mul_positive {x : ℝ} (hx : 0 < x) :
    riemannTheta x = 1 + 2 * ∑' k : ℕ, positiveThetaTerm k x := by
  let f : ℤ → ℝ := fun n ↦ Real.exp (-Real.pi * x * (n : ℝ) ^ 2)
  have hfEven : f.Even := by
    intro n
    simp [f]
  have hfSummable : Summable f := summable_int_thetaTerms hx
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat hfEven hfSummable
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f n)] at hsplit
  simpa [riemannTheta, positiveThetaTerm, modeN, f, Nat.cast_succ] using hsplit

/-- Exact `HasSum` form used by the kernel-series bridge. -/
theorem hasSum_positiveThetaTerms {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ ↦ positiveThetaTerm k x) ((riemannTheta x - 1) / 2) := by
  have hs : Summable (fun k : ℕ ↦ positiveThetaTerm k x) := by
    have h := (summable_nat_thetaTerms hx).comp_injective Nat.succ_injective
    exact h.congr fun k ↦ by simp [positiveThetaTerm, modeN, Function.comp_apply]
  have htotal : (∑' k : ℕ, positiveThetaTerm k x) = (riemannTheta x - 1) / 2 := by
    have htheta := riemannTheta_eq_one_add_two_mul_positive hx
    nlinarith
  rw [← htotal]
  exact hs.hasSum

end PF4
