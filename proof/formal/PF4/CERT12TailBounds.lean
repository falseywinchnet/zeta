/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CERT12Coordinates
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Literal CERT12 infinite-tail coordinate bounds

This module places the complete normalized theta tail, including every mode
`n >= 3`, inside the exact seven-coordinate `coreE` box.  The proof uses the
maintained closed relative estimate for the genuinely infinite `n >= 4` tail
and a decreasing real profile for the exact `n = 3` term.
-/

namespace PF4.CERT12TailBounds

open Set Polynomial
open PF4.CERT12ThetaTail
open PF4.CERT12Coordinates
open PF4.CERT12Inequalities.Perturbation.Generated

/-- Absolute value profile of the exact normalized `n = 3` coordinate on
`x >= 3`. -/
noncomputable def thirdProfile (j : ℕ) (x : ℝ) : ℝ :=
  9 * Real.exp (-8 * x) *
      ((-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x)) /
    (2 * x - 3)

/-- Positive numerator of `-thirdProfile'` on `x >= 3`. -/
noncomputable def thirdDecay (j : ℕ) (x : ℝ) : ℝ :=
  (8 * (2 * x - 3) + 2) *
      ((-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x)) -
    9 * (2 * x - 3) *
      ((-1 : ℝ) ^ j * (PF4.certPoly j).derivative.eval (9 * x))

theorem thirdDecay_pos {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 3 ≤ x) :
    0 < thirdDecay j x := by
  let z := x - 3
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hx_eq : x = z + 3 := by dsimp [z]; ring
  rw [hx_eq]
  interval_cases j <;>
    norm_num [thirdDecay, PF4.certPoly, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul] <;>
    ring_nf <;>
    nlinarith [pow_nonneg hz 2, pow_nonneg hz 3, pow_nonneg hz 4,
      pow_nonneg hz 5, pow_nonneg hz 6, pow_nonneg hz 7,
      pow_nonneg hz 8]

theorem hasDerivAt_thirdProfile (j : ℕ) {x : ℝ} (hx : 3 < x) :
    HasDerivAt (thirdProfile j)
      (-9 * Real.exp (-8 * x) * thirdDecay j x / (2 * x - 3) ^ 2) x := by
  have hden : 2 * x - 3 ≠ 0 := by linarith
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-8 * y))
      (Real.exp (-8 * x) * (-8)) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (Real.hasDerivAt_exp (-8 * x)).comp x
        ((hasDerivAt_id x).const_mul (-8))
  have hpoly : HasDerivAt
      (fun y : ℝ => (-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * y))
      (((-1 : ℝ) ^ j) *
        ((PF4.certPoly j).derivative.eval (9 * x) * 9)) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (((PF4.certPoly j).hasDerivAt (9 * x)).comp x
        ((hasDerivAt_id x).const_mul 9)).const_mul ((-1 : ℝ) ^ j)
  have hdenDeriv : HasDerivAt (fun y : ℝ => 2 * y - 3) 2 x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul 2).sub_const 3
  have hquot := ((hexp.const_mul 9).mul hpoly).div hdenDeriv hden
  unfold thirdProfile thirdDecay
  have hfun :
      (((fun y : ℝ => 9 * Real.exp (-8 * y)) *
          fun y : ℝ => (-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * y)) /
        fun y : ℝ => 2 * y - 3) =
      (fun y : ℝ => 9 * Real.exp (-8 * y) *
        ((-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * y)) /
        (2 * y - 3)) := by
    funext y
    rfl
  rw [hfun] at hquot
  apply hquot.congr_deriv
  simp only [Pi.mul_apply]
  ring

theorem strictAntiOn_thirdProfile (j : ℕ) (hj : j ≤ 6) :
    StrictAntiOn (thirdProfile j) (Set.Ici 3) := by
  have hcont : ContinuousOn (thirdProfile j) (Set.Ici 3) := by
    intro x hx
    have hx3 : 3 ≤ x := hx
    have hden : 2 * x - 3 ≠ 0 := by linarith
    unfold thirdProfile
    fun_prop
  apply strictAntiOn_of_deriv_neg (convex_Ici 3) hcont
  intro x hx
  have hx3 : 3 < x := by
    rw [interior_Ici] at hx
    exact hx
  have hd := hasDerivAt_thirdProfile j hx3
  rw [hd.deriv]
  have hdecay := thirdDecay_pos hj hx3.le
  have hden : 0 < (2 * x - 3) ^ 2 := sq_pos_of_pos (by linarith)
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) (Real.exp_pos _)) hdecay)
    hden

theorem norm_thirdModeJet_eq_signed
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ‖thirdModeJet j t‖ = (-1 : ℝ) ^ j * thirdModeJet j t := by
  have hp := normalizedModeJet_alternating_pos hj (k := 2) (by omega) ht
  rw [Real.norm_eq_abs]
  unfold thirdModeJet
  interval_cases j <;> norm_num at hp ⊢ <;> linarith

theorem norm_thirdModeJet_eq_profile
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ‖thirdModeJet j t‖ = thirdProfile j (certX t) := by
  rw [norm_thirdModeJet_eq_signed hj ht]
  unfold thirdModeJet
  rw [normalizedModeJet_eq j 2 ht]
  norm_num [PF4.modeN]
  unfold thirdProfile
  rw [show Real.exp (-(8 * certX t)) = Real.exp (-8 * certX t) by
    congr 1
    ring]
  ring

theorem thirdProfile_le_at_three
    {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 3 ≤ x) :
    thirdProfile j x ≤ thirdProfile j 3 := by
  by_cases h : x = 3
  · simp [h]
  · exact ((strictAntiOn_thirdProfile j hj) (by simp) hx
      (lt_of_le_of_ne hx (Ne.symm h))).le

theorem exp_neg_24_lt_inv_25000000000 :
    Real.exp (-24) < (1 / 25000000000 : ℝ) := by
  have hsum : (25000000000 : ℝ) <
      ∑ i ∈ Finset.range 60, (24 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have he : (25000000000 : ℝ) < Real.exp 24 :=
    hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 60)
  have hinv := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 25000000000) he
  simpa [one_div, ← Real.exp_neg] using hinv

theorem thirdProfile_core_bound (j : Fin 7) :
    (1001 / 1000 : ℝ) * thirdProfile j 3 < coreE j := by
  have he := exp_neg_24_lt_inv_25000000000
  fin_cases j <;>
    norm_num [thirdProfile, PF4.certPoly, coreE,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul] at he ⊢ <;>
    nlinarith

theorem norm_fullModeTail_lt_coreE
    (j : Fin 7) {t : ℝ} (ht : 0 ≤ t) :
    ‖fullModeTail j t‖ < coreE j := by
  have hj : (j : ℕ) ≤ 6 := by omega
  have hsplit := fullModeTail_eq_third_add_later
    (summable_fullModeTail_of_nonneg hj ht)
  have hrelative := laterModeTail_lt_one_thousandth_closed hj ht
  have hx := certX_ge_three ht
  have hthird := norm_thirdModeJet_eq_profile hj ht
  have hmono := thirdProfile_le_at_three hj hx
  calc
    ‖fullModeTail j t‖ =
        ‖thirdModeJet j t + laterModeTail j t‖ := by rw [hsplit]
    _ ≤ ‖thirdModeJet j t‖ + ‖laterModeTail j t‖ := norm_add_le _ _
    _ < ‖thirdModeJet j t‖ +
        (1 / 1000 : ℝ) * ‖thirdModeJet j t‖ := by gcongr
    _ = (1001 / 1000 : ℝ) * thirdProfile j (certX t) := by
      rw [hthird]
      ring
    _ ≤ (1001 / 1000 : ℝ) * thirdProfile j 3 := by gcongr
    _ < coreE j := thirdProfile_core_bound j

/-- The literal infinite theta tail lies inside the complete perturbation box.
There is no cutoff, sampled range, or assumed error vector. -/
theorem abs_fullTailJet_le_coreE {t : ℝ} (ht : 0 ≤ t) (j : Fin 7) :
    |fullTailJet t j| ≤ coreE j := by
  rw [← Real.norm_eq_abs]
  exact (norm_fullModeTail_lt_coreE j ht).le

end PF4.CERT12TailBounds

#print axioms PF4.CERT12TailBounds.abs_fullTailJet_le_coreE
