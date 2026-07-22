/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CERT12CompactClosure
import PF4.CERT12C4OuterMargins
import PF4.CERT12F2OuterMargins
import PF4.GlobalKernelJetIdentification
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace PF4.CERT12OuterClosure

open Set Polynomial

/-! The elementary absolute envelope is valid already from `s=5`. -/

theorem certPoly_abs_le_outerEnvelope
    {j : ℕ} (hj : j ≤ 6) {s : ℝ} (hs : 5 ≤ s) :
    |(PF4.certPoly j).eval s| ≤ 2 ^ (j + 1) * s ^ (j + 1) := by
  let z := s - 5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hpow : ∀ n : ℕ, 0 ≤ z ^ n := fun n => pow_nonneg hz n
  have hs_eq : s = z + 5 := by dsimp [z]; ring
  rw [hs_eq]
  rw [abs_le]
  interval_cases j <;>
    norm_num [PF4.certPoly, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  all_goals ring_nf
  all_goals try constructor
  all_goals nlinarith [hpow 0, hpow 1, hpow 2, hpow 3, hpow 4, hpow 5, hpow 6, hpow 7]

theorem exp_15_gt_three_million :
    (3000000 : ℝ) < Real.exp 15 := by
  have hsum : (3000000 : ℝ) <
      ∑ i ∈ Finset.range 50, (15 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 50)

theorem exp_neg_three_mul_lt_inv_three_million {x : ℝ}
    (hx : (5 : ℝ) ≤ x) :
    Real.exp (-3 * x) < 1 / 3000000 := by
  have harg : (15 : ℝ) ≤ 3 * x := by linarith
  have hexp : (3000000 : ℝ) < Real.exp (3 * x) :=
    exp_15_gt_three_million.trans_le (Real.exp_monotone harg)
  have hinv := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 3000000) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

theorem abs_twoModeNormalizedJet_le_outer
    {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 5 ≤ x) :
    |PF4.CERT12Coordinates.twoModeNormalizedJet j x (Real.exp (-3 * x))| ≤
      2 ^ (j + 2) * x ^ j := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hden : 0 < 2 * x - 3 := by linarith
  have hypos : 0 < Real.exp (-3 * x) := Real.exp_pos _
  have hy := exp_neg_three_mul_lt_inv_three_million hx
  have hp := certPoly_abs_le_outerEnvelope hj hx
  have hp4 := certPoly_abs_le_outerEnvelope hj
    (show 5 ≤ 4 * x by nlinarith)
  have hfactor : 4 ^ (j + 2) * Real.exp (-3 * x) ≤ (1 : ℝ) := by
    interval_cases j <;> norm_num at hy ⊢ <;> nlinarith
  rw [PF4.CERT12Coordinates.twoModeNormalizedJet, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |(PF4.certPoly j).eval x +
        4 * Real.exp (-3 * x) * (PF4.certPoly j).eval (4 * x)| ≤
        |(PF4.certPoly j).eval x| +
          |4 * Real.exp (-3 * x) * (PF4.certPoly j).eval (4 * x)| :=
      abs_add_le _ _
    _ = |(PF4.certPoly j).eval x| +
        4 * Real.exp (-3 * x) * |(PF4.certPoly j).eval (4 * x)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_pos hypos]
    _ ≤ 2 ^ (j + 1) * x ^ (j + 1) +
        4 * Real.exp (-3 * x) *
          (2 ^ (j + 1) * (4 * x) ^ (j + 1)) := by gcongr
    _ = (2 ^ (j + 1) * x ^ (j + 1)) *
        (1 + 4 ^ (j + 2) * Real.exp (-3 * x)) := by ring
    _ ≤ (2 ^ (j + 1) * x ^ (j + 1)) * 2 := by
      gcongr
      linarith
    _ ≤ (2 ^ (j + 2) * x ^ j) * (2 * x - 3) := by
      have hxpow : 0 ≤ x ^ j := pow_nonneg hxpos.le _
      rw [show (2 : ℝ) ^ (j + 1) * x ^ (j + 1) * 2 =
          2 ^ (j + 2) * x ^ j * x by ring]
      gcongr
      linarith

theorem thirdProfile_le_outerHalf
    {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 5 ≤ x) :
    PF4.CERT12TailBounds.thirdProfile j x ≤
      2 ^ (j + 1) * 3 ^ (2 * j + 4) * x ^ j * Real.exp (-8 * x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hden : 0 < 2 * x - 3 := by linarith
  have hp := certPoly_abs_le_outerEnvelope hj
    (show 5 ≤ 9 * x by nlinarith)
  rw [PF4.CERT12TailBounds.thirdProfile]
  apply (div_le_iff₀ hden).2
  calc
    9 * Real.exp (-8 * x) *
        ((-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x)) ≤
      9 * Real.exp (-8 * x) * |(PF4.certPoly j).eval (9 * x)| := by
        have hsigned : (-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x) ≤
            |(PF4.certPoly j).eval (9 * x)| := by
          calc
            (-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x) ≤
                |(-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x)| := le_abs_self _
            _ = |(PF4.certPoly j).eval (9 * x)| := by
              rw [abs_mul, abs_pow]
              norm_num
        exact mul_le_mul_of_nonneg_left hsigned (by positivity)
    _ ≤ 9 * Real.exp (-8 * x) *
        (2 ^ (j + 1) * (9 * x) ^ (j + 1)) := by gcongr
    _ = (2 ^ (j + 1) * 3 ^ (2 * j + 4) * x ^ j *
        Real.exp (-8 * x)) * x := by
      have h9 : (9 : ℝ) ^ j = 3 ^ (j * 2) := by
        calc
          (9 : ℝ) ^ j = (3 ^ 2) ^ j := by norm_num
          _ = 3 ^ (2 * j) := by rw [pow_mul]
          _ = 3 ^ (j * 2) := by rw [Nat.mul_comm]
      rw [show (9 * x) ^ (j + 1) = 9 ^ (j + 1) * x ^ (j + 1) by
        rw [mul_pow], show (9 : ℝ) ^ (j + 1) = 9 ^ j * 9 by rw [pow_succ], h9]
      ring
    _ ≤ (2 ^ (j + 1) * 3 ^ (2 * j + 4) * x ^ j *
        Real.exp (-8 * x)) * (2 * x - 3) := by
      gcongr
      linarith


/-- The complete literal tail is at most the third-mode profile times 1001/1000. -/
theorem norm_fullModeTail_lt_profile
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ‖PF4.CERT12ThetaTail.fullModeTail j t‖ <
      (1001 / 1000 : ℝ) * PF4.CERT12TailBounds.thirdProfile j (PF4.CERT12ThetaTail.certX t) := by
  have hsplit := PF4.CERT12ThetaTail.fullModeTail_eq_third_add_later
    (PF4.CERT12ThetaTail.summable_fullModeTail_of_nonneg hj ht)
  have hrelative := PF4.CERT12ThetaTail.laterModeTail_lt_one_thousandth_closed hj ht
  have hthird := PF4.CERT12TailBounds.norm_thirdModeJet_eq_profile hj ht
  calc
    ‖PF4.CERT12ThetaTail.fullModeTail j t‖ =
        ‖PF4.CERT12ThetaTail.thirdModeJet j t + PF4.CERT12ThetaTail.laterModeTail j t‖ := by rw [hsplit]
    _ ≤ ‖PF4.CERT12ThetaTail.thirdModeJet j t‖ + ‖PF4.CERT12ThetaTail.laterModeTail j t‖ := norm_add_le _ _
    _ < ‖PF4.CERT12ThetaTail.thirdModeJet j t‖ +
        (1 / 1000 : ℝ) * ‖PF4.CERT12ThetaTail.thirdModeJet j t‖ := by gcongr
    _ = (1001 / 1000 : ℝ) * PF4.CERT12TailBounds.thirdProfile j (PF4.CERT12ThetaTail.certX t) := by
      rw [hthird]
      ring

theorem norm_fullModeTail_lt_outer
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t)
    (hx : 5 ≤ PF4.CERT12ThetaTail.certX t) :
    ‖PF4.CERT12ThetaTail.fullModeTail j t‖ <
      2 ^ (j + 2) * 3 ^ (2 * j + 4) * PF4.CERT12ThetaTail.certX t ^ j *
        Real.exp (-8 * PF4.CERT12ThetaTail.certX t) := by
  have htail := norm_fullModeTail_lt_profile hj ht
  have hprofile := thirdProfile_le_outerHalf hj hx
  let A := 2 ^ (j + 1) * 3 ^ (2 * j + 4) * PF4.CERT12ThetaTail.certX t ^ j *
    Real.exp (-8 * PF4.CERT12ThetaTail.certX t)
  have hA : 0 < A := by dsimp [A]; positivity
  have hscale : (1001 / 1000 : ℝ) * A < 2 * A := by nlinarith
  calc
    ‖PF4.CERT12ThetaTail.fullModeTail j t‖ <
        (1001 / 1000 : ℝ) * PF4.CERT12TailBounds.thirdProfile j (PF4.CERT12ThetaTail.certX t) := htail
    _ ≤ (1001 / 1000 : ℝ) * A := by
      dsimp [A]
      gcongr
    _ < 2 * A := hscale
    _ = 2 ^ (j + 2) * 3 ^ (2 * j + 4) * PF4.CERT12ThetaTail.certX t ^ j *
        Real.exp (-8 * PF4.CERT12ThetaTail.certX t) := by dsimp [A]; ring

theorem strictAntiOn_pow_mul_exp_outer
    {w k : ℕ} (hw : w ≤ 12) (hk : 1 ≤ k) :
    StrictAntiOn
      (fun x : ℝ => x ^ w * Real.exp (-8 * k * x)) (Set.Ici 5) := by
  have hcont : ContinuousOn
      (fun x : ℝ => x ^ w * Real.exp (-8 * k * x)) (Set.Ici 5) := by
    fun_prop
  apply strictAntiOn_of_deriv_neg (convex_Ici 5) hcont
  intro x hx
  rw [interior_Ici] at hx
  have hx5 : 5 < x := hx
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hcoef : (w : ℝ) - 8 * k * x < 0 := by
    have hw' : (w : ℝ) ≤ 12 := by exact_mod_cast hw
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hkx : x ≤ k * x := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right hk' hxpos.le
    nlinarith
  have hlin : HasDerivAt (fun y : ℝ => -8 * k * y) (-8 * k) x := by
    simpa [id_eq] using (hasDerivAt_id x).const_mul (-8 * (k : ℝ))
  have hraw := (hasDerivAt_pow w x).mul
    (Real.hasDerivAt_exp (-8 * k * x) |>.comp x hlin)
  have heq : (fun y : ℝ => y ^ w * Real.exp (-8 * k * y)) =ᶠ[nhds x]
      ((fun y : ℝ => y ^ w) * (Real.exp ∘ fun y : ℝ => -8 * k * y)) :=
    Filter.Eventually.of_forall fun _ => rfl
  have hraw' := hraw.congr_of_eventuallyEq heq
  rw [hraw'.deriv]
  by_cases hw0 : w = 0
  · subst w
    norm_num
    positivity
  · have hw1 : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr hw0
    have hpow : x ^ w = x ^ (w - 1) * x := by
      conv_lhs => rw [show w = (w - 1) + 1 by omega, pow_succ]
    rw [hpow]
    rw [show (Real.exp ∘ fun y : ℝ => -8 * k * y) x =
      Real.exp (-8 * k * x) by rfl]
    rw [show (Real.exp (-8 * k * x) * (-8 * k)) =
      Real.exp (-8 * k * x) * (-8 * k) by rfl]
    ring_nf
    have hneg := mul_neg_of_pos_of_neg
      (mul_pos (pow_pos hxpos (w - 1))
        (Real.exp_pos (-(x * (k : ℝ) * 8)))) hcoef
    nlinarith [hneg]

theorem pow_mul_exp_outer_le_endpoint
    {w k : ℕ} (hw : w ≤ 12) (hk : 1 ≤ k) {x : ℝ} (hx : 5 ≤ x) :
    x ^ w * Real.exp (-8 * k * x) ≤
      5 ^ w * Real.exp (-8 * k * 5) := by
  by_cases h : x = 5
  · simp [h]
  · exact ((strictAntiOn_pow_mul_exp_outer hw hk)
      (by norm_num) hx (lt_of_le_of_ne hx (Ne.symm h))).le

noncomputable def outerBaseAt (x : ℝ) (j : Fin 7) : ℝ :=
  2 ^ ((j : ℕ) + 2) * x ^ (j : ℕ)

noncomputable def outerErrorAt (x : ℝ) (j : Fin 7) : ℝ :=
  2 ^ ((j : ℕ) + 2) * 3 ^ (2 * (j : ℕ) + 4) * x ^ (j : ℕ) *
    Real.exp (-8 * x)

noncomputable def qOuterBudget (r : ℝ) : ℝ :=
  518400 * r + 136048896 * r ^ 2

noncomputable def f2OuterBudget (r : ℝ) : ℝ :=
  377534545920 * r + 4998692009410560 * r ^ 2 +
  3534664311817371648 * r ^ 3 + 840669537675383930880 * r ^ 4 +
  85831335711191413555200 * r ^ 5 +
  3305098278324909156335616 * r ^ 6

noncomputable def c4OuterBudget (r : ℝ) : ℝ :=
  342660376166400 * r + 248230673903970680832 * r ^ 2 +
  3584348563373387100979200 * r ^ 3 +
  1223830676774023504745988096 * r ^ 4

theorem q_polynomialErrorBudget_outerAt (x : ℝ) :
    PF4.CERT12Inequalities.Perturbation.polynomialErrorBudget PF4.CERT12Inequalities.Perturbation.Generated.qTerms (outerBaseAt x) (outerErrorAt x) =
      x ^ 2 * qOuterBudget (Real.exp (-8 * x)) := by
  norm_num (config := { maxSteps := 10000000 }) [PF4.CERT12Inequalities.Perturbation.polynomialErrorBudget, PF4.CERT12Inequalities.Perturbation.monomialErrorBudget, PF4.CERT12Inequalities.Perturbation.Generated.qTerms,
    outerBaseAt, outerErrorAt, qOuterBudget, Fin.sum_univ_succ,
    PF4.CERT12Inequalities.Perturbation.prod_fin7_erase, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Fin.prod_univ_succ]
  ring

theorem f2_polynomialErrorBudget_outerAt (x : ℝ) :
    PF4.CERT12Inequalities.Perturbation.polynomialErrorBudget PF4.CERT12Inequalities.Perturbation.Generated.f2Terms (outerBaseAt x) (outerErrorAt x) =
      x ^ 6 * f2OuterBudget (Real.exp (-8 * x)) := by
  norm_num (config := { maxSteps := 10000000 }) [PF4.CERT12Inequalities.Perturbation.polynomialErrorBudget, PF4.CERT12Inequalities.Perturbation.monomialErrorBudget, PF4.CERT12Inequalities.Perturbation.Generated.f2Terms,
    outerBaseAt, outerErrorAt, f2OuterBudget, Fin.sum_univ_succ,
    PF4.CERT12Inequalities.Perturbation.prod_fin7_erase, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Fin.prod_univ_succ]
  ring

theorem c4_polynomialErrorBudget_outerAt (x : ℝ) :
    PF4.CERT12Inequalities.Perturbation.polynomialErrorBudget PF4.CERT12Inequalities.Perturbation.Generated.c4Terms (outerBaseAt x) (outerErrorAt x) =
      x ^ 12 * c4OuterBudget (Real.exp (-8 * x)) := by
  norm_num (config := { maxSteps := 10000000 }) [PF4.CERT12Inequalities.Perturbation.polynomialErrorBudget, PF4.CERT12Inequalities.Perturbation.monomialErrorBudget, PF4.CERT12Inequalities.Perturbation.Generated.c4Terms,
    outerBaseAt, outerErrorAt, c4OuterBudget, Fin.sum_univ_succ,
    PF4.CERT12Inequalities.Perturbation.prod_fin7_erase, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Fin.prod_univ_succ]
  ring


theorem exp_40_gt_two_e17 :
    (200000000000000000 : ℝ) < Real.exp 40 := by
  have hsum : (200000000000000000 : ℝ) <
      ∑ i ∈ Finset.range 100, (40 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 100)

theorem exp_neg_40_lt_inv_two_e17 :
    Real.exp (-40) < (1 / 200000000000000000 : ℝ) := by
  have hi := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 200000000000000000) exp_40_gt_two_e17
  simpa [one_div, ← Real.exp_neg] using hi

theorem outer_term_le_rational_endpoint
    {w k : ℕ} (hw : w ≤ 12) (hk : 1 ≤ k) {x : ℝ} (hx : 5 ≤ x) :
    x ^ w * Real.exp (-8 * x) ^ k ≤
      5 ^ w * (1 / 200000000000000000 : ℝ) ^ k := by
  have hmono := pow_mul_exp_outer_le_endpoint hw hk hx
  have hexp := exp_neg_40_lt_inv_two_e17
  rw [← Real.exp_nat_mul] at ⊢
  rw [show (k : ℝ) * (-8 * x) = -8 * k * x by ring]
  calc
    x ^ w * Real.exp (-8 * k * x) ≤
        5 ^ w * Real.exp (-8 * k * 5) := hmono
    _ = 5 ^ w * Real.exp (-40) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ 5 ^ w * (1 / 200000000000000000 : ℝ) ^ k := by
      gcongr

theorem q_polynomialErrorBudget_outer_lt {x : ℝ} (hx : 5 ≤ x) :
    PF4.CERT12Inequalities.Perturbation.polynomialErrorBudget PF4.CERT12Inequalities.Perturbation.Generated.qTerms (outerBaseAt x) (outerErrorAt x) < 10 := by
  rw [q_polynomialErrorBudget_outerAt]
  have h1 := outer_term_le_rational_endpoint (w := 2) (k := 1)
    (by norm_num) (by norm_num) hx
  have h2 := outer_term_le_rational_endpoint (w := 2) (k := 2)
    (by norm_num) (by norm_num) hx
  dsimp [qOuterBudget]
  ring_nf at h1 h2 ⊢
  nlinarith

theorem f2_polynomialErrorBudget_outer_lt {x : ℝ} (hx : 5 ≤ x) :
    PF4.CERT12Inequalities.Perturbation.polynomialErrorBudget PF4.CERT12Inequalities.Perturbation.Generated.f2Terms (outerBaseAt x) (outerErrorAt x) < 1000 := by
  rw [f2_polynomialErrorBudget_outerAt]
  have h1 := outer_term_le_rational_endpoint (w := 6) (k := 1)
    (by norm_num) (by norm_num) hx
  have h2 := outer_term_le_rational_endpoint (w := 6) (k := 2)
    (by norm_num) (by norm_num) hx
  have h3 := outer_term_le_rational_endpoint (w := 6) (k := 3)
    (by norm_num) (by norm_num) hx
  have h4 := outer_term_le_rational_endpoint (w := 6) (k := 4)
    (by norm_num) (by norm_num) hx
  have h5 := outer_term_le_rational_endpoint (w := 6) (k := 5)
    (by norm_num) (by norm_num) hx
  have h6 := outer_term_le_rational_endpoint (w := 6) (k := 6)
    (by norm_num) (by norm_num) hx
  dsimp [f2OuterBudget]
  ring_nf at h1 h2 h3 h4 h5 h6 ⊢
  nlinarith

theorem c4_polynomialErrorBudget_outer_lt {x : ℝ} (hx : 5 ≤ x) :
    PF4.CERT12Inequalities.Perturbation.polynomialErrorBudget PF4.CERT12Inequalities.Perturbation.Generated.c4Terms (outerBaseAt x) (outerErrorAt x) < 50000000 := by
  rw [c4_polynomialErrorBudget_outerAt]
  have h1 := outer_term_le_rational_endpoint (w := 12) (k := 1)
    (by norm_num) (by norm_num) hx
  have h2 := outer_term_le_rational_endpoint (w := 12) (k := 2)
    (by norm_num) (by norm_num) hx
  have h3 := outer_term_le_rational_endpoint (w := 12) (k := 3)
    (by norm_num) (by norm_num) hx
  have h4 := outer_term_le_rational_endpoint (w := 12) (k := 4)
    (by norm_num) (by norm_num) hx
  dsimp [c4OuterBudget]
  ring_nf at h1 h2 h3 h4 ⊢
  nlinarith

private noncomputable def baseJet (t : ℝ) (j : Fin 7) : ℝ :=
  PF4.CERT12Coordinates.twoModeNormalizedJet j (PF4.CERT12ThetaTail.certX t) (Real.exp (-3 * PF4.CERT12ThetaTail.certX t))

private noncomputable def tailJet (t : ℝ) (j : Fin 7) : ℝ :=
  PF4.CERT12ThetaTail.fullModeTail j t

theorem abs_baseJet_le_outerBaseAt {t : ℝ} (hx : 5 ≤ PF4.CERT12ThetaTail.certX t)
    (j : Fin 7) : |baseJet t j| ≤ outerBaseAt (PF4.CERT12ThetaTail.certX t) j := by
  exact abs_twoModeNormalizedJet_le_outer (by omega) hx

theorem abs_tailJet_le_outerErrorAt {t : ℝ} (ht : 0 ≤ t)
    (hx : 5 ≤ PF4.CERT12ThetaTail.certX t) (j : Fin 7) :
    |tailJet t j| ≤ outerErrorAt (PF4.CERT12ThetaTail.certX t) j := by
  rw [← Real.norm_eq_abs]
  exact (norm_fullModeTail_lt_outer (by omega) ht hx).le

theorem abs_q_literal_perturbation_lt_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ PF4.CERT12ThetaTail.certX t) :
    |PF4.ClearedJetCertificateBridge.clearedQ
        (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
        (baseJet t 2 + tailJet t 2) -
      PF4.ClearedJetCertificateBridge.clearedQ
        (baseJet t 0) (baseJet t 1) (baseJet t 2)| < 10 := by
  have h := PF4.CERT12Inequalities.Perturbation.abs_polynomialValue_add_sub_le PF4.CERT12Inequalities.Perturbation.Generated.qTerms (baseJet t) (tailJet t)
    (outerBaseAt (PF4.CERT12ThetaTail.certX t)) (outerErrorAt (PF4.CERT12ThetaTail.certX t))
    (by intro i; unfold outerBaseAt; positivity)
    (by intro i; unfold outerErrorAt; positivity)
    (abs_baseJet_le_outerBaseAt hx) (abs_tailJet_le_outerErrorAt ht hx)
  rw [PF4.CERT12Inequalities.Perturbation.Generated.qTerms_value, PF4.CERT12Inequalities.Perturbation.Generated.qTerms_value] at h
  exact h.trans_lt (q_polynomialErrorBudget_outer_lt hx)

theorem abs_f2_literal_perturbation_lt_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ PF4.CERT12ThetaTail.certX t) :
    |PF4.ClearedJetCertificateBridge.clearedF2
        (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
        (baseJet t 2 + tailJet t 2) (baseJet t 3 + tailJet t 3)
        (baseJet t 4 + tailJet t 4) -
      PF4.ClearedJetCertificateBridge.clearedF2
        (baseJet t 0) (baseJet t 1) (baseJet t 2)
        (baseJet t 3) (baseJet t 4)| < 1000 := by
  have h := PF4.CERT12Inequalities.Perturbation.abs_polynomialValue_add_sub_le PF4.CERT12Inequalities.Perturbation.Generated.f2Terms (baseJet t) (tailJet t)
    (outerBaseAt (PF4.CERT12ThetaTail.certX t)) (outerErrorAt (PF4.CERT12ThetaTail.certX t))
    (by intro i; unfold outerBaseAt; positivity)
    (by intro i; unfold outerErrorAt; positivity)
    (abs_baseJet_le_outerBaseAt hx) (abs_tailJet_le_outerErrorAt ht hx)
  rw [PF4.CERT12Inequalities.Perturbation.Generated.f2Terms_value, PF4.CERT12Inequalities.Perturbation.Generated.f2Terms_value] at h
  exact h.trans_lt (f2_polynomialErrorBudget_outer_lt hx)

theorem abs_c4_literal_perturbation_lt_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ PF4.CERT12ThetaTail.certX t) :
    |PF4.ClearedJetCertificateBridge.clearedC4
        (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
        (baseJet t 2 + tailJet t 2) (baseJet t 3 + tailJet t 3)
        (baseJet t 4 + tailJet t 4) (baseJet t 5 + tailJet t 5)
        (baseJet t 6 + tailJet t 6) -
      PF4.ClearedJetCertificateBridge.clearedC4
        (baseJet t 0) (baseJet t 1) (baseJet t 2) (baseJet t 3)
        (baseJet t 4) (baseJet t 5) (baseJet t 6)| < 50000000 := by
  have h := PF4.CERT12Inequalities.Perturbation.abs_polynomialValue_add_sub_le PF4.CERT12Inequalities.Perturbation.Generated.c4Terms (baseJet t) (tailJet t)
    (outerBaseAt (PF4.CERT12ThetaTail.certX t)) (outerErrorAt (PF4.CERT12ThetaTail.certX t))
    (by intro i; unfold outerBaseAt; positivity)
    (by intro i; unfold outerErrorAt; positivity)
    (abs_baseJet_le_outerBaseAt hx) (abs_tailJet_le_outerErrorAt ht hx)
  rw [PF4.CERT12Inequalities.Perturbation.Generated.c4Terms_value, PF4.CERT12Inequalities.Perturbation.Generated.c4Terms_value] at h
  exact h.trans_lt (c4_polynomialErrorBudget_outer_lt hx)

/-! Direct decreasing-correction certificate for the cleared q margin. -/

noncomputable def qMarginBase (x : ℝ) : ℝ :=
  16*x^3 - 88*x^2 + 180*x - 90

noncomputable def qMarginNeg (x : ℝ) : ℝ :=
  2304*x^4 - 5600*x^3 + 5424*x^2 - 1200*x

noncomputable def qMarginPos (x : ℝ) : ℝ :=
  16384*x^3 - 12288*x^2 + 3840*x

noncomputable def qMarginDecay (x : ℝ) : ℝ :=
  3*qMarginNeg x*qMarginBase x -
    (9216*x^3 - 16800*x^2 + 10848*x - 1200)*qMarginBase x +
    qMarginNeg x*(48*x^2 - 176*x + 180)

noncomputable def qMarginRatio (x : ℝ) : ℝ :=
  qMarginNeg x * Real.exp (-3*x) / qMarginBase x

theorem qMarginCorePolynomial_decomposition (x y : ℝ) :
    PF4.CERT12Inequalities.Generated.qMarginCorePolynomial x y =
      qMarginBase x - qMarginNeg x*y + qMarginPos x*y^2 := by
  simp [PF4.CERT12Inequalities.Generated.qMarginCorePolynomial, qMarginBase, qMarginNeg, qMarginPos]
  ring

theorem qMarginBase_pos {x : ℝ} (hx : 5 ≤ x) : 0 < qMarginBase x := by
  let z := x-5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [qMarginBase]
  ring_nf
  nlinarith [sq_nonneg z, pow_nonneg hz 3]

theorem qMarginNeg_pos {x : ℝ} (hx : 5 ≤ x) : 0 < qMarginNeg x := by
  let z := x-5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [qMarginNeg]
  ring_nf
  nlinarith [sq_nonneg z, pow_nonneg hz 3, pow_nonneg hz 4]

theorem qMarginPos_nonneg {x : ℝ} (hx : 5 ≤ x) : 0 ≤ qMarginPos x := by
  let z := x-5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [qMarginPos]
  ring_nf
  positivity

theorem qMarginDecay_pos {x : ℝ} (hx : 5 ≤ x) : 0 < qMarginDecay x := by
  let z := x-5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [qMarginDecay, qMarginBase, qMarginNeg] <;> ring_nf <;>
    positivity

theorem hasDerivAt_qMarginRatio {x : ℝ} (hx : 5 ≤ x) :
    HasDerivAt qMarginRatio
      (-Real.exp (-3*x)*qMarginDecay x/(qMarginBase x)^2) x := by
  have hb := (qMarginBase_pos hx).ne'
  have hn : HasDerivAt qMarginNeg
      (2304*4*x^3 - 5600*3*x^2 + 5424*2*x - 1200) x := by
    unfold qMarginNeg
    have hraw := ((((hasDerivAt_pow 4 x).const_mul (2304 : ℝ)).sub
      ((hasDerivAt_pow 3 x).const_mul (5600 : ℝ))).add
      ((hasDerivAt_pow 2 x).const_mul (5424 : ℝ))).sub
      ((hasDerivAt_id x).const_mul (1200 : ℝ))
    exact hraw.congr_deriv (by ring)
  have hbase : HasDerivAt qMarginBase
      (16*3*x^2 - 88*2*x + 180) x := by
    unfold qMarginBase
    have hraw := ((((hasDerivAt_pow 3 x).const_mul (16 : ℝ)).sub
      ((hasDerivAt_pow 2 x).const_mul (88 : ℝ))).add
      ((hasDerivAt_id x).const_mul (180 : ℝ))).sub
      (hasDerivAt_const x (90 : ℝ))
    exact hraw.congr_deriv (by ring)
  have hlin : HasDerivAt (fun y : ℝ => -3*y) (-3) x := by
    simpa [id_eq] using (hasDerivAt_id x).const_mul (-3 : ℝ)
  have hexp := Real.hasDerivAt_exp (-3*x) |>.comp x hlin
  unfold qMarginRatio
  have hquot := (hn.mul hexp).div hbase hb
  have heq : (fun y => qMarginNeg y * Real.exp (-3*y) / qMarginBase y) =ᶠ[nhds x]
      (qMarginNeg * (Real.exp ∘ fun y => -3*y) / qMarginBase) :=
    Filter.Eventually.of_forall fun _ => rfl
  apply (hquot.congr_of_eventuallyEq heq).congr_deriv
  unfold qMarginDecay qMarginBase qMarginNeg
  simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply]
  field_simp [hb]
  ring

theorem strictAntiOn_qMarginRatio :
    StrictAntiOn qMarginRatio (Set.Ici 5) := by
  have hcont : ContinuousOn qMarginRatio (Set.Ici 5) := by
    intro x hx
    have hb := (qMarginBase_pos hx).ne'
    unfold qMarginBase at hb
    unfold qMarginRatio qMarginNeg qMarginBase
    fun_prop
  apply strictAntiOn_of_deriv_neg (convex_Ici 5) hcont
  intro x hx
  rw [interior_Ici] at hx
  have hd := hasDerivAt_qMarginRatio hx.le
  rw [hd.deriv]
  have hdecay := qMarginDecay_pos hx.le
  have hb := qMarginBase_pos hx.le
  have hsq : 0 < qMarginBase x ^ 2 := sq_pos_of_pos hb
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _)) hdecay) hsq

theorem qMarginRatio_lt_one {x : ℝ} (hx : 5 ≤ x) :
    qMarginRatio x < 1 := by
  have hend : qMarginRatio 5 < 1 := by
    have he := exp_neg_three_mul_lt_inv_three_million
      (show (5 : ℝ) ≤ 5 by norm_num)
    norm_num [qMarginRatio, qMarginNeg, qMarginBase] at he ⊢
    nlinarith
  by_cases h : x=5
  · simpa [h] using hend
  · exact ((strictAntiOn_qMarginRatio (by norm_num) hx
      (lt_of_le_of_ne hx (Ne.symm h))).trans_le hend.le)

theorem qTwoModeMarginNumerator_pos_outer {x : ℝ} (hx : 5 ≤ x) :
    0 < PF4.CERT12Inequalities.Generated.qMarginCorePolynomial x (Real.exp (-3*x)) := by
  rw [qMarginCorePolynomial_decomposition]
  have hb := qMarginBase_pos hx
  have hm := qMarginNeg_pos hx
  have hp := qMarginPos_nonneg hx
  have he := Real.exp_pos (-3*x)
  have hr := qMarginRatio_lt_one hx
  have hmb : qMarginNeg x * Real.exp (-3*x) < qMarginBase x := by
    rw [qMarginRatio, div_lt_one hb] at hr
    exact hr
  nlinarith [mul_nonneg hp (sq_nonneg (Real.exp (-3*x)))]

theorem clearedQ_twoMode_gt_ten_outer {x : ℝ} (hx : 5 ≤ x) :
    10 < PF4.ClearedJetCertificateBridge.clearedQ
      (PF4.CERT12Coordinates.twoModeNormalizedJet 0 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 1 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 2 x (Real.exp (-3*x))) := by
  have hx0 : (157/50 : ℝ) ≤ x := by linarith
  have hden : 0 < 2 * x - 3 := by linarith
  rw [← sub_pos, PF4.CERT12TwoModeMargins.clearedQ_twoMode_sub_ten _ _
    hden.ne']
  exact div_pos (qTwoModeMarginNumerator_pos_outer hx)
    (pow_pos hden 2)

theorem clearedF2_twoMode_gt_thousand_outer {x : ℝ} (hx : 5 ≤ x) :
    1000 < PF4.ClearedJetCertificateBridge.clearedF2
      (PF4.CERT12Coordinates.twoModeNormalizedJet 0 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 1 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 2 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 3 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 4 x (Real.exp (-3*x))) := by
  have hden : 0 < 2 * x - 3 := by linarith
  rw [← sub_pos, PF4.CERT12TwoModeMargins.clearedF2_twoMode_sub_thousand _ _
    hden.ne']
  exact div_pos
    (PF4.CERT12F2OuterMargins.f2MarginCore_region_pos hx
      (Real.exp_pos _).le (exp_neg_three_mul_lt_inv_three_million hx).le)
    (pow_pos hden 6)

/-! Direct decreasing-correction certificate for the cleared C4 margin. -/

noncomputable def c4MarginRatio1 (x : ℝ) : ℝ :=
  PF4.CERT12C4OuterMargins.c4MarginNeg1 x * Real.exp (-3*x) / PF4.CERT12C4OuterMargins.c4MarginBase x

noncomputable def c4MarginRatio3 (x : ℝ) : ℝ :=
  PF4.CERT12C4OuterMargins.c4MarginNeg3 x * Real.exp (-9*x) / PF4.CERT12C4OuterMargins.c4MarginBase x

theorem hasDerivAt_c4MarginRatio1 {x : ℝ} (hx : 5 ≤ x) :
    HasDerivAt c4MarginRatio1
      (-Real.exp (-3*x)*PF4.CERT12C4OuterMargins.c4MarginDecay1 x/(PF4.CERT12C4OuterMargins.c4MarginBase x)^2) x := by
  have hb := (PF4.CERT12C4OuterMargins.c4MarginBase_pos hx).ne'
  have hn : HasDerivAt PF4.CERT12C4OuterMargins.c4MarginNeg1
      ((-312563957760)*8*x^7 + (-173237403648)*10*x^9 +
       (-15792537600)*6*x^5 + (-14077919232)*12*x^11 +
       1528823808*13*x^12 + 61970448384*11*x^10 +
       141059358720*7*x^6 + 308900560896*9*x^8) x := by
    unfold PF4.CERT12C4OuterMargins.c4MarginNeg1
    have h0 := (hasDerivAt_pow 8 x).const_mul (-312563957760 : ℝ)
    have h1 := h0.add ((hasDerivAt_pow 10 x).const_mul (-173237403648 : ℝ))
    have h2 := h1.add ((hasDerivAt_pow 6 x).const_mul (-15792537600 : ℝ))
    have h3 := h2.add ((hasDerivAt_pow 12 x).const_mul (-14077919232 : ℝ))
    have h4 := h3.add ((hasDerivAt_pow 13 x).const_mul (1528823808 : ℝ))
    have h5 := h4.add ((hasDerivAt_pow 11 x).const_mul (61970448384 : ℝ))
    have h6 := h5.add ((hasDerivAt_pow 7 x).const_mul (141059358720 : ℝ))
    have hraw := h6.add ((hasDerivAt_pow 9 x).const_mul (308900560896 : ℝ))
    exact hraw.congr_deriv (by ring)
  have hbase : HasDerivAt PF4.CERT12C4OuterMargins.c4MarginBase
      ((-10800000000)*2*x + (-800000000)*4*x^3 +
       (-41287680)*7*x^6 + (-4718592)*9*x^8 + 786432*10*x^9 +
       17694720*8*x^7 + 46448640*6*x^5 + 4800000000*3*x^2 +
       10800000000) x := by
    unfold PF4.CERT12C4OuterMargins.c4MarginBase
    have h0 := (hasDerivAt_const x (-4050000000 : ℝ)).add
      ((hasDerivAt_pow 2 x).const_mul (-10800000000 : ℝ))
    have h1 := h0.add ((hasDerivAt_pow 4 x).const_mul (-800000000 : ℝ))
    have h2 := h1.add ((hasDerivAt_pow 7 x).const_mul (-41287680 : ℝ))
    have h3 := h2.add ((hasDerivAt_pow 9 x).const_mul (-4718592 : ℝ))
    have h4 := h3.add ((hasDerivAt_pow 10 x).const_mul (786432 : ℝ))
    have h5 := h4.add ((hasDerivAt_pow 8 x).const_mul (17694720 : ℝ))
    have h6 := h5.add ((hasDerivAt_pow 6 x).const_mul (46448640 : ℝ))
    have h7 := h6.add ((hasDerivAt_pow 3 x).const_mul (4800000000 : ℝ))
    have hraw := h7.add ((hasDerivAt_id x).const_mul (10800000000 : ℝ))
    exact hraw.congr_deriv (by ring)
  have hlin : HasDerivAt (fun y : ℝ => -3*y) (-3) x := by
    simpa [id_eq] using (hasDerivAt_id x).const_mul (-3 : ℝ)
  have hexp := Real.hasDerivAt_exp (-3*x) |>.comp x hlin
  unfold c4MarginRatio1
  have hquot := (hn.mul hexp).div hbase hb
  have heq : (fun y => PF4.CERT12C4OuterMargins.c4MarginNeg1 y *
      Real.exp (-3*y) / PF4.CERT12C4OuterMargins.c4MarginBase y) =ᶠ[nhds x]
      (PF4.CERT12C4OuterMargins.c4MarginNeg1 *
        (Real.exp ∘ fun y => -3*y) / PF4.CERT12C4OuterMargins.c4MarginBase) :=
    Filter.Eventually.of_forall fun _ => rfl
  apply (hquot.congr_of_eventuallyEq heq).congr_deriv
  unfold PF4.CERT12C4OuterMargins.c4MarginDecay1
    PF4.CERT12C4OuterMargins.c4MarginBase
    PF4.CERT12C4OuterMargins.c4MarginNeg1
  simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply]
  field_simp [hb]
  ring

theorem hasDerivAt_c4MarginRatio3 {x : ℝ} (hx : 5 ≤ x) :
    HasDerivAt c4MarginRatio3
      (-Real.exp (-9*x)*PF4.CERT12C4OuterMargins.c4MarginDecay3 x/(PF4.CERT12C4OuterMargins.c4MarginBase x)^2) x := by
  have hb := (PF4.CERT12C4OuterMargins.c4MarginBase_pos hx).ne'
  have hn : HasDerivAt PF4.CERT12C4OuterMargins.c4MarginNeg3
      ((-519124442677248)*10*x^9 + (-305687754178560)*8*x^7 +
       (-124197569298432)*12*x^11 + (-16171558502400)*6*x^5 +
       25048249270272*13*x^12 + 103223163617280*7*x^6 +
       319756557090816*11*x^10 + 522657825030144*9*x^8) x := by
    unfold PF4.CERT12C4OuterMargins.c4MarginNeg3
    have h0 := (hasDerivAt_pow 10 x).const_mul (-519124442677248 : ℝ)
    have h1 := h0.add ((hasDerivAt_pow 8 x).const_mul (-305687754178560 : ℝ))
    have h2 := h1.add ((hasDerivAt_pow 12 x).const_mul (-124197569298432 : ℝ))
    have h3 := h2.add ((hasDerivAt_pow 6 x).const_mul (-16171558502400 : ℝ))
    have h4 := h3.add ((hasDerivAt_pow 13 x).const_mul (25048249270272 : ℝ))
    have h5 := h4.add ((hasDerivAt_pow 7 x).const_mul (103223163617280 : ℝ))
    have h6 := h5.add ((hasDerivAt_pow 11 x).const_mul (319756557090816 : ℝ))
    have hraw := h6.add ((hasDerivAt_pow 9 x).const_mul (522657825030144 : ℝ))
    exact hraw.congr_deriv (by ring)
  have hbase : HasDerivAt PF4.CERT12C4OuterMargins.c4MarginBase
      ((-10800000000)*2*x + (-800000000)*4*x^3 +
       (-41287680)*7*x^6 + (-4718592)*9*x^8 + 786432*10*x^9 +
       17694720*8*x^7 + 46448640*6*x^5 + 4800000000*3*x^2 +
       10800000000) x := by
    unfold PF4.CERT12C4OuterMargins.c4MarginBase
    have h0 := (hasDerivAt_const x (-4050000000 : ℝ)).add
      ((hasDerivAt_pow 2 x).const_mul (-10800000000 : ℝ))
    have h1 := h0.add ((hasDerivAt_pow 4 x).const_mul (-800000000 : ℝ))
    have h2 := h1.add ((hasDerivAt_pow 7 x).const_mul (-41287680 : ℝ))
    have h3 := h2.add ((hasDerivAt_pow 9 x).const_mul (-4718592 : ℝ))
    have h4 := h3.add ((hasDerivAt_pow 10 x).const_mul (786432 : ℝ))
    have h5 := h4.add ((hasDerivAt_pow 8 x).const_mul (17694720 : ℝ))
    have h6 := h5.add ((hasDerivAt_pow 6 x).const_mul (46448640 : ℝ))
    have h7 := h6.add ((hasDerivAt_pow 3 x).const_mul (4800000000 : ℝ))
    have hraw := h7.add ((hasDerivAt_id x).const_mul (10800000000 : ℝ))
    exact hraw.congr_deriv (by ring)
  have hlin : HasDerivAt (fun y : ℝ => -9*y) (-9) x := by
    simpa [id_eq] using (hasDerivAt_id x).const_mul (-9 : ℝ)
  have hexp := Real.hasDerivAt_exp (-9*x) |>.comp x hlin
  unfold c4MarginRatio3
  have hquot := (hn.mul hexp).div hbase hb
  have heq : (fun y => PF4.CERT12C4OuterMargins.c4MarginNeg3 y *
      Real.exp (-9*y) / PF4.CERT12C4OuterMargins.c4MarginBase y) =ᶠ[nhds x]
      (PF4.CERT12C4OuterMargins.c4MarginNeg3 *
        (Real.exp ∘ fun y => -9*y) / PF4.CERT12C4OuterMargins.c4MarginBase) :=
    Filter.Eventually.of_forall fun _ => rfl
  apply (hquot.congr_of_eventuallyEq heq).congr_deriv
  unfold PF4.CERT12C4OuterMargins.c4MarginDecay3
    PF4.CERT12C4OuterMargins.c4MarginBase
    PF4.CERT12C4OuterMargins.c4MarginNeg3
  simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply]
  field_simp [hb]
  ring

theorem strictAntiOn_c4MarginRatio1 :
    StrictAntiOn c4MarginRatio1 (Set.Ici 5) := by
  have hcont : ContinuousOn c4MarginRatio1 (Set.Ici 5) := by
    intro x hx
    have hb := (PF4.CERT12C4OuterMargins.c4MarginBase_pos hx).ne'
    unfold PF4.CERT12C4OuterMargins.c4MarginBase at hb
    unfold c4MarginRatio1 PF4.CERT12C4OuterMargins.c4MarginNeg1
      PF4.CERT12C4OuterMargins.c4MarginBase
    fun_prop
  apply strictAntiOn_of_deriv_neg (convex_Ici 5) hcont
  intro x hx
  rw [interior_Ici] at hx
  have hd := hasDerivAt_c4MarginRatio1 hx.le
  rw [hd.deriv]
  have hdecay := PF4.CERT12C4OuterMargins.c4MarginDecay1_pos hx.le
  have hb := PF4.CERT12C4OuterMargins.c4MarginBase_pos hx.le
  have hsq : 0 < PF4.CERT12C4OuterMargins.c4MarginBase x ^ 2 := sq_pos_of_pos hb
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _)) hdecay) hsq

theorem strictAntiOn_c4MarginRatio3 :
    StrictAntiOn c4MarginRatio3 (Set.Ici 5) := by
  have hcont : ContinuousOn c4MarginRatio3 (Set.Ici 5) := by
    intro x hx
    have hb := (PF4.CERT12C4OuterMargins.c4MarginBase_pos hx).ne'
    unfold PF4.CERT12C4OuterMargins.c4MarginBase at hb
    unfold c4MarginRatio3 PF4.CERT12C4OuterMargins.c4MarginNeg3
      PF4.CERT12C4OuterMargins.c4MarginBase
    fun_prop
  apply strictAntiOn_of_deriv_neg (convex_Ici 5) hcont
  intro x hx
  rw [interior_Ici] at hx
  have hd := hasDerivAt_c4MarginRatio3 hx.le
  rw [hd.deriv]
  have hdecay := PF4.CERT12C4OuterMargins.c4MarginDecay3_pos hx.le
  have hb := PF4.CERT12C4OuterMargins.c4MarginBase_pos hx.le
  have hsq : 0 < PF4.CERT12C4OuterMargins.c4MarginBase x ^ 2 := sq_pos_of_pos hb
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _)) hdecay) hsq

theorem c4MarginRatio_sum_lt_one {x : ℝ} (hx : 5 ≤ x) :
    c4MarginRatio1 x + c4MarginRatio3 x < 1 := by
  have he15 := exp_neg_three_mul_lt_inv_three_million
    (show (5 : ℝ) ≤ 5 by norm_num)
  have he45 : Real.exp (-45) < (1/3000000 : ℝ)^3 := by
    calc
      Real.exp (-45) = Real.exp (-15) ^ 3 := by
        convert Real.exp_nat_mul (-15 : ℝ) 3 using 1 <;> norm_num
      _ < (1 / 3000000 : ℝ) ^ 3 := by
        have hp := pow_lt_pow_left₀ (n := 3) he15 (Real.exp_pos _).le
          (by norm_num)
        norm_num at hp ⊢
        exact hp
  have h1end : c4MarginRatio1 5 <
      PF4.CERT12C4OuterMargins.c4MarginNeg1 5*(1/3000000 : ℝ)/PF4.CERT12C4OuterMargins.c4MarginBase 5 := by
    norm_num [c4MarginRatio1, PF4.CERT12C4OuterMargins.c4MarginNeg1, PF4.CERT12C4OuterMargins.c4MarginBase] at he15 ⊢
    nlinarith
  have h3end : c4MarginRatio3 5 <
      PF4.CERT12C4OuterMargins.c4MarginNeg3 5*(1/3000000 : ℝ)^3/PF4.CERT12C4OuterMargins.c4MarginBase 5 := by
    norm_num [c4MarginRatio3, PF4.CERT12C4OuterMargins.c4MarginNeg3, PF4.CERT12C4OuterMargins.c4MarginBase] at he45 ⊢
    nlinarith
  have hend : c4MarginRatio1 5 + c4MarginRatio3 5 < 1 := by
    have hexact : PF4.CERT12C4OuterMargins.c4MarginNeg1 5*(1/3000000 : ℝ)/PF4.CERT12C4OuterMargins.c4MarginBase 5 +
        PF4.CERT12C4OuterMargins.c4MarginNeg3 5*(1/3000000 : ℝ)^3/PF4.CERT12C4OuterMargins.c4MarginBase 5 < 1 := by
      norm_num [PF4.CERT12C4OuterMargins.c4MarginNeg1, PF4.CERT12C4OuterMargins.c4MarginNeg3, PF4.CERT12C4OuterMargins.c4MarginBase]
    linarith
  have h1 : c4MarginRatio1 x ≤ c4MarginRatio1 5 := by
    by_cases h : x=5
    · simp [h]
    · exact (strictAntiOn_c4MarginRatio1 (by norm_num) hx
        (lt_of_le_of_ne hx (Ne.symm h))).le
  have h3 : c4MarginRatio3 x ≤ c4MarginRatio3 5 := by
    by_cases h : x=5
    · simp [h]
    · exact (strictAntiOn_c4MarginRatio3 (by norm_num) hx
        (lt_of_le_of_ne hx (Ne.symm h))).le
  linarith

theorem c4TwoModeMarginNumerator_pos_outer {x : ℝ} (hx : 5 ≤ x) :
    0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x (Real.exp (-3*x)) := by
  rw [PF4.CERT12C4OuterMargins.decomposition]
  have hb := PF4.CERT12C4OuterMargins.c4MarginBase_pos hx
  have hp2 := PF4.CERT12C4OuterMargins.c4MarginPos2_pos hx
  have hp4 := PF4.CERT12C4OuterMargins.c4MarginPos4_pos hx
  have he := Real.exp_pos (-3*x)
  have hr := c4MarginRatio_sum_lt_one hx
  have hexp3 : Real.exp (-3*x)^3 = Real.exp (-9*x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hneg : PF4.CERT12C4OuterMargins.c4MarginNeg1 x*Real.exp (-3*x) +
      PF4.CERT12C4OuterMargins.c4MarginNeg3 x*Real.exp (-3*x)^3 < PF4.CERT12C4OuterMargins.c4MarginBase x := by
    rw [hexp3]
    rw [c4MarginRatio1, c4MarginRatio3, ← add_div, div_lt_one hb] at hr
    exact hr
  nlinarith [mul_nonneg hp2.le (sq_nonneg (Real.exp (-3*x))),
    mul_nonneg hp4.le (pow_nonneg he.le 4)]

theorem clearedC4_twoMode_gt_margin_outer {x : ℝ} (hx : 5 ≤ x) :
    50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (PF4.CERT12Coordinates.twoModeNormalizedJet 0 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 1 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 2 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 3 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 4 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 5 x (Real.exp (-3*x)))
      (PF4.CERT12Coordinates.twoModeNormalizedJet 6 x (Real.exp (-3*x))) := by
  have hx0 : (157/50 : ℝ) ≤ x := by linarith
  have hden : 0 < 2 * x - 3 := by linarith
  rw [← sub_pos, PF4.CERT12TwoModeMargins.clearedC4_twoMode_sub_margin _ _
    hden.ne']
  exact div_pos (c4TwoModeMarginNumerator_pos_outer hx)
    (pow_pos hden 4)

/-! ## Literal outer and universal half-line closure -/

theorem normalizedSeriesJet_eq_base_add_tail
    (j : Fin 7) {t : ℝ} (ht : 0 ≤ t) :
    PF4.CERT12ThetaTail.normalizedSeriesJet j t = baseJet t j + tailJet t j := by
  simpa [baseJet, tailJet, PF4.CERT12Coordinates.twoModeJet,
    PF4.CERT12Coordinates.fullTailJet, PF4.CERT12Coordinates.certY] using
    (PF4.CERT12Coordinates.normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) j ht)

theorem normalized_clearedQ_pos_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ PF4.CERT12ThetaTail.certX t) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (PF4.CERT12ThetaTail.normalizedSeriesJet 0 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 1 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 2 t) := by
  have hbase : 10 < PF4.ClearedJetCertificateBridge.clearedQ
      (baseJet t 0) (baseJet t 1) (baseJet t 2) := by
    simpa [baseJet] using clearedQ_twoMode_gt_ten_outer hx
  have hpert := abs_q_literal_perturbation_lt_outer ht hx
  rw [abs_lt] at hpert
  have hpos : 0 < PF4.ClearedJetCertificateBridge.clearedQ
      (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
      (baseJet t 2 + tailJet t 2) := by linarith
  simpa [← normalizedSeriesJet_eq_base_add_tail (j := (0 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (1 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (2 : Fin 7)) ht] using hpos

theorem normalized_clearedF2_pos_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ PF4.CERT12ThetaTail.certX t) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (PF4.CERT12ThetaTail.normalizedSeriesJet 0 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 1 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 2 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 3 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 4 t) := by
  have hx0 : (157/50 : ℝ) ≤ PF4.CERT12ThetaTail.certX t := by linarith
  have hbase : 1000 < PF4.ClearedJetCertificateBridge.clearedF2
      (baseJet t 0) (baseJet t 1) (baseJet t 2) (baseJet t 3)
      (baseJet t 4) := by
    simpa [baseJet] using clearedF2_twoMode_gt_thousand_outer hx
  have hpert := abs_f2_literal_perturbation_lt_outer ht hx
  rw [abs_lt] at hpert
  have hpos : 0 < PF4.ClearedJetCertificateBridge.clearedF2
      (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
      (baseJet t 2 + tailJet t 2) (baseJet t 3 + tailJet t 3)
      (baseJet t 4 + tailJet t 4) := by linarith
  simpa [← normalizedSeriesJet_eq_base_add_tail (j := (0 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (1 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (2 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (3 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (4 : Fin 7)) ht] using hpos

theorem normalized_clearedC4_pos_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ PF4.CERT12ThetaTail.certX t) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (PF4.CERT12ThetaTail.normalizedSeriesJet 0 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 1 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 2 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 3 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 4 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 5 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 6 t) := by
  have hbase : 50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (baseJet t 0) (baseJet t 1) (baseJet t 2) (baseJet t 3)
      (baseJet t 4) (baseJet t 5) (baseJet t 6) := by
    simpa [baseJet] using clearedC4_twoMode_gt_margin_outer hx
  have hpert := abs_c4_literal_perturbation_lt_outer ht hx
  rw [abs_lt] at hpert
  have hpos : 0 < PF4.ClearedJetCertificateBridge.clearedC4
      (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
      (baseJet t 2 + tailJet t 2) (baseJet t 3 + tailJet t 3)
      (baseJet t 4 + tailJet t 4) (baseJet t 5 + tailJet t 5)
      (baseJet t 6 + tailJet t 6) := by linarith
  simpa [← normalizedSeriesJet_eq_base_add_tail (j := (0 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (1 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (2 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (3 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (4 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (5 : Fin 7)) ht,
    ← normalizedSeriesJet_eq_base_add_tail (j := (6 : Fin 7)) ht] using hpos

theorem normalized_clearedQ_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (PF4.CERT12ThetaTail.normalizedSeriesJet 0 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 1 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 2 t) := by
  by_cases hx : PF4.CERT12ThetaTail.certX t ≤ 5
  · exact PF4.CERT12CompactClosure.normalized_clearedQ_pos_of_certX_le_five ht hx
  · exact normalized_clearedQ_pos_outer ht (le_of_not_ge hx)

theorem normalized_clearedF2_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (PF4.CERT12ThetaTail.normalizedSeriesJet 0 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 1 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 2 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 3 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 4 t) := by
  by_cases hx : PF4.CERT12ThetaTail.certX t ≤ 5
  · exact PF4.CERT12CompactClosure.normalized_clearedF2_pos_of_certX_le_five ht hx
  · exact normalized_clearedF2_pos_outer ht (le_of_not_ge hx)

theorem normalized_clearedC4_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (PF4.CERT12ThetaTail.normalizedSeriesJet 0 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 1 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 2 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 3 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 4 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 5 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 6 t) := by
  by_cases hx : PF4.CERT12ThetaTail.certX t ≤ 5
  · exact PF4.CERT12CompactClosure.normalized_clearedC4_pos_of_certX_le_five ht hx
  · exact normalized_clearedC4_pos_outer ht (le_of_not_ge hx)

theorem normalized_cleared_signs_pos {t : ℝ} (ht : 0 ≤ t) :
    (0 < PF4.ClearedJetCertificateBridge.clearedQ
      (PF4.CERT12ThetaTail.normalizedSeriesJet 0 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 1 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 2 t)) ∧
    (0 < PF4.ClearedJetCertificateBridge.clearedF2
      (PF4.CERT12ThetaTail.normalizedSeriesJet 0 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 1 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 2 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 3 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 4 t)) ∧
    (0 < PF4.ClearedJetCertificateBridge.clearedC4
      (PF4.CERT12ThetaTail.normalizedSeriesJet 0 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 1 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 2 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 3 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 4 t) (PF4.CERT12ThetaTail.normalizedSeriesJet 5 t)
      (PF4.CERT12ThetaTail.normalizedSeriesJet 6 t)) :=
  ⟨normalized_clearedQ_pos ht, normalized_clearedF2_pos ht,
    normalized_clearedC4_pos ht⟩

theorem normalizedSeriesJet_eq_globalNormalized (j : ℕ) (t : ℝ) :
    PF4.CERT12ThetaTail.normalizedSeriesJet j t = PF4.GlobalKernelJetIdentification.normalizedThetaSeriesJet j t := by
  rfl

theorem terminalQuotD_global_kernel_pos
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    ∀ t, 0 < PF4.TranslationQuotientTower.terminalQuotD
      (PF4.GlobalKernelJetIdentification.kernelJet 0) (PF4.GlobalKernelJetIdentification.kernelJet 1) (PF4.GlobalKernelJetIdentification.kernelJet 2) (PF4.GlobalKernelJetIdentification.kernelJet 3)
      a c b d t := by
  apply PF4.GlobalKernelJetIdentification.terminalQuotD_kernelJet_pos_of_nonneg_normalizedClearedSigns
    (hQ := fun t ht => by
      simpa only [← normalizedSeriesJet_eq_globalNormalized] using
        normalized_clearedQ_pos ht)
    (hF2 := fun t ht => by
      simpa only [← normalizedSeriesJet_eq_globalNormalized] using
        normalized_clearedF2_pos ht)
    (hC4 := fun t ht => by
      simpa only [← normalizedSeriesJet_eq_globalNormalized] using
        normalized_clearedC4_pos ht)
    hac hcb hbd

end PF4.CERT12OuterClosure

#print axioms PF4.CERT12OuterClosure.normalized_cleared_signs_pos
#print axioms PF4.CERT12OuterClosure.terminalQuotD_global_kernel_pos
