/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CERT12Coordinates
import PF4.CERT12QMargins
import PF4.CERT12F2Margins
import PF4.CERT12C4MidMargins
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000

/-!
# Exact CERT12 two-mode margins on the compact band

This module rewrites the cleared q, F2, and C4 margins of the exact first two
normalized theta modes as rational-polynomial numerators over positive powers
of `2*x-3`.  The maintained split Bernstein certificates then give margins
strictly larger than the complete perturbation budgets through `x = 5`.
-/

namespace PF4.CERT12TwoModeMargins

open Finset
open PF4.CERT12Coordinates
open PF4.CERT12ExpBounds
open PF4.CERT12Inequalities.Generated
open PF4.CERT12C4MidMargins

theorem exp_10_gt_22000 : (22000 : ℝ) < Real.exp 10 := by
  have hsum : (22000 : ℝ) <
      ∑ i ∈ range 30, (10 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 30)

theorem exp_10_lt_23000 : Real.exp 10 < (23000 : ℝ) := by
  have he : Real.exp 1 < (2.719 : ℝ) := by
    have h := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
      (n := 10) (by norm_num)
    norm_num [sum_range_succ] at h ⊢
    linarith
  calc
    Real.exp 10 = Real.exp 1 ^ 10 := by
      convert Real.exp_nat_mul (1 : ℝ) 10 using 1 <;> norm_num
    _ < (2.719 : ℝ) ^ 10 := by
      exact pow_lt_pow_left₀ he (Real.exp_pos 1).le (by omega)
    _ < 23000 := by norm_num

theorem exp_21_div_2_gt_36000 : (36000 : ℝ) < Real.exp (21 / 2) := by
  have hsum : (36000 : ℝ) <
      ∑ i ∈ range 32, (21 / 2 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 32)

theorem exp_12_gt_160000 : (160000 : ℝ) < Real.exp 12 := by
  have hsum : (160000 : ℝ) <
      ∑ i ∈ range 35, (12 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 35)

theorem exp_27_div_2_gt_700000 : (700000 : ℝ) < Real.exp (27 / 2) := by
  have hsum : (700000 : ℝ) <
      ∑ i ∈ range 38, (27 / 2 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 38)

theorem exp_neg_three_mul_lt_inv_22000 {x : ℝ}
    (hx : (10 / 3 : ℝ) ≤ x) :
    Real.exp (-3 * x) < 1 / 22000 := by
  have harg : (10 : ℝ) ≤ 3 * x := by linarith
  have hexp : (22000 : ℝ) < Real.exp (3 * x) :=
    exp_10_gt_22000.trans_le (Real.exp_monotone harg)
  have hinv := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 22000) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

theorem inv_23000_lt_exp_neg_three_mul {x : ℝ}
    (hx : x ≤ (10 / 3 : ℝ)) :
    1 / 23000 < Real.exp (-3 * x) := by
  have harg : 3 * x ≤ (10 : ℝ) := by linarith
  have hexp : Real.exp (3 * x) < (23000 : ℝ) :=
    (Real.exp_monotone harg).trans_lt exp_10_lt_23000
  have hinv := one_div_lt_one_div_of_lt (Real.exp_pos (3 * x)) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

theorem exp_neg_three_mul_lt_inv_of_exp_bound
    {x a N : ℝ} (hax : a ≤ 3 * x) (hN : N < Real.exp a) (hN0 : 0 < N) :
    Real.exp (-3 * x) < 1 / N := by
  have h := hN.trans_le (Real.exp_monotone hax)
  have hi := one_div_lt_one_div_of_lt hN0 h
  simpa [one_div, ← Real.exp_neg] using hi

/-- Exact cleared-q margin identity for the first two normalized modes. -/
theorem clearedQ_twoMode_sub_ten (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedQ
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) - 10 =
      qMarginCorePolynomial x y / (2 * x - 3) ^ 2 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedQ, qMarginCorePolynomial]
  field_simp [hx]
  ring

/-- Exact cleared-F2 margin identity for the first two normalized modes. -/
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

/-- Exact cleared-C4 margin identity for the first two normalized modes. -/
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

theorem qMarginNumerator_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < qMarginCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact qMarginCore_box_pos hx0 hsplit (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    have h := qMarginMid_box_pos hlow hx5 (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_22000 hlow).le
    simpa [qMarginCorePolynomial, qMarginMidPolynomial] using h

theorem f2MarginNumerator_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < f2MarginCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact f2MarginCore_box_pos hx0 hsplit
      (inv_23000_lt_exp_neg_three_mul hsplit).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    have h := f2MarginMid_box_pos hlow hx5 (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_22000 hlow).le
    simpa [f2MarginCorePolynomial, f2MarginMidPolynomial] using h

theorem c4MarginNumerator_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < c4MarginCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hA : x ≤ 10 / 3
  · exact c4MarginCore_box_pos hx0 hA (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  have h10 : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hA).le
  by_cases hB : x ≤ 7 / 2
  · exact c4BandA_box_pos h10 hB (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_22000 h10).le
  have h7 : (7 / 2 : ℝ) ≤ x := (lt_of_not_ge hB).le
  by_cases hC : x ≤ 4
  · exact c4BandB_box_pos h7 hC (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_of_exp_bound (by linarith)
        exp_21_div_2_gt_36000 (by norm_num)).le
  have h4 : (4 : ℝ) ≤ x := (lt_of_not_ge hC).le
  by_cases hD : x ≤ 9 / 2
  · exact c4BandC_box_pos h4 hD (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_of_exp_bound (by linarith)
        exp_12_gt_160000 (by norm_num)).le
  have h9 : (9 / 2 : ℝ) ≤ x := (lt_of_not_ge hD).le
  exact c4BandD_box_pos h9 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_of_exp_bound (by linarith)
      exp_27_div_2_gt_700000 (by norm_num)).le

theorem clearedQ_twoMode_gt_ten_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    10 < PF4.ClearedJetCertificateBridge.clearedQ
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x))) := by
  have hden : 0 < 2 * x - 3 := by linarith
  rw [← sub_pos, clearedQ_twoMode_sub_ten _ _ hden.ne']
  exact div_pos (qMarginNumerator_pos_to_five hx0 hx5) (pow_pos hden 2)

theorem clearedF2_twoMode_gt_thousand_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    1000 < PF4.ClearedJetCertificateBridge.clearedF2
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x))) := by
  have hden : 0 < 2 * x - 3 := by linarith
  rw [← sub_pos, clearedF2_twoMode_sub_thousand _ _ hden.ne']
  exact div_pos (f2MarginNumerator_pos_to_five hx0 hx5) (pow_pos hden 6)

theorem clearedC4_twoMode_gt_margin_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 5 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 6 x (Real.exp (-3 * x))) := by
  have hden : 0 < 2 * x - 3 := by linarith
  rw [← sub_pos, clearedC4_twoMode_sub_margin _ _ hden.ne']
  exact div_pos (c4MarginNumerator_pos_to_five hx0 hx5) (pow_pos hden 4)

end PF4.CERT12TwoModeMargins

#print axioms PF4.CERT12TwoModeMargins.clearedQ_twoMode_gt_ten_to_five
#print axioms PF4.CERT12TwoModeMargins.clearedF2_twoMode_gt_thousand_to_five
#print axioms PF4.CERT12TwoModeMargins.clearedC4_twoMode_gt_margin_to_five
