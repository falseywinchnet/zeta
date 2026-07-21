/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact real exponential bounds for CERT12

Finite Taylor lower sums provide the exponential comparisons used to place
the natural curve `y = exp (-3*x)` inside the rational certificate boxes.
-/

namespace PF4.CERT12ExpBounds

open Finset

theorem exp_471_div_50_gt_12000 :
    (12000 : ℝ) < Real.exp (471 / 50) := by
  have hsum : (12000 : ℝ) <
      ∑ i ∈ range 30, (471 / 50 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 30)

theorem exp_neg_three_mul_lt_inv_12000 {x : ℝ}
    (hx : (157 / 50 : ℝ) ≤ x) :
    Real.exp (-3 * x) < 1 / 12000 := by
  have harg : (471 / 50 : ℝ) ≤ 3 * x := by linarith
  have hexp : (12000 : ℝ) < Real.exp (3 * x) :=
    exp_471_div_50_gt_12000.trans_le (Real.exp_monotone harg)
  have hinv := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 12000) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

end PF4.CERT12ExpBounds

#print axioms PF4.CERT12ExpBounds.exp_neg_three_mul_lt_inv_12000
