import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option linter.style.header false

namespace PF4.CERT12Inequalities

open Finset

theorem exp_471_div_50_gt_12000 :
    (12000 : ℝ) < Real.exp (471 / 50) := by
  have hsum : (12000 : ℝ) <
      ∑ i ∈ range 30, (471 / 50 : ℝ) ^ i / i ! := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 30)

theorem exp_10_gt_22000 : (22000 : ℝ) < Real.exp 10 := by
  have hsum : (22000 : ℝ) <
      ∑ i ∈ range 30, (10 : ℝ) ^ i / i ! := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 30)

theorem exp_10_lt_23000 : Real.exp 10 < (23000 : ℝ) := by
  calc
    Real.exp 10 = Real.exp 1 ^ 10 := by
      convert Real.exp_nat_mul (1 : ℝ) 10 using 1 <;> norm_num
    _ < (2.7182818286 : ℝ) ^ 10 := by
      exact pow_lt_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9 (by omega)
    _ < 23000 := by norm_num

theorem exp_15_gt_3000000 : (3000000 : ℝ) < Real.exp 15 := by
  have hsum : (3000000 : ℝ) <
      ∑ i ∈ range 40, (15 : ℝ) ^ i / i ! := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 40)

theorem exp_neg_three_mul_lt_inv_12000 {x : ℝ}
    (hx : (157 / 50 : ℝ) ≤ x) :
    Real.exp (-3 * x) < 1 / 12000 := by
  have harg : (471 / 50 : ℝ) ≤ 3 * x := by linarith
  have hexp : (12000 : ℝ) < Real.exp (3 * x) :=
    exp_471_div_50_gt_12000.trans_le (Real.exp_monotone harg)
  have hinv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 12000) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

theorem exp_neg_three_mul_lt_inv_22000 {x : ℝ}
    (hx : (10 / 3 : ℝ) ≤ x) :
    Real.exp (-3 * x) < 1 / 22000 := by
  have harg : (10 : ℝ) ≤ 3 * x := by linarith
  have hexp : (22000 : ℝ) < Real.exp (3 * x) :=
    exp_10_gt_22000.trans_le (Real.exp_monotone harg)
  have hinv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 22000) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

theorem inv_23000_lt_exp_neg_three_mul {x : ℝ}
    (hx : x ≤ (10 / 3 : ℝ)) :
    1 / 23000 < Real.exp (-3 * x) := by
  have harg : 3 * x ≤ (10 : ℝ) := by linarith
  have hexp : Real.exp (3 * x) < (23000 : ℝ) :=
    (Real.exp_monotone harg).trans_lt exp_10_lt_23000
  have hinv := one_div_lt_one_div_of_lt (Real.exp_pos (3 * x)) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

theorem exp_neg_three_mul_lt_inv_3000000 {x : ℝ}
    (hx : (5 : ℝ) ≤ x) :
    Real.exp (-3 * x) < 1 / 3000000 := by
  have harg : (15 : ℝ) ≤ 3 * x := by linarith
  have hexp : (3000000 : ℝ) < Real.exp (3 * x) :=
    exp_15_gt_3000000.trans_le (Real.exp_monotone harg)
  have hinv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3000000) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

end PF4.CERT12Inequalities
