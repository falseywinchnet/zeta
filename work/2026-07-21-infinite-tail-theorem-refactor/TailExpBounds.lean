import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-! Exact Taylor bounds used by the relative-tail theorem. -/

namespace PF4.InfiniteTailRefactor

open Finset

theorem exp_21_gt_1000000 : (1000000 : ℝ) < Real.exp 21 := by
  have hsum : (1000000 : ℝ) <
      ∑ i ∈ range 50, (21 : ℝ) ^ i / i ! := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 50)

theorem exp_27_gt_500000000000 :
    (500000000000 : ℝ) < Real.exp 27 := by
  have hsum : (500000000000 : ℝ) <
      ∑ i ∈ range 60, (27 : ℝ) ^ i / i ! := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 60)

theorem five_four_pow_sixteen_lt_36 :
    ((5 : ℝ) / 4) ^ 16 < 36 := by norm_num

theorem geometric_ratio_constant_lt :
    ((5 : ℝ) / 4) ^ 16 / Real.exp 27 < 1 / 1000000000 := by
  have he := exp_27_gt_500000000000
  have hp := five_four_pow_sixteen_lt_36
  have he0 : 0 < Real.exp 27 := Real.exp_pos 27
  rw [div_lt_iff₀ he0]
  calc
    ((5 : ℝ) / 4) ^ 16 < 36 := hp
    _ < (1 / 1000000000 : ℝ) * Real.exp 27 := by
      nlinarith

end PF4.InfiniteTailRefactor

#print axioms PF4.InfiniteTailRefactor.geometric_ratio_constant_lt
