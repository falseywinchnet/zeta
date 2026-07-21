import PF4.CERT12TailPolynomial
import Mathlib.Tactic

set_option linter.style.header false

namespace PF4.CERT12ReplayRepair

open Finset
open PF4.CERT12TailPolynomial

theorem relative_tail_endpoint_constant
    {j : ℕ} (hj : j ≤ 6) :
    (2 : ℝ) * 2 ^ (j + 1) * 4 ^ (2 * j + 4) * 3 ^ (j + 1) *
        Real.exp (-21) <
      (1 / 1000 : ℝ) * 9 *
        ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) := by
  have hc := relative_tail_coefficient_lt_1000 hj
  have he : (1000000 : ℝ) < Real.exp 21 := by
    have hsum : (1000000 : ℝ) <
        ∑ i ∈ range 50, (21 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
      norm_num [sum_range_succ]
    exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 50)
  have he0 := Real.exp_pos 21
  rw [show Real.exp (-21) = (Real.exp 21)⁻¹ by
    rw [← Real.exp_neg]]
  rw [inv_eq_one_div]
  rw [show
    (2 : ℝ) * 2 ^ (j + 1) * 4 ^ (2 * j + 4) * 3 ^ (j + 1) *
        (1 / Real.exp 21) =
      ((2 : ℝ) * 2 ^ (j + 1) * 4 ^ (2 * j + 4) * 3 ^ (j + 1)) /
        Real.exp 21 by ring]
  rw [div_lt_iff₀ he0]
  have hA :
      0 < (2 : ℝ) * 2 ^ (j + 1) * 4 ^ (2 * j + 4) * 3 ^ (j + 1) := by
    positivity
  have hB : 0 < (-1 : ℝ) ^ j * (PF4.certPoly j).eval 27 := by
    nlinarith
  have hm :
      ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) * 1000000 <
        ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) * Real.exp 21 :=
    mul_lt_mul_of_pos_left he hB
  nlinarith

end PF4.CERT12ReplayRepair

#print axioms PF4.CERT12ReplayRepair.relative_tail_endpoint_constant
