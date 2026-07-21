/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CERT12TailPolynomial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# CERT12 exponential half-line bounds

Closed real-exponential estimates used to control the complete theta tail.
Finite Taylor sums occur only as exact lower bounds for `Real.exp`; no sampled
range is used.
-/

namespace PF4.CERT12TailExponential

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

theorem pow_mul_exp_neg_seven_le_endpoint
    {m : ℕ} (hm : m ≤ 7) {x : ℝ} (hx : 3 ≤ x) :
    x ^ m * Real.exp (-7 * x) ≤
      3 ^ m * Real.exp (-21) := by
  have hratio0 : 0 ≤ x / 3 := by positivity
  have hratio : x / 3 ≤ Real.exp (x - 3) := by
    calc
      x / 3 ≤ (x - 3) + 1 := by linarith
      _ ≤ Real.exp (x - 3) := Real.add_one_le_exp (x - 3)
  have hpow : (x / 3) ^ m ≤ Real.exp (7 * (x - 3)) := by
    calc
      (x / 3) ^ m ≤ Real.exp (x - 3) ^ m := by gcongr
      _ = Real.exp (m * (x - 3)) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (7 * (x - 3)) := by
        apply Real.exp_monotone
        have hxm : 0 ≤ x - 3 := by linarith
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hxm
  calc
    x ^ m * Real.exp (-7 * x) =
        3 ^ m * ((x / 3) ^ m * Real.exp (-7 * x)) := by
      rw [div_pow]
      field_simp
    _ ≤ 3 ^ m *
        (Real.exp (7 * (x - 3)) * Real.exp (-7 * x)) := by
      gcongr
    _ = 3 ^ m * Real.exp (-21) := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem successive_tail_majorant_ratio_lt
    {j n : ℕ} (hj : j ≤ 6) (hn : 4 ≤ n) {x : ℝ} (hx : 3 ≤ x) :
    (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (2 * j + 4) *
        Real.exp (-((2 * n + 1 : ℕ) : ℝ) * x) <
      (1 / 1000000000 : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hfrac0 : 0 ≤ (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by positivity
  have hfrac : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 5 / 4 := by
    rw [div_le_iff₀ hn0]
    push_cast
    nlinarith
  have hpow :
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (2 * j + 4) ≤
        ((5 : ℝ) / 4) ^ 16 := by
    calc
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (2 * j + 4) ≤
          ((5 : ℝ) / 4) ^ (2 * j + 4) := by gcongr
      _ ≤ ((5 : ℝ) / 4) ^ 16 := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
  have harg :
      -(((2 * n + 1 : ℕ) : ℝ) * x) ≤ (-27 : ℝ) := by
    have hcount : (9 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 9 ≤ 2 * n + 1 by omega)
    nlinarith
  have hexp :
      Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * x)) ≤ Real.exp (-27) :=
    Real.exp_monotone harg
  have he27 : (500000000000 : ℝ) < Real.exp 27 := by
    have hsum : (500000000000 : ℝ) <
        ∑ i ∈ range 60, (27 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
      norm_num [sum_range_succ]
    exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 60)
  have he0 := Real.exp_pos 27
  have hconstant :
      ((5 : ℝ) / 4) ^ 16 * Real.exp (-27) <
        (1 / 1000000000 : ℝ) := by
    rw [show Real.exp (-27) = (Real.exp 27)⁻¹ by
      rw [← Real.exp_neg]]
    rw [inv_eq_one_div]
    rw [show ((5 : ℝ) / 4) ^ 16 * (1 / Real.exp 27) =
      ((5 : ℝ) / 4) ^ 16 / Real.exp 27 by ring]
    rw [div_lt_iff₀ he0]
    have hp : ((5 : ℝ) / 4) ^ 16 < 36 := by norm_num
    nlinarith
  simpa only [neg_mul] using
    (mul_le_mul hpow hexp (Real.exp_nonneg _)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4) _)).trans_lt hconstant

end PF4.CERT12TailExponential

#print axioms PF4.CERT12TailExponential.relative_tail_endpoint_constant
#print axioms PF4.CERT12TailExponential.pow_mul_exp_neg_seven_le_endpoint
#print axioms PF4.CERT12TailExponential.successive_tail_majorant_ratio_lt
