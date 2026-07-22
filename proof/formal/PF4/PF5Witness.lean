import PF4.PF5WitnessAlgebra
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
import PF4.CERT12ThetaTail
import PF4.KernelAnalytic

set_option linter.style.header false
set_option linter.unnecessarySeqFocus false

namespace PF4.PF5WitnessExp

open Finset

noncomputable def taylorSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, x ^ k / (k.factorial : ℝ)

noncomputable def taylorError (x : ℝ) (n : ℕ) : ℝ :=
  |x| ^ n * ((n + 1 : ℕ) : ℝ) / ((n.factorial : ℝ) * n)

theorem exp_nonneg_taylor_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    taylorSum x n ≤ Real.exp x ∧
      Real.exp x ≤ taylorSum x n + taylorError x n := by
  constructor
  · exact Real.sum_le_exp_of_nonneg hx0 n
  · have h := Real.exp_bound' hx0 hx1 hn
    convert h using 1 <;> simp only [taylorSum, taylorError,
      abs_of_nonneg hx0] <;> push_cast <;> ring

theorem exp_nonneg_bounds_of_taylor {x lower upper : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {n : ℕ} (hn : 0 < n)
    (hlower : lower ≤ taylorSum x n)
    (hupper : taylorSum x n + taylorError x n ≤ upper) :
    lower ≤ Real.exp x ∧ Real.exp x ≤ upper := by
  have h := exp_nonneg_taylor_bounds hx0 hx1 hn
  exact ⟨hlower.trans h.1, h.2.trans hupper⟩

theorem exp_neg_taylor_bounds {q : ℝ} (hq0 : 0 ≤ q)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hq1 : q / m ≤ 1)
    (hlower : 0 ≤ taylorSum (-(q / m)) n - taylorError (-(q / m)) n) :
    (taylorSum (-(q / m)) n - taylorError (-(q / m)) n) ^ m ≤
        Real.exp (-q) ∧
      Real.exp (-q) ≤
        (taylorSum (-(q / m)) n + taylorError (-(q / m)) n) ^ m := by
  have hzabs : |-(q / m)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg (div_nonneg hq0 (by positivity))]
    exact hq1
  have hb : |Real.exp (-(q / m)) - taylorSum (-(q / m)) n| ≤
      taylorError (-(q / m)) n := by
    have h := Real.exp_bound hzabs hn
    convert h using 1 <;> simp only [taylorSum, taylorError] <;> push_cast <;> ring
  have hbounds := abs_le.mp hb
  have hlo : taylorSum (-(q / m)) n - taylorError (-(q / m)) n ≤
      Real.exp (-(q / m)) := by
    linarith [hbounds.1]
  have hhi : Real.exp (-(q / m)) ≤
      taylorSum (-(q / m)) n + taylorError (-(q / m)) n := by
    linarith [hbounds.2]
  have hid : Real.exp (-q) = Real.exp (-(q / m)) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hid]
  constructor
  · exact pow_le_pow_left₀ hlower hlo m
  · exact pow_le_pow_left₀ (Real.exp_nonneg _) hhi m

theorem exp_neg_bounds_of_taylor {q lower upper : ℝ}
    (hq0 : 0 ≤ q) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hq1 : q / m ≤ 1)
    (hbase : 0 ≤ taylorSum (-(q / m)) n - taylorError (-(q / m)) n)
    (hlower : lower ≤
      (taylorSum (-(q / m)) n - taylorError (-(q / m)) n) ^ m)
    (hupper :
      (taylorSum (-(q / m)) n + taylorError (-(q / m)) n) ^ m ≤ upper) :
    lower ≤ Real.exp (-q) ∧ Real.exp (-q) ≤ upper := by
  have h := exp_neg_taylor_bounds hq0 hm hn hq1 hbase
  exact ⟨hlower.trans h.1, h.2.trans hupper⟩

theorem exp_neg_lower_of_taylor {q lower : ℝ}
    (hq0 : 0 ≤ q) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hq1 : q / m ≤ 1)
    (hbase : 0 ≤ taylorSum (-(q / m)) n - taylorError (-(q / m)) n)
    (hlower : lower ≤
      (taylorSum (-(q / m)) n - taylorError (-(q / m)) n) ^ m) :
    lower ≤ Real.exp (-q) := by
  exact hlower.trans (exp_neg_taylor_bounds hq0 hm hn hq1 hbase).1

theorem exp_neg_upper_of_taylor {q upper : ℝ}
    (hq0 : 0 ≤ q) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hq1 : q / m ≤ 1)
    (hbase : 0 ≤ taylorSum (-(q / m)) n - taylorError (-(q / m)) n)
    (hupper :
      (taylorSum (-(q / m)) n + taylorError (-(q / m)) n) ^ m ≤ upper) :
    Real.exp (-q) ≤ upper := by
  exact (exp_neg_taylor_bounds hq0 hm hn hq1 hbase).2.trans hupper

theorem exp_neg_between_of_endpoints {x xl xu lower upper : ℝ}
    (hxl : xl ≤ x) (hxu : x ≤ xu)
    (hlower : lower ≤ Real.exp (-xu))
    (hupper : Real.exp (-xl) ≤ upper) :
    lower ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ upper := by
  constructor
  · exact hlower.trans (Real.exp_monotone (by linarith))
  · exact (Real.exp_monotone (by linarith)).trans hupper

theorem exp_211_div_1000_bounds :
    (1234912355061 / 1000000000000 : ℝ) ≤ Real.exp (211 / 1000) ∧
      Real.exp (211 / 1000) ≤ (617456177531 / 500000000000 : ℝ) := by
  have h := exp_nonneg_taylor_bounds
    (x := (211 / 1000 : ℝ)) (by norm_num) (by norm_num) (n := 30) (by norm_num)
  constructor
  · exact (by norm_num [taylorSum, sum_range_succ] :
        (1234912355061 / 1000000000000 : ℝ) ≤ taylorSum (211 / 1000) 30).trans h.1
  · exact h.2.trans (by norm_num [taylorSum, taylorError, sum_range_succ])

theorem exp_211_div_500_bounds :
    (1525008524683 / 1000000000000 : ℝ) ≤ Real.exp (211 / 500) ∧
      Real.exp (211 / 500) ≤ (381252131171 / 250000000000 : ℝ) := by
  apply exp_nonneg_bounds_of_taylor (n := 24) <;>
    norm_num [taylorSum, taylorError, sum_range_succ]

theorem exp_633_div_1000_bounds :
    (376650373741 / 200000000000 : ℝ) ≤ Real.exp (633 / 1000) ∧
      Real.exp (633 / 1000) ≤ (941625934353 / 500000000000 : ℝ) := by
  apply exp_nonneg_bounds_of_taylor (n := 24) <;>
    norm_num [taylorSum, taylorError, sum_range_succ]

theorem exp_211_div_250_bounds :
    (581412750089 / 250000000000 : ℝ) ≤ Real.exp (211 / 250) ∧
      Real.exp (211 / 250) ≤ (2325651000357 / 1000000000000 : ℝ) := by
  apply exp_nonneg_bounds_of_taylor (n := 24) <;>
    norm_num [taylorSum, taylorError, sum_range_succ]

theorem exp_211_div_4000_bounds :
    (8235672427 / 7812500000 : ℝ) ≤ Real.exp (211 / 4000) ∧
      Real.exp (211 / 4000) ≤ (1054166070657 / 1000000000000 : ℝ) := by
  apply exp_nonneg_bounds_of_taylor (n := 24) <;>
    norm_num [taylorSum, taylorError, sum_range_succ]

theorem exp_211_div_2000_bounds :
    (555633052261 / 500000000000 : ℝ) ≤ Real.exp (211 / 2000) ∧
      Real.exp (211 / 2000) ≤ (1111266104523 / 1000000000000 : ℝ) := by
  apply exp_nonneg_bounds_of_taylor (n := 24) <;>
    norm_num [taylorSum, taylorError, sum_range_succ]

theorem exp_633_div_4000_bounds :
    (585729511429 / 500000000000 : ℝ) ≤ Real.exp (633 / 4000) ∧
      Real.exp (633 / 4000) ≤ (1171459022859 / 1000000000000 : ℝ) := by
  apply exp_nonneg_bounds_of_taylor (n := 24) <;>
    norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k0n1_bounds {x : ℝ}
    (hxl : (3141592653589 / 1000000000000 : ℝ) ≤ x)
    (hxu : x ≤ (314159265359 / 100000000000 : ℝ)) :
    (43213918263763 / 1000000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (43213918263807 / 1000000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 4) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 4) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k0n2_bounds {x : ℝ}
    (hxl : (3141592653589 / 250000000000 : ℝ) ≤ x)
    (hxu : x ≤ (314159265359 / 25000000000 : ℝ)) :
    (871835589 / 250000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (3487342357 / 1000000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 13) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 13) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k1n1_bounds {x : ℝ}
    (hxl : (1939795791243 / 500000000000 : ℝ) ≤ x)
    (hxu : x ≤ (3879591582491 / 1000000000000 : ℝ)) :
    (4131852212571 / 200000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (20659261062959 / 1000000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 4) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 4) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k1n2_bounds {x : ℝ}
    (hxl : (1939795791243 / 125000000000 : ℝ) ≤ x)
    (hxu : x ≤ (3879591582491 / 250000000000 : ℝ)) :
    (36432513 / 200000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (91081283 / 500000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 16) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 16) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k2n1_bounds {x : ℝ}
    (hxl : (958191115561 / 200000000000 : ℝ) ≤ x)
    (hxu : x ≤ (479095557781 / 100000000000 : ℝ)) :
    (4152258988033 / 500000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (8304517976109 / 1000000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 5) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 5) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k2n2_bounds {x : ℝ}
    (hxl : (958191115561 / 50000000000 : ℝ) ≤ x)
    (hxu : x ≤ (479095557781 / 25000000000 : ℝ)) :
    (4756173 / 1000000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (2378087 / 500000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 20) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 20) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k3n1_bounds {x : ℝ}
    (hxl : (2958205117791 / 500000000000 : ℝ) ≤ x)
    (hxu : x ≤ (5916410235587 / 1000000000000 : ℝ)) :
    (538971347001 / 200000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (2694856735019 / 1000000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 6) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 6) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k3n2_bounds {x : ℝ}
    (hxl : (2958205117791 / 125000000000 : ℝ) ≤ x)
    (hxu : x ≤ (5916410235587 / 250000000000 : ℝ)) :
    (2637 / 50000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (52741 / 1000000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 24) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 24) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k4n1_bounds {x : ℝ}
    (hxl : (1826562024383 / 250000000000 : ℝ) ≤ x)
    (hxu : x ≤ (28540031631 / 3906250000 : ℝ)) :
    (335665550851 / 500000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (335665550853 / 500000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 8) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 8) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem decay_k4n2_bounds {x : ℝ}
    (hxl : (1826562024383 / 62500000000 : ℝ) ≤ x)
    (hxu : x ≤ (28540031631 / 976562500 : ℝ)) :
    (203 / 1000000000000000 : ℝ) ≤ Real.exp (-x) ∧
      Real.exp (-x) ≤ (51 / 250000000000000 : ℝ) := by
  apply exp_neg_between_of_endpoints hxl hxu
  · apply exp_neg_lower_of_taylor (m := 30) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]
  · apply exp_neg_upper_of_taylor (m := 30) (n := 24) <;>
      norm_num [taylorSum, taylorError, sum_range_succ]

theorem exp_neg_28_le : Real.exp (-28) ≤ (7 / 10000000000000 : ℝ) := by
  apply exp_neg_upper_of_taylor (m := 28) (n := 24) <;>
    norm_num [taylorSum, taylorError, sum_range_succ]

theorem exp_neg_34_le : Real.exp (-34) ≤ (1 / 100000000000000 : ℝ) := by
  apply exp_neg_upper_of_taylor (m := 34) (n := 24) <;>
    norm_num [taylorSum, taylorError, sum_range_succ]

theorem exp_neg_314159265359_div_100000000000_bounds :
    (43213918263763 / 1000000000000000 : ℝ) ≤
        Real.exp (-(314159265359 / 100000000000 : ℝ)) ∧
      Real.exp (-(314159265359 / 100000000000 : ℝ)) ≤
        (43213918263807 / 1000000000000000 : ℝ) := by
  have h := exp_neg_taylor_bounds
    (q := (314159265359 / 100000000000 : ℝ)) (by norm_num)
    (m := 4) (n := 40) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [taylorSum, taylorError, sum_range_succ])
  constructor
  · exact (by norm_num [taylorSum, taylorError, sum_range_succ] :
        (43213918263763 / 1000000000000000 : ℝ) ≤
          (taylorSum (-(314159265359 / 100000000000 / 4 : ℝ)) 40 -
            taylorError (-(314159265359 / 100000000000 / 4 : ℝ)) 40) ^ 4).trans h.1
  · exact h.2.trans (by norm_num [taylorSum, taylorError, sum_range_succ])

end PF4.PF5WitnessExp

namespace PF4.PF5WitnessKernel

open PF4.CERT12ThetaTail
open PF4.PF5WitnessExp

structure Bound (x lower upper : ℝ) : Prop where
  lower_le : lower ≤ x
  le_upper : x ≤ upper

namespace Bound

theorem weaken {x l u l' u' : ℝ} (h : Bound x l u)
    (hl : l' ≤ l) (hu : u ≤ u') : Bound x l' u' :=
  ⟨hl.trans h.lower_le, h.le_upper.trans hu⟩

theorem add {x l u y m v : ℝ} (hx : Bound x l u) (hy : Bound y m v) :
    Bound (x + y) (l + m) (u + v) :=
  ⟨add_le_add hx.lower_le hy.lower_le, add_le_add hx.le_upper hy.le_upper⟩

theorem mul_nonneg {x l u y m v : ℝ} (hx : Bound x l u) (hy : Bound y m v)
    (hl : 0 ≤ l) (hm : 0 ≤ m) : Bound (x * y) (l * m) (u * v) := by
  have hx0 : 0 ≤ x := hl.trans hx.lower_le
  have hy0 : 0 ≤ y := hm.trans hy.lower_le
  have hu0 : 0 ≤ u := hx0.trans hx.le_upper
  constructor
  · exact mul_le_mul hx.lower_le hy.lower_le hm hx0
  · exact mul_le_mul hx.le_upper hy.le_upper hy0 hu0

end Bound

theorem kernelMode_eq (k : ℕ) (t : ℝ) :
    PF4.thetaMode k t =
      Real.exp (t / 2) *
        (2 * PF4.modeX k t * (2 * PF4.modeX k t - 3)) *
        Real.exp (-PF4.modeX k t) := by
  unfold PF4.thetaMode PF4.modeX
  rw [show Real.exp ((9 / 2) * t) =
      Real.exp (t / 2) * Real.exp (2 * t) ^ 2 by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring]
  rw [show Real.exp ((5 / 2) * t) =
      Real.exp (t / 2) * Real.exp (2 * t) by
    rw [← Real.exp_add]
    congr 1
    ring]
  ring_nf

theorem quadraticFactor_mono_bounds {x lower upper : ℝ}
    (hl : 3 ≤ lower) (hxl : lower ≤ x) (hxu : x ≤ upper) :
    Bound (2 * x * (2 * x - 3))
      (2 * lower * (2 * lower - 3))
      (2 * upper * (2 * upper - 3)) := by
  constructor
  · have hx : lower ≤ x := hxl
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : 0 ≤ 4 * (x + lower) - 6)]
  · have hu : 3 ≤ upper := hl.trans (hxl.trans hxu)
    nlinarith [mul_nonneg (sub_nonneg.mpr hxu) (by linarith : 0 ≤ 4 * (x + upper) - 6)]

theorem thetaMode_bounds {k : ℕ} {t al au xl xu dl du : ℝ}
    (hamp : Bound (Real.exp (t / 2)) al au)
    (hx : Bound (PF4.modeX k t) xl xu)
    (hdecay : Bound (Real.exp (-PF4.modeX k t)) dl du)
    (hxl : 3 ≤ xl) (hal : 0 ≤ al) (hdl : 0 ≤ dl) :
    Bound (PF4.thetaMode k t)
      (al * (2 * xl * (2 * xl - 3)) * dl)
      (au * (2 * xu * (2 * xu - 3)) * du) := by
  rw [kernelMode_eq]
  have hp := quadraticFactor_mono_bounds hxl hx.lower_le hx.le_upper
  have hpl : 0 ≤ 2 * xl * (2 * xl - 3) := by
    have : 0 ≤ xl := by linarith
    have : 0 ≤ 2 * xl - 3 := by linarith
    positivity
  exact (hamp.mul_nonneg hp hal hpl).mul_nonneg hdecay
    (mul_nonneg hal hpl) hdl

theorem thetaSeries_eq_first_three_relative {t : ℝ} (ht : 0 ≤ t) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 / 1000 ∧
      PF4.thetaSeries t =
        PF4.thetaMode 0 t + PF4.thetaMode 1 t +
          PF4.thetaMode 2 t * (1 + δ) := by
  obtain ⟨δ, hδ0, hδ1, hδeq⟩ :=
    normalizedSeriesJet_eq_first_three_relative (j := 0) (by norm_num) ht
  refine ⟨δ, hδ0, hδ1, ?_⟩
  have hs := (firstModeScale_pos ht).ne'
  simp only [normalizedSeriesJet, PF4.thetaSeriesJet_zero_eq,
    normalizedModeJet, thirdModeJet, firstModeScale,
    PF4.thetaModeJet_zero_eq_thetaMode] at hδeq
  have hden : PF4.thetaMode 0 t ≠ 0 := by
    simpa [firstModeScale, PF4.thetaModeJet_zero_eq_thetaMode] using hs
  apply (div_left_inj' hden).mp
  calc
    PF4.thetaSeries t / PF4.thetaMode 0 t =
        PF4.thetaMode 0 t / PF4.thetaMode 0 t +
          PF4.thetaMode 1 t / PF4.thetaMode 0 t +
          (PF4.thetaMode 2 t / PF4.thetaMode 0 t) * (1 + δ) := hδeq
    _ = (PF4.thetaMode 0 t + PF4.thetaMode 1 t +
          PF4.thetaMode 2 t * (1 + δ)) / PF4.thetaMode 0 t := by ring

theorem thetaSeries_bounds_from_modes {t l0 u0 l1 u1 u2 : ℝ}
    (ht : 0 ≤ t)
    (h0 : Bound (PF4.thetaMode 0 t) l0 u0)
    (h1 : Bound (PF4.thetaMode 1 t) l1 u1)
    (h2 : Bound (PF4.thetaMode 2 t) 0 u2) :
    Bound (PF4.thetaSeries t) (l0 + l1)
      (u0 + u1 + u2 * (1001 / 1000)) := by
  obtain ⟨δ, hδ0, hδ1, heq⟩ := thetaSeries_eq_first_three_relative ht
  have hδu : 1 + δ ≤ 1001 / 1000 := by linarith
  have h2nonneg : 0 ≤ PF4.thetaMode 2 t := h2.lower_le
  have htail0 : 0 ≤ PF4.thetaMode 2 t * (1 + δ) :=
    mul_nonneg h2nonneg (by linarith)
  have htailu : PF4.thetaMode 2 t * (1 + δ) ≤ u2 * (1001 / 1000) := by
    exact mul_le_mul h2.le_upper hδu (by linarith)
      (h2nonneg.trans h2.le_upper)
  rw [heq]
  exact ⟨by linarith [h0.lower_le, h1.lower_le],
    by linarith [h0.le_upper, h1.le_upper]⟩

theorem modeX_zero_bounds_of_exp {t el eu : ℝ}
    (he : Bound (Real.exp (2 * t)) el eu) (hel : 0 ≤ el) :
    Bound (PF4.modeX 0 t)
      ((314159265358979323846 / 100000000000000000000 : ℝ) * el)
      ((314159265358979323847 / 100000000000000000000 : ℝ) * eu) := by
  unfold PF4.modeX PF4.modeN
  convert (Bound.mk Real.pi_gt_d20.le Real.pi_lt_d20.le).mul_nonneg he
    (by norm_num) hel using 1 <;> norm_num

theorem modeX_scale_bounds {k : ℕ} {t xl xu : ℝ}
    (hx : Bound (PF4.modeX 0 t) xl xu) :
    Bound (PF4.modeX k t) (PF4.modeN k ^ 2 * xl) (PF4.modeN k ^ 2 * xu) := by
  have heq := PF4.CERT12ThetaTail.modeX_eq_modeN_sq_mul_certX k t
  unfold certX at heq
  rw [heq]
  exact ⟨mul_le_mul_of_nonneg_left hx.lower_le (sq_nonneg _),
    mul_le_mul_of_nonneg_left hx.le_upper (sq_nonneg _)⟩

theorem globalRiemannKernel_bounds_of_boxes
    {t al au xl xu d0l d0u d1l d1u d2u : ℝ}
    (ht : 0 ≤ t)
    (hamp : Bound (Real.exp (t / 2)) al au)
    (hx0 : Bound (PF4.modeX 0 t) xl xu)
    (hd0 : Bound (Real.exp (-PF4.modeX 0 t)) d0l d0u)
    (hd1 : Bound (Real.exp (-PF4.modeX 1 t)) d1l d1u)
    (hd2 : Bound (Real.exp (-PF4.modeX 2 t)) 0 d2u)
    (hxl : 3 ≤ xl) (hal : 0 ≤ al) (hd0l : 0 ≤ d0l) (hd1l : 0 ≤ d1l) :
    Bound (PF4.globalRiemannKernel t)
      (al * (2 * xl * (2 * xl - 3)) * d0l +
        al * (2 * (4 * xl) * (2 * (4 * xl) - 3)) * d1l)
      (au * (2 * xu * (2 * xu - 3)) * d0u +
        au * (2 * (4 * xu) * (2 * (4 * xu) - 3)) * d1u +
        (au * (2 * (9 * xu) * (2 * (9 * xu) - 3)) * d2u) *
          (1001 / 1000)) := by
  have hx1 := modeX_scale_bounds (k := 1) hx0
  have hx2 := modeX_scale_bounds (k := 2) hx0
  have hx1' : Bound (PF4.modeX 1 t) (4 * xl) (4 * xu) := by
    convert hx1 using 1 <;> norm_num [PF4.modeN]
  have hx2' : Bound (PF4.modeX 2 t) (9 * xl) (9 * xu) := by
    convert hx2 using 1 <;> norm_num [PF4.modeN]
  have hm0 := thetaMode_bounds hamp hx0 hd0 hxl hal hd0l
  have hm1 := thetaMode_bounds hamp hx1' hd1
    (show (3 : ℝ) ≤ 4 * xl by nlinarith) hal hd1l
  have hm2 := thetaMode_bounds hamp hx2' hd2
    (show (3 : ℝ) ≤ 9 * xl by nlinarith) hal
    (by norm_num)
  have hm2' : Bound (PF4.thetaMode 2 t) 0
      (au * (2 * (9 * xu) * (2 * (9 * xu) - 3)) * d2u) := by
    convert hm2 using 1 <;> ring
  rw [PF4.globalRiemannKernel_eq_thetaSeries_of_nonneg ht]
  exact thetaSeries_bounds_from_modes ht hm0 hm1 hm2'

theorem globalRiemannKernel_zero_bounds :
    Bound (PF4.globalRiemannKernel 0)
      (893393799 / 1000000000 : ℝ)
      (893393802 / 1000000000 : ℝ) := by
  have hamp : Bound (Real.exp ((0 : ℝ) / 2)) 1 1 :=
    ⟨by norm_num, by norm_num⟩
  have hx0 : Bound (PF4.modeX 0 0)
      (3141592653589 / 1000000000000 : ℝ)
      (314159265359 / 100000000000 : ℝ) := by
    unfold PF4.modeX PF4.modeN
    norm_num
    constructor
    · linarith [Real.pi_gt_d20]
    · linarith [Real.pi_lt_d20]
  have hx1 := modeX_scale_bounds (k := 1) hx0
  have hx2 := modeX_scale_bounds (k := 2) hx0
  have hx1' : Bound (PF4.modeX 1 0)
      (3141592653589 / 250000000000 : ℝ)
      (314159265359 / 25000000000 : ℝ) := by
    convert hx1 using 1 <;> norm_num [PF4.modeN]
  have hx2' : Bound (PF4.modeX 2 0)
      (9 * (3141592653589 / 1000000000000 : ℝ))
      (9 * (314159265359 / 100000000000 : ℝ)) := by
    convert hx2 using 1 <;> norm_num [PF4.modeN]
  have hd0 : Bound (Real.exp (-PF4.modeX 0 0))
      (43213918263763 / 1000000000000000 : ℝ)
      (43213918263807 / 1000000000000000 : ℝ) :=
    ⟨(decay_k0n1_bounds hx0.lower_le hx0.le_upper).1,
      (decay_k0n1_bounds hx0.lower_le hx0.le_upper).2⟩
  have hd1 : Bound (Real.exp (-PF4.modeX 1 0))
      (871835589 / 250000000000000 : ℝ)
      (3487342357 / 1000000000000000 : ℝ) :=
    ⟨(decay_k0n2_bounds hx1'.lower_le hx1'.le_upper).1,
      (decay_k0n2_bounds hx1'.lower_le hx1'.le_upper).2⟩
  have hx2ge : (28 : ℝ) ≤ PF4.modeX 2 0 := by
    calc
      (28 : ℝ) ≤ 9 * (3141592653589 / 1000000000000 : ℝ) := by norm_num
      _ ≤ PF4.modeX 2 0 := hx2'.lower_le
  have hd2 : Bound (Real.exp (-PF4.modeX 2 0)) 0
      (7 / 10000000000000 : ℝ) := by
    constructor
    · exact (Real.exp_pos _).le
    · exact (Real.exp_monotone (neg_le_neg hx2ge)).trans exp_neg_28_le
  have hm0 := thetaMode_bounds hamp hx0 hd0 (by norm_num) (by norm_num) (by norm_num)
  have hm1 := thetaMode_bounds hamp hx1' hd1
    (by norm_num) (by norm_num) (by norm_num)
  have hm2 := thetaMode_bounds hamp hx2' hd2
    (by norm_num) (by norm_num) (by norm_num)
  have hm2' : Bound (PF4.thetaMode 2 0) 0
      (1 * (2 * (9 * (314159265359 / 100000000000 : ℝ)) *
        (2 * (9 * (314159265359 / 100000000000 : ℝ)) - 3)) *
          (7 / 10000000000000)) := by
    convert hm2 using 1 <;> ring
  have hs := thetaSeries_bounds_from_modes (t := 0) (by norm_num) hm0 hm1 hm2'
  rw [PF4.globalRiemannKernel_eq_thetaSeries_of_nonneg (by norm_num)]
  apply hs.weaken <;> norm_num

theorem globalRiemannKernel_one_bounds :
    Bound (PF4.globalRiemannKernel (211 / 2000))
      (804382231 / 1000000000 : ℝ)
      (804382232 / 1000000000 : ℝ) := by
  have he2 : Bound (Real.exp (2 * (211 / 2000 : ℝ)))
      (1234912355061 / 1000000000000 : ℝ)
      (617456177531 / 500000000000 : ℝ) := by
    simpa only [show (2 * (211 / 2000 : ℝ)) = 211 / 1000 by norm_num] using
      (Bound.mk exp_211_div_1000_bounds.1 exp_211_div_1000_bounds.2)
  have hamp : Bound (Real.exp ((211 / 2000 : ℝ) / 2))
      (8235672427 / 7812500000 : ℝ)
      (1054166070657 / 1000000000000 : ℝ) := by
    simpa only [show ((211 / 2000 : ℝ) / 2) = 211 / 4000 by norm_num] using
      (Bound.mk exp_211_div_4000_bounds.1 exp_211_div_4000_bounds.2)
  have hxraw := modeX_zero_bounds_of_exp he2 (by norm_num)
  have hx0 : Bound (PF4.modeX 0 (211 / 2000))
      (1939795791243 / 500000000000 : ℝ)
      (3879591582491 / 1000000000000 : ℝ) :=
    hxraw.weaken (by norm_num) (by norm_num)
  have hx1 := modeX_scale_bounds (k := 1) hx0
  have hx2 := modeX_scale_bounds (k := 2) hx0
  have hx1' : Bound (PF4.modeX 1 (211 / 2000))
      (1939795791243 / 125000000000 : ℝ)
      (3879591582491 / 250000000000 : ℝ) := by
    convert hx1 using 1 <;> norm_num [PF4.modeN]
  have hx2' : Bound (PF4.modeX 2 (211 / 2000))
      (9 * (1939795791243 / 500000000000 : ℝ))
      (9 * (3879591582491 / 1000000000000 : ℝ)) := by
    convert hx2 using 1 <;> norm_num [PF4.modeN]
  have hd0 : Bound (Real.exp (-PF4.modeX 0 (211 / 2000)))
      (4131852212571 / 200000000000000 : ℝ)
      (20659261062959 / 1000000000000000 : ℝ) :=
    ⟨(decay_k1n1_bounds hx0.lower_le hx0.le_upper).1,
      (decay_k1n1_bounds hx0.lower_le hx0.le_upper).2⟩
  have hd1 : Bound (Real.exp (-PF4.modeX 1 (211 / 2000)))
      (36432513 / 200000000000000 : ℝ)
      (91081283 / 500000000000000 : ℝ) :=
    ⟨(decay_k1n2_bounds hx1'.lower_le hx1'.le_upper).1,
      (decay_k1n2_bounds hx1'.lower_le hx1'.le_upper).2⟩
  have hx2ge : (34 : ℝ) ≤ PF4.modeX 2 (211 / 2000) := by
    calc
      (34 : ℝ) ≤ 9 * (1939795791243 / 500000000000 : ℝ) := by norm_num
      _ ≤ PF4.modeX 2 (211 / 2000) := by
        exact hx2'.lower_le
  have hd2 : Bound (Real.exp (-PF4.modeX 2 (211 / 2000))) 0
      (1 / 100000000000000 : ℝ) :=
    ⟨(Real.exp_pos _).le,
      (Real.exp_monotone (neg_le_neg hx2ge)).trans exp_neg_34_le⟩
  have hk := globalRiemannKernel_bounds_of_boxes (by norm_num) hamp hx0 hd0 hd1 hd2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply hk.weaken <;> norm_num

theorem globalRiemannKernel_two_bounds :
    Bound (PF4.globalRiemannKernel (211 / 1000))
      (582025473 / 1000000000 : ℝ)
      (582025474 / 1000000000 : ℝ) := by
  have he2 : Bound (Real.exp (2 * (211 / 1000 : ℝ)))
      (1525008524683 / 1000000000000 : ℝ)
      (381252131171 / 250000000000 : ℝ) := by
    simpa only [show (2 * (211 / 1000 : ℝ)) = 211 / 500 by norm_num] using
      (Bound.mk exp_211_div_500_bounds.1 exp_211_div_500_bounds.2)
  have hamp : Bound (Real.exp ((211 / 1000 : ℝ) / 2))
      (555633052261 / 500000000000 : ℝ)
      (1111266104523 / 1000000000000 : ℝ) := by
    simpa only [show ((211 / 1000 : ℝ) / 2) = 211 / 2000 by norm_num] using
      (Bound.mk exp_211_div_2000_bounds.1 exp_211_div_2000_bounds.2)
  have hxraw := modeX_zero_bounds_of_exp he2 (by norm_num)
  have hx0 : Bound (PF4.modeX 0 (211 / 1000))
      (958191115561 / 200000000000 : ℝ)
      (479095557781 / 100000000000 : ℝ) :=
    hxraw.weaken (by norm_num) (by norm_num)
  have hx1raw := modeX_scale_bounds (k := 1) hx0
  have hx2raw := modeX_scale_bounds (k := 2) hx0
  have hx1 : Bound (PF4.modeX 1 (211 / 1000))
      (958191115561 / 50000000000 : ℝ)
      (479095557781 / 25000000000 : ℝ) := by
    convert hx1raw using 1 <;> norm_num [PF4.modeN]
  have hx2 : Bound (PF4.modeX 2 (211 / 1000))
      (9 * (958191115561 / 200000000000 : ℝ))
      (9 * (479095557781 / 100000000000 : ℝ)) := by
    convert hx2raw using 1 <;> norm_num [PF4.modeN]
  have hd0 : Bound (Real.exp (-PF4.modeX 0 (211 / 1000)))
      (4152258988033 / 500000000000000 : ℝ)
      (8304517976109 / 1000000000000000 : ℝ) :=
    ⟨(decay_k2n1_bounds hx0.lower_le hx0.le_upper).1,
      (decay_k2n1_bounds hx0.lower_le hx0.le_upper).2⟩
  have hd1 : Bound (Real.exp (-PF4.modeX 1 (211 / 1000)))
      (4756173 / 1000000000000000 : ℝ)
      (2378087 / 500000000000000 : ℝ) :=
    ⟨(decay_k2n2_bounds hx1.lower_le hx1.le_upper).1,
      (decay_k2n2_bounds hx1.lower_le hx1.le_upper).2⟩
  have hx2ge : (34 : ℝ) ≤ PF4.modeX 2 (211 / 1000) := by
    calc
      (34 : ℝ) ≤ 9 * (958191115561 / 200000000000 : ℝ) := by norm_num
      _ ≤ PF4.modeX 2 (211 / 1000) := hx2.lower_le
  have hd2 : Bound (Real.exp (-PF4.modeX 2 (211 / 1000))) 0
      (1 / 100000000000000 : ℝ) :=
    ⟨(Real.exp_pos _).le,
      (Real.exp_monotone (neg_le_neg hx2ge)).trans exp_neg_34_le⟩
  have hk := globalRiemannKernel_bounds_of_boxes (by norm_num) hamp hx0 hd0 hd1 hd2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply hk.weaken <;> norm_num

theorem globalRiemannKernel_three_bounds :
    Bound (PF4.globalRiemannKernel (633 / 2000))
      (329951899 / 1000000000 : ℝ)
      (329951900 / 1000000000 : ℝ) := by
  have he2 : Bound (Real.exp (2 * (633 / 2000 : ℝ)))
      (376650373741 / 200000000000 : ℝ)
      (941625934353 / 500000000000 : ℝ) := by
    simpa only [show (2 * (633 / 2000 : ℝ)) = 633 / 1000 by norm_num] using
      (Bound.mk exp_633_div_1000_bounds.1 exp_633_div_1000_bounds.2)
  have hamp : Bound (Real.exp ((633 / 2000 : ℝ) / 2))
      (585729511429 / 500000000000 : ℝ)
      (1171459022859 / 1000000000000 : ℝ) := by
    simpa only [show ((633 / 2000 : ℝ) / 2) = 633 / 4000 by norm_num] using
      (Bound.mk exp_633_div_4000_bounds.1 exp_633_div_4000_bounds.2)
  have hxraw := modeX_zero_bounds_of_exp he2 (by norm_num)
  have hx0 : Bound (PF4.modeX 0 (633 / 2000))
      (2958205117791 / 500000000000 : ℝ)
      (5916410235587 / 1000000000000 : ℝ) :=
    hxraw.weaken (by norm_num) (by norm_num)
  have hx1raw := modeX_scale_bounds (k := 1) hx0
  have hx2raw := modeX_scale_bounds (k := 2) hx0
  have hx1 : Bound (PF4.modeX 1 (633 / 2000))
      (2958205117791 / 125000000000 : ℝ)
      (5916410235587 / 250000000000 : ℝ) := by
    convert hx1raw using 1 <;> norm_num [PF4.modeN]
  have hx2 : Bound (PF4.modeX 2 (633 / 2000))
      (9 * (2958205117791 / 500000000000 : ℝ))
      (9 * (5916410235587 / 1000000000000 : ℝ)) := by
    convert hx2raw using 1 <;> norm_num [PF4.modeN]
  have hd0 : Bound (Real.exp (-PF4.modeX 0 (633 / 2000)))
      (538971347001 / 200000000000000 : ℝ)
      (2694856735019 / 1000000000000000 : ℝ) :=
    ⟨(decay_k3n1_bounds hx0.lower_le hx0.le_upper).1,
      (decay_k3n1_bounds hx0.lower_le hx0.le_upper).2⟩
  have hd1 : Bound (Real.exp (-PF4.modeX 1 (633 / 2000)))
      (2637 / 50000000000000 : ℝ)
      (52741 / 1000000000000000 : ℝ) :=
    ⟨(decay_k3n2_bounds hx1.lower_le hx1.le_upper).1,
      (decay_k3n2_bounds hx1.lower_le hx1.le_upper).2⟩
  have hx2ge : (34 : ℝ) ≤ PF4.modeX 2 (633 / 2000) := by
    calc
      (34 : ℝ) ≤ 9 * (2958205117791 / 500000000000 : ℝ) := by norm_num
      _ ≤ PF4.modeX 2 (633 / 2000) := hx2.lower_le
  have hd2 : Bound (Real.exp (-PF4.modeX 2 (633 / 2000))) 0
      (1 / 100000000000000 : ℝ) :=
    ⟨(Real.exp_pos _).le,
      (Real.exp_monotone (neg_le_neg hx2ge)).trans exp_neg_34_le⟩
  have hk := globalRiemannKernel_bounds_of_boxes (by norm_num) hamp hx0 hd0 hd1 hd2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply hk.weaken <;> norm_num

theorem globalRiemannKernel_four_bounds :
    Bound (PF4.globalRiemannKernel (211 / 500))
      (140676936 / 1000000000 : ℝ)
      (140676937 / 1000000000 : ℝ) := by
  have he2 : Bound (Real.exp (2 * (211 / 500 : ℝ)))
      (581412750089 / 250000000000 : ℝ)
      (2325651000357 / 1000000000000 : ℝ) := by
    simpa only [show (2 * (211 / 500 : ℝ)) = 211 / 250 by norm_num] using
      (Bound.mk exp_211_div_250_bounds.1 exp_211_div_250_bounds.2)
  have hamp : Bound (Real.exp ((211 / 500 : ℝ) / 2))
      (1234912355061 / 1000000000000 : ℝ)
      (617456177531 / 500000000000 : ℝ) := by
    simpa only [show ((211 / 500 : ℝ) / 2) = 211 / 1000 by norm_num] using
      (Bound.mk exp_211_div_1000_bounds.1 exp_211_div_1000_bounds.2)
  have hxraw := modeX_zero_bounds_of_exp he2 (by norm_num)
  have hx0 : Bound (PF4.modeX 0 (211 / 500))
      (1826562024383 / 250000000000 : ℝ)
      (28540031631 / 3906250000 : ℝ) :=
    hxraw.weaken (by norm_num) (by norm_num)
  have hx1raw := modeX_scale_bounds (k := 1) hx0
  have hx2raw := modeX_scale_bounds (k := 2) hx0
  have hx1 : Bound (PF4.modeX 1 (211 / 500))
      (1826562024383 / 62500000000 : ℝ)
      (28540031631 / 976562500 : ℝ) := by
    convert hx1raw using 1 <;> norm_num [PF4.modeN]
  have hx2 : Bound (PF4.modeX 2 (211 / 500))
      (9 * (1826562024383 / 250000000000 : ℝ))
      (9 * (28540031631 / 3906250000 : ℝ)) := by
    convert hx2raw using 1 <;> norm_num [PF4.modeN]
  have hd0 : Bound (Real.exp (-PF4.modeX 0 (211 / 500)))
      (335665550851 / 500000000000000 : ℝ)
      (335665550853 / 500000000000000 : ℝ) :=
    ⟨(decay_k4n1_bounds hx0.lower_le hx0.le_upper).1,
      (decay_k4n1_bounds hx0.lower_le hx0.le_upper).2⟩
  have hd1 : Bound (Real.exp (-PF4.modeX 1 (211 / 500)))
      (203 / 1000000000000000 : ℝ)
      (51 / 250000000000000 : ℝ) :=
    ⟨(decay_k4n2_bounds hx1.lower_le hx1.le_upper).1,
      (decay_k4n2_bounds hx1.lower_le hx1.le_upper).2⟩
  have hx2ge : (34 : ℝ) ≤ PF4.modeX 2 (211 / 500) := by
    calc
      (34 : ℝ) ≤ 9 * (1826562024383 / 250000000000 : ℝ) := by norm_num
      _ ≤ PF4.modeX 2 (211 / 500) := hx2.lower_le
  have hd2 : Bound (Real.exp (-PF4.modeX 2 (211 / 500))) 0
      (1 / 100000000000000 : ℝ) :=
    ⟨(Real.exp_pos _).le,
      (Real.exp_monotone (neg_le_neg hx2ge)).trans exp_neg_34_le⟩
  have hk := globalRiemannKernel_bounds_of_boxes (by norm_num) hamp hx0 hd0 hd1 hd2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  apply hk.weaken <;> norm_num

end PF4.PF5WitnessKernel

namespace PF4

open PF4.PF5WitnessAlgebra
open PF4.PF5WitnessKernel

noncomputable def pf5WitnessSpacing : ℝ := 211 / 2000

noncomputable def pf5WitnessNodes : Fin 5 → ℝ :=
  fun i => ((i : ℕ) : ℝ) * pf5WitnessSpacing

theorem pf5WitnessSpacing_pos : 0 < pf5WitnessSpacing := by
  norm_num [pf5WitnessSpacing]

theorem pf5WitnessNodes_strictMono : StrictMono pf5WitnessNodes := by
  intro i j hij
  unfold pf5WitnessNodes
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) pf5WitnessSpacing_pos

theorem translationMatrix_pf5WitnessNodes_eq_equallySpaced :
    translationMatrix globalRiemannKernel pf5WitnessNodes pf5WitnessNodes =
      equallySpacedMatrix globalRiemannKernel 0 pf5WitnessSpacing := by
  ext i j
  unfold translationMatrix equallySpacedMatrix pf5WitnessNodes pf5WitnessSpacing
  unfold signedIndexDifference
  push_cast
  ring_nf

theorem equallySpacedMatrix_pf5Witness_eq_toeplitz5 :
    equallySpacedMatrix globalRiemannKernel 0 pf5WitnessSpacing =
      toeplitz5
        (globalRiemannKernel 0)
        (globalRiemannKernel (211 / 2000))
        (globalRiemannKernel (211 / 1000))
        (globalRiemannKernel (633 / 2000))
        (globalRiemannKernel (211 / 500)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [equallySpacedMatrix, signedIndexDifference, pf5WitnessSpacing, toeplitz5] <;>
    first | rfl | exact globalRiemannKernel_even _

theorem equallySpacedMatrix_pf5Witness_det_neg :
    (equallySpacedMatrix (n := 5) globalRiemannKernel 0 pf5WitnessSpacing).det < 0 := by
  rw [equallySpacedMatrix_pf5Witness_eq_toeplitz5]
  exact toeplitz5_neg_of_bounds
    globalRiemannKernel_zero_bounds.lower_le
    globalRiemannKernel_zero_bounds.le_upper
    globalRiemannKernel_one_bounds.lower_le
    globalRiemannKernel_one_bounds.le_upper
    globalRiemannKernel_two_bounds.lower_le
    globalRiemannKernel_two_bounds.le_upper
    globalRiemannKernel_three_bounds.lower_le
    globalRiemannKernel_three_bounds.le_upper
    globalRiemannKernel_four_bounds.lower_le
    globalRiemannKernel_four_bounds.le_upper

/-- Exact CERT17 order-five obstruction at spacing 211/2000, stated against
the maintained primary Riemann kernel and translation-minor orientation. -/
theorem globalRiemannKernel_pf5WitnessNodes_translationMinor_neg :
    translationMinor globalRiemannKernel pf5WitnessNodes pf5WitnessNodes < 0 := by
  unfold translationMinor
  rw [translationMatrix_pf5WitnessNodes_eq_equallySpaced]
  exact equallySpacedMatrix_pf5Witness_det_neg

/-- Literal T2 statement: the maintained primary Riemann kernel has a negative
order-five translation minor at the exact rational spacing `211/2000`. -/
theorem globalRiemannKernel_orderFive_translationMinor_neg :
    translationMinor globalRiemannKernel
      (fun i : Fin 5 => ((i : ℕ) : ℝ) * (211 / 2000 : ℝ))
      (fun j : Fin 5 => ((j : ℕ) : ℝ) * (211 / 2000 : ℝ)) < 0 := by
  have hnodes :
      (fun i : Fin 5 => ((i : ℕ) : ℝ) * (211 / 2000 : ℝ)) =
        pf5WitnessNodes := by
    funext i
    rfl
  rw [hnodes]
  exact globalRiemannKernel_pf5WitnessNodes_translationMinor_neg

end PF4
