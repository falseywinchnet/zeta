/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CERT12GeometricTsum
import PF4.ClearedJetCertificateBridge
import PF4.Kernel
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Literal normalized theta-tail control for CERT12

This module connects the maintained half-line and geometric-series bounds to
the literal `PF4.thetaSeriesJet`.  Its exported theorem removes the infinite
tail from the theorem-facing boundary without a finite cutoff.
-/

namespace PF4.CERT12ThetaTail

open Finset Set
open PF4.CERT12TailPolynomial
open PF4.CERT12TailExponential
open PF4.CERT12GeometricTsum

noncomputable def firstModeScale (t : ℝ) : ℝ := PF4.thetaModeJet 0 0 t

noncomputable def normalizedModeJet (j k : ℕ) (t : ℝ) : ℝ :=
  PF4.thetaModeJet j k t / firstModeScale t

noncomputable def certX (t : ℝ) : ℝ := PF4.modeX 0 t

noncomputable def normalizedSeriesJet (j : ℕ) (t : ℝ) : ℝ :=
  PF4.thetaSeriesJet j t / firstModeScale t

/-- The exact first term of the old tail: index `k=2`, hence theta mode
`n=k+1=3`. -/
noncomputable def thirdModeJet (j : ℕ) (t : ℝ) : ℝ :=
  normalizedModeJet j 2 t

/-- The genuinely infinite remainder after peeling off `n=3`; its first
term is `k=3`, hence `n=4`. -/
noncomputable def laterModeTail (j : ℕ) (t : ℝ) : ℝ :=
  ∑' r : ℕ, normalizedModeJet j (r + 3) t

/-- The tail used by the previous two-mode decomposition. -/
noncomputable def fullModeTail (j : ℕ) (t : ℝ) : ℝ :=
  ∑' r : ℕ, normalizedModeJet j (r + 2) t

theorem modeX_ge_27 {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    27 ≤ PF4.modeX k t := by
  have hn : (3 : ℝ) ≤ PF4.modeN k := by
    change (3 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.add_le_add_right hk 1
  have hn2 : (9 : ℝ) ≤ PF4.modeN k ^ 2 := by nlinarith
  have he : (1 : ℝ) ≤ Real.exp (2 * t) :=
    (Real.one_le_exp_iff).2 (by linarith)
  unfold PF4.modeX
  calc
    (27 : ℝ) = 3 * 9 * 1 := by norm_num
    _ ≤ Real.pi * PF4.modeN k ^ 2 * Real.exp (2 * t) := by
      gcongr
      exact Real.pi_gt_three.le

theorem certX_ge_three {t : ℝ} (ht : 0 ≤ t) : 3 ≤ certX t := by
  have he : (1 : ℝ) ≤ Real.exp (2 * t) :=
    (Real.one_le_exp_iff).2 (by linarith)
  unfold certX PF4.modeX PF4.modeN
  norm_num
  calc
    (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    _ ≤ Real.pi * Real.exp (2 * t) :=
      le_mul_of_one_le_right Real.pi_pos.le he

theorem modeX_eq_modeN_sq_mul_certX (k : ℕ) (t : ℝ) :
    PF4.modeX k t = PF4.modeN k ^ 2 * certX t := by
  simp [PF4.modeX, certX, PF4.modeN]
  ring

theorem firstModeScale_eq (t : ℝ) :
    firstModeScale t =
      2 * Real.pi * Real.exp ((5 / 2) * t) *
        (2 * certX t - 3) * Real.exp (-certX t) := by
  unfold firstModeScale PF4.thetaModeJet certX PF4.modeX PF4.modeN PF4.certPoly
  norm_num [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]

theorem firstModeScale_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < firstModeScale t := by
  have hx := certX_ge_three ht
  have hden : 0 < 2 * certX t - 3 := by linarith
  rw [firstModeScale_eq]
  positivity

theorem normalizedModeJet_eq
    (j k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    normalizedModeJet j k t =
      PF4.modeN k ^ 2 *
        Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
        (PF4.certPoly j).eval (PF4.modeN k ^ 2 * certX t) /
        (2 * certX t - 3) := by
  have hs := (firstModeScale_pos ht).ne'
  have hx := certX_ge_three ht
  have hden : 2 * certX t - 3 ≠ 0 := by linarith
  unfold normalizedModeJet
  rw [firstModeScale_eq]
  unfold PF4.thetaModeJet
  rw [modeX_eq_modeN_sq_mul_certX]
  have hscale :
      2 * Real.pi * Real.exp ((5 / 2) * t) * (2 * certX t - 3) *
          Real.exp (-certX t) ≠ 0 := by
    rw [← firstModeScale_eq]
    exact hs
  apply (div_eq_iff hscale).2
  rw [show Real.exp (-(PF4.modeN k ^ 2 * certX t)) =
      Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
        Real.exp (-certX t) by
    rw [← Real.exp_add]
    congr 1
    ring]
  field_simp [hden]

theorem thirdMode_norm_lower
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    9 * Real.exp (-8 * certX t) *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) /
        (2 * certX t - 3) ≤
      ‖thirdModeJet j t‖ := by
  have hx := certX_ge_three ht
  have hden : 0 < 2 * certX t - 3 := by linarith
  have hp := thirdMode_abs_certPoly_endpoint_le hj hx
  unfold thirdModeJet
  rw [normalizedModeJet_eq j 2 ht, Real.norm_eq_abs]
  norm_num [PF4.modeN]
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
    abs_of_pos (Real.exp_pos _), abs_of_pos hden]
  gcongr

noncomputable def normalizedModeMajorant
    (j k : ℕ) (t : ℝ) : ℝ :=
  2 ^ (j + 1) * PF4.modeN k ^ (2 * j + 4) * certX t ^ (j + 1) *
    Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) /
    (2 * certX t - 3)

theorem norm_normalizedModeJet_le_majorant
    {j k : ℕ} (hj : j ≤ 6) (hk : 2 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    ‖normalizedModeJet j k t‖ ≤ normalizedModeMajorant j k t := by
  have hx := certX_ge_three ht
  have hden : 0 < 2 * certX t - 3 := by linarith
  have hs : 27 ≤ PF4.modeN k ^ 2 * certX t := by
    rw [← modeX_eq_modeN_sq_mul_certX]
    exact modeX_ge_27 hk ht
  have hp := abs_certPoly_le_envelope hj hs
  rw [normalizedModeJet_eq j k ht, Real.norm_eq_abs]
  unfold normalizedModeMajorant
  rw [abs_div, abs_mul, abs_mul,
    abs_of_nonneg (sq_nonneg (PF4.modeN k)),
    abs_of_pos (Real.exp_pos _), abs_of_pos hden]
  calc
    PF4.modeN k ^ 2 * Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
          |(PF4.certPoly j).eval (PF4.modeN k ^ 2 * certX t)| /
        (2 * certX t - 3) ≤
      PF4.modeN k ^ 2 * Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
          (2 ^ (j + 1) *
            (PF4.modeN k ^ 2 * certX t) ^ (j + 1)) /
        (2 * certX t - 3) := by gcongr
    _ = 2 ^ (j + 1) * PF4.modeN k ^ (2 * j + 4) *
          certX t ^ (j + 1) *
          Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) /
        (2 * certX t - 3) := by
      rw [mul_pow]
      ring

theorem normalizedModeMajorant_succ_eq
    (j k : ℕ) (t : ℝ) :
    normalizedModeMajorant j (k + 1) t =
      normalizedModeMajorant j k t *
        (((PF4.modeN (k + 1)) / PF4.modeN k) ^ (2 * j + 4) *
          Real.exp (-(2 * PF4.modeN k + 1) * certX t)) := by
  have hn0 : PF4.modeN k ≠ 0 := (PF4.modeN_pos k).ne'
  have hexp :
      Real.exp (-(PF4.modeN (k + 1) ^ 2 - 1) * certX t) =
        Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
          Real.exp (-(2 * PF4.modeN k + 1) * certX t) := by
    rw [← Real.exp_add]
    congr 1
    simp [PF4.modeN]
    ring
  unfold normalizedModeMajorant
  rw [hexp, div_pow]
  field_simp

theorem normalizedModeMajorant_succ_lt
    {j k : ℕ} (hj : j ≤ 6) (hk : 3 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    normalizedModeMajorant j (k + 1) t <
      normalizedModeMajorant j k t * (1 / 1000000000 : ℝ) := by
  have hx := certX_ge_three ht
  have hratio := successive_tail_majorant_ratio_lt
    hj (n := k + 1) (by omega) hx
  have hden : 0 < 2 * certX t - 3 := by linarith
  have hmajor : 0 < normalizedModeMajorant j k t := by
    unfold normalizedModeMajorant
    have hn := PF4.modeN_pos k
    positivity
  rw [normalizedModeMajorant_succ_eq]
  have hratio' :
      (PF4.modeN (k + 1) / PF4.modeN k) ^ (2 * j + 4) *
          Real.exp (-(2 * PF4.modeN k + 1) * certX t) <
        (1 / 1000000000 : ℝ) := by
    simpa only [PF4.modeN, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat,
      neg_add_rev] using hratio
  exact mul_lt_mul_of_pos_left hratio' hmajor

theorem normalizedModeMajorant_geometric
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) (r : ℕ) :
    normalizedModeMajorant j (r + 3) t ≤
      normalizedModeMajorant j 3 t * (1 / 1000000000 : ℝ) ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      have hstep := normalizedModeMajorant_succ_lt
        hj (k := r + 3) (by omega) ht
      calc
        normalizedModeMajorant j (r + 1 + 3) t =
            normalizedModeMajorant j ((r + 3) + 1) t := by congr 2
        _ ≤ normalizedModeMajorant j (r + 3) t *
            (1 / 1000000000 : ℝ) := hstep.le
        _ ≤ (normalizedModeMajorant j 3 t *
              (1 / 1000000000 : ℝ) ^ r) *
            (1 / 1000000000 : ℝ) := by gcongr
        _ = normalizedModeMajorant j 3 t *
            (1 / 1000000000 : ℝ) ^ (r + 1) := by rw [pow_succ]; ring

theorem norm_later_mode_term_geometric
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) (r : ℕ) :
    ‖normalizedModeJet j (r + 3) t‖ ≤
      normalizedModeMajorant j 3 t * (1 / 1000000000 : ℝ) ^ r :=
  (norm_normalizedModeJet_le_majorant hj (by omega) ht).trans
    (normalizedModeMajorant_geometric hj ht r)

theorem two_later_majorant_lt_third_lower
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    2 * normalizedModeMajorant j 3 t <
      (1 / 1000 : ℝ) *
        (9 * Real.exp (-8 * certX t) *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) /
          (2 * certX t - 3)) := by
  have hx := certX_ge_three ht
  have hden : 0 < 2 * certX t - 3 := by linarith
  have hdecay := pow_mul_exp_neg_seven_le_endpoint
    (m := j + 1) (by omega) hx
  have hendpoint := relative_tail_endpoint_constant hj
  have h8 : Real.exp (-8 * certX t) = Real.exp (-(8 * certX t)) := by
    congr 1
    ring
  rw [h8]
  have hcore :
      2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4) *
          certX t ^ (j + 1) * Real.exp (-7 * certX t) <
        (1 / 1000 : ℝ) * 9 *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) := by
    calc
      2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4) *
          certX t ^ (j + 1) * Real.exp (-7 * certX t) =
        (2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4)) *
          (certX t ^ (j + 1) * Real.exp (-7 * certX t)) := by ring
      _ ≤ (2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4)) *
          (3 ^ (j + 1) * Real.exp (-21)) := by gcongr
      _ < (1 / 1000 : ℝ) * 9 *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) := by
        simpa only [mul_assoc] using hendpoint
  unfold normalizedModeMajorant
  norm_num [PF4.modeN]
  rw [show Real.exp (-(15 * certX t)) =
      Real.exp (-7 * certX t) * Real.exp (-(8 * certX t)) by
    rw [← Real.exp_add]
    congr 1
    ring]
  calc
    2 *
        (2 ^ (j + 1) * 4 ^ (2 * j + 4) * certX t ^ (j + 1) *
          (Real.exp (-7 * certX t) * Real.exp (-(8 * certX t))) /
          (2 * certX t - 3)) =
      (2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4) *
          certX t ^ (j + 1) * Real.exp (-7 * certX t)) *
        (Real.exp (-(8 * certX t)) / (2 * certX t - 3)) := by ring
    _ < ((1 / 1000 : ℝ) * 9 *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27)) *
        (Real.exp (-(8 * certX t)) / (2 * certX t - 3)) := by
      gcongr
    _ = (1 / 1000 : ℝ) *
        (9 * Real.exp (-(8 * certX t)) *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) /
          (2 * certX t - 3)) := by ring

/-- Every individual normalized mode `n>=3` has the same alternating strict
sign through derivative order six. -/
theorem normalizedModeJet_alternating_pos
    {j k : ℕ} (hj : j ≤ 6) (hk : 2 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    0 < (-1 : ℝ) ^ j * normalizedModeJet j k t := by
  have hp := certPoly_alternating_pos hj (modeX_ge_27 hk ht)
  have hden : 0 < 2 * certX t - 3 := by
    have hx := certX_ge_three ht
    linarith
  rw [normalizedModeJet_eq j k ht]
  rw [show (-1 : ℝ) ^ j *
      (PF4.modeN k ^ 2 *
          Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
          (PF4.certPoly j).eval (PF4.modeN k ^ 2 * certX t) /
          (2 * certX t - 3)) =
      PF4.modeN k ^ 2 *
        Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
        ((-1 : ℝ) ^ j *
          (PF4.certPoly j).eval (PF4.modeN k ^ 2 * certX t)) /
        (2 * certX t - 3) by ring]
  rw [modeX_eq_modeN_sq_mul_certX] at hp
  apply div_pos
  · exact mul_pos
      (mul_pos (sq_pos_of_pos (PF4.modeN_pos k)) (Real.exp_pos _)) hp
  · exact hden

theorem summable_thetaMode_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k : ℕ => PF4.thetaMode k t := by
  let B := t + 1
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) B := by
    dsimp [B]
    constructor <;> linarith
  have hzero : Summable fun k : ℕ => PF4.hModeJet 0 k t := by
    rw [funext fun k => PF4.hModeJet_zero_eq_hMode k t]
    exact (PF4.hasSum_nat_thetaTerms t).summable.mul_left
      (2 * Real.exp (t / 2)) |>.congr (fun k => by simp [PF4.hMode])
  have htwo : Summable fun k : ℕ => PF4.hModeJet 2 k t :=
    (PF4.HIntervalControl.summable_intervalMajorant B 1).of_norm_bounded fun k =>
      PF4.HIntervalControl.norm_hModeJet_le_intervalMajorant B 1 k htIoo
  exact (htwo.sub (hzero.mul_left (1 / 4 : ℝ))).div_const 2 |>.congr
    (fun k => PF4.secondOrder_hMode_eq_thetaMode k t)

theorem summable_thetaModeJet_of_nonneg
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k : ℕ => PF4.thetaModeJet j k t := by
  cases j with
  | zero =>
      simpa only [PF4.thetaModeJet_zero_eq_thetaMode] using
        summable_thetaMode_of_nonneg ht
  | succ j =>
      let B := t + 1
      have htIoo : t ∈ Set.Ioo (-1 : ℝ) B := by
        dsimp [B]
        constructor <;> linarith
      exact (PF4.IntervalControl.summable_intervalMajorant B j).of_norm_bounded
        fun k => PF4.IntervalControl.norm_thetaModeJet_le_intervalMajorant
          B j k htIoo

theorem summable_normalizedModeJet_of_nonneg
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k : ℕ => normalizedModeJet j k t := by
  simpa only [normalizedModeJet] using
    (summable_thetaModeJet_of_nonneg hj ht).div_const (firstModeScale t)

theorem normalizedSeriesJet_eq_tsum_normalizedModeJet
    (j : ℕ) (t : ℝ) :
    normalizedSeriesJet j t = ∑' k : ℕ, normalizedModeJet j k t := by
  unfold normalizedSeriesJet normalizedModeJet PF4.thetaSeriesJet
  rw [tsum_div_const]

theorem summable_fullModeTail_of_nonneg
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun r : ℕ => normalizedModeJet j (r + 2) t := by
  simpa [Function.comp_def, Nat.add_comm] using
    (summable_normalizedModeJet_of_nonneg hj ht).comp_injective
      (add_right_injective 2)

/-- The genuinely infinite `n>=4` remainder has the exact alternating weak
sign; this already uses every summand, not a truncation. -/
theorem laterModeTail_alternating_nonneg
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (-1 : ℝ) ^ j * laterModeTail j t := by
  unfold laterModeTail
  rw [← tsum_mul_left]
  exact tsum_nonneg fun r =>
    (normalizedModeJet_alternating_pos hj (k := r + 3) (by omega) ht).le

theorem fullModeTail_eq_third_add_later
    {j : ℕ} {t : ℝ}
    (hs : Summable fun r : ℕ => normalizedModeJet j (r + 2) t) :
    fullModeTail j t = thirdModeJet j t + laterModeTail j t := by
  have hsplit := hs.sum_add_tsum_nat_add 1
  unfold fullModeTail thirdModeJet laterModeTail
  calc
    (∑' r : ℕ, normalizedModeJet j (r + 2) t) =
        (∑ i ∈ Finset.range 1, normalizedModeJet j (i + 2) t) +
          ∑' i : ℕ, normalizedModeJet j (i + 1 + 2) t := hsplit.symm
    _ = normalizedModeJet j 2 t +
        ∑' r : ℕ, normalizedModeJet j (r + 3) t := by
      simp only [sum_range_one]

/-- The complete old tail, including every mode `n>=3`, has a strict
alternating sign through jet order six. -/
theorem fullModeTail_alternating_pos
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    0 < (-1 : ℝ) ^ j * fullModeTail j t := by
  rw [fullModeTail_eq_third_add_later
    (summable_fullModeTail_of_nonneg hj ht)]
  have hthird := normalizedModeJet_alternating_pos hj (k := 2) (by omega) ht
  have hlater := laterModeTail_alternating_nonneg hj ht
  rw [show (-1 : ℝ) ^ j *
      (thirdModeJet j t + laterModeTail j t) =
      (-1 : ℝ) ^ j * thirdModeJet j t +
        (-1 : ℝ) ^ j * laterModeTail j t by ring]
  exact add_pos_of_pos_of_nonneg hthird hlater

/-- The intended concrete interface: the complete `n>=4` remainder is less
than one thousandth of the exact `n=3` term. -/
theorem laterModeTail_lt_one_thousandth
    {j : ℕ} {t A q : ℝ}
    (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ r,
      ‖normalizedModeJet j (r + 3) t‖ ≤ A * q ^ r)
    (henvelope : A * (1 - q)⁻¹ < (1 / 1000 : ℝ) * ‖thirdModeJet j t‖) :
    ‖laterModeTail j t‖ <
      (1 / 1000 : ℝ) * ‖thirdModeJet j t‖ := by
  exact norm_tsum_lt_relative_of_geometric_bound
    (fun r => normalizedModeJet j (r + 3) t)
    A q (thirdModeJet j t) (1 / 1000)
    hA hq0 hq1 hbound henvelope

/-- Closed, universal relative estimate for the literal infinite theta tail.
There is no remaining geometric-majorant premise and no finite truncation. -/
theorem laterModeTail_lt_one_thousandth_closed
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ‖laterModeTail j t‖ <
      (1 / 1000 : ℝ) * ‖thirdModeJet j t‖ := by
  let A := normalizedModeMajorant j 3 t
  let q : ℝ := 1 / 1000000000
  have hA : 0 < A := by
    dsimp [A, normalizedModeMajorant]
    have hx := certX_ge_three ht
    have hden : 0 < 2 * certX t - 3 := by linarith
    norm_num [PF4.modeN]
    positivity
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have hbound : ∀ r,
      ‖normalizedModeJet j (r + 3) t‖ ≤ A * q ^ r := by
    intro r
    exact norm_later_mode_term_geometric hj ht r
  have hinv : (1 - q)⁻¹ < (2 : ℝ) := by
    norm_num [q]
  have hlower := thirdMode_norm_lower hj ht
  have htwo := two_later_majorant_lt_third_lower hj ht
  have henvelope : A * (1 - q)⁻¹ <
      (1 / 1000 : ℝ) * ‖thirdModeJet j t‖ := by
    calc
      A * (1 - q)⁻¹ < A * 2 := by gcongr
      _ = 2 * normalizedModeMajorant j 3 t := by dsimp [A]; ring
      _ < (1 / 1000 : ℝ) *
          (9 * Real.exp (-8 * certX t) *
            ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) /
            (2 * certX t - 3)) := htwo
      _ ≤ (1 / 1000 : ℝ) * ‖thirdModeJet j t‖ := by gcongr
  exact laterModeTail_lt_one_thousandth
    hA.le hq0 hq1 hbound henvelope

/-- The theorem-facing refactor: once the relative geometric estimate is
discharged, the old seven-coordinate tail is not an arbitrary error vector.
Each coordinate is its exact `n=3` value times `1+δ`, with one dimensionless
parameter in `[0,10⁻³)`. -/
theorem fullModeTail_eq_third_mul_one_add_relative
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t)
    (hrelative : ‖laterModeTail j t‖ <
      (1 / 1000 : ℝ) * ‖thirdModeJet j t‖) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 / 1000 ∧
      fullModeTail j t = thirdModeJet j t * (1 + δ) := by
  let σ : ℝ := (-1 : ℝ) ^ j
  let third := thirdModeJet j t
  let later := laterModeTail j t
  have hthird : 0 < σ * third := by
    exact normalizedModeJet_alternating_pos hj (by omega) ht
  have hlater : 0 ≤ σ * later := by
    exact laterModeTail_alternating_nonneg hj ht
  have hσ : σ ≠ 0 := by simp [σ]
  have hthird0 : third ≠ 0 := by
    intro h
    rw [h] at hthird
    simp at hthird
  let δ := (σ * later) / (σ * third)
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    exact div_nonneg hlater hthird.le
  have hδeq : δ = later / third := by
    dsimp [δ]
    field_simp
  have habsthird : 0 < ‖third‖ := norm_pos_iff.mpr hthird0
  have hδabs : ‖δ‖ = ‖later‖ / ‖third‖ := by
    rw [hδeq, norm_div]
  have hδlt : δ < 1 / 1000 := by
    apply lt_of_le_of_lt (Real.le_norm_self δ)
    rw [hδabs]
    exact (div_lt_iff₀ habsthird).2 hrelative
  refine ⟨δ, hδ0, hδlt, ?_⟩
  have hlater_eq : later = third * δ := by
    rw [hδeq]
    field_simp [hthird0]
  rw [fullModeTail_eq_third_add_later
    (summable_fullModeTail_of_nonneg hj ht)]
  change third + later = third * (1 + δ)
  rw [hlater_eq]
  ring

/-- Final closed theorem-facing form of the infinite tail refactor. -/
theorem fullModeTail_eq_third_mul_one_add_relative_closed
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 / 1000 ∧
      fullModeTail j t = thirdModeJet j t * (1 + δ) := by
  exact fullModeTail_eq_third_mul_one_add_relative hj ht
    (laterModeTail_lt_one_thousandth_closed hj ht)

/-- The literal normalized theta-series jet is exactly two leading modes plus
the exact third mode times a relative factor in `[1,1.001)`.  The infinite
tail no longer appears in the exported theorem statement. -/
theorem normalizedSeriesJet_eq_first_three_relative
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 / 1000 ∧
      normalizedSeriesJet j t =
        normalizedModeJet j 0 t + normalizedModeJet j 1 t +
          thirdModeJet j t * (1 + δ) := by
  obtain ⟨δ, hδ0, hδ1, htail⟩ :=
    fullModeTail_eq_third_mul_one_add_relative_closed hj ht
  refine ⟨δ, hδ0, hδ1, ?_⟩
  rw [normalizedSeriesJet_eq_tsum_normalizedModeJet]
  have hsplit :=
    (summable_normalizedModeJet_of_nonneg hj ht).sum_add_tsum_nat_add 2
  rw [← hsplit]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  change normalizedModeJet j 0 t + normalizedModeJet j 1 t +
      fullModeTail j t =
    normalizedModeJet j 0 t + normalizedModeJet j 1 t +
      thirdModeJet j t * (1 + δ)
  rw [htail]


end PF4.CERT12ThetaTail

#print axioms PF4.CERT12ThetaTail.laterModeTail_lt_one_thousandth_closed
#print axioms PF4.CERT12ThetaTail.fullModeTail_eq_third_mul_one_add_relative_closed
#print axioms PF4.CERT12ThetaTail.normalizedSeriesJet_eq_first_three_relative
