import PF4.ClearedJetCertificateBridge
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact first-two-mode and tail decomposition

This file connects the literal maintained theta jet to the normalization used
by the finite and perturbative CERT12 certificates.
-/

namespace PF4.CERT12Inequalities.ThetaTail

open Finset Set

noncomputable def certX (t : ℝ) : ℝ := PF4.modeX 0 t
noncomputable def certY (t : ℝ) : ℝ := Real.exp (-3 * certX t)
noncomputable def firstModeScale (t : ℝ) : ℝ := PF4.thetaModeJet 0 0 t

noncomputable def normalizedModeJet (j k : ℕ) (t : ℝ) : ℝ :=
  PF4.thetaModeJet j k t / firstModeScale t

noncomputable def normalizedSeriesJet (j : ℕ) (t : ℝ) : ℝ :=
  PF4.thetaSeriesJet j t / firstModeScale t

noncomputable def twoModeNormalizedJet (j : ℕ) (t : ℝ) : ℝ :=
  ((PF4.certPoly j).eval (certX t) +
      4 * certY t * (PF4.certPoly j).eval (4 * certX t)) /
    (2 * certX t - 3)

noncomputable def normalizedTailJet (j : ℕ) (t : ℝ) : ℝ :=
  ∑' r : ℕ, normalizedModeJet j (r + 2) t

theorem certX_eq (t : ℝ) :
    certX t = Real.pi * Real.exp (2 * t) := by
  simp [certX, PF4.modeX, PF4.modeN]

theorem certX_ge_pi {t : ℝ} (ht : 0 ≤ t) : Real.pi ≤ certX t := by
  rw [certX_eq]
  have he : 1 ≤ Real.exp (2 * t) := (Real.one_le_exp_iff).2 (by linarith)
  nlinarith [Real.pi_pos]

theorem certX_ge_157_div_50 {t : ℝ} (ht : 0 ≤ t) :
    (157 / 50 : ℝ) ≤ certX t := by
  exact (le_of_lt (Real.pi_gt_d20.trans' (by norm_num))).trans (certX_ge_pi ht)

theorem certPoly_zero_eval (x : ℝ) :
    (PF4.certPoly 0).eval x = 2 * x - 3 := by
  simp [PF4.certPoly]

theorem firstModeScale_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < firstModeScale t := by
  have hx := certX_ge_pi ht
  have hden : 0 < 2 * certX t - 3 := by
    nlinarith [Real.pi_gt_three]
  unfold firstModeScale PF4.thetaModeJet
  rw [show PF4.modeX 0 t = certX t by rfl, certPoly_zero_eval]
  simp only [PF4.modeN, Nat.cast_one, one_pow, mul_one]
  positivity

theorem modeX_eq_modeN_sq_mul_certX (k : ℕ) (t : ℝ) :
    PF4.modeX k t = PF4.modeN k ^ 2 * certX t := by
  rw [certX_eq]
  unfold PF4.modeX
  ring

theorem normalizedModeJet_eq (j k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    normalizedModeJet j k t =
      PF4.modeN k ^ 2 *
        Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
        (PF4.certPoly j).eval (PF4.modeN k ^ 2 * certX t) /
        (2 * certX t - 3) := by
  have hs := (firstModeScale_pos ht).ne'
  unfold normalizedModeJet firstModeScale PF4.thetaModeJet
  rw [modeX_eq_modeN_sq_mul_certX, certPoly_zero_eval]
  rw [show PF4.modeX 0 t = certX t by rfl]
  simp only [PF4.modeN, Nat.cast_one, one_pow, mul_one]
  field_simp
  rw [← Real.exp_add]
  congr 1
  ring

theorem normalizedModeJet_zero (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    normalizedModeJet j 0 t =
      (PF4.certPoly j).eval (certX t) / (2 * certX t - 3) := by
  rw [normalizedModeJet_eq j 0 ht]
  simp [PF4.modeN]

theorem normalizedModeJet_one (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    normalizedModeJet j 1 t =
      4 * certY t * (PF4.certPoly j).eval (4 * certX t) /
        (2 * certX t - 3) := by
  rw [normalizedModeJet_eq j 1 ht]
  simp [PF4.modeN, certY]
  ring

theorem normalizedModeJet_zero_add_one (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    normalizedModeJet j 0 t + normalizedModeJet j 1 t =
      twoModeNormalizedJet j t := by
  rw [normalizedModeJet_zero j ht, normalizedModeJet_one j ht]
  unfold twoModeNormalizedJet
  ring

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

/-- Exact full normalized jet = first two normalized modes + the tail starting
at the original theta mode `n=3`. -/
theorem normalizedSeriesJet_eq_twoMode_add_tail
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    normalizedSeriesJet j t =
      twoModeNormalizedJet j t + normalizedTailJet j t := by
  rw [normalizedSeriesJet_eq_tsum_normalizedModeJet]
  have hsplit := (summable_normalizedModeJet_of_nonneg hj ht).sum_add_tsum_nat_add 2
  rw [← hsplit]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd]
  rw [normalizedModeJet_zero_add_one j ht]
  rfl

end PF4.CERT12Inequalities.ThetaTail
