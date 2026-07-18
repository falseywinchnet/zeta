/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.Measures
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Curvature-coordinate triangular normalizers

This file proves PO-0023 and PO-0024 from an actual twice-differentiable
coordinate function, then discharges the analytic normalization inputs of
PO-0030 and PO-0031. The normalizers are constructed, not assumed.
-/

namespace PF4.Curvature

open MeasureTheory Set
open scoped Interval
open PF4.Densities PF4.Normalization PF4.Measures

noncomputable def chordSlope (Q : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (Q b - Q a) / (b - a)

noncomputable def coordinateLambda (Q : ℝ → ℝ) (p z w : ℝ) : ℝ :=
  (w - p) + chordSlope Q p z - chordSlope Q z w

noncomputable def coordinateDelta (Q Q1 : ℝ → ℝ) (p z : ℝ) : ℝ :=
  ((z - p) + Q1 p - chordSlope Q p z) / (z - p)

def curvature (Q2 : ℝ → ℝ) (t : ℝ) : ℝ := 2 - Q2 t

private noncomputable def increasingPrimitive
    (Q Q1 : ℝ → ℝ) (p t : ℝ) : ℝ :=
  (t - p) ^ 2 - (t - p) * Q1 t + Q t

private noncomputable def decreasingPrimitive
    (Q Q1 : ℝ → ℝ) (z t : ℝ) : ℝ :=
  -(z - t) ^ 2 - (z - t) * Q1 t - Q t

private theorem hasDerivAt_increasingPrimitive
    {Q Q1 Q2 : ℝ → ℝ} {p t : ℝ}
    (hQ : HasDerivAt Q (Q1 t) t) (hQ1 : HasDerivAt Q1 (Q2 t) t) :
    HasDerivAt (increasingPrimitive Q Q1 p)
      ((t - p) * curvature Q2 t) t := by
  unfold increasingPrimitive curvature
  convert (((hasDerivAt_id t).sub_const p).pow 2).sub
      (((hasDerivAt_id t).sub_const p).mul hQ1) |>.add hQ using 1 <;> ring

private theorem hasDerivAt_decreasingPrimitive
    {Q Q1 Q2 : ℝ → ℝ} {z t : ℝ}
    (hQ : HasDerivAt Q (Q1 t) t) (hQ1 : HasDerivAt Q1 (Q2 t) t) :
    HasDerivAt (decreasingPrimitive Q Q1 z)
      ((z - t) * curvature Q2 t) t := by
  unfold decreasingPrimitive curvature
  convert ((((hasDerivAt_id t).const_sub z).pow 2).neg.sub
      (((hasDerivAt_id t).const_sub z).mul hQ1)).sub hQ using 1 <;> ring

theorem increasing_integral
    {Q Q1 Q2 : ℝ → ℝ} {p z : ℝ} (hpz : p ≤ z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p z, HasDerivAt Q1 (Q2 t) t) :
    (∫ t in p..z, (t - p) * curvature Q2 t) =
      (z - p) ^ 2 - (z - p) * Q1 z + Q z - Q p := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_increasingPrimitive (hQ t ht) (hQ1 t ht))]
  simp [increasingPrimitive]

theorem decreasing_integral
    {Q Q1 Q2 : ℝ → ℝ} {p z : ℝ} (hpz : p ≤ z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p z, HasDerivAt Q1 (Q2 t) t) :
    (∫ t in p..z, (z - t) * curvature Q2 t) =
      (z - p) ^ 2 + (z - p) * Q1 p + Q p - Q z := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_decreasingPrimitive (hQ t ht) (hQ1 t ht))]
  simp [decreasingPrimitive]
  ring

/-- PO-0023: the coordinate normalizer is the sum of its two triangular
curvature integrals. -/
theorem coordinateLambda_eq_triangular
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ} (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t) :
    coordinateLambda Q p z w =
      (∫ t in p..z, (t - p) * curvature Q2 t) / (z - p) +
      (∫ t in z..w, (w - t) * curvature Q2 t) / (w - z) := by
  rw [increasing_integral hpz.le
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hQ1 t ⟨ht.1, ht.2.trans hzw.le⟩),
    decreasing_integral hzw.le
      (fun t ht => hQ t ⟨hpz.le.trans ht.1, ht.2⟩)
      (fun t ht => hQ1 t ⟨hpz.le.trans ht.1, ht.2⟩)]
  unfold coordinateLambda chordSlope
  field_simp [sub_ne_zero.mpr hpz.ne, sub_ne_zero.mpr hzw.ne]
  ring

/-- The left endpoint derivative of `Lambda` is the negative coordinate
`delta`; thus `delta` is not a detached positive parameter. -/
theorem hasDerivAt_coordinateLambda_left
    {Q Q1 : ℝ → ℝ} {p z w : ℝ} (hpz : p < z)
    (hQ : HasDerivAt Q (Q1 p) p) :
    HasDerivAt (fun x => coordinateLambda Q x z w)
      (-coordinateDelta Q Q1 p z) p := by
  have hnum : HasDerivAt (fun x => Q z - Q x) (-Q1 p) p :=
    (hasDerivAt_const p (Q z)).sub hQ
  have hden : HasDerivAt (fun x : ℝ => z - x) (-1) p :=
    (hasDerivAt_id p).const_sub z
  have hquot := hnum.div hden (sub_ne_zero.mpr hpz.ne)
  have hmain : HasDerivAt
      (fun x : ℝ => (w - x) + (Q z - Q x) / (z - x) -
        (Q w - Q z) / (w - z))
      (-1 + ((-Q1 p) * (z - p) - (Q z - Q p) * (-1)) /
        (z - p) ^ 2 - 0) p :=
    ((hasDerivAt_id p).const_sub w).add hquot |>.sub_const
      ((Q w - Q z) / (w - z))
  convert hmain using 1
  · ext x; rfl
  · unfold coordinateDelta chordSlope
    field_simp [sub_ne_zero.mpr hpz.ne]
    ring

/-- PO-0024: the derivative-defined `delta` has the decreasing triangular
representation. -/
theorem coordinateDelta_eq_triangular
    {Q Q1 Q2 : ℝ → ℝ} {p z : ℝ} (hpz : p < z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p z, HasDerivAt Q1 (Q2 t) t) :
    coordinateDelta Q Q1 p z =
      (∫ t in p..z, (z - t) * curvature Q2 t) / (z - p) ^ 2 := by
  rw [decreasing_integral hpz.le hQ hQ1]
  unfold coordinateDelta chordSlope
  field_simp [sub_ne_zero.mpr hpz.ne]
  ring

theorem coordinateDelta_pos
    {Q Q1 Q2 : ℝ → ℝ} {p z : ℝ} (hpz : p < z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p z, HasDerivAt Q1 (Q2 t) t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p z))
    (hκpos : ∀ t ∈ Icc p z, 0 < curvature Q2 t) :
    0 < coordinateDelta Q Q1 p z := by
  have hcont : ContinuousOn (fun t => (z - t) * curvature Q2 t) (Icc p z) :=
    (continuous_const.sub continuous_id).continuousOn.mul hκcont
  have hraw : 0 < ∫ t in p..z, (z - t) * curvature Q2 t :=
    intervalIntegral.integral_pos hpz hcont
      (fun t ht => mul_nonneg (sub_nonneg.mpr ht.2) (hκpos t ht).le)
      ⟨(p + z) / 2, by constructor <;> linarith,
        mul_pos (by linarith)
          (hκpos ((p + z) / 2) (by constructor <;> linarith))⟩
  rw [coordinateDelta_eq_triangular hpz hQ hQ1]
  exact div_pos hraw (sq_pos_of_pos (sub_pos.mpr hpz))

theorem coordinateLambda_pos
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ} (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w))
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t) :
    0 < coordinateLambda Q p z w := by
  have hlcont : ContinuousOn (fun t => (t - p) * curvature Q2 t) (Icc p z) :=
    (continuous_id.sub continuous_const).continuousOn.mul
      (hκcont.mono fun _ ht => ⟨ht.1, ht.2.trans hzw.le⟩)
  have hrcont : ContinuousOn (fun t => (w - t) * curvature Q2 t) (Icc z w) :=
    (continuous_const.sub continuous_id).continuousOn.mul
      (hκcont.mono fun _ ht => ⟨hpz.le.trans ht.1, ht.2⟩)
  have hl : 0 < ∫ t in p..z, (t - p) * curvature Q2 t :=
    intervalIntegral.integral_pos hpz hlcont
      (fun t ht => mul_nonneg (sub_nonneg.mpr ht.1)
        (hκpos t ⟨ht.1, ht.2.trans hzw.le⟩).le)
      ⟨(p + z) / 2, by constructor <;> linarith,
        mul_pos (by linarith)
          (hκpos ((p + z) / 2) (by constructor <;> linarith))⟩
  have hr : 0 < ∫ t in z..w, (w - t) * curvature Q2 t :=
    intervalIntegral.integral_pos hzw hrcont
      (fun t ht => mul_nonneg (sub_nonneg.mpr ht.2)
        (hκpos t ⟨hpz.le.trans ht.1, ht.2⟩).le)
      ⟨(z + w) / 2, by constructor <;> linarith,
        mul_pos (by linarith)
          (hκpos ((z + w) / 2) (by constructor <;> linarith))⟩
  rw [coordinateLambda_eq_triangular hpz hzw hQ hQ1]
  exact add_pos (div_pos hl (sub_pos.mpr hpz)) (div_pos hr (sub_pos.mpr hzw))

private theorem muDensity_continuousOn
    {Q Q1 Q2 : ℝ → ℝ} {p z : ℝ} (hpz : p < z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p z, HasDerivAt Q1 (Q2 t) t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p z))
    (hκpos : ∀ t ∈ Icc p z, 0 < curvature Q2 t) :
    ContinuousOn (leftMuDensity (curvature Q2) z (z - p)
      (coordinateDelta Q Q1 p z)) (Icc p z) := by
  unfold leftMuDensity
  apply ((continuous_const.sub continuous_id).continuousOn.mul hκcont).div
    continuousOn_const
  intro _ _
  exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hpz.ne))
    (coordinateDelta_pos hpz hQ hQ1 hκcont hκpos).ne'

private theorem leftNuDensity_continuousOn
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ} (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w))
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t) :
    ContinuousOn (leftNuDensity (curvature Q2) p (z - p)
      (coordinateLambda Q p z w)) (Icc p z) := by
  unfold leftNuDensity
  apply ((continuous_id.sub continuous_const).continuousOn.mul
    (hκcont.mono fun _ ht => ⟨ht.1, ht.2.trans hzw.le⟩)).div continuousOn_const
  intro _ _
  exact mul_ne_zero (sub_ne_zero.mpr hpz.ne)
    (coordinateLambda_pos hpz hzw hQ hQ1 hκcont hκpos).ne'

private theorem rightNuDensity_continuousOn
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ} (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w))
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t) :
    ContinuousOn (rightNuDensity (curvature Q2) w (w - z)
      (coordinateLambda Q p z w)) (Icc z w) := by
  unfold rightNuDensity
  apply ((continuous_const.sub continuous_id).continuousOn.mul
    (hκcont.mono fun _ ht => ⟨hpz.le.trans ht.1, ht.2⟩)).div continuousOn_const
  intro _ _
  exact mul_ne_zero (sub_ne_zero.mpr hzw.ne)
    (coordinateLambda_pos hpz hzw hQ hQ1 hκcont hκpos).ne'

/-- PO-0030: the derivative-defined triangular law `mu` is a probability
measure. -/
theorem coordinate_mu_isProbabilityMeasure
    {Q Q1 Q2 : ℝ → ℝ} {p z : ℝ} (hpz : p < z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p z, HasDerivAt Q1 (Q2 t) t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p z))
    (hκpos : ∀ t ∈ Icc p z, 0 < curvature Q2 t) :
    IsProbabilityMeasure
      (muMeasure (curvature Q2) p z (z - p) (coordinateDelta Q Q1 p z)) := by
  have hδ := coordinateDelta_pos hpz hQ hQ1 hκcont hκpos
  have hmass : (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p)
      (coordinateDelta Q Q1 p z) t) = 1 := by
    apply leftMuDensity_intervalIntegral_eq_one (sub_pos.mpr hpz) hδ
    rw [coordinateDelta_eq_triangular hpz hQ hQ1]
    field_simp [sub_ne_zero.mpr hpz.ne]
  apply mu_isProbabilityMeasure
  exact muMeasure_univ_eq_one hpz hκpos (sub_pos.mpr hpz) hδ
    ((muDensity_continuousOn hpz hQ hQ1 hκcont hκpos).intervalIntegrable_of_Icc hpz.le)
    hmass

/-- PO-0031: the two-piece triangular law `nu` with its coordinate-derived
normalizer is a probability measure. -/
theorem coordinate_nu_isProbabilityMeasure
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ} (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w))
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t) :
    IsProbabilityMeasure
      (nuMeasure (curvature Q2) p z w (z - p) (w - z)
        (coordinateLambda Q p z w)) := by
  have hΛ := coordinateLambda_pos hpz hzw hQ hQ1 hκcont hκpos
  have hmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p)
        (coordinateLambda Q p z w) t) +
      (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z)
        (coordinateLambda Q p z w) t) = 1 := by
    apply nuDensities_intervalIntegral_eq_one (sub_pos.mpr hpz)
      (sub_pos.mpr hzw) hΛ
    exact (coordinateLambda_eq_triangular hpz hzw hQ hQ1).symm
  apply nu_isProbabilityMeasure
  exact nuMeasure_univ_eq_one hpz hzw
    (fun t ht => hκpos t ⟨ht.1, ht.2.trans hzw.le⟩)
    (fun t ht => hκpos t ⟨hpz.le.trans ht.1, ht.2⟩)
    (sub_pos.mpr hpz) (sub_pos.mpr hzw) hΛ
    ((leftNuDensity_continuousOn hpz hzw hQ hQ1 hκcont hκpos)
      |>.intervalIntegrable_of_Icc hpz.le)
    ((rightNuDensity_continuousOn hpz hzw hQ hQ1 hκcont hκpos)
      |>.intervalIntegrable_of_Icc hzw.le) hmass

end PF4.Curvature
