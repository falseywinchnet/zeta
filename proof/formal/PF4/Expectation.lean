/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option linter.style.header false

/-!
# Expectation/CDF integration by parts

This file proves PO-0039.  Expectations are Bochner integrals against the
concrete measures from `PF4.Measures`; the CDF transport integral is obtained
by integration by parts with every endpoint term retained.
-/

namespace PF4.Expectation

open Filter MeasureTheory Set
open scoped Interval ENNReal
open PF4.Densities PF4.Normalization PF4.Measures PF4.CDF

/-- Expectation of a real function against a measure. -/
noncomputable def measureExpectation (μ : Measure ℝ) (A : ℝ → ℝ) : ℝ :=
  ∫ t, A t ∂μ

/-- The accumulated integral of a density from a fixed left endpoint. -/
noncomputable def cumulative (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in a..t, f x

theorem continuous_cumulative {a : ℝ} {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (cumulative a f) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hf.integral_hasStrictDerivAt a t).hasDerivAt.continuousAt

/-- Integration against a restricted-density measure is the corresponding
ordinary interval integral. -/
theorem expectation_restrictedDensityMeasure_eq
    {a b : ℝ} {f A : ℝ → ℝ}
    (hab : a ≤ b) (hf : Continuous f)
    (hnonneg : ∀ t ∈ Ioc a b, 0 ≤ f t) :
    measureExpectation (restrictedDensityMeasure a b f) A =
      ∫ t in a..b, f t * A t := by
  rw [measureExpectation, restrictedDensityMeasure,
    integral_withDensity_eq_integral_toReal_smul hf.measurable.ennreal_ofReal]
  · rw [intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [ENNReal.toReal_ofReal (hnonneg t ht)]
    simp
  · exact Eventually.of_forall fun _ => by simp

/-- A continuous test function is integrable against a compactly supported
continuous restricted density. -/
theorem integrable_restrictedDensityMeasure
    {a b : ℝ} {f A : ℝ → ℝ}
    (hab : a ≤ b) (hf : Continuous f) (hA : Continuous A)
    (hnonneg : ∀ t ∈ Ioc a b, 0 ≤ f t) :
    Integrable A (restrictedDensityMeasure a b f) := by
  rw [restrictedDensityMeasure,
    integrable_withDensity_iff_integrable_smul'
      hf.measurable.ennreal_ofReal (Eventually.of_forall fun _ => by simp)]
  have hprod : IntegrableOn (fun t => f t * A t) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1
      ((hf.mul hA).intervalIntegrable a b)
  apply hprod.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [ENNReal.toReal_ofReal (hnonneg t ht)]
  simp

/-- Integration by parts for a density accumulated from zero at `a`. -/
theorem intervalIntegral_mul_density
    {a b : ℝ} {f A D : ℝ → ℝ}
    (hf : Continuous f) (hA : ∀ t, HasDerivAt A (D t) t)
    (hD : IntervalIntegrable D volume a b) :
    (∫ t in a..b, A t * f t) =
      A b * (∫ t in a..b, f t) -
        ∫ t in a..b, D t * cumulative a f t := by
  have hF : ∀ t, HasDerivAt (cumulative a f) (f t) t := fun t => by
    exact (hf.integral_hasStrictDerivAt a t).hasDerivAt
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => hA t) (fun t _ => hF t) hD (hf.intervalIntegrable a b)
  simpa [cumulative] using h

/-- Integration by parts when the accumulated density begins with mass `c`
at the left endpoint. -/
theorem intervalIntegral_mul_density_with_initial
    {a b c : ℝ} {f A D : ℝ → ℝ}
    (hf : Continuous f) (hA : ∀ t, HasDerivAt A (D t) t)
    (hD : IntervalIntegrable D volume a b) :
    (∫ t in a..b, A t * f t) =
      A b * (c + ∫ t in a..b, f t) - A a * c -
        ∫ t in a..b, D t * (c + cumulative a f t) := by
  have hF : ∀ t,
      HasDerivAt (fun u => c + cumulative a f u) (f t) t := fun t => by
    simpa only [cumulative] using
      (hf.integral_hasStrictDerivAt a t).hasDerivAt.const_add c
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => hA t) (fun t _ => hF t) hD (hf.intervalIntegrable a b)
  simpa [cumulative] using h

theorem muExpectation_eq_interval
    {κ A : ℝ → ℝ} {p z L δ : ℝ}
    (hpz : p < z) (hκ : ∀ t ∈ Icc p z, 0 < κ t)
    (hκcont : Continuous κ) (hL : 0 < L) (hδ : 0 < δ) :
    measureExpectation (muMeasure κ p z L δ) A =
      ∫ t in p..z, A t * leftMuDensity κ z L δ t := by
  have hf : Continuous (leftMuDensity κ z L δ) := by
    unfold leftMuDensity
    fun_prop
  rw [muMeasure, expectation_restrictedDensityMeasure_eq hpz.le hf]
  · apply intervalIntegral.integral_congr
    intro t _
    ring
  · intro t ht
    by_cases htz : t = z
    · simp [leftMuDensity, htz]
    · exact (leftMuDensity_pos (lt_of_le_of_ne ht.2 htz)
        (hκ t ⟨le_of_lt ht.1, ht.2⟩) hL hδ).le

theorem nuExpectation_eq_intervals
    {κ A : ℝ → ℝ} {p z w L R Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hκ : ∀ t ∈ Icc p w, 0 < κ t) (hκcont : Continuous κ)
    (hAcont : Continuous A) (hL : 0 < L) (hR : 0 < R) (hΛ : 0 < Λ) :
    measureExpectation (nuMeasure κ p z w L R Λ) A =
      (∫ t in p..z, A t * leftNuDensity κ p L Λ t) +
        ∫ t in z..w, A t * rightNuDensity κ w R Λ t := by
  have hleftcont : Continuous (leftNuDensity κ p L Λ) := by
    unfold leftNuDensity
    fun_prop
  have hrightcont : Continuous (rightNuDensity κ w R Λ) := by
    unfold rightNuDensity
    fun_prop
  have hleft0 : ∀ t ∈ Ioc p z, 0 ≤ leftNuDensity κ p L Λ t := by
    intro t ht
    exact (leftNuDensity_pos ht.1
      (hκ t ⟨le_of_lt ht.1, ht.2.trans hzw.le⟩) hL hΛ).le
  have hright0 : ∀ t ∈ Ioc z w, 0 ≤ rightNuDensity κ w R Λ t := by
    intro t ht
    by_cases htw : t = w
    · simp [rightNuDensity, htw]
    · exact (rightNuDensity_pos (lt_of_le_of_ne ht.2 htw)
        (hκ t ⟨hpz.le.trans (le_of_lt ht.1), ht.2⟩) hR hΛ).le
  have hleftInt : Integrable A
      (restrictedDensityMeasure p z (leftNuDensity κ p L Λ)) :=
    integrable_restrictedDensityMeasure hpz.le hleftcont hAcont hleft0
  have hrightInt : Integrable A
      (restrictedDensityMeasure z w (rightNuDensity κ w R Λ)) :=
    integrable_restrictedDensityMeasure hzw.le hrightcont hAcont hright0
  have hleftEq := expectation_restrictedDensityMeasure_eq
    hpz.le hleftcont hleft0 (A := A)
  have hrightEq := expectation_restrictedDensityMeasure_eq
    hzw.le hrightcont hright0 (A := A)
  rw [measureExpectation, nuMeasure, integral_add_measure hleftInt hrightInt]
  rw [measureExpectation] at hleftEq hrightEq
  rw [hleftEq, hrightEq]
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro t _ <;> ring

/-- PO-0039: the difference of the two concrete expectations is exactly the
CDF-gap transport integral.  The proof splits at `z`; the two `ν` boundary
terms there cancel, while the constant right CDF of `μ` carries its `A z`
boundary to the common `A w` endpoint. -/
theorem expectation_difference_eq_cdfGap_integral
    {κ A D : ℝ → ℝ} {p z w L R δ Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hκ : ∀ t ∈ Icc p w, 0 < κ t) (hκcont : Continuous κ)
    (hAcont : Continuous A) (hA : ∀ t, HasDerivAt A (D t) t)
    (hD : IntervalIntegrable D volume p w)
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hμmass : (∫ t in p..z, leftMuDensity κ z L δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity κ p L Λ t) +
        (∫ t in z..w, rightNuDensity κ w R Λ t) = 1) :
    measureExpectation (nuMeasure κ p z w L R Λ) A -
        measureExpectation (muMeasure κ p z L δ) A =
      ∫ t in p..w, cdfGap κ p z w L R δ Λ t * D t := by
  let fμ : ℝ → ℝ := leftMuDensity κ z L δ
  let fνL : ℝ → ℝ := leftNuDensity κ p L Λ
  let fνR : ℝ → ℝ := rightNuDensity κ w R Λ
  let Fμ : ℝ → ℝ := cumulative p fμ
  let FνL : ℝ → ℝ := cumulative p fνL
  let mνL : ℝ := ∫ t in p..z, fνL t
  let FνR : ℝ → ℝ := fun t => mνL + cumulative z fνR t
  have hpw : p < w := hpz.trans hzw
  have hκleft : ∀ t ∈ Icc p z, 0 < κ t := fun t ht =>
    hκ t ⟨ht.1, ht.2.trans hzw.le⟩
  have hfμ : Continuous fμ := by
    change Continuous (fun t : ℝ => (z - t) * κ t / (L ^ 2 * δ))
    fun_prop
  have hfνL : Continuous fνL := by
    change Continuous (fun t : ℝ => (t - p) * κ t / (L * Λ))
    fun_prop
  have hfνR : Continuous fνR := by
    change Continuous (fun t : ℝ => (w - t) * κ t / (R * Λ))
    fun_prop
  have hDleft : IntervalIntegrable D volume p z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpz.le).2 <|
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpw.le).1 hD).mono_set
        fun t ht => ⟨ht.1, ht.2.trans hzw.le⟩
  have hDright : IntervalIntegrable D volume z w :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hzw.le).2 <|
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpw.le).1 hD).mono_set
        fun t ht => ⟨hpz.trans ht.1, ht.2⟩
  have hμint : IntervalIntegrable fμ volume p z := hfμ.intervalIntegrable p z
  have hνLint : IntervalIntegrable fνL volume p z := hfνL.intervalIntegrable p z
  have hνRint : IntervalIntegrable fνR volume z w := hfνR.intervalIntegrable z w
  have hμmeasure : muMeasure κ p z L δ Set.univ = 1 :=
    muMeasure_univ_eq_one hpz hκleft hL hδ hμint (by simpa [fμ] using hμmass)
  have hμExpectation := muExpectation_eq_interval
    (A := A) hpz hκleft hκcont hL hδ
  have hνExpectation := nuExpectation_eq_intervals
    (A := A) hpz hzw hκ hκcont hAcont hL hR hΛ
  have hμparts := intervalIntegral_mul_density hfμ hA hDleft
  have hνLparts := intervalIntegral_mul_density hfνL hA hDleft
  have hνRparts := intervalIntegral_mul_density_with_initial
    (c := mνL) hfνR hA hDright
  have hμvalue : measureExpectation (muMeasure κ p z L δ) A =
      A z - ∫ t in p..z, D t * Fμ t := by
    rw [hμExpectation]
    change (∫ t in p..z, A t * fμ t) = _
    rw [hμparts]
    change A z * (∫ t in p..z, fμ t) - (∫ t in p..z, D t * Fμ t) = _
    rw [show (∫ t in p..z, fμ t) = 1 by simpa [fμ] using hμmass]
    ring
  have hνvalue : measureExpectation (nuMeasure κ p z w L R Λ) A =
      A w - (∫ t in p..z, D t * FνL t) -
        ∫ t in z..w, D t * FνR t := by
    rw [hνExpectation]
    change (∫ t in p..z, A t * fνL t) +
      (∫ t in z..w, A t * fνR t) = _
    rw [hνLparts, hνRparts]
    change
      (A z * (∫ t in p..z, fνL t) -
          ∫ t in p..z, D t * FνL t) +
        (A w * (mνL + ∫ t in z..w, fνR t) - A z * mνL -
          ∫ t in z..w, D t * FνR t) = _
    have hmass : mνL + ∫ t in z..w, fνR t = 1 := by
      simpa [mνL, fνL, fνR] using hνmass
    rw [hmass]
    simp only [mνL]
    ring
  have hFTC : (∫ t in z..w, D t) = A w - A z :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hA t) hDright
  have hμextended : measureExpectation (muMeasure κ p z L δ) A =
      A w - (∫ t in p..z, D t * Fμ t) - ∫ t in z..w, D t := by
    rw [hμvalue, hFTC]
    ring
  have hFμcont : Continuous Fμ := continuous_cumulative hfμ
  have hFνLcont : Continuous FνL := continuous_cumulative hfνL
  have hFνRcont : Continuous FνR := by
    dsimp [FνR]
    exact (continuous_const.add (continuous_cumulative hfνR))
  have hDFμ : IntervalIntegrable (fun t => D t * Fμ t) volume p z :=
    hDleft.mul_continuousOn hFμcont.continuousOn
  have hDFνL : IntervalIntegrable (fun t => D t * FνL t) volume p z :=
    hDleft.mul_continuousOn hFνLcont.continuousOn
  have hDFνR : IntervalIntegrable (fun t => D t * FνR t) volume z w :=
    hDright.mul_continuousOn hFνRcont.continuousOn
  have hleftAlgebra :
      (∫ t in p..z, (Fμ t - FνL t) * D t) =
        (∫ t in p..z, D t * Fμ t) - ∫ t in p..z, D t * FνL t := by
    rw [← intervalIntegral.integral_sub hDFμ hDFνL]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hrightAlgebra :
      (∫ t in z..w, (1 - FνR t) * D t) =
        (∫ t in z..w, D t) - ∫ t in z..w, D t * FνR t := by
    rw [← intervalIntegral.integral_sub hDright hDFνR]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hgapLeft : ∀ t ∈ Icc p z,
      cdfGap κ p z w L R δ Λ t = Fμ t - FνL t := by
    intro t ht
    have hμt : IntervalIntegrable (leftMuDensity κ z L δ) volume p t :=
      hfμ.intervalIntegrable p t
    have hνt : IntervalIntegrable (leftNuDensity κ p L Λ) volume p t :=
      hfνL.intervalIntegrable p t
    rw [cdfGap,
      muCDF_eq_leftIntegral ht.1 ht.2 hκleft hL hδ hμt,
      nuCDF_eq_leftIntegral ht.1 ht.2 hκleft hL hΛ hνt]
    rfl
  have hgapRight : ∀ t ∈ Icc z w,
      cdfGap κ p z w L R δ Λ t = 1 - FνR t := by
    intro t ht
    have hνRt : IntervalIntegrable (rightNuDensity κ w R Λ) volume z t :=
      hfνR.intervalIntegrable z t
    rw [cdfGap, muCDF_eq_one ht.1 hμmeasure,
      nuCDF_eq_leftMass_add_rightIntegral hpz ht.1 ht.2 hκ
        hL hR hΛ hνLint hνRt]
    rfl
  have hgapDleft : IntervalIntegrable
      (fun t => cdfGap κ p z w L R δ Λ t * D t) volume p z := by
    apply (hDleft.continuousOn_mul (hFμcont.sub hFνLcont).continuousOn).congr
    intro t ht
    rw [uIoc_of_le hpz.le] at ht
    change (Fμ t - FνL t) * D t = cdfGap κ p z w L R δ Λ t * D t
    rw [hgapLeft t ⟨le_of_lt ht.1, ht.2⟩]
  have hgapDright : IntervalIntegrable
      (fun t => cdfGap κ p z w L R δ Λ t * D t) volume z w := by
    have hOneSub : Continuous (fun t : ℝ => 1 - FνR t) :=
      continuous_const.sub hFνRcont
    apply (hDright.continuousOn_mul hOneSub.continuousOn).congr
    intro t ht
    rw [uIoc_of_le hzw.le] at ht
    change (1 - FνR t) * D t = cdfGap κ p z w L R δ Λ t * D t
    rw [hgapRight t ⟨le_of_lt ht.1, ht.2⟩]
  have hleftActual :
      (∫ t in p..z, cdfGap κ p z w L R δ Λ t * D t) =
        ∫ t in p..z, (Fμ t - FνL t) * D t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hpz.le] at ht
    change cdfGap κ p z w L R δ Λ t * D t = (Fμ t - FνL t) * D t
    rw [hgapLeft t ht]
  have hrightActual :
      (∫ t in z..w, cdfGap κ p z w L R δ Λ t * D t) =
        ∫ t in z..w, (1 - FνR t) * D t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hzw.le] at ht
    change cdfGap κ p z w L R δ Λ t * D t = (1 - FνR t) * D t
    rw [hgapRight t ht]
  rw [← intervalIntegral.integral_add_adjacent_intervals hgapDleft hgapDright]
  rw [hνvalue, hμextended, hleftActual, hleftAlgebra,
    hrightActual, hrightAlgebra]
  ring

end PF4.Expectation
