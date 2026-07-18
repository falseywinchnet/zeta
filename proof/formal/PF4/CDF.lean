/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.Measures

set_option linter.style.header false

/-!
# CDF gap and its strict support

The CDFs below are taken from the concrete measures in `PF4.Measures`.  In
particular, strict right mass is proved from a positive density on a nonempty
interval and is never introduced as an unconstrained positive variable.
-/

namespace PF4.CDF

open MeasureTheory ProbabilityTheory Set
open scoped Interval ENNReal
open PF4.Crossing PF4.Densities PF4.Normalization PF4.Measures

noncomputable def muCDF
    (κ : ℝ → ℝ) (p z L δ t : ℝ) : ℝ :=
  (muMeasure κ p z L δ).real (Iic t)

noncomputable def nuCDF
    (κ : ℝ → ℝ) (p z w L R Λ t : ℝ) : ℝ :=
  (nuMeasure κ p z w L R Λ).real (Iic t)

noncomputable def cdfGap
    (κ : ℝ → ℝ) (p z w L R δ Λ t : ℝ) : ℝ :=
  muCDF κ p z L δ t - nuCDF κ p z w L R Λ t

theorem muCDF_eq_probabilityTheory_cdf
    {κ : ℝ → ℝ} {p z L δ : ℝ}
    (hmass : muMeasure κ p z L δ Set.univ = 1) (t : ℝ) :
    muCDF κ p z L δ t = ProbabilityTheory.cdf (muMeasure κ p z L δ) t := by
  letI : IsProbabilityMeasure (muMeasure κ p z L δ) :=
    mu_isProbabilityMeasure hmass
  rw [ProbabilityTheory.cdf_eq_real]
  rfl

theorem nuCDF_eq_probabilityTheory_cdf
    {κ : ℝ → ℝ} {p z w L R Λ : ℝ}
    (hmass : nuMeasure κ p z w L R Λ Set.univ = 1) (t : ℝ) :
    nuCDF κ p z w L R Λ t =
      ProbabilityTheory.cdf (nuMeasure κ p z w L R Λ) t := by
  letI : IsProbabilityMeasure (nuMeasure κ p z w L R Λ) :=
    nu_isProbabilityMeasure hmass
  rw [ProbabilityTheory.cdf_eq_real]
  rfl

theorem muCDF_eq_leftIntegral
    {κ : ℝ → ℝ} {p z L δ y : ℝ}
    (hpy : p ≤ y) (hyz : y ≤ z)
    (hκ : ∀ t ∈ Icc p z, 0 < κ t)
    (hL : 0 < L) (hδ : 0 < δ)
    (hint : IntervalIntegrable (leftMuDensity κ z L δ) volume p y) :
    muCDF κ p z L δ y = ∫ t in p..y, leftMuDensity κ z L δ t := by
  rw [muCDF, muMeasure]
  apply restrictedDensityMeasure_real_Iic hpy hyz hint
  intro t ht
  by_cases htz : t = z
  · simp [leftMuDensity, htz]
  · exact (leftMuDensity_pos (lt_of_le_of_ne (ht.2.trans hyz) htz)
      (hκ t ⟨le_of_lt ht.1, ht.2.trans hyz⟩) hL hδ).le

theorem nuCDF_eq_leftIntegral
    {κ : ℝ → ℝ} {p z w L R Λ y : ℝ}
    (hpy : p ≤ y) (hyz : y ≤ z)
    (hκ : ∀ t ∈ Icc p z, 0 < κ t)
    (hL : 0 < L) (hΛ : 0 < Λ)
    (hint : IntervalIntegrable (leftNuDensity κ p L Λ) volume p y) :
    nuCDF κ p z w L R Λ y = ∫ t in p..y, leftNuDensity κ p L Λ t := by
  rw [nuCDF, nuMeasure, Measure.real, Measure.add_apply,
    restrictedDensityMeasure_Iic hpy hyz hint,
    restrictedDensityMeasure_Iic_eq_zero hyz]
  · have hnonneg :
        0 ≤ ∫ t in p..y, leftNuDensity κ p L Λ t := by
      rw [intervalIntegral.integral_of_le hpy]
      exact integral_nonneg_of_ae <| (ae_restrict_mem measurableSet_Ioc).mono fun t ht =>
        (leftNuDensity_pos ht.1
          (hκ t ⟨le_of_lt ht.1, ht.2.trans hyz⟩) hL hΛ).le
    simp [ENNReal.toReal_ofReal hnonneg]
  · intro t ht
    exact (leftNuDensity_pos ht.1
      (hκ t ⟨le_of_lt ht.1, ht.2.trans hyz⟩) hL hΛ).le

/-- To the right of `z`, `μ` has accumulated its full probability mass. -/
theorem muCDF_eq_one
    {κ : ℝ → ℝ} {p z L δ y : ℝ} (hzy : z ≤ y)
    (hmass : muMeasure κ p z L δ Set.univ = 1) :
    muCDF κ p z L δ y = 1 := by
  letI : IsProbabilityMeasure (muMeasure κ p z L δ) :=
    mu_isProbabilityMeasure hmass
  have hright : muMeasure κ p z L δ (Ioi y) = 0 := by
    rw [muMeasure]
    exact restrictedDensityMeasure_Ioi_eq_zero hzy
  have hprob := probReal_add_probReal_compl
    (μ := muMeasure κ p z L δ) (s := Iic y) measurableSet_Iic
  simp only [compl_Iic] at hprob
  have hrightReal : (muMeasure κ p z L δ).real (Ioi y) = 0 := by
    rw [Measure.real, hright]
    simp
  rw [hrightReal, add_zero] at hprob
  exact hprob

/-- On `[z,w]`, the CDF of `ν` is its complete left mass plus the accumulated
right density. -/
theorem nuCDF_eq_leftMass_add_rightIntegral
    {κ : ℝ → ℝ} {p z w L R Λ y : ℝ}
    (hpz : p < z) (hzy : z ≤ y) (hyw : y ≤ w)
    (hκ : ∀ t ∈ Icc p w, 0 < κ t)
    (hL : 0 < L) (hR : 0 < R) (hΛ : 0 < Λ)
    (hleft : IntervalIntegrable (leftNuDensity κ p L Λ) volume p z)
    (hright : IntervalIntegrable (rightNuDensity κ w R Λ) volume z y) :
    nuCDF κ p z w L R Λ y =
      (∫ t in p..z, leftNuDensity κ p L Λ t) +
        ∫ t in z..y, rightNuDensity κ w R Λ t := by
  have hleft0 : 0 ≤ ∫ t in p..z, leftNuDensity κ p L Λ t := by
    apply intervalIntegral.integral_nonneg hpz.le
    intro t ht
    by_cases htp : t = p
    · simp [leftNuDensity, htp]
    · exact (leftNuDensity_pos (lt_of_le_of_ne ht.1 (Ne.symm htp))
        (hκ t ⟨ht.1, ht.2.trans (hzy.trans hyw)⟩) hL hΛ).le
  have hright0 : 0 ≤ ∫ t in z..y, rightNuDensity κ w R Λ t := by
    apply intervalIntegral.integral_nonneg hzy
    intro t ht
    by_cases htw : t = w
    · simp [rightNuDensity, htw]
    · exact (rightNuDensity_pos (lt_of_le_of_ne (ht.2.trans hyw) htw)
        (hκ t ⟨hpz.le.trans ht.1, ht.2.trans hyw⟩) hR hΛ).le
  rw [nuCDF, nuMeasure, Measure.real, Measure.add_apply,
    restrictedDensityMeasure_Iic_of_right hpz.le hzy hleft,
    restrictedDensityMeasure_Iic hzy hyw hright]
  · rw [← ENNReal.ofReal_add hleft0 hright0,
      ENNReal.toReal_ofReal (add_nonneg hleft0 hright0)]
  · intro t ht
    by_cases htw : t = w
    · simp [rightNuDensity, htw]
    · exact (rightNuDensity_pos (lt_of_le_of_ne (ht.2.trans hyw) htw)
        (hκ t ⟨hpz.le.trans (le_of_lt ht.1), ht.2.trans hyw⟩) hR hΛ).le
  · intro t ht
    exact (leftNuDensity_pos ht.1
      (hκ t ⟨le_of_lt ht.1, ht.2.trans (hzy.trans hyw)⟩) hL hΛ).le

/-- Before the unique density crossing, the actual CDF gap is strictly
positive because it is the integral of the strictly positive density
difference over a nonempty interval. -/
theorem cdfGap_pos_before_crossing
    {κ : ℝ → ℝ} {p z w L R δ Λ y : ℝ}
    (hpy : p < y) (hyc : y < crossingPoint p z L δ Λ)
    (hpz : p < z) (hκ : ∀ t ∈ Icc p z, 0 < κ t)
    (hκcont : Continuous κ)
    (hL : 0 < L) (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hμint : IntervalIntegrable (leftMuDensity κ z L δ) volume p y)
    (hνint : IntervalIntegrable (leftNuDensity κ p L Λ) volume p y) :
    0 < cdfGap κ p z w L R δ Λ y := by
  have hcz : crossingPoint p z L δ Λ < z :=
    (crossingPoint_mem hpz hΛ (mul_pos hL hδ)).2
  have hyz : y ≤ z := (hyc.trans hcz).le
  rw [cdfGap, muCDF_eq_leftIntegral hpy.le hyz hκ hL hδ hμint,
    nuCDF_eq_leftIntegral hpy.le hyz hκ hL hΛ hνint,
    ← intervalIntegral.integral_sub hμint hνint]
  apply intervalIntegral.integral_pos hpy
  · apply Continuous.continuousOn
    unfold leftMuDensity leftNuDensity
    fun_prop
  · intro t ht
    exact (leftDensity_difference_pos_iff ht.1
      (lt_of_le_of_lt ht.2 (hyc.trans hcz))
      (hκ t ⟨le_of_lt ht.1, ht.2.trans hyz⟩) hΛ hL hδ).2
        (lt_of_le_of_lt ht.2 hyc) |>.le
  · refine ⟨(p + y) / 2, by constructor <;> linarith, ?_⟩
    exact (leftDensity_difference_pos_iff (by linarith) (by linarith)
      (hκ ((p + y) / 2) (by constructor <;> linarith)) hΛ hL hδ).2 (by linarith)

/-- From the crossing through `z`, the gap is a positive right-tail mass plus
a nonnegative reverse-density integral.  This is the formal replacement for
the former vacuous `Wz > 0` assertion. -/
theorem cdfGap_pos_from_crossing_to_z
    {κ : ℝ → ℝ} {p z w L R δ Λ y : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hcy : crossingPoint p z L δ Λ ≤ y) (hyz : y < z)
    (hκ : ∀ t ∈ Icc p w, 0 < κ t) (hκcont : Continuous κ)
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hμfull : IntervalIntegrable (leftMuDensity κ z L δ) volume p z)
    (hνfull : IntervalIntegrable (leftNuDensity κ p L Λ) volume p z)
    (hμprefix : IntervalIntegrable (leftMuDensity κ z L δ) volume p y)
    (hνprefix : IntervalIntegrable (leftNuDensity κ p L Λ) volume p y)
    (hμmass : (∫ t in p..z, leftMuDensity κ z L δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity κ p L Λ t) +
        (∫ t in z..w, rightNuDensity κ w R Λ t) = 1) :
    0 < cdfGap κ p z w L R δ Λ y := by
  have hcp := crossingPoint_mem hpz hΛ (mul_pos hL hδ)
  have hpy : p < y := hcp.1.trans_le hcy
  have hκleft : ∀ t ∈ Icc p z, 0 < κ t := fun t ht =>
    hκ t ⟨ht.1, ht.2.trans hzw.le⟩
  rw [cdfGap,
    muCDF_eq_leftIntegral hpy.le hyz.le hκleft hL hδ hμprefix,
    nuCDF_eq_leftIntegral hpy.le hyz.le hκleft hL hΛ hνprefix]
  have hμsplit := intervalIntegral.integral_interval_sub_left hμfull hμprefix
  have hνsplit := intervalIntegral.integral_interval_sub_left hνfull hνprefix
  have hμsuffix : IntervalIntegrable (leftMuDensity κ z L δ) volume y z :=
    hμprefix.symm.trans hμfull
  have hνsuffix : IntervalIntegrable (leftNuDensity κ p L Λ) volume y z :=
    hνprefix.symm.trans hνfull
  have htailpos : 0 < ∫ t in z..w, rightNuDensity κ w R Λ t := by
    apply intervalIntegral.integral_pos hzw
    · apply Continuous.continuousOn
      unfold rightNuDensity
      fun_prop
    · intro t ht
      by_cases htw : t = w
      · simp [rightNuDensity, htw]
      · exact (rightNuDensity_pos (lt_of_le_of_ne ht.2 htw)
          (hκ t ⟨hpz.le.trans (le_of_lt ht.1), ht.2⟩) hR hΛ).le
    · refine ⟨(z + w) / 2, by constructor <;> linarith, ?_⟩
      exact rightNuDensity_pos (by linarith)
        (hκ ((z + w) / 2) (by constructor <;> linarith)) hR hΛ
  have hreverse :
      0 ≤ ∫ t in y..z,
        (leftNuDensity κ p L Λ t - leftMuDensity κ z L δ t) := by
    apply intervalIntegral.integral_nonneg hyz.le
    intro t ht
    by_cases htz : t = z
    · subst t
      simp only [leftMuDensity, sub_self, zero_mul, zero_div, sub_zero]
      exact (leftNuDensity_pos hpz (hκ z ⟨hpz.le, hzw.le⟩) hL hΛ).le
    by_cases htc : t = crossingPoint p z L δ Λ
    · subst t
      have heq := (leftDensity_eq_iff_crossingPoint hcp.1 hcp.2
          (hκ (crossingPoint p z L δ Λ)
            ⟨hcp.1.le, hcp.2.le.trans hzw.le⟩) hΛ hL hδ).2 rfl
      linarith
    · have hct : crossingPoint p z L δ Λ < t :=
        lt_of_le_of_ne (hcy.trans ht.1) (Ne.symm htc)
      have hneg := (leftDensity_difference_neg_iff
        (hcp.1.trans_le (hcy.trans ht.1))
        (lt_of_le_of_ne ht.2 htz)
        (hκ t ⟨(hcp.1.trans_le (hcy.trans ht.1)).le, ht.2.trans hzw.le⟩)
        hΛ hL hδ).2 hct
      linarith
  rw [intervalIntegral.integral_sub hνsuffix hμsuffix] at hreverse
  linarith

/-- On the right interval the CDF gap is strict because `μ` has already
accumulated all its mass while `ν` has a concrete positive tail. -/
theorem cdfGap_pos_right
    {κ : ℝ → ℝ} {p z w L R δ Λ y : ℝ}
    (hzy : z ≤ y) (hyw : y < w)
    (hκ : ∀ t ∈ Icc y w, 0 < κ t)
    (hκcont : Continuous κ)
    (hR : 0 < R) (hΛ : 0 < Λ)
    (hμmass : muMeasure κ p z L δ Set.univ = 1)
    (hνmass : nuMeasure κ p z w L R Λ Set.univ = 1) :
    0 < cdfGap κ p z w L R δ Λ y := by
  letI : IsProbabilityMeasure (muMeasure κ p z L δ) :=
    mu_isProbabilityMeasure hμmass
  letI : IsProbabilityMeasure (nuMeasure κ p z w L R Λ) :=
    nu_isProbabilityMeasure hνmass
  have hμright : muMeasure κ p z L δ (Ioi y) = 0 := by
    rw [muMeasure]
    exact restrictedDensityMeasure_Ioi_eq_zero hzy
  have hμcdf : muCDF κ p z L δ y = 1 := by
    have hprob := probReal_add_probReal_compl
      (μ := muMeasure κ p z L δ) (s := Iic y) measurableSet_Iic
    simp only [compl_Iic] at hprob
    simpa [muCDF, Measure.real, hμright] using hprob
  have hrightcont : ContinuousOn (rightNuDensity κ w R Λ) (Icc y w) := by
    apply Continuous.continuousOn
    unfold rightNuDensity
    fun_prop
  have hstrictTail :
      0 < nuMeasure κ p z w L R Λ (Ioc y w) :=
    nuMeasure_Ioc_pos hzy hyw hκ hR hΛ hrightcont
  have htail : 0 < nuMeasure κ p z w L R Λ (Ioi y) :=
    lt_of_lt_of_le hstrictTail <| measure_mono fun t ht => ht.1
  have htailReal : 0 < (nuMeasure κ p z w L R Λ).real (Ioi y) := by
    rw [Measure.real]
    exact ENNReal.toReal_pos htail.ne' (measure_ne_top _ _)
  have hνprob := probReal_add_probReal_compl
    (μ := nuMeasure κ p z w L R Λ) (s := Iic y) measurableSet_Iic
  simp only [compl_Iic] at hνprob
  rw [cdfGap, hμcdf, nuCDF]
  linarith

theorem cdfGap_left_endpoint
    {κ : ℝ → ℝ} {p z w L R δ Λ : ℝ} (hpz : p ≤ z) :
    cdfGap κ p z w L R δ Λ p = 0 := by
  rw [cdfGap, muCDF, nuCDF, muMeasure, nuMeasure]
  simp only [Measure.real, Measure.add_apply]
  rw [
    restrictedDensityMeasure_Iic_eq_zero (a := p) (b := z) le_rfl,
    restrictedDensityMeasure_Iic_eq_zero (a := p) (b := z) le_rfl,
    restrictedDensityMeasure_Iic_eq_zero (a := z) (b := w) hpz]
  simp

theorem cdfGap_right_endpoint
    {κ : ℝ → ℝ} {p z w L R δ Λ : ℝ} (hzw : z ≤ w)
    (hμmass : muMeasure κ p z L δ Set.univ = 1)
    (hνmass : nuMeasure κ p z w L R Λ Set.univ = 1) :
    cdfGap κ p z w L R δ Λ w = 0 := by
  letI : IsProbabilityMeasure (muMeasure κ p z L δ) :=
    mu_isProbabilityMeasure hμmass
  letI : IsProbabilityMeasure (nuMeasure κ p z w L R Λ) :=
    nu_isProbabilityMeasure hνmass
  have hμright : muMeasure κ p z L δ (Ioi w) = 0 := by
    rw [muMeasure]
    exact restrictedDensityMeasure_Ioi_eq_zero hzw
  have hνright : nuMeasure κ p z w L R Λ (Ioi w) = 0 := by
    rw [nuMeasure, Measure.add_apply,
      restrictedDensityMeasure_Ioi_eq_zero hzw,
      restrictedDensityMeasure_Ioi_eq_zero le_rfl]
    simp
  have hμprob := probReal_add_probReal_compl
    (μ := muMeasure κ p z L δ) (s := Iic w) measurableSet_Iic
  have hνprob := probReal_add_probReal_compl
    (μ := nuMeasure κ p z w L R Λ) (s := Iic w) measurableSet_Iic
  simp only [compl_Iic] at hμprob hνprob
  have hμrightReal : (muMeasure κ p z L δ).real (Ioi w) = 0 := by
    rw [Measure.real, hμright]
    simp
  have hνrightReal : (nuMeasure κ p z w L R Λ).real (Ioi w) = 0 := by
    rw [Measure.real, hνright]
    simp
  rw [hμrightReal, add_zero] at hμprob
  rw [hνrightReal, add_zero] at hνprob
  rw [cdfGap, muCDF, nuCDF, hμprob, hνprob, sub_self]

/-- The complete non-vacuous interior CDF theorem.  Every hypothesis is an
upstream analytic or normalization property of the displayed densities; no
gap value is assumed positive. -/
theorem cdfGap_pos
    {κ : ℝ → ℝ} {p z w L R δ Λ y : ℝ}
    (hpz : p < z) (hzw : z < w) (hpy : p < y) (hyw : y < w)
    (hκ : ∀ t ∈ Icc p w, 0 < κ t) (hκcont : Continuous κ)
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hμfull : IntervalIntegrable (leftMuDensity κ z L δ) volume p z)
    (hνfull : IntervalIntegrable (leftNuDensity κ p L Λ) volume p z)
    (hright : IntervalIntegrable (rightNuDensity κ w R Λ) volume z w)
    (hμmass : (∫ t in p..z, leftMuDensity κ z L δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity κ p L Λ t) +
        (∫ t in z..w, rightNuDensity κ w R Λ t) = 1) :
    0 < cdfGap κ p z w L R δ Λ y := by
  have hκleft : ∀ t ∈ Icc p z, 0 < κ t := fun t ht =>
    hκ t ⟨ht.1, ht.2.trans hzw.le⟩
  have hκright : ∀ t ∈ Icc z w, 0 < κ t := fun t ht =>
    hκ t ⟨hpz.le.trans ht.1, ht.2⟩
  have hμmeasure : muMeasure κ p z L δ Set.univ = 1 :=
    muMeasure_univ_eq_one hpz hκleft hL hδ hμfull hμmass
  have hνmeasure : nuMeasure κ p z w L R Λ Set.univ = 1 :=
    nuMeasure_univ_eq_one hpz hzw hκleft hκright hL hR hΛ
      hνfull hright hνmass
  rcases lt_or_ge y (crossingPoint p z L δ Λ) with hyc | hcy
  · have hyz : y < z := hyc.trans
      (crossingPoint_mem hpz hΛ (mul_pos hL hδ)).2
    have hμprefix : IntervalIntegrable (leftMuDensity κ z L δ) volume p y :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hpy.le).2 <|
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpz.le).1 hμfull).mono_set
          (Ioc_subset_Ioc_right hyz.le)
    have hνprefix : IntervalIntegrable (leftNuDensity κ p L Λ) volume p y :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hpy.le).2 <|
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpz.le).1 hνfull).mono_set
          (Ioc_subset_Ioc_right hyz.le)
    exact cdfGap_pos_before_crossing hpy hyc hpz hκleft hκcont
      hL hδ hΛ hμprefix hνprefix
  · rcases lt_or_ge y z with hyz | hzy
    · have hμprefix : IntervalIntegrable (leftMuDensity κ z L δ) volume p y :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hpy.le).2 <|
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpz.le).1 hμfull).mono_set
            (Ioc_subset_Ioc_right hyz.le)
      have hνprefix : IntervalIntegrable (leftNuDensity κ p L Λ) volume p y :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hpy.le).2 <|
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpz.le).1 hνfull).mono_set
            (Ioc_subset_Ioc_right hyz.le)
      exact cdfGap_pos_from_crossing_to_z hpz hzw hcy hyz hκ hκcont
        hL hR hδ hΛ hμfull hνfull hμprefix hνprefix hμmass hνmass
    · have hκtail : ∀ t ∈ Icc y w, 0 < κ t := fun t ht =>
        hκ t ⟨hpz.le.trans (hzy.trans ht.1), ht.2⟩
      exact cdfGap_pos_right hzy hyw hκtail hκcont hR hΛ hμmeasure hνmeasure

end PF4.CDF
