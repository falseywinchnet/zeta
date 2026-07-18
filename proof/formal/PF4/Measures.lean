/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.Normalization
import Mathlib.Probability.CDF

set_option linter.style.header false

/-!
# The triangular probability measures

This file constructs the measures used by the crossing argument.  The support
restriction and density belong to the same definition; normalization is then a
theorem about that concrete measure, not a separate symbolic assertion.
-/

namespace PF4.Measures

open MeasureTheory Set
open scoped ENNReal Interval
open PF4.Densities PF4.Normalization

/-- Lebesgue measure on `(a,b]`, weighted by the nonnegative part of `f`. -/
noncomputable def restrictedDensityMeasure (a b : ℝ) (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioc a b)).withDensity fun t => ENNReal.ofReal (f t)

/-- The total mass of a restricted density is the corresponding interval
integral when the density is integrable and nonnegative on its support. -/
theorem restrictedDensityMeasure_univ
    {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hnonneg : ∀ t ∈ Ioc a b, 0 ≤ f t) :
    restrictedDensityMeasure a b f Set.univ =
      ENNReal.ofReal (∫ t in a..b, f t) := by
  rw [restrictedDensityMeasure, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hab]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
  · exact (ae_restrict_mem measurableSet_Ioc).mono hnonneg

/-- Restricting farther to a terminal subinterval only changes the lower
endpoint of the density integral. -/
theorem restrictedDensityMeasure_Ioc
    {a y b : ℝ} {f : ℝ → ℝ}
    (hay : a ≤ y) (hyb : y ≤ b)
    (hf : IntervalIntegrable f volume y b)
    (hnonneg : ∀ t ∈ Ioc y b, 0 ≤ f t) :
    restrictedDensityMeasure a b f (Ioc y b) =
      ENNReal.ofReal (∫ t in y..b, f t) := by
  rw [restrictedDensityMeasure, withDensity_apply _ measurableSet_Ioc]
  rw [Measure.restrict_restrict measurableSet_Ioc]
  simp only [Ioc_inter_Ioc, max_eq_left hay, min_self]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hyb]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hyb).1 hf
  · exact (ae_restrict_mem measurableSet_Ioc).mono hnonneg

/-- The measure accumulated through `y` is the prefix interval integral,
embedded in `ℝ≥0∞`. -/
theorem restrictedDensityMeasure_Iic
    {a y b : ℝ} {f : ℝ → ℝ}
    (hay : a ≤ y) (hyb : y ≤ b)
    (hf : IntervalIntegrable f volume a y)
    (hnonneg : ∀ t ∈ Ioc a y, 0 ≤ f t) :
    restrictedDensityMeasure a b f (Iic y) =
      ENNReal.ofReal (∫ t in a..y, f t) := by
  rw [restrictedDensityMeasure, withDensity_apply _ measurableSet_Iic]
  rw [Measure.restrict_restrict measurableSet_Iic]
  simp only [Iic_inter_Ioc_of_le hyb]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le hay]
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hay).1 hf
  · exact (ae_restrict_mem measurableSet_Ioc).mono hnonneg

/-- The real mass accumulated through `y` is the prefix interval integral. -/
theorem restrictedDensityMeasure_real_Iic
    {a y b : ℝ} {f : ℝ → ℝ}
    (hay : a ≤ y) (hyb : y ≤ b)
    (hf : IntervalIntegrable f volume a y)
    (hnonneg : ∀ t ∈ Ioc a y, 0 ≤ f t) :
    (restrictedDensityMeasure a b f).real (Iic y) =
      ∫ t in a..y, f t := by
  rw [Measure.real, restrictedDensityMeasure_Iic hay hyb hf hnonneg,
    ENNReal.toReal_ofReal]
  rw [intervalIntegral.integral_of_le hay]
  exact integral_nonneg_of_ae <| (ae_restrict_mem measurableSet_Ioc).mono hnonneg

/-- A restricted density has accumulated no mass weakly before its left
support endpoint. -/
theorem restrictedDensityMeasure_Iic_eq_zero
    {a b y : ℝ} {f : ℝ → ℝ} (hya : y ≤ a) :
    restrictedDensityMeasure a b f (Iic y) = 0 := by
  rw [restrictedDensityMeasure, withDensity_apply _ measurableSet_Iic]
  rw [Measure.restrict_restrict measurableSet_Iic]
  have hempty : Iic y ∩ Ioc a b = ∅ := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, iff_false]
    exact fun ht => (not_lt_of_ge (ht.1.trans hya)) ht.2.1
  rw [hempty, Measure.restrict_empty]
  simp

theorem restrictedDensityMeasure_real_Iic_eq_zero
    {a b y : ℝ} {f : ℝ → ℝ} (hya : y ≤ a) :
    (restrictedDensityMeasure a b f).real (Iic y) = 0 := by
  rw [Measure.real, restrictedDensityMeasure_Iic_eq_zero hya]
  simp

/-- No mass lies strictly to the right of the support endpoint. -/
theorem restrictedDensityMeasure_Ioi_eq_zero
    {a b y : ℝ} {f : ℝ → ℝ} (hby : b ≤ y) :
    restrictedDensityMeasure a b f (Ioi y) = 0 := by
  rw [restrictedDensityMeasure, withDensity_apply _ measurableSet_Ioi]
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hempty : Ioi y ∩ Ioc a b = ∅ := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc, mem_empty_iff_false, iff_false]
    exact fun ht => (not_lt_of_ge (ht.2.2.trans hby)) ht.1
  rw [hempty, Measure.restrict_empty]
  simp

/-- The left triangular law `μ`. -/
noncomputable def muMeasure
    (κ : ℝ → ℝ) (p z L δ : ℝ) : Measure ℝ :=
  restrictedDensityMeasure p z (leftMuDensity κ z L δ)

/-- The two-piece triangular law `ν`. -/
noncomputable def nuMeasure
    (κ : ℝ → ℝ) (p z w L R Λ : ℝ) : Measure ℝ :=
  restrictedDensityMeasure p z (leftNuDensity κ p L Λ) +
    restrictedDensityMeasure z w (rightNuDensity κ w R Λ)

theorem muMeasure_univ_eq_one
    {κ : ℝ → ℝ} {p z L δ : ℝ}
    (hpz : p < z) (hκ : ∀ t ∈ Icc p z, 0 < κ t)
    (hL : 0 < L) (hδ : 0 < δ)
    (hint : IntervalIntegrable (leftMuDensity κ z L δ) volume p z)
    (hmass : (∫ t in p..z, leftMuDensity κ z L δ t) = 1) :
    muMeasure κ p z L δ Set.univ = 1 := by
  rw [muMeasure, restrictedDensityMeasure_univ hpz.le hint]
  · simp [hmass]
  · intro t ht
    by_cases htz : t = z
    · simp [leftMuDensity, htz]
    · exact (leftMuDensity_pos (lt_of_le_of_ne ht.2 htz)
        (hκ t ⟨le_of_lt ht.1, ht.2⟩) hL hδ).le

theorem nuMeasure_univ_eq_one
    {κ : ℝ → ℝ} {p z w L R Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hκleft : ∀ t ∈ Icc p z, 0 < κ t)
    (hκright : ∀ t ∈ Icc z w, 0 < κ t)
    (hL : 0 < L) (hR : 0 < R) (hΛ : 0 < Λ)
    (hleft : IntervalIntegrable (leftNuDensity κ p L Λ) volume p z)
    (hright : IntervalIntegrable (rightNuDensity κ w R Λ) volume z w)
    (hmass :
      (∫ t in p..z, leftNuDensity κ p L Λ t) +
        (∫ t in z..w, rightNuDensity κ w R Λ t) = 1) :
    nuMeasure κ p z w L R Λ Set.univ = 1 := by
  rw [nuMeasure, Measure.add_apply,
    restrictedDensityMeasure_univ hpz.le hleft,
    restrictedDensityMeasure_univ hzw.le hright]
  · rw [← ENNReal.ofReal_add]
    · simp [hmass]
    · exact intervalIntegral.integral_nonneg hpz.le fun t ht =>
        if htp : t = p then by simp [leftNuDensity, htp]
        else (leftNuDensity_pos (lt_of_le_of_ne ht.1 (Ne.symm htp))
          (hκleft t ht) hL hΛ).le
    · exact intervalIntegral.integral_nonneg hzw.le fun t ht =>
        if htw : t = w then by simp [rightNuDensity, htw]
        else (rightNuDensity_pos (lt_of_le_of_ne ht.2 htw)
          (hκright t ht) hR hΛ).le
  · intro t ht
    by_cases htw : t = w
    · simp [rightNuDensity, htw]
    · exact (rightNuDensity_pos (lt_of_le_of_ne ht.2 htw)
        (hκright t ⟨le_of_lt ht.1, ht.2⟩) hR hΛ).le
  · intro t ht
    exact (leftNuDensity_pos ht.1
      (hκleft t ⟨le_of_lt ht.1, ht.2⟩) hL hΛ).le

/-- A mass-one proof supplies mathlib's probability-measure interface without
adding a new axiom or a global instance. -/
theorem mu_isProbabilityMeasure
    {κ : ℝ → ℝ} {p z L δ : ℝ}
    (hmass : muMeasure κ p z L δ Set.univ = 1) :
    IsProbabilityMeasure (muMeasure κ p z L δ) :=
  ⟨hmass⟩

theorem nu_isProbabilityMeasure
    {κ : ℝ → ℝ} {p z w L R Λ : ℝ}
    (hmass : nuMeasure κ p z w L R Λ Set.univ = 1) :
    IsProbabilityMeasure (nuMeasure κ p z w L R Λ) :=
  ⟨hmass⟩

/-- The right tail of `ν` has strictly positive mass.  The proof exhibits the
positive interval integral which supplies that mass; no endpoint-gap variable
is assumed positive. -/
theorem nuMeasure_Ioc_pos
    {κ : ℝ → ℝ} {p z w L R Λ y : ℝ}
    (hzy : z ≤ y) (hyw : y < w)
    (hκ : ∀ t ∈ Icc y w, 0 < κ t)
    (hR : 0 < R) (hΛ : 0 < Λ)
    (hcont : ContinuousOn (rightNuDensity κ w R Λ) (Icc y w)) :
    0 < nuMeasure κ p z w L R Λ (Ioc y w) := by
  have hint : IntervalIntegrable (rightNuDensity κ w R Λ) volume y w :=
    hcont.intervalIntegrable_of_Icc hyw.le
  have hright :
      0 < restrictedDensityMeasure z w (rightNuDensity κ w R Λ) (Ioc y w) := by
    rw [restrictedDensityMeasure_Ioc hzy hyw.le hint]
    · exact ENNReal.ofReal_pos.2 <| intervalIntegral.integral_pos hyw hcont
        (fun t ht => if htw : t = w then by simp [rightNuDensity, htw]
          else (rightNuDensity_pos (lt_of_le_of_ne ht.2 htw)
            (hκ t ⟨le_of_lt ht.1, ht.2⟩) hR hΛ).le)
        ⟨(y + w) / 2, by constructor <;> linarith,
          rightNuDensity_pos (by linarith)
            (hκ ((y + w) / 2) (by constructor <;> linarith)) hR hΛ⟩
    · intro t ht
      by_cases htw : t = w
      · simp [rightNuDensity, htw]
      · exact (rightNuDensity_pos (lt_of_le_of_ne ht.2 htw)
          (hκ t ⟨le_of_lt ht.1, ht.2⟩) hR hΛ).le
  rw [nuMeasure, Measure.add_apply]
  apply lt_of_lt_of_le hright
  have hle := add_le_add_right
    (show (0 : ℝ≥0∞) ≤ restrictedDensityMeasure p z
      (leftNuDensity κ p L Λ) (Ioc y w) from bot_le)
    (restrictedDensityMeasure z w (rightNuDensity κ w R Λ) (Ioc y w))
  simpa [add_comm] using hle

end PF4.Measures
