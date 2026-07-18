/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.Expectation

set_option linter.style.header false

/-!
# Positive CDF transport

This file formalizes the positive end of the CERT9 transport chain.  Its input
gap is the CDF gap of the concrete measures, and its weight is the displayed
curvature quotient.  Strictness is witnessed at the midpoint of a nonempty
interval; it is not encoded in a fresh positive scalar.
-/

namespace PF4.Transport

open MeasureTheory Set
open scoped Interval
open PF4.CDF PF4.Densities PF4.Normalization PF4.Measures PF4.Expectation

/-- The curvature weight which appears after the transport integration by
parts. -/
noncomputable def curvatureWeight
    (Q κ C4 : ℝ → ℝ) (t : ℝ) : ℝ :=
  C4 t / (Q t ^ 6 * κ t ^ 2)

theorem curvatureWeight_pos
    {Q κ C4 : ℝ → ℝ} {t : ℝ}
    (hQ : 0 < Q t) (hκ : 0 < κ t) (hC4 : 0 < C4 t) :
    0 < curvatureWeight Q κ C4 t := by
  rw [curvatureWeight]
  exact div_pos hC4 (mul_pos (pow_pos hQ 6) (pow_pos hκ 2))

/-- The CDF-weighted transport integral. -/
noncomputable def transportIntegral
    (gap Q κ C4 : ℝ → ℝ) (p w : ℝ) : ℝ :=
  ∫ t in p..w, gap t * curvatureWeight Q κ C4 t

/-- The PO-0039 identity specialized to the independently defined curvature
transport weight.  This is an object-level connection: neither the expectation
difference nor `transportIntegral` is defined in terms of the other. -/
theorem concrete_expectationDifference_eq_transportIntegral
    {κ Q C4 A : ℝ → ℝ} {p z w L R δ Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hκ : ∀ t ∈ Icc p w, 0 < κ t) (hκcont : Continuous κ)
    (hAcont : Continuous A)
    (hA : ∀ t, HasDerivAt A (curvatureWeight Q κ C4 t) t)
    (hweight : IntervalIntegrable (curvatureWeight Q κ C4) volume p w)
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hμmass : (∫ t in p..z, leftMuDensity κ z L δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity κ p L Λ t) +
        (∫ t in z..w, rightNuDensity κ w R Λ t) = 1) :
    measureExpectation (nuMeasure κ p z w L R Λ) A -
        measureExpectation (muMeasure κ p z L δ) A =
      transportIntegral (cdfGap κ p z w L R δ Λ) Q κ C4 p w := by
  rw [transportIntegral]
  exact expectation_difference_eq_cdfGap_integral hpz hzw hκ hκcont
    hAcont hA hweight hL hR hδ hΛ hμmass hνmass

/-- A continuous nonnegative gap which is strict in the interior gives a
strictly positive transport integral against a strictly positive curvature
weight. -/
theorem transportIntegral_pos
    {gap Q κ C4 : ℝ → ℝ} {p w : ℝ}
    (hpw : p < w)
    (hgap0 : ∀ t ∈ Icc p w, 0 ≤ gap t)
    (hgap : ∀ t ∈ Ioo p w, 0 < gap t)
    (hQ : ∀ t ∈ Icc p w, 0 < Q t)
    (hκ : ∀ t ∈ Icc p w, 0 < κ t)
    (hC4 : ∀ t ∈ Icc p w, 0 < C4 t)
    (hcont : ContinuousOn
      (fun t => gap t * curvatureWeight Q κ C4 t) (Icc p w)) :
    0 < transportIntegral gap Q κ C4 p w := by
  rw [transportIntegral]
  apply intervalIntegral.integral_pos hpw hcont
  · intro t ht
    have ht' : t ∈ Icc p w := ⟨le_of_lt ht.1, ht.2⟩
    exact mul_nonneg (hgap0 t ht')
      (curvatureWeight_pos (hQ t ht') (hκ t ht') (hC4 t ht')).le
  · refine ⟨(p + w) / 2, by constructor <;> linarith, ?_⟩
    exact mul_pos
      (hgap ((p + w) / 2) (by constructor <;> linarith))
      (curvatureWeight_pos
        (hQ ((p + w) / 2) (by constructor <;> linarith))
        (hκ ((p + w) / 2) (by constructor <;> linarith))
        (hC4 ((p + w) / 2) (by constructor <;> linarith)))

/-- The numerator `N` in the final transport sign identity. -/
noncomputable def transportNumerator
    (δ Λ : ℝ) (gap Q κ C4 : ℝ → ℝ) (p w : ℝ) : ℝ :=
  δ * Λ * transportIntegral gap Q κ C4 p w

theorem transportNumerator_pos
    {δ Λ : ℝ} {gap Q κ C4 : ℝ → ℝ} {p w : ℝ}
    (hδ : 0 < δ) (hΛ : 0 < Λ)
    (htransport : 0 < transportIntegral gap Q κ C4 p w) :
    0 < transportNumerator δ Λ gap Q κ C4 p w := by
  rw [transportNumerator]
  exact mul_pos (mul_pos hδ hΛ) htransport

/-- The exact final expression for `∂ξΨ` once the transport numerator has
been identified. -/
noncomputable def partialXiExpression (Qp Λ N : ℝ) : ℝ :=
  -Qp * N / Λ ^ 2

theorem partialXiExpression_neg
    {Qp Λ N : ℝ} (hQp : 0 < Qp) (hΛ : 0 < Λ) (hN : 0 < N) :
    partialXiExpression Qp Λ N < 0 := by
  rw [partialXiExpression]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hQp) hN)
    (pow_pos hΛ 2)

/-- The sign bridge used by CERT9: an independently derived exact identity
with the displayed expression transfers strict positivity of `N` to the
strict negative derivative. -/
theorem partialXiPsi_neg_of_transport
    {partialXiPsi Qp Λ N : ℝ}
    (hbridge : partialXiPsi = partialXiExpression Qp Λ N)
    (hQp : 0 < Qp) (hΛ : 0 < Λ) (hN : 0 < N) :
    partialXiPsi < 0 := by
  rw [hbridge]
  exact partialXiExpression_neg hQp hΛ hN

/-- Direct assembly for the concrete triangular CDF gap. -/
theorem concrete_transportNumerator_pos
    {κ Q C4 : ℝ → ℝ} {p z w L R δ Λ : ℝ}
    (hpw : p < w) (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hgap0 : ∀ t ∈ Icc p w,
      0 ≤ cdfGap κ p z w L R δ Λ t)
    (hgap : ∀ t ∈ Ioo p w,
      0 < cdfGap κ p z w L R δ Λ t)
    (hQ : ∀ t ∈ Icc p w, 0 < Q t)
    (hκ : ∀ t ∈ Icc p w, 0 < κ t)
    (hC4 : ∀ t ∈ Icc p w, 0 < C4 t)
    (hcont : ContinuousOn
      (fun t => cdfGap κ p z w L R δ Λ t *
        curvatureWeight Q κ C4 t) (Icc p w)) :
    0 < transportNumerator δ Λ
      (cdfGap κ p z w L R δ Λ) Q κ C4 p w := by
  apply transportNumerator_pos hδ hΛ
  exact transportIntegral_pos hpw hgap0 hgap hQ hκ hC4 hcont

/-- End-to-end assembly from the displayed triangular density data to the
strictly positive CERT9 transport numerator.  Unlike
`concrete_transportNumerator_pos`, this theorem derives both gap hypotheses
from the measure/CDF construction. -/
theorem concrete_transportNumerator_pos_from_measures
    {κ Q C4 : ℝ → ℝ} {p z w L R δ Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hκ : ∀ t ∈ Icc p w, 0 < κ t) (hκcont : Continuous κ)
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hμfull : IntervalIntegrable (PF4.Densities.leftMuDensity κ z L δ) volume p z)
    (hνfull : IntervalIntegrable (PF4.Densities.leftNuDensity κ p L Λ) volume p z)
    (hright : IntervalIntegrable
      (PF4.Normalization.rightNuDensity κ w R Λ) volume z w)
    (hμmass :
      (∫ t in p..z, PF4.Densities.leftMuDensity κ z L δ t) = 1)
    (hνmass :
      (∫ t in p..z, PF4.Densities.leftNuDensity κ p L Λ t) +
        (∫ t in z..w, PF4.Normalization.rightNuDensity κ w R Λ t) = 1)
    (hQ : ∀ t ∈ Icc p w, 0 < Q t)
    (hC4 : ∀ t ∈ Icc p w, 0 < C4 t)
    (hcont : ContinuousOn
      (fun t => cdfGap κ p z w L R δ Λ t *
        curvatureWeight Q κ C4 t) (Icc p w)) :
    0 < transportNumerator δ Λ
      (cdfGap κ p z w L R δ Λ) Q κ C4 p w := by
  have hκleft : ∀ t ∈ Icc p z, 0 < κ t := fun t ht =>
    hκ t ⟨ht.1, ht.2.trans hzw.le⟩
  have hκright : ∀ t ∈ Icc z w, 0 < κ t := fun t ht =>
    hκ t ⟨hpz.le.trans ht.1, ht.2⟩
  have hμmeasure : PF4.Measures.muMeasure κ p z L δ Set.univ = 1 :=
    PF4.Measures.muMeasure_univ_eq_one hpz hκleft hL hδ hμfull hμmass
  have hνmeasure : PF4.Measures.nuMeasure κ p z w L R Λ Set.univ = 1 :=
    PF4.Measures.nuMeasure_univ_eq_one hpz hzw hκleft hκright hL hR hΛ
      hνfull hright hνmass
  apply concrete_transportNumerator_pos (hpz.trans hzw) hδ hΛ
  · intro t ht
    by_cases htp : t = p
    · subst t
      rw [cdfGap_left_endpoint hpz.le]
    by_cases htw : t = w
    · subst t
      rw [cdfGap_right_endpoint hzw.le hμmeasure hνmeasure]
    exact (cdfGap_pos hpz hzw
      (lt_of_le_of_ne ht.1 (Ne.symm htp))
      (lt_of_le_of_ne ht.2 htw)
      hκ hκcont hL hR hδ hΛ hμfull hνfull hright hμmass hνmass).le
  · intro t ht
    exact cdfGap_pos hpz hzw ht.1 ht.2 hκ hκcont hL hR hδ hΛ
      hμfull hνfull hright hμmass hνmass
  · exact hQ
  · exact hκ
  · exact hC4
  · exact hcont

end PF4.Transport
