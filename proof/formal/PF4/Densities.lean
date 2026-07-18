/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.Crossing

set_option linter.style.header false

/-!
# Density identity bridge

This file connects the constructive ratio in `PF4.Crossing` to the actual left
density formulas used for `μ` and `ν`. It proves positivity, ratio identity,
the unique density crossing, and the exact sign pattern of the density
difference. Measure normalization and CDF statements remain separate
obligations.
-/

namespace PF4.Densities

open PF4.Crossing

/-- The density of `μ` on the open left interval `(p,z)`. -/
noncomputable def leftMuDensity
    (κ : ℝ → ℝ) (z L δ t : ℝ) : ℝ :=
  (z - t) * κ t / (L ^ 2 * δ)

/-- The density of `ν` on the open left interval `(p,z)`. -/
noncomputable def leftNuDensity
    (κ : ℝ → ℝ) (p L Λ t : ℝ) : ℝ :=
  (t - p) * κ t / (L * Λ)

theorem leftMuDensity_pos
    {κ : ℝ → ℝ} {z L δ t : ℝ}
    (htz : t < z) (hκ : 0 < κ t) (hL : 0 < L) (hδ : 0 < δ) :
    0 < leftMuDensity κ z L δ t := by
  rw [leftMuDensity]
  exact div_pos (mul_pos (sub_pos.mpr htz) hκ)
    (mul_pos (pow_pos hL 2) hδ)

theorem leftNuDensity_pos
    {κ : ℝ → ℝ} {p L Λ t : ℝ}
    (hpt : p < t) (hκ : 0 < κ t) (hL : 0 < L) (hΛ : 0 < Λ) :
    0 < leftNuDensity κ p L Λ t := by
  rw [leftNuDensity]
  exact div_pos (mul_pos (sub_pos.mpr hpt) hκ) (mul_pos hL hΛ)

theorem leftDensity_ratio
    {κ : ℝ → ℝ} {p z L δ Λ t : ℝ}
    (hpt : p < t) (htz : t < z) (hκ : 0 < κ t)
    (hL : 0 < L) (hδ : 0 < δ) (hΛ : 0 < Λ) :
    leftMuDensity κ z L δ t / leftNuDensity κ p L Λ t =
      densityRatio p z L δ Λ t := by
  have htp : t - p ≠ 0 := sub_ne_zero.mpr hpt.ne'
  have hzt : z - t ≠ 0 := sub_ne_zero.mpr htz.ne'
  rw [leftMuDensity, leftNuDensity, densityRatio]
  field_simp [hκ.ne', hL.ne', hδ.ne', hΛ.ne', htp, hzt]

theorem leftDensity_eq_iff_crossingPoint
    {κ : ℝ → ℝ} {p z L δ Λ t : ℝ}
    (hpt : p < t) (htz : t < z) (hκ : 0 < κ t)
    (hΛ : 0 < Λ) (hL : 0 < L) (hδ : 0 < δ) :
    leftMuDensity κ z L δ t = leftNuDensity κ p L Λ t ↔
      t = crossingPoint p z L δ Λ := by
  have hν : leftNuDensity κ p L Λ t ≠ 0 :=
    (leftNuDensity_pos hpt hκ hL hΛ).ne'
  rw [← div_eq_one_iff_eq hν, leftDensity_ratio hpt htz hκ hL hδ hΛ]
  exact densityRatio_eq_one_iff hpt hΛ hL hδ

theorem leftDensity_difference_factorization
    {κ : ℝ → ℝ} {p z L δ Λ t : ℝ}
    (hpt : p < t) (htz : t < z) (hκ : 0 < κ t)
    (hL : 0 < L) (hδ : 0 < δ) (hΛ : 0 < Λ) :
    leftMuDensity κ z L δ t - leftNuDensity κ p L Λ t =
      leftNuDensity κ p L Λ t * (densityRatio p z L δ Λ t - 1) := by
  have hν : leftNuDensity κ p L Λ t ≠ 0 :=
    (leftNuDensity_pos hpt hκ hL hΛ).ne'
  calc
    leftMuDensity κ z L δ t - leftNuDensity κ p L Λ t =
        leftNuDensity κ p L Λ t *
          (leftMuDensity κ z L δ t / leftNuDensity κ p L Λ t - 1) := by
      field_simp [hν]
    _ = leftNuDensity κ p L Λ t *
          (densityRatio p z L δ Λ t - 1) := by
      rw [leftDensity_ratio hpt htz hκ hL hδ hΛ]

theorem leftDensity_difference_pos_iff
    {κ : ℝ → ℝ} {p z L δ Λ t : ℝ}
    (hpt : p < t) (htz : t < z) (hκ : 0 < κ t)
    (hΛ : 0 < Λ) (hL : 0 < L) (hδ : 0 < δ) :
    0 < leftMuDensity κ z L δ t - leftNuDensity κ p L Λ t ↔
      t < crossingPoint p z L δ Λ := by
  have hν : 0 < leftNuDensity κ p L Λ t :=
    leftNuDensity_pos hpt hκ hL hΛ
  rw [leftDensity_difference_factorization hpt htz hκ hL hδ hΛ,
    mul_pos_iff_of_pos_left hν, sub_pos]
  exact densityRatio_gt_one_iff hpt hΛ hL hδ

theorem leftDensity_difference_neg_iff
    {κ : ℝ → ℝ} {p z L δ Λ t : ℝ}
    (hpt : p < t) (htz : t < z) (hκ : 0 < κ t)
    (hΛ : 0 < Λ) (hL : 0 < L) (hδ : 0 < δ) :
    leftMuDensity κ z L δ t - leftNuDensity κ p L Λ t < 0 ↔
      crossingPoint p z L δ Λ < t := by
  have hν : 0 < leftNuDensity κ p L Λ t :=
    leftNuDensity_pos hpt hκ hL hΛ
  rw [leftDensity_difference_factorization hpt htz hκ hL hδ hΛ]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with hgood | hbad
    · exact (densityRatio_lt_one_iff hpt hΛ hL hδ).1 (sub_neg.mp hgood.2)
    · exact False.elim ((not_lt_of_ge hν.le) hbad.1)
  · intro hcross
    exact mul_neg_of_pos_of_neg hν
      (sub_neg.mpr ((densityRatio_lt_one_iff hpt hΛ hL hδ).2 hcross))

end PF4.Densities
