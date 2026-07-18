/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.Densities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Triangular-density normalization

This file formalizes the exact mass cancellations in PO-0030 and PO-0031.
The hypotheses are the triangular integral identities that define `δ` and
`Λ`; positivity and analytic derivation of those identities belong to the
curvature-coordinate layer.
-/

namespace PF4.Normalization

open scoped Interval
open PF4.Densities

/-- The density of `ν` on the open right interval `(z,w)`. -/
noncomputable def rightNuDensity
    (κ : ℝ → ℝ) (w R Λ t : ℝ) : ℝ :=
  (w - t) * κ t / (R * Λ)

theorem rightNuDensity_pos
    {κ : ℝ → ℝ} {w R Λ t : ℝ}
    (htw : t < w) (hκ : 0 < κ t) (hR : 0 < R) (hΛ : 0 < Λ) :
    0 < rightNuDensity κ w R Λ t := by
  rw [rightNuDensity]
  exact div_pos (mul_pos (sub_pos.mpr htw) hκ) (mul_pos hR hΛ)

/-- The triangular identity defining `δ` makes the left `μ` density have
exact interval mass one. -/
theorem leftMuDensity_intervalIntegral_eq_one
    {κ : ℝ → ℝ} {p z L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ)
    (hraw : (∫ t in p..z, (z - t) * κ t) = L ^ 2 * δ) :
    (∫ t in p..z, leftMuDensity κ z L δ t) = 1 := by
  change (∫ t in p..z, ((z - t) * κ t) / (L ^ 2 * δ)) = 1
  rw [intervalIntegral.integral_div, hraw]
  exact div_self (mul_ne_zero (pow_ne_zero 2 hL.ne') hδ.ne')

/-- The two triangular terms defining `Λ` make the two pieces of the `ν`
density have combined interval mass one. -/
theorem nuDensities_intervalIntegral_eq_one
    {κ : ℝ → ℝ} {p z w L R Λ : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hΛ : 0 < Λ)
    (hraw :
      (∫ t in p..z, (t - p) * κ t) / L +
        (∫ t in z..w, (w - t) * κ t) / R = Λ) :
    (∫ t in p..z, leftNuDensity κ p L Λ t) +
        (∫ t in z..w, rightNuDensity κ w R Λ t) = 1 := by
  simp only [leftNuDensity, rightNuDensity, intervalIntegral.integral_div]
  calc
    (∫ t in p..z, (t - p) * κ t) / (L * Λ) +
          (∫ t in z..w, (w - t) * κ t) / (R * Λ) =
        ((∫ t in p..z, (t - p) * κ t) / L +
          (∫ t in z..w, (w - t) * κ t) / R) / Λ := by
      field_simp [hL.ne', hR.ne', hΛ.ne']
    _ = Λ / Λ := by rw [hraw]
    _ = 1 := div_self hΛ.ne'

end PF4.Normalization
