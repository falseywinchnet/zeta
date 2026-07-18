import PF4.Curvature
import PF4.CDF

set_option linter.style.header false

/-!
# Closed cumulative triangular weights

The primary objects here are deterministic normalized integrals and their
endpoint closed forms. Measures and probability CDFs appear only in bridge
theorems.
-/

namespace PF4.Advancement.ClosedCumulativeGap

open MeasureTheory Set
open scoped Interval
open PF4.Curvature PF4.Densities PF4.Normalization PF4.Measures PF4.CDF

noncomputable def increasingBoundary
    (Q Q1 : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (x - a) ^ 2 - (x - a) * Q1 x + Q x

noncomputable def decreasingBoundary
    (Q Q1 : ℝ → ℝ) (a x : ℝ) : ℝ :=
  -(a - x) ^ 2 - (a - x) * Q1 x - Q x

theorem hasDerivAt_increasingBoundary
    {Q Q1 Q2 : ℝ → ℝ} {a x : ℝ}
    (hQ : HasDerivAt Q (Q1 x) x) (hQ1 : HasDerivAt Q1 (Q2 x) x) :
    HasDerivAt (increasingBoundary Q Q1 a)
      ((x - a) * curvature Q2 x) x := by
  unfold increasingBoundary curvature
  have hx : HasDerivAt (fun t : ℝ => t - a) 1 x := by
    simpa only [id_eq] using (hasDerivAt_id x).sub_const a
  apply ((hx.pow 2).sub (hx.mul hQ1) |>.add hQ).congr_deriv
  ring

theorem hasDerivAt_decreasingBoundary
    {Q Q1 Q2 : ℝ → ℝ} {a x : ℝ}
    (hQ : HasDerivAt Q (Q1 x) x) (hQ1 : HasDerivAt Q1 (Q2 x) x) :
    HasDerivAt (decreasingBoundary Q Q1 a)
      ((a - x) * curvature Q2 x) x := by
  unfold decreasingBoundary curvature
  have hx : HasDerivAt (fun t : ℝ => a - t) (-1) x := by
    simpa only [id_eq] using (hasDerivAt_id x).const_sub a
  apply (((hx.pow 2).neg.sub (hx.mul hQ1)).sub hQ).congr_deriv
  ring

theorem increasing_integral_closed
    {Q Q1 Q2 : ℝ → ℝ} {a x y : ℝ}
    (hQ : ∀ t ∈ uIcc x y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc x y, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (t - a) * curvature Q2 t) volume x y) :
    (∫ t in x..y, (t - a) * curvature Q2 t) =
      increasingBoundary Q Q1 a y - increasingBoundary Q Q1 a x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_increasingBoundary (hQ t ht) (hQ1 t ht)) hint]

theorem decreasing_integral_closed
    {Q Q1 Q2 : ℝ → ℝ} {a x y : ℝ}
    (hQ : ∀ t ∈ uIcc x y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc x y, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (a - t) * curvature Q2 t) volume x y) :
    (∫ t in x..y, (a - t) * curvature Q2 t) =
      decreasingBoundary Q Q1 a y - decreasingBoundary Q Q1 a x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_decreasingBoundary (hQ t ht) (hQ1 t ht)) hint]

/-- Closed normalized cumulative weight of the left-decreasing triangle. -/
noncomputable def closedMuLeft
    (Q Q1 : ℝ → ℝ) (p z δ y : ℝ) : ℝ :=
  (decreasingBoundary Q Q1 z y - decreasingBoundary Q Q1 z p) /
    ((z - p) ^ 2 * δ)

/-- Closed normalized cumulative weight of the left-increasing triangle. -/
noncomputable def closedNuLeft
    (Q Q1 : ℝ → ℝ) (p z Λ y : ℝ) : ℝ :=
  (increasingBoundary Q Q1 p y - increasingBoundary Q Q1 p p) /
    ((z - p) * Λ)

/-- The closed cumulative gap on `[p,z]`. -/
noncomputable def closedGapLeft
    (Q Q1 : ℝ → ℝ) (p z δ Λ y : ℝ) : ℝ :=
  closedMuLeft Q Q1 p z δ y - closedNuLeft Q Q1 p z Λ y

/-- The closed right-tail gap on `[z,w]`. -/
noncomputable def closedGapRight
    (Q Q1 : ℝ → ℝ) (z w Λ y : ℝ) : ℝ :=
  ((w - y) ^ 2 + (w - y) * Q1 y + Q y - Q w) / ((w - z) * Λ)

theorem closedGapLeft_expanded
    {Q Q1 : ℝ → ℝ} {p z δ Λ y : ℝ} :
    closedGapLeft Q Q1 p z δ Λ y =
      (-(z - y) ^ 2 - (z - y) * Q1 y - Q y +
          (z - p) ^ 2 + (z - p) * Q1 p + Q p) / ((z - p) ^ 2 * δ) -
      ((y - p) ^ 2 - (y - p) * Q1 y + Q y - Q p) / ((z - p) * Λ) := by
  unfold closedGapLeft closedMuLeft closedNuLeft
    increasingBoundary decreasingBoundary
  ring

theorem closedMuLeft_eq_integral
    {Q Q1 Q2 : ℝ → ℝ} {p z δ y : ℝ}
    (hQ : ∀ t ∈ uIcc p y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc p y, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (z - t) * curvature Q2 t) volume p y) :
    closedMuLeft Q Q1 p z δ y =
      ∫ t in p..y, leftMuDensity (curvature Q2) z (z - p) δ t := by
  change _ = ∫ t in p..y, ((z - t) * curvature Q2 t) / ((z - p) ^ 2 * δ)
  rw [closedMuLeft, intervalIntegral.integral_div,
    decreasing_integral_closed hQ hQ1 hint]

theorem closedNuLeft_eq_integral
    {Q Q1 Q2 : ℝ → ℝ} {p z Λ y : ℝ}
    (hQ : ∀ t ∈ uIcc p y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc p y, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (t - p) * curvature Q2 t) volume p y) :
    closedNuLeft Q Q1 p z Λ y =
      ∫ t in p..y, leftNuDensity (curvature Q2) p (z - p) Λ t := by
  change _ = ∫ t in p..y, ((t - p) * curvature Q2 t) / ((z - p) * Λ)
  rw [closedNuLeft, intervalIntegral.integral_div,
    increasing_integral_closed hQ hQ1 hint]

theorem closedGapLeft_eq_integral_difference
    {Q Q1 Q2 : ℝ → ℝ} {p z δ Λ y : ℝ}
    (hQ : ∀ t ∈ uIcc p y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc p y, HasDerivAt Q1 (Q2 t) t)
    (hmu : IntervalIntegrable (fun t => (z - t) * curvature Q2 t) volume p y)
    (hnu : IntervalIntegrable (fun t => (t - p) * curvature Q2 t) volume p y) :
    closedGapLeft Q Q1 p z δ Λ y =
      (∫ t in p..y, leftMuDensity (curvature Q2) z (z - p) δ t) -
      ∫ t in p..y, leftNuDensity (curvature Q2) p (z - p) Λ t := by
  rw [closedGapLeft, closedMuLeft_eq_integral hQ hQ1 hmu,
    closedNuLeft_eq_integral hQ hQ1 hnu]

theorem closedGapRight_eq_tail_integral
    {Q Q1 Q2 : ℝ → ℝ} {z w Λ y : ℝ}
    (hQ : ∀ t ∈ uIcc y w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc y w, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (w - t) * curvature Q2 t) volume y w) :
    closedGapRight Q Q1 z w Λ y =
      ∫ t in y..w, rightNuDensity (curvature Q2) w (w - z) Λ t := by
  change _ = ∫ t in y..w, ((w - t) * curvature Q2 t) / ((w - z) * Λ)
  rw [intervalIntegral.integral_div, decreasing_integral_closed hQ hQ1 hint]
  unfold closedGapRight decreasingBoundary
  ring

theorem closedGapLeft_at_p
    {Q Q1 : ℝ → ℝ} {p z δ Λ : ℝ} :
    closedGapLeft Q Q1 p z δ Λ p = 0 := by
  simp [closedGapLeft, closedMuLeft, closedNuLeft]

theorem closedGapRight_at_w
    {Q Q1 : ℝ → ℝ} {z w Λ : ℝ} :
    closedGapRight Q Q1 z w Λ w = 0 := by
  simp [closedGapRight]

end PF4.Advancement.ClosedCumulativeGap
