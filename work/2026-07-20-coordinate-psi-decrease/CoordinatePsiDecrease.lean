import PF4.FinalAssembly
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option linter.style.header false

/-!
# From the maintained coordinate-Psi derivative sign to strict decrease

This advancement candidate discharges the literal monotonicity premise used
by the P000115 terminal quotient wrapper. It assumes only the analytic inputs
already exposed by the maintained final coordinate assembly.
-/

namespace PF4.Advancement.CoordinatePsiDecrease

open Set PF4.Curvature PF4.CoordinateSignBridge

/-- For fixed ordered right endpoints, the maintained coordinate Psi is
strictly decreasing throughout the admissible left-endpoint interval. -/
theorem coordinatePsi_strictAntiOn_Iio_from_determinantC4
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ} {z w : ℝ}
    (hzw : z < w)
    (hQ : ∀ t, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t, HasDerivAt Q2 (Q3 t) t)
    (hQ3 : ∀ t, HasDerivAt Q3 (Q4 t) t)
    (hQ4cont : Continuous Q4)
    (hQpos : ∀ t, 0 < Q t)
    (hκpos : ∀ t, 0 < curvature Q2 t)
    (hdetC4pos : ∀ t,
      0 < PF4.C4Invariant.determinantC4Function Q Q1 Q2 Q3 Q4 t) :
    StrictAntiOn (fun p => coordinatePsi Q Q1 p z w) (Iio z) := by
  let f := fun p => coordinatePsi Q Q1 p z w
  have hderiv : ∀ p ∈ Iio z, deriv f p < 0 := by
    intro p hp
    have hmul := PF4.FinalAssembly.coordinatePartialXiPsi_neg_from_determinantC4
      hp hzw hQ hQ1 hQ2 hQ3 hQ4cont hQpos hκpos hdetC4pos
    dsimp [f] at hmul ⊢
    nlinarith [hQpos p]
  have hcont : ContinuousOn f (Iio z) := by
    intro p hp
    exact (differentiableAt_of_deriv_ne_zero (hderiv p hp).ne).continuousAt
      |>.continuousWithinAt
  apply strictAntiOn_of_deriv_neg (convex_Iio z) hcont
  intro p hp
  have hp' : p ∈ Iio z := by simpa only [interior_Iio] using hp
  exact hderiv p hp'

/-- Exact ordered-point form required by the terminal quotient bridge. -/
theorem coordinatePsi_decreases_on_ordered_points_from_determinantC4
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ}
    (hQ : ∀ t, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t, HasDerivAt Q2 (Q3 t) t)
    (hQ3 : ∀ t, HasDerivAt Q3 (Q4 t) t)
    (hQ4cont : Continuous Q4)
    (hQpos : ∀ t, 0 < Q t)
    (hκpos : ∀ t, 0 < curvature Q2 t)
    (hdetC4pos : ∀ t,
      0 < PF4.C4Invariant.determinantC4Function Q Q1 Q2 Q3 Q4 t) :
    ∀ p₁ p₂ z w, p₁ < p₂ → p₂ < z → z < w →
      coordinatePsi Q Q1 p₂ z w < coordinatePsi Q Q1 p₁ z w := by
  intro p₁ p₂ z w hp₁₂ hp₂z hzw
  have hanti := coordinatePsi_strictAntiOn_Iio_from_determinantC4 hzw
    hQ hQ1 hQ2 hQ3 hQ4cont hQpos hκpos hdetC4pos
  exact hanti (hp₁₂.trans hp₂z) hp₂z hp₁₂

end PF4.Advancement.CoordinatePsiDecrease

#print axioms PF4.Advancement.CoordinatePsiDecrease.coordinatePsi_strictAntiOn_Iio_from_determinantC4
#print axioms PF4.Advancement.CoordinatePsiDecrease.coordinatePsi_decreases_on_ordered_points_from_determinantC4
