import PF4.Expectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option linter.style.header false

/-!
Candidate formalization of PO-0038.  This file lives in advancement work until
a later refine round audits and integrates it.
-/

namespace PF4.TransportObjectCandidate

open MeasureTheory Set
open scoped Interval
open PF4.Densities PF4.Normalization PF4.Measures PF4.Expectation

/-- The paper's primitive `A₀`, with named jet functions kept independent. -/
noncomputable def paperPrimitive
    (Q Q1 κ κ1 : ℝ → ℝ) (y : ℝ) : ℝ :=
  3 * (y - Q1 y) - Q y * (κ1 y / κ y)

/-- The first elementary primitive in the transport cancellation. -/
noncomputable def transportH
    (Q Q1 Q2 : ℝ → ℝ) (y : ℝ) : ℝ :=
  3 * y ^ 2 - 3 * Q y - 3 * y * Q1 y + Q1 y ^ 2 + Q y * Q2 y

/-- The second elementary primitive in the transport cancellation. -/
noncomputable def transportJ
    (Q Q1 : ℝ → ℝ) (y : ℝ) : ℝ :=
  y ^ 3 - 3 * y * Q y + Q y * Q1 y

theorem transportJ_hasDerivAt
    {Q Q1 Q2 : ℝ → ℝ} {y : ℝ}
    (hQ : HasDerivAt Q (Q1 y) y)
    (hQ1 : HasDerivAt Q1 (Q2 y) y) :
    HasDerivAt (transportJ Q Q1) (transportH Q Q1 Q2 y) y := by
  change HasDerivAt
    (fun x => x ^ 3 - 3 * x * Q x + Q x * Q1 x)
    (3 * y ^ 2 - 3 * Q y - 3 * y * Q1 y + Q1 y ^ 2 + Q y * Q2 y) y
  convert! (hasDerivAt_pow 3 y).sub
      (((hasDerivAt_id y).mul hQ).const_mul 3) |>.add
      (hQ.mul hQ1) using 1
  · funext x
    simp [id_eq]
    ring
  · simp [id_eq]
    ring

theorem transportH_hasDerivAt
    {Q Q1 Q2 Q3 κ κ1 : ℝ → ℝ} {y : ℝ}
    (hQ : HasDerivAt Q (Q1 y) y)
    (hQ1 : HasDerivAt Q1 (Q2 y) y)
    (hQ2 : HasDerivAt Q2 (Q3 y) y)
    (hκ : κ y = 2 - Q2 y) (hκ1 : κ1 y = -Q3 y)
    (hκne : κ y ≠ 0) :
    HasDerivAt (transportH Q Q1 Q2)
      (κ y * paperPrimitive Q Q1 κ κ1 y) y := by
  have hraw : HasDerivAt (transportH Q Q1 Q2)
      (6 * y - 6 * Q1 y - 3 * y * Q2 y +
        3 * Q1 y * Q2 y + Q y * Q3 y) y := by
    change HasDerivAt
      (fun x => 3 * x ^ 2 - 3 * Q x - 3 * x * Q1 x +
        Q1 x ^ 2 + Q x * Q2 x) _ y
    convert!
      (hasDerivAt_pow 2 y).const_mul 3 |>.sub
        (hQ.const_mul 3) |>.sub
        (((hasDerivAt_id y).mul hQ1).const_mul 3) |>.add
        (hQ1.pow 2) |>.add (hQ.mul hQ2) using 1
    · funext x
      simp [id_eq]
      ring
    · simp [id_eq]
      ring
  convert hraw using 1
  have hden : 2 - Q2 y ≠ 0 := by
    rw [← hκ]
    exact hκne
  rw [paperPrimitive, hκ, hκ1]
  field_simp [hden]
  ring

/-- FTC form for the left-decreasing triangular weight. -/
theorem integral_decreasing_linear_mul_deriv
    {G H J : ℝ → ℝ} {a b : ℝ}
    (hH : ∀ t, HasDerivAt H (G t) t)
    (hJ : ∀ t, HasDerivAt J (H t) t)
    (hint : IntervalIntegrable (fun t => (b - t) * G t) volume a b) :
    (∫ t in a..b, (b - t) * G t) =
      (J b - J a) - (b - a) * H a := by
  have hP : ∀ t, HasDerivAt (fun x => (b - x) * H x + J x)
      ((b - t) * G t) t := by
    intro t
    convert! (((hasDerivAt_id t).const_sub b).mul (hH t)).add
      (hJ t) using 1
    simp [id_eq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hP t) hint]
  ring

/-- FTC form for the left-increasing triangular weight. -/
theorem integral_increasing_linear_mul_deriv
    {G H J : ℝ → ℝ} {a b : ℝ}
    (hH : ∀ t, HasDerivAt H (G t) t)
    (hJ : ∀ t, HasDerivAt J (H t) t)
    (hint : IntervalIntegrable (fun t => (t - a) * G t) volume a b) :
    (∫ t in a..b, (t - a) * G t) =
      (b - a) * H b - (J b - J a) := by
  have hP : ∀ t, HasDerivAt (fun x => (x - a) * H x - J x)
      ((t - a) * G t) t := by
    intro t
    convert! (((hasDerivAt_id t).sub_const a).mul (hH t)).sub
      (hJ t) using 1
    simp [id_eq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hP t) hint]
  ring

/-- The endpoint expression obtained from the two actual expectations before
the separate endpoint cancellation is applied. -/
noncomputable def expectationEndpoint
    (H J : ℝ → ℝ) (p z w L R δ Λ : ℝ) : ℝ :=
  (-(J z - J p) / L + (J w - J z) / R) / Λ +
    (L * H p - (J z - J p)) / (L ^ 2 * δ)

/-- The concrete Bochner expectation difference reduces to the explicit
endpoint expression.  The internal `H z` terms are retained until the last
field calculation and cancel there. -/
theorem concrete_expectationDifference_eq_expectationEndpoint
    {Q Q1 Q2 Q3 κ κ1 : ℝ → ℝ} {p z w L R δ Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hLgap : L = z - p) (hRgap : R = w - z)
    (hQ : ∀ t, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t, HasDerivAt Q2 (Q3 t) t)
    (hκeq : ∀ t, κ t = 2 - Q2 t) (hκ1eq : ∀ t, κ1 t = -Q3 t)
    (hκ : ∀ t, 0 < κ t) (hκcont : Continuous κ)
    (hAcont : Continuous (paperPrimitive Q Q1 κ κ1))
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hΛ : 0 < Λ) :
    measureExpectation (nuMeasure κ p z w L R Λ)
        (paperPrimitive Q Q1 κ κ1) -
      measureExpectation (muMeasure κ p z L δ)
        (paperPrimitive Q Q1 κ κ1) =
      expectationEndpoint (transportH Q Q1 Q2) (transportJ Q Q1)
        p z w L R δ Λ := by
  let A := paperPrimitive Q Q1 κ κ1
  let H := transportH Q Q1 Q2
  let J := transportJ Q Q1
  let G : ℝ → ℝ := fun t => κ t * A t
  have hκinterval : ∀ t ∈ Icc p w, 0 < κ t := fun t _ => hκ t
  have hκleft : ∀ t ∈ Icc p z, 0 < κ t := fun t _ => hκ t
  have hH : ∀ t, HasDerivAt H (G t) t := by
    intro t
    exact transportH_hasDerivAt (hQ t) (hQ1 t) (hQ2 t)
      (hκeq t) (hκ1eq t) (hκ t).ne'
  have hJ : ∀ t, HasDerivAt J (H t) t := by
    intro t
    exact transportJ_hasDerivAt (hQ t) (hQ1 t)
  have hGcont : Continuous G := hκcont.mul hAcont
  have hdecLeft :
      (∫ t in p..z, (z - t) * G t) =
        (J z - J p) - (z - p) * H p :=
    integral_decreasing_linear_mul_deriv hH hJ
      ((show Continuous (fun t : ℝ => (z - t) * G t) by fun_prop).intervalIntegrable p z)
  have hincLeft :
      (∫ t in p..z, (t - p) * G t) =
        (z - p) * H z - (J z - J p) :=
    integral_increasing_linear_mul_deriv hH hJ
      ((show Continuous (fun t : ℝ => (t - p) * G t) by fun_prop).intervalIntegrable p z)
  have hdecRight :
      (∫ t in z..w, (w - t) * G t) =
        (J w - J z) - (w - z) * H z :=
    integral_decreasing_linear_mul_deriv hH hJ
      ((show Continuous (fun t : ℝ => (w - t) * G t) by fun_prop).intervalIntegrable z w)
  have hμ := muExpectation_eq_interval
    (A := A) hpz hκleft hκcont hL hδ
  have hν := nuExpectation_eq_intervals
    (A := A) hpz hzw hκinterval hκcont hAcont hL hR hΛ
  have hμIntegral :
      (∫ t in p..z, A t * leftMuDensity κ z L δ t) =
        (∫ t in p..z, (z - t) * G t) / (L ^ 2 * δ) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [leftMuDensity, G, A]
    ring
  have hνLeftIntegral :
      (∫ t in p..z, A t * leftNuDensity κ p L Λ t) =
        (∫ t in p..z, (t - p) * G t) / (L * Λ) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [leftNuDensity, G, A]
    ring
  have hνRightIntegral :
      (∫ t in z..w, A t * rightNuDensity κ w R Λ t) =
        (∫ t in z..w, (w - t) * G t) / (R * Λ) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [rightNuDensity, G, A]
    ring
  rw [hν, hμ, hμIntegral, hνLeftIntegral, hνRightIntegral,
    hdecLeft, hincLeft, hdecRight]
  change _ = expectationEndpoint H J p z w L R δ Λ
  rw [← hLgap, ← hRgap]
  rw [expectationEndpoint]
  field_simp [hL.ne', hR.ne', hδ.ne', hΛ.ne']
  ring

/-- Secant slope `Q[c,d]` used in the paper's endpoint expansion. -/
noncomputable def chordSlope (Q : ℝ → ℝ) (c d : ℝ) : ℝ :=
  (Q d - Q c) / (d - c)

/-- The endpoint chord moment `U(c,d)` from S08. -/
noncomputable def chordMoment
    (Q Q1 : ℝ → ℝ) (c d : ℝ) : ℝ :=
  Q c + Q d - (Q d * Q1 d - Q c * Q1 c) / (d - c) +
    (Q d - Q c) ^ 2 / (d - c) ^ 2

/-- The paper's expanded transport object, defined without reference to any
measure or expectation. -/
noncomputable def expandedTransportK
    (Q Q1 Q2 : ℝ → ℝ) (p z w L _R δ Λ : ℝ) : ℝ :=
  Λ + Q1 p - chordSlope Q p z +
    (chordMoment Q Q1 p z - chordMoment Q Q1 z w) / Λ +
    (chordMoment Q Q1 p z - Q p * (2 - Q2 p)) / (L * δ)

/-- The cleared-denominator endpoint cancellation from Appendix A3.  Endpoint
jets remain arbitrary; the only relations used are the displayed gap,
`delta`, and `Lambda` formulas. -/
theorem expectationEndpoint_eq_expandedTransportK
    {Q Q1 Q2 : ℝ → ℝ} {p z w L R δ Λ : ℝ}
    (hLgap : L = z - p) (hRgap : R = w - z)
    (hδid : δ = (L + Q1 p - chordSlope Q p z) / L)
    (hΛid : Λ = L + R + chordSlope Q p z - chordSlope Q z w)
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hΛ : 0 < Λ) :
    expectationEndpoint (transportH Q Q1 Q2) (transportJ Q Q1)
        p z w L R δ Λ =
      expandedTransportK Q Q1 Q2 p z w L R δ Λ := by
  have hz : z = p + L := by linarith
  have hw : w = p + L + R := by linarith
  subst z
  subst w
  simp only [expectationEndpoint, expandedTransportK, transportH, transportJ,
    chordSlope, chordMoment]
  field_simp [hL.ne', hR.ne', hδ.ne', hΛ.ne']
  rw [hδid, hΛid]
  simp only [chordSlope]
  field_simp [hL.ne', hR.ne']
  ring

/-- Candidate closure of PO-0038: the independently expanded paper object is
the difference of the two actual Bochner expectations. -/
theorem expandedTransportK_eq_concrete_expectationDifference
    {Q Q1 Q2 Q3 κ κ1 : ℝ → ℝ} {p z w L R δ Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hLgap : L = z - p) (hRgap : R = w - z)
    (hδid : δ = (L + Q1 p - chordSlope Q p z) / L)
    (hΛid : Λ = L + R + chordSlope Q p z - chordSlope Q z w)
    (hQ : ∀ t, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t, HasDerivAt Q2 (Q3 t) t)
    (hκeq : ∀ t, κ t = 2 - Q2 t) (hκ1eq : ∀ t, κ1 t = -Q3 t)
    (hκ : ∀ t, 0 < κ t) (hκcont : Continuous κ)
    (hAcont : Continuous (paperPrimitive Q Q1 κ κ1))
    (hL : 0 < L) (hR : 0 < R) (hδ : 0 < δ) (hΛ : 0 < Λ) :
    expandedTransportK Q Q1 Q2 p z w L R δ Λ =
      measureExpectation (nuMeasure κ p z w L R Λ)
          (paperPrimitive Q Q1 κ κ1) -
        measureExpectation (muMeasure κ p z L δ)
          (paperPrimitive Q Q1 κ κ1) := by
  rw [concrete_expectationDifference_eq_expectationEndpoint hpz hzw
    hLgap hRgap hQ hQ1 hQ2 hκeq hκ1eq hκ hκcont hAcont hL hR hδ hΛ]
  exact (expectationEndpoint_eq_expandedTransportK hLgap hRgap hδid hΛid
    hL hR hδ hΛ).symm

end PF4.TransportObjectCandidate

#print axioms PF4.TransportObjectCandidate.transportJ_hasDerivAt
#print axioms PF4.TransportObjectCandidate.transportH_hasDerivAt
#print axioms PF4.TransportObjectCandidate.concrete_expectationDifference_eq_expectationEndpoint
#print axioms PF4.TransportObjectCandidate.expectationEndpoint_eq_expandedTransportK
#print axioms PF4.TransportObjectCandidate.expandedTransportK_eq_concrete_expectationDifference
