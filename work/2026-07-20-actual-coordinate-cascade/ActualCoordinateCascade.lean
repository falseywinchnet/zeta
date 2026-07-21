import PF4.LocalFinalAssembly
import PF4.TranslationQuotientPsi
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option linter.style.header false

/-!
# Actual-coordinate decrease and the terminal cascade

This advancement candidate turns the maintained pointwise sign
`Q(y(x)) * ∂ᵧ Psi(y(x); y(m), y(r)) < 0` into strict decrease in the
original variable `x`.  It then inserts that decrease directly into the exact
terminal translation-quotient factorization.  No coordinate realization,
global coordinate monotonicity, terminal sign, gap object, or central identity
is assumed.
-/

namespace PF4.Advancement.ActualCoordinateCascade

open Set
open PF4.Curvature PF4.CoordinateSignBridge
open PF4.CurvatureCoordinateRealization
open PF4.TranslationQuotientSigns PF4.TranslationQuotientTower
open PF4.TranslationQuotientPsi

/-- For fixed ordered original right endpoints, the maintained actual-range
coordinate `Psi` is strictly decreasing after composition with `y = -S`.

The derivative of this composition is exactly the product whose strict
negativity was closed by `PF4.LocalFinalAssembly.actualCoordinatePartialXiPsi_neg`.
-/
theorem actualCoordinatePsi_strictAntiOn_Iio
    {S q q1 q2 q3 q4 : ℝ → ℝ} {m r : ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hq3 : ∀ u, HasDerivAt q3 (q4 u) u)
    (hq4cont : Continuous q4)
    (hqpos : ∀ u, 0 < q u)
    (hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u)
    (hC4pos : ∀ u, 0 < kernelDeterminantC4 q q1 q2 q3 q4 u)
    (hmr : m < r) :
    StrictAntiOn
      (fun x => coordinatePsi (coordinateQ S q) (coordinateQ1 S q q1)
        (kernelCoordinate S x) (kernelCoordinate S m) (kernelCoordinate S r))
      (Iio m) := by
  let ψ := fun y => coordinatePsi (coordinateQ S q) (coordinateQ1 S q q1)
    y (kernelCoordinate S m) (kernelCoordinate S r)
  let g := fun x => ψ (kernelCoordinate S x)
  have hderiv : ∀ x ∈ Iio m, deriv g x < 0 := by
    intro x hx
    have hmul := PF4.LocalFinalAssembly.actualCoordinatePartialXiPsi_neg
      hS hq hq1 hq2 hq3 hq4cont hqpos hF2pos hC4pos hx hmr
    have hψneg : deriv ψ (kernelCoordinate S x) < 0 := by
      dsimp [ψ] at hmul ⊢
      rw [coordinateQ_apply_kernelCoordinate hS hqpos] at hmul
      nlinarith [hqpos x]
    have hψderiv : HasDerivAt ψ (deriv ψ (kernelCoordinate S x))
        (kernelCoordinate S x) :=
      (differentiableAt_of_deriv_ne_zero hψneg.ne).hasDerivAt
    have hgderiv : HasDerivAt g
        (deriv ψ (kernelCoordinate S x) * q x) x := by
      dsimp [g]
      exact hψderiv.comp x (hasDerivAt_kernelCoordinate hS x)
    rw [hgderiv.deriv]
    nlinarith [hψneg, hqpos x]
  have hcont : ContinuousOn g (Iio m) := by
    intro x hx
    exact (differentiableAt_of_deriv_ne_zero (hderiv x hx).ne).continuousAt
      |>.continuousWithinAt
  change StrictAntiOn g (Iio m)
  apply strictAntiOn_of_deriv_neg (convex_Iio m) hcont
  intro x hx
  have hx' : x ∈ Iio m := by simpa only [interior_Iio] using hx
  exact hderiv x hx'

/-- Ordered-point form of actual-range coordinate-`Psi` decrease.  Every
coordinate argument in the conclusion is constructed from an original point;
there is no assertion about unattained coordinate values. -/
theorem actualCoordinatePsi_decreases_on_ordered_points
    {S q q1 q2 q3 q4 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hq3 : ∀ u, HasDerivAt q3 (q4 u) u)
    (hq4cont : Continuous q4)
    (hqpos : ∀ u, 0 < q u)
    (hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u)
    (hC4pos : ∀ u, 0 < kernelDeterminantC4 q q1 q2 q3 q4 u)
    {x₁ x₂ m r : ℝ} (hx₁₂ : x₁ < x₂) (hx₂m : x₂ < m) (hmr : m < r) :
    coordinatePsi (coordinateQ S q) (coordinateQ1 S q q1)
        (kernelCoordinate S x₂) (kernelCoordinate S m) (kernelCoordinate S r) <
      coordinatePsi (coordinateQ S q) (coordinateQ1 S q q1)
        (kernelCoordinate S x₁) (kernelCoordinate S m) (kernelCoordinate S r) := by
  have hanti := actualCoordinatePsi_strictAntiOn_Iio hS hq hq1 hq2 hq3
    hq4cont hqpos hF2pos hC4pos hmr
  exact hanti (hx₁₂.trans hx₂m) hx₂m hx₁₂

/-- The lower three-point `Lambda` is positive on ordered original points.
This closes the lower cascade sign from the actual coordinate construction:
`lowerLambda` is the coordinate `Lambda`, whose positive integral formula is
available on the compact coordinate interval. -/
theorem lowerLambda_pos_of_actualCoordinate
    {S q q1 q2 q3 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hqpos : ∀ u, 0 < q u)
    (hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u)
    {x m r : ℝ} (hxm : x < m) (hmr : m < r) :
    0 < lowerLambda S q x m r := by
  let Q := coordinateQ S q
  let Q1 := coordinateQ1 S q q1
  let Q2 := coordinateQ2 S q q1 q2
  let p := kernelCoordinate S x
  let z := kernelCoordinate S m
  let w := kernelCoordinate S r
  have hmono := kernelCoordinate_strictMono hS hqpos
  have hpz : p < z := hmono hxm
  have hzw : z < w := hmono hmr
  have hrange : Icc p w ⊆ Set.range (kernelCoordinate S) := by
    dsimp [p, w]
    exact PF4.RangeLocalFinalAssembly.kernelCoordinate_Icc_subset_range hS hqpos
  have hQ : ∀ y ∈ Icc p w, HasDerivAt Q (Q1 y) y := by
    intro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q, Q1]
    rw [coordinateQ1_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ hS hq hqpos u
  have hQ1 : ∀ y ∈ Icc p w, HasDerivAt Q1 (Q2 y) y := by
    intro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q1, Q2]
    rw [coordinateQ2_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ1 hS hq hq1 hqpos u
  have hQ2cont : ContinuousOn Q2 (Icc p w) := by
    intro y hy
    rcases hrange hy with ⟨u, rfl⟩
    exact (hasDerivAt_coordinateQ2 hS hq hq1 hq2 hqpos u).continuousAt
      |>.continuousWithinAt
  have hkcont : ContinuousOn (curvature Q2) (Icc p w) := by
    unfold curvature
    exact continuousOn_const.sub hQ2cont
  have hkpos : ∀ y ∈ Icc p w, 0 < curvature Q2 y := by
    intro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q2]
    exact curvature_coordinateQ2_pos_on_range hS hqpos hF2pos u
  have hcoord : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw hQ hQ1 hkcont hkpos
  have hQreal : ∀ u, Q (kernelCoordinate S u) = q u := by
    intro u
    exact coordinateQ_apply_kernelCoordinate hS hqpos u
  rw [lowerLambda_eq_coordinateLambda hQreal]
  exact hcoord

/-- The actual constructed curvature coordinate closes the terminal
translation-quotient cascade.  The only remaining sign inputs are the named
analytic kernel inequalities `q > 0`, `F₂ > 0`, and `det C₄ > 0`.

In particular, coordinate realization and coordinate-`Psi` decrease are
conclusions used inside this proof, not premises of the theorem.
-/
theorem terminalQuotD_pos_of_actualCoordinateCascade
    {Phi Phi1 Phi2 Phi3 q1 q2 q3 q4 : ℝ → ℝ}
    (hPhi : ∀ u, HasDerivAt Phi (Phi1 u) u)
    (hPhi1 : ∀ u, HasDerivAt Phi1 (Phi2 u) u)
    (hPhi2 : ∀ u, HasDerivAt Phi2 (Phi3 u) u)
    (hPhipos : ∀ u, 0 < Phi u)
    (hqpos : ∀ u, 0 < kernelCurvature Phi Phi1 Phi2 u)
    (hq : ∀ u, HasDerivAt (kernelCurvature Phi Phi1 Phi2) (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hq3 : ∀ u, HasDerivAt q3 (q4 u) u)
    (hq4cont : Continuous q4)
    (hF2pos : ∀ u,
      0 < kernelF2 (kernelCurvature Phi Phi1 Phi2) q1 q2 u)
    (hC4pos : ∀ u,
      0 < kernelDeterminantC4
        (kernelCurvature Phi Phi1 Phi2) q1 q2 q3 q4 u)
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    ∀ t, 0 < terminalQuotD Phi Phi1 Phi2 Phi3 a c b d t := by
  let S := logSlope Phi Phi1
  let q := kernelCurvature Phi Phi1 Phi2
  let Q := coordinateQ S q
  let Q1 := coordinateQ1 S q q1
  have hS : ∀ u, HasDerivAt S (-q u) u := by
    intro u
    exact hasDerivAt_logSlope hPhi hPhi1 hPhipos u
  have hLambda : ∀ x m r, x < m → m < r →
      0 < lowerLambda S q x m r := by
    intro x m r hxm hmr
    exact lowerLambda_pos_of_actualCoordinate hS hq hq1 hq2 hqpos hF2pos
      hxm hmr
  have hfirst := firstQuotD_pos_of_kernelCurvature_pos
    hPhi hPhi1 hPhipos hqpos hac
  have hsecondB := secondQuotD_pos_of_lowerLambda_pos
    hPhi hPhi1 hPhipos hqpos hLambda hac hcb
  have hsecondD := secondQuotD_pos_of_lowerLambda_pos
    hPhi hPhi1 hPhipos hqpos hLambda hac (hcb.trans hbd)
  have hSanti := logSlope_strictAnti_of_kernelCurvature_pos
    hPhi hPhi1 hPhipos hqpos
  have hchord : ∀ {u v : ℝ}, u < v → slopeChord S u v ≠ 0 := by
    intro u v huv
    exact (slopeChord_pos_of_lt hSanti huv).ne'
  have hQreal : ∀ u, Q (kernelCoordinate S u) = q u := by
    intro u
    exact coordinateQ_apply_kernelCoordinate hS hqpos u
  have hQ1real : ∀ u, Q1 (kernelCoordinate S u) = q1 u / q u := by
    intro u
    exact coordinateQ1_apply_kernelCoordinate hS hqpos u
  intro t
  have hAb : ∀ s, slopeChord S (s - b) (s - a) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAd : ∀ s, slopeChord S (s - d) (s - a) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAc : ∀ s, slopeChord S (s - c) (s - a) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAbc : ∀ s, slopeChord S (s - b) (s - c) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAdc : ∀ s, slopeChord S (s - d) (s - c) ≠ 0 :=
    fun s => hchord (by linarith)
  have hLambdaB : ∀ s, lowerLambda S q (s - b) (s - c) (s - a) ≠ 0 :=
    fun s => (hLambda _ _ _ (by linarith) (by linarith)).ne'
  have hLambdaD : ∀ s, lowerLambda S q (s - d) (s - c) (s - a) ≠ 0 :=
    fun s => (hLambda _ _ _ (by linarith) (by linarith)).ne'
  rw [terminalQuotD_eq_terminalQuot_mul_coordinatePsi_sub hPhi hPhi1 hPhi2
    hPhipos hqpos hq hQreal hQ1real a c b d hfirst hAb hAd hAc hAbc hAdc
    hLambdaB hLambdaD hsecondB]
  have hPsi : coordinatePsi Q Q1
        (kernelCoordinate S (t - b)) (kernelCoordinate S (t - c))
        (kernelCoordinate S (t - a)) <
      coordinatePsi Q Q1
        (kernelCoordinate S (t - d)) (kernelCoordinate S (t - c))
        (kernelCoordinate S (t - a)) := by
    exact actualCoordinatePsi_decreases_on_ordered_points
      hS hq hq1 hq2 hq3 hq4cont hqpos hF2pos hC4pos
      (by linarith) (by linarith) (by linarith)
  exact mul_pos (div_pos (hsecondD t) (hsecondB t)) (sub_pos.mpr hPsi)

end PF4.Advancement.ActualCoordinateCascade

#print axioms PF4.Advancement.ActualCoordinateCascade.actualCoordinatePsi_strictAntiOn_Iio
#print axioms PF4.Advancement.ActualCoordinateCascade.actualCoordinatePsi_decreases_on_ordered_points
#print axioms PF4.Advancement.ActualCoordinateCascade.lowerLambda_pos_of_actualCoordinate
#print axioms PF4.Advancement.ActualCoordinateCascade.terminalQuotD_pos_of_actualCoordinateCascade
