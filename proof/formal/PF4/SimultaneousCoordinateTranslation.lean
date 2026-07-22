import PF4.PaperObjectClosure

set_option linter.style.header false

/-!
# Simultaneous translation in the actual curvature coordinate

This module closes the multivariable chain-rule seam in PO-0025.  Translation
is constructed from literal original-variable endpoint curves; no inverse is
differentiated outside the actual coordinate range.
-/

namespace PF4.SimultaneousCoordinateTranslation

open PF4.CoordinateSignBridge PF4.Curvature
open PF4.CurvatureCoordinateRealization PF4.PaperObjectClosure
open PF4.TranslationQuotientPsi PF4.TransportObject

/-- An original-variable translation has coordinate velocity `q`. -/
theorem hasDerivAt_kernelCoordinate_translate
    {S q : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (u a : ℝ) :
    HasDerivAt (fun h => kernelCoordinate S (u + h)) (q (u + a)) a := by
  have hinner : HasDerivAt (fun h : ℝ => u + h) 1 a := by
    simpa only [id_eq] using (hasDerivAt_id a).const_add u
  have hcomp := (hasDerivAt_kernelCoordinate hS (u + a)).comp a hinner
  have hg : HasDerivAt (fun h => kernelCoordinate S (u + h))
      (q (u + a) * 1) a :=
    hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  exact hg.congr_deriv (mul_one _)

/-- Along curves whose velocities are the coordinate vector field, the chord
slope derivative is its endpoint-speed sum minus the maintained chord moment.
-/
theorem hasDerivAt_chordSlope_along_coordinateTranslation
    {Q Q1 p z : ℝ → ℝ} {a : ℝ}
    (hp : HasDerivAt p (Q (p a)) a)
    (hz : HasDerivAt z (Q (z a)) a)
    (hQp : HasDerivAt Q (Q1 (p a)) (p a))
    (hQz : HasDerivAt Q (Q1 (z a)) (z a))
    (hgap : z a - p a ≠ 0) :
    HasDerivAt (fun h => chordSlope Q (p h) (z h))
      (Q (p a) + Q (z a) - chordMoment Q Q1 (p a) (z a)) a := by
  have hQpc := hQp.comp a hp
  have hQzc := hQz.comp a hz
  have hnum := hQzc.sub hQpc
  have hden := hz.sub hp
  have hraw := hnum.fun_div hden hgap
  apply hraw.congr_deriv
  simp only [PF4.TransportObject.chordMoment, Function.comp_apply, Pi.sub_apply]
  field_simp [hgap]
  ring

/-- The endpoint vector field differentiates the maintained `Lambda` to the
maintained simultaneous-translation formula `T Lambda`. -/
theorem hasDerivAt_coordinateLambda_along_translation
    {Q Q1 p z w : ℝ → ℝ} {a : ℝ}
    (hp : HasDerivAt p (Q (p a)) a)
    (hz : HasDerivAt z (Q (z a)) a)
    (hw : HasDerivAt w (Q (w a)) a)
    (hQp : HasDerivAt Q (Q1 (p a)) (p a))
    (hQz : HasDerivAt Q (Q1 (z a)) (z a))
    (hQw : HasDerivAt Q (Q1 (w a)) (w a))
    (hpz : z a - p a ≠ 0) (hzw : w a - z a ≠ 0) :
    HasDerivAt (fun h => coordinateLambda Q (p h) (z h) (w h))
      (coordinateTLambda Q Q1 (p a) (z a) (w a)) a := by
  have hpzD := hasDerivAt_chordSlope_along_coordinateTranslation
    hp hz hQp hQz hpz
  have hzwD := hasDerivAt_chordSlope_along_coordinateTranslation
    hz hw hQz hQw hzw
  have hraw := ((hw.sub hp).add hpzD).sub hzwD
  apply hraw.congr_deriv
  simp only [PF4.CoordinateSignBridge.coordinateTLambda]
  ring

/-- The exact translation derivative of `delta`.  The term
`-Q(p) * (2-Q''(p))` records the derivative of the nonconstant endpoint speed
and is the term lost by an illegal constant-vector-field commutation. -/
theorem hasDerivAt_coordinateDelta_along_translation
    {Q Q1 Q2 p z : ℝ → ℝ} {a : ℝ}
    (hp : HasDerivAt p (Q (p a)) a)
    (hz : HasDerivAt z (Q (z a)) a)
    (hQp : HasDerivAt Q (Q1 (p a)) (p a))
    (hQz : HasDerivAt Q (Q1 (z a)) (z a))
    (hQ1p : HasDerivAt Q1 (Q2 (p a)) (p a))
    (hgap : z a - p a ≠ 0) :
    HasDerivAt (fun h => coordinateDelta Q Q1 (p h) (z h))
      (coordinateTDelta Q Q1 Q2 (p a) (z a)) a := by
  have hchord := hasDerivAt_chordSlope_along_coordinateTranslation
    hp hz hQp hQz hgap
  have hgapD := hz.sub hp
  have hQ1pc := hQ1p.comp a hp
  have hnum := (hgapD.add hQ1pc).sub hchord
  have hraw := hnum.fun_div hgapD hgap
  apply hraw.congr_deriv
  simp only [PF4.Curvature.coordinateDelta,
    PF4.CoordinateSignBridge.coordinateTDelta, PF4.Curvature.curvature,
    Function.comp_apply, Pi.add_apply, Pi.sub_apply]
  field_simp [hgap]
  ring

/-! ## Literal actual-kernel specialization -/

/-- The literal coordinate endpoint curve. -/
noncomputable def actualEndpointCurve (u : ℝ) : ℝ → ℝ :=
  fun a => kernelCoordinate actualKernelSlope (u + a)

theorem hasDerivAt_actualEndpointCurve (u a : ℝ) :
    HasDerivAt (actualEndpointCurve u)
      (actualCoordinateQ (actualEndpointCurve u a)) a := by
  have h := hasDerivAt_kernelCoordinate_translate
    hasDerivAt_actualKernelSlope u a
  rw [show actualCoordinateQ (actualEndpointCurve u a) =
      actualKernelCurvature (u + a) by
    unfold actualCoordinateQ actualEndpointCurve
    exact coordinateQ_apply_kernelCoordinate hasDerivAt_actualKernelSlope
      actualKernelCurvature_pos (u + a)]
  exact h

/-- PO-0025: every literal endpoint, `Lambda`, and `delta` follows the named
coordinate translation field.  The final equality identifies the maintained
`Psi = Lambda + T Lambda / Lambda` with the derivative just constructed.
All statements hold at every real translation parameter. -/
theorem actual_simultaneousCoordinateTranslation
    {u v w a : ℝ} (huv : u < v) (hvw : v < w) :
    HasDerivAt (actualEndpointCurve u)
        (actualCoordinateQ (actualEndpointCurve u a)) a ∧
    HasDerivAt (actualEndpointCurve v)
        (actualCoordinateQ (actualEndpointCurve v a)) a ∧
    HasDerivAt (actualEndpointCurve w)
        (actualCoordinateQ (actualEndpointCurve w a)) a ∧
    HasDerivAt
      (fun h => coordinateLambda actualCoordinateQ
        (actualEndpointCurve u h) (actualEndpointCurve v h)
        (actualEndpointCurve w h))
      (coordinateTLambda actualCoordinateQ actualCoordinateQ1
        (actualEndpointCurve u a) (actualEndpointCurve v a)
        (actualEndpointCurve w a)) a ∧
    HasDerivAt
      (fun h => coordinateDelta actualCoordinateQ actualCoordinateQ1
        (actualEndpointCurve u h) (actualEndpointCurve v h))
      (coordinateTDelta actualCoordinateQ actualCoordinateQ1 actualCoordinateQ2
        (actualEndpointCurve u a) (actualEndpointCurve v a)) a ∧
    coordinatePsi actualCoordinateQ actualCoordinateQ1
        (actualEndpointCurve u a) (actualEndpointCurve v a)
        (actualEndpointCurve w a) =
      coordinateLambda actualCoordinateQ
          (actualEndpointCurve u a) (actualEndpointCurve v a)
          (actualEndpointCurve w a) +
        deriv (fun h => coordinateLambda actualCoordinateQ
          (actualEndpointCurve u h) (actualEndpointCurve v h)
          (actualEndpointCurve w h)) a /
        coordinateLambda actualCoordinateQ
          (actualEndpointCurve u a) (actualEndpointCurve v a)
          (actualEndpointCurve w a) := by
  let p := actualEndpointCurve u
  let z := actualEndpointCurve v
  let w' := actualEndpointCurve w
  have hp := hasDerivAt_actualEndpointCurve u a
  have hz := hasDerivAt_actualEndpointCurve v a
  have hw := hasDerivAt_actualEndpointCurve w a
  have hjp := coordinateJet_on_range hasDerivAt_actualKernelSlope
    actualKernelCurvature_derivativeTower.1
    actualKernelCurvature_derivativeTower.2.1
    actualKernelCurvature_derivativeTower.2.2.1
    actualKernelCurvature_derivativeTower.2.2.2
    actualKernelCurvature_pos (p a) (by
      exact ⟨u + a, rfl⟩)
  have hjz := coordinateJet_on_range hasDerivAt_actualKernelSlope
    actualKernelCurvature_derivativeTower.1
    actualKernelCurvature_derivativeTower.2.1
    actualKernelCurvature_derivativeTower.2.2.1
    actualKernelCurvature_derivativeTower.2.2.2
    actualKernelCurvature_pos (z a) (by
      exact ⟨v + a, rfl⟩)
  have hjw := coordinateJet_on_range hasDerivAt_actualKernelSlope
    actualKernelCurvature_derivativeTower.1
    actualKernelCurvature_derivativeTower.2.1
    actualKernelCurvature_derivativeTower.2.2.1
    actualKernelCurvature_derivativeTower.2.2.2
    actualKernelCurvature_pos (w' a) (by
      exact ⟨w + a, rfl⟩)
  have hpz : z a - p a ≠ 0 := by
    apply sub_ne_zero.mpr
    exact (kernelCoordinate_strictMono hasDerivAt_actualKernelSlope
      actualKernelCurvature_pos (by linarith : u + a < v + a)).ne'
  have hzw : w' a - z a ≠ 0 := by
    apply sub_ne_zero.mpr
    exact (kernelCoordinate_strictMono hasDerivAt_actualKernelSlope
      actualKernelCurvature_pos (by linarith : v + a < w + a)).ne'
  have hLambda := hasDerivAt_coordinateLambda_along_translation hp hz hw
    hjp.1 hjz.1 hjw.1 hpz hzw
  have hDelta := hasDerivAt_coordinateDelta_along_translation hp hz
    hjp.1 hjz.1 hjp.2.1 hpz
  refine ⟨hp, hz, hw, hLambda, hDelta, ?_⟩
  unfold coordinatePsi
  rw [hLambda.deriv]
  rfl

end PF4.SimultaneousCoordinateTranslation
