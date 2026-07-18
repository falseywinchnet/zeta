import PF4.Transport
import PF4.TransportObject

set_option linter.style.header false

/-!
# Coordinate sign bridge

The objects below are endpoint formulas. The derivative theorem does not take
the desired sign identity or a detached numerator as a premise.
-/

namespace PF4.Advancement.CoordinateSignBridge

open Set
open PF4.Cumulative PF4.Curvature PF4.Transport PF4.TransportObject

/-- Simultaneous translation of the coordinate normalizer, in its exact
endpoint-moment form. -/
noncomputable def coordinateTLambda
    (Q Q1 : ℝ → ℝ) (p z w : ℝ) : ℝ :=
  chordMoment Q Q1 z w - chordMoment Q Q1 p z

/-- Simultaneous translation of the left normalizer, in its exact endpoint
form. -/
noncomputable def coordinateTDelta
    (Q Q1 Q2 : ℝ → ℝ) (p z : ℝ) : ℝ :=
  (chordMoment Q Q1 p z -
      (Q z - Q p) * coordinateDelta Q Q1 p z -
      Q p * curvature Q2 p) / (z - p)

/-- The paper numerator, defined from the actual coordinate endpoint objects. -/
noncomputable def coordinateNumerator
    (Q Q1 Q2 : ℝ → ℝ) (p z w : ℝ) : ℝ :=
  let δ := coordinateDelta Q Q1 p z
  let Λ := coordinateLambda Q p z w
  δ * Λ ^ 2 + Q1 p * δ * Λ +
    Λ * coordinateTDelta Q Q1 Q2 p z -
    δ * coordinateTLambda Q Q1 p z w

/-- The three-point object `Psi = Lambda + T log Lambda`, written as
`Lambda + T Lambda / Lambda` before differentiating. -/
noncomputable def coordinatePsi
    (Q Q1 : ℝ → ℝ) (p z w : ℝ) : ℝ :=
  coordinateLambda Q p z w +
    coordinateTLambda Q Q1 p z w / coordinateLambda Q p z w

/-- The independently expanded transport object is exactly the logarithmic
rate `N/(delta Lambda)`. -/
theorem coordinateNumerator_eq_deltaLambda_mul_expandedTransportK
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z)
    (hδ : coordinateDelta Q Q1 p z ≠ 0)
    (hΛ : coordinateLambda Q p z w ≠ 0) :
    coordinateNumerator Q Q1 Q2 p z w =
      coordinateDelta Q Q1 p z * coordinateLambda Q p z w *
        expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
          (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) := by
  unfold coordinateNumerator coordinateTDelta coordinateTLambda
    expandedTransportK
  have hgap : z - p ≠ 0 := sub_ne_zero.mpr hpz.ne'
  field_simp [hgap, hδ, hΛ]
  unfold chordSlope curvature
  field_simp [hgap]
  ring

/-- Calculus core: once the actual left derivatives of `Lambda` and
`T Lambda` have been derived, differentiation of the independently defined
`Psi` produces the paper numerator with its exact sign. -/
theorem coordinatePsi_hasDerivAt_of_endpoint_derivatives
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ}
    (hΛ : coordinateLambda Q p z w ≠ 0)
    (hLambdaDeriv : HasDerivAt (fun x => coordinateLambda Q x z w)
      (-coordinateDelta Q Q1 p z) p)
    (hTLambdaDeriv : HasDerivAt (fun x => coordinateTLambda Q Q1 x z w)
      (-(Q1 p * coordinateDelta Q Q1 p z +
        coordinateTDelta Q Q1 Q2 p z)) p) :
    HasDerivAt (fun x => coordinatePsi Q Q1 x z w)
      (-coordinateNumerator Q Q1 Q2 p z w /
        coordinateLambda Q p z w ^ 2) p := by
  unfold coordinatePsi
  apply (hLambdaDeriv.add (hTLambdaDeriv.div hLambdaDeriv hΛ)).congr_deriv
  unfold coordinateNumerator
  field_simp [hΛ]
  ring

/-- The left derivative of the chord moment is the exact combination
`Q'(p) delta + T delta`; this is the endpoint form of the commutation step. -/
theorem chordMoment_left_hasDerivAt
    {Q Q1 Q2 : ℝ → ℝ} {p z : ℝ}
    (hpz : p < z)
    (hQ : HasDerivAt Q (Q1 p) p)
    (hQ1 : HasDerivAt Q1 (Q2 p) p) :
    HasDerivAt (fun x => chordMoment Q Q1 x z)
      (Q1 p * coordinateDelta Q Q1 p z +
        coordinateTDelta Q Q1 Q2 p z) p := by
  have hgap : HasDerivAt (fun x : ℝ => z - x) (-1) p := by
    simpa only [id_eq] using (hasDerivAt_id p).const_sub z
  have hgapne : z - p ≠ 0 := sub_ne_zero.mpr hpz.ne'
  have hQz : HasDerivAt (fun _ : ℝ => Q z) 0 p := hasDerivAt_const p (Q z)
  have hQ1z : HasDerivAt (fun _ : ℝ => Q1 z) 0 p := hasDerivAt_const p (Q1 z)
  have hnum := (hQz.mul hQ1z).sub (hQ.mul hQ1)
  have hquot := hnum.div hgap hgapne
  have hdiff := hQz.sub hQ
  have hsquareQuot := (hdiff.pow 2).div (hgap.pow 2) (pow_ne_zero 2 hgapne)
  have hraw := ((hQ.add hQz).sub hquot).add hsquareQuot
  rw [show (fun x => chordMoment Q Q1 x z) =
      ((Q + fun _ => Q z) -
          (((fun _ => Q z) * fun _ => Q1 z) - Q * Q1) / fun x => z - x) +
        ((fun _ => Q z) - Q) ^ 2 / (fun x => z - x) ^ 2 by
    funext x
    rfl]
  apply hraw.congr_deriv
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  unfold coordinateTDelta coordinateDelta chordMoment chordSlope curvature
  field_simp [hgapne]
  ring

/-- The endpoint moment formula for `T Lambda` has the required actual left
derivative; no mixed derivative is assumed. -/
theorem coordinateTLambda_hasDerivAt_left
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z)
    (hQ : HasDerivAt Q (Q1 p) p)
    (hQ1 : HasDerivAt Q1 (Q2 p) p) :
    HasDerivAt (fun x => coordinateTLambda Q Q1 x z w)
      (-(Q1 p * coordinateDelta Q Q1 p z +
        coordinateTDelta Q Q1 Q2 p z)) p := by
  unfold coordinateTLambda
  have hraw := (hasDerivAt_const p (chordMoment Q Q1 z w)).sub
    (chordMoment_left_hasDerivAt hpz hQ hQ1)
  have heq : Filter.EventuallyEq (nhds p)
      (fun x => chordMoment Q Q1 z w - chordMoment Q Q1 x z)
      ((fun _ : ℝ => chordMoment Q Q1 z w) -
        fun x => chordMoment Q Q1 x z) :=
    Filter.Eventually.of_forall fun _ => rfl
  apply (hraw.congr_of_eventuallyEq heq).congr_deriv
  ring

/-- PO-0026/0027 candidate in the curvature coordinate: the independently
defined `Psi` has the exact displayed left derivative. -/
theorem coordinatePsi_hasDerivAt
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z)
    (hΛ : coordinateLambda Q p z w ≠ 0)
    (hQ : HasDerivAt Q (Q1 p) p)
    (hQ1 : HasDerivAt Q1 (Q2 p) p) :
    HasDerivAt (fun x => coordinatePsi Q Q1 x z w)
      (-coordinateNumerator Q Q1 Q2 p z w /
        coordinateLambda Q p z w ^ 2) p := by
  apply coordinatePsi_hasDerivAt_of_endpoint_derivatives hΛ
  · exact hasDerivAt_coordinateLambda_left hpz hQ
  · exact coordinateTLambda_hasDerivAt_left hpz hQ hQ1

/-- Multiplying the left-coordinate derivative by the coordinate speed gives
the displayed partial-xi expression. -/
theorem coordinatePartialXi_eq_partialXiExpression
    {Q Q1 Q2 : ℝ → ℝ} {p z w partialP : ℝ}
    (hpartialP : partialP =
      -coordinateNumerator Q Q1 Q2 p z w /
        coordinateLambda Q p z w ^ 2) :
    Q p * partialP = partialXiExpression (Q p)
      (coordinateLambda Q p z w) (coordinateNumerator Q Q1 Q2 p z w) := by
  rw [hpartialP]
  unfold partialXiExpression
  ring

/-- PO-0027 candidate: the independently defined coordinate `Psi`, after
conversion from the left-coordinate derivative to `partial_xi`, is exactly
the displayed negative rational expression. -/
theorem coordinatePartialXiPsi_eq
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z)
    (hΛ : coordinateLambda Q p z w ≠ 0)
    (hQ : HasDerivAt Q (Q1 p) p)
    (hQ1 : HasDerivAt Q1 (Q2 p) p) :
    Q p * deriv (fun x => coordinatePsi Q Q1 x z w) p =
      partialXiExpression (Q p) (coordinateLambda Q p z w)
        (coordinateNumerator Q Q1 Q2 p z w) := by
  apply coordinatePartialXi_eq_partialXiExpression
  exact (coordinatePsi_hasDerivAt hpz hΛ hQ hQ1).deriv

/-- The exact identity transfers positivity of the independently defined
coordinate numerator to the strict derivative sign. -/
theorem coordinatePartialXiPsi_neg
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z)
    (hΛ : 0 < coordinateLambda Q p z w)
    (hQpos : 0 < Q p)
    (hQ : HasDerivAt Q (Q1 p) p)
    (hQ1 : HasDerivAt Q1 (Q2 p) p)
    (hN : 0 < coordinateNumerator Q Q1 Q2 p z w) :
    Q p * deriv (fun x => coordinatePsi Q Q1 x z w) p < 0 := by
  rw [coordinatePartialXiPsi_eq hpz hΛ.ne' hQ hQ1]
  exact partialXiExpression_neg hQpos hΛ hN

/-- Exact handoff from the independently expanded `K` object to the already
defined deterministic transport numerator. This theorem exposes, rather than
hides, the remaining central-identity premise. -/
theorem coordinateNumerator_eq_transportNumerator_of_centralIdentity
    {Q Q1 Q2 C4 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z)
    (hδ : coordinateDelta Q Q1 p z ≠ 0)
    (hΛ : coordinateLambda Q p z w ≠ 0)
    (hcentral :
      expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
          (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
        transportIntegral
          (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
            (coordinateLambda Q p z w)) Q (curvature Q2) C4 p w) :
    coordinateNumerator Q Q1 Q2 p z w =
      transportNumerator (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w)
        (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
          (coordinateLambda Q p z w)) Q (curvature Q2) C4 p w := by
  rw [coordinateNumerator_eq_deltaLambda_mul_expandedTransportK hpz hδ hΛ,
    hcentral]
  rfl

/-- PO-0041 assembly candidate with one named unresolved edge: the exact
central identity between the expanded endpoint object and deterministic
transport integral. No sign conclusion is included in that premise. -/
theorem coordinatePartialXiPsi_neg_of_centralIdentity
    {Q Q1 Q2 C4 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hQcont : Continuous Q) (hQ1cont : Continuous Q1)
    (hQpos : ∀ t ∈ Icc p w, 0 < Q t)
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t)
    (hκcont : Continuous (curvature Q2))
    (hC4cont : Continuous C4)
    (hC4pos : ∀ t ∈ Icc p w, 0 < C4 t)
    (hcentral :
      expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
          (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
        transportIntegral
          (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
            (coordinateLambda Q p z w)) Q (curvature Q2) C4 p w) :
    Q p * deriv (fun x => coordinatePsi Q Q1 x z w) p < 0 := by
  have hδ : 0 < coordinateDelta Q Q1 p z :=
    coordinateDelta_pos hpz
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hQ1 t ⟨ht.1, ht.2.trans hzw.le⟩)
      hκcont.continuousOn
      (fun t ht => hκpos t ⟨ht.1, ht.2.trans hzw.le⟩)
  have hΛ : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw hQ hQ1 hκcont.continuousOn hκpos
  have htransport := coordinateTransportNumerator_pos_closed hpz hzw hQ hQ1
    hQcont hQ1cont hQpos hκpos hκcont hC4cont hC4pos
  have hN : 0 < coordinateNumerator Q Q1 Q2 p z w := by
    rw [coordinateNumerator_eq_transportNumerator_of_centralIdentity hpz
      hδ.ne' hΛ.ne' hcentral]
    exact htransport
  exact coordinatePartialXiPsi_neg hpz hΛ (hQpos p ⟨le_rfl, hpz.le.trans hzw.le⟩)
    (hQ p ⟨le_rfl, hpz.le.trans hzw.le⟩)
    (hQ1 p ⟨le_rfl, hpz.le.trans hzw.le⟩) hN

end PF4.Advancement.CoordinateSignBridge

#print axioms PF4.Advancement.CoordinateSignBridge.coordinateNumerator_eq_deltaLambda_mul_expandedTransportK
#print axioms PF4.Advancement.CoordinateSignBridge.coordinatePsi_hasDerivAt_of_endpoint_derivatives
#print axioms PF4.Advancement.CoordinateSignBridge.coordinatePartialXi_eq_partialXiExpression
#print axioms PF4.Advancement.CoordinateSignBridge.chordMoment_left_hasDerivAt
#print axioms PF4.Advancement.CoordinateSignBridge.coordinateTLambda_hasDerivAt_left
#print axioms PF4.Advancement.CoordinateSignBridge.coordinatePsi_hasDerivAt
#print axioms PF4.Advancement.CoordinateSignBridge.coordinatePartialXiPsi_eq
#print axioms PF4.Advancement.CoordinateSignBridge.coordinatePartialXiPsi_neg
#print axioms PF4.Advancement.CoordinateSignBridge.coordinateNumerator_eq_transportNumerator_of_centralIdentity
#print axioms PF4.Advancement.CoordinateSignBridge.coordinatePartialXiPsi_neg_of_centralIdentity
