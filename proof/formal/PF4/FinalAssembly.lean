import PF4.CoordinateSignBridge
import PF4.CentralIdentity
import PF4.C4Invariant
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option linter.style.header false

namespace PF4.FinalAssembly

open Set
open PF4.Cumulative PF4.Curvature PF4.Transport

/-- The two independently introduced names for the primitive-derived
curvature numerator denote the same function. -/
theorem derivedC4_eq_primitiveDerivedC4
    (Q Q1 Q2 Q3 Q4 : ℝ → ℝ) :
    PF4.CentralIdentity.derivedC4
        Q Q1 Q2 (curvature Q2) (fun t => -Q3 t)
        (fun t => -Q4 t) =
      PF4.C4Invariant.primitiveDerivedC4
        Q Q1 Q2 Q3 Q4 := by
  funext t
  unfold PF4.CentralIdentity.derivedC4
    PF4.CentralIdentity.primitiveRate
    PF4.C4Invariant.primitiveDerivedC4 curvature
  rfl

/-- Continuity needed by the positive transport theorem is derived from the
jet tower and strict curvature, not assumed for the numerator. -/
theorem primitiveDerivedC4_continuous
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ}
    (hQcont : Continuous Q) (hQ1cont : Continuous Q1)
    (hQ2cont : Continuous Q2) (hQ3cont : Continuous Q3)
    (hQ4cont : Continuous Q4)
    (hκpos : ∀ t, 0 < curvature Q2 t) :
    Continuous (PF4.C4Invariant.primitiveDerivedC4
      Q Q1 Q2 Q3 Q4) := by
  have hκcont : Continuous (curvature Q2) := by
    unfold curvature
    fun_prop
  have hratio1 : Continuous (fun t => (-Q3 t) / curvature Q2 t) :=
    hQ3cont.neg.div hκcont (fun t => (hκpos t).ne')
  have hratio2 : Continuous (fun t =>
      ((-Q4 t) * curvature Q2 t - (-Q3 t) ^ 2) /
        curvature Q2 t ^ 2) :=
    ((hQ4cont.neg.mul hκcont).sub (hQ3cont.neg.pow 2)).div
      (hκcont.pow 2) (fun t => pow_ne_zero 2 (hκpos t).ne')
  rw [← derivedC4_eq_primitiveDerivedC4 Q Q1 Q2 Q3 Q4]
  unfold PF4.CentralIdentity.derivedC4
    PF4.CentralIdentity.primitiveRate
  exact ((hQcont.pow 6).mul (hκcont.pow 2)).mul
    (((continuous_const.mul (continuous_const.sub hQ2cont)).sub
      (hQ1cont.mul hratio1)).sub (hQcont.mul hratio2))

/-- P000102 turns positivity of the primary determinant into positivity of
the exact P000101 transport numerator, pointwise and without a sign shortcut. -/
theorem derivedC4_pos_of_determinantC4_pos
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ}
    (hκpos : ∀ t, 0 < curvature Q2 t)
    (hdetpos : ∀ t,
      0 < PF4.C4Invariant.determinantC4Function
        Q Q1 Q2 Q3 Q4 t) :
    ∀ t, 0 < PF4.CentralIdentity.derivedC4
      Q Q1 Q2 (curvature Q2)
      (fun x => -Q3 x) (fun x => -Q4 x) t := by
  intro t
  rw [derivedC4_eq_primitiveDerivedC4,
    ← PF4.C4Invariant.determinantC4Function_eq_primitiveDerivedC4 (by
      intro x
      simpa [curvature] using hκpos x)]
  exact hdetpos t

/-- PO-0029: positivity of the primary determinant and the positive cleared
factors imply positivity of the primitive rate `D`. -/
theorem primitiveRate_pos_of_determinantC4_pos
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ} {t : ℝ}
    (hQpos : 0 < Q t) (hκpos : ∀ x, 0 < curvature Q2 x)
    (hdetpos : ∀ x,
      0 < PF4.C4Invariant.determinantC4Function Q Q1 Q2 Q3 Q4 x) :
    0 < PF4.CentralIdentity.primitiveRate Q Q1 Q2 (curvature Q2)
      (fun x => -Q3 x) (fun x => -Q4 x) t := by
  have hderived := derivedC4_pos_of_determinantC4_pos hκpos hdetpos t
  unfold PF4.CentralIdentity.derivedC4 at hderived
  have hfactor : 0 < Q t ^ 6 * curvature Q2 t ^ 2 :=
    mul_pos (pow_pos hQpos 6) (pow_pos (hκpos t) 2)
  exact pos_of_mul_pos_right hderived hfactor.le

/-- Premise-free PO-0041 assembly relative to the named upstream analytic
inputs. The central transport identity and the `C4` formula are theorems, not
hypotheses of this statement. -/
theorem coordinatePartialXiPsi_neg_from_determinantC4
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t, HasDerivAt Q2 (Q3 t) t)
    (hQ3 : ∀ t, HasDerivAt Q3 (Q4 t) t)
    (hQ4cont : Continuous Q4)
    (hQpos : ∀ t, 0 < Q t)
    (hκpos : ∀ t, 0 < curvature Q2 t)
    (hdetC4pos : ∀ t,
      0 < PF4.C4Invariant.determinantC4Function
        Q Q1 Q2 Q3 Q4 t) :
    Q p * deriv (fun x =>
      PF4.CoordinateSignBridge.coordinatePsi Q Q1 x z w) p < 0 := by
  let C4 := PF4.CentralIdentity.derivedC4
    Q Q1 Q2 (curvature Q2)
    (fun x => -Q3 x) (fun x => -Q4 x)
  have hQcont : Continuous Q := by
    rw [continuous_iff_continuousAt]
    exact fun t => (hQ t).continuousAt
  have hQ1cont : Continuous Q1 := by
    rw [continuous_iff_continuousAt]
    exact fun t => (hQ1 t).continuousAt
  have hQ2cont : Continuous Q2 := by
    rw [continuous_iff_continuousAt]
    exact fun t => (hQ2 t).continuousAt
  have hQ3cont : Continuous Q3 := by
    rw [continuous_iff_continuousAt]
    exact fun t => (hQ3 t).continuousAt
  have hκcont : Continuous (curvature Q2) := by
    unfold curvature
    fun_prop
  have hC4cont : Continuous C4 := by
    dsimp [C4]
    rw [derivedC4_eq_primitiveDerivedC4]
    exact primitiveDerivedC4_continuous hQcont hQ1cont hQ2cont hQ3cont
      hQ4cont hκpos
  have hC4pos : ∀ t ∈ Icc p w, 0 < C4 t := by
    intro t _
    dsimp [C4]
    exact derivedC4_pos_of_determinantC4_pos hκpos hdetC4pos t
  have hcentral :
      PF4.TransportObject.expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
          (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
        transportIntegral
          (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
            (coordinateLambda Q p z w)) Q (curvature Q2) C4 p w := by
    dsimp [C4]
    exact PF4.CentralIdentity.expandedTransportK_eq_coordinateTransportIntegral
      hpz hzw hQ
      hQ1 hQ2 hQ3 hQ4cont hQpos hκpos hκcont
  exact PF4.CoordinateSignBridge.coordinatePartialXiPsi_neg_of_centralIdentity hpz hzw
    (fun t _ => hQ t) (fun t _ => hQ1 t) hQcont hQ1cont
    (fun t _ => hQpos t) (fun t _ => hκpos t) hκcont hC4cont hC4pos hcentral

/-- For fixed ordered right endpoints, determinant positivity makes the
maintained coordinate `Psi` strictly decreasing throughout the admissible
left-endpoint interval. This derives monotonicity from the actual derivative
sign theorem; it is not an additional sign premise. -/
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
    StrictAntiOn (fun p =>
      PF4.CoordinateSignBridge.coordinatePsi Q Q1 p z w) (Iio z) := by
  let f := fun p => PF4.CoordinateSignBridge.coordinatePsi Q Q1 p z w
  have hderiv : ∀ p ∈ Iio z, deriv f p < 0 := by
    intro p hp
    have hmul := coordinatePartialXiPsi_neg_from_determinantC4 hp hzw
      hQ hQ1 hQ2 hQ3 hQ4cont hQpos hκpos hdetC4pos
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

/-- Ordered-point form of determinant-derived coordinate-`Psi` decrease. -/
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
      PF4.CoordinateSignBridge.coordinatePsi Q Q1 p₂ z w <
        PF4.CoordinateSignBridge.coordinatePsi Q Q1 p₁ z w := by
  intro p₁ p₂ z w hp₁₂ hp₂z hzw
  have hanti := coordinatePsi_strictAntiOn_Iio_from_determinantC4 hzw
    hQ hQ1 hQ2 hQ3 hQ4cont hQpos hκpos hdetC4pos
  exact hanti (hp₁₂.trans hp₂z) hp₂z hp₁₂

end PF4.FinalAssembly
