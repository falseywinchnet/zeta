import CoordinateSignBridge
import CentralTransportIdentity
import C4CurvatureIdentity

set_option linter.style.header false

namespace PF4.Advancement.FinalDerivativeAssembly

open Set
open PF4.Cumulative PF4.Curvature PF4.Transport

/-- The two independently introduced names for the primitive-derived
curvature numerator denote the same function. -/
theorem derivedC4_eq_primitiveDerivedC4
    (Q Q1 Q2 Q3 Q4 : ℝ → ℝ) :
    PF4.Advancement.CentralTransportIdentity.derivedC4
        Q Q1 Q2 (curvature Q2) (fun t => -Q3 t)
        (fun t => -Q4 t) =
      PF4.Advancement.C4CurvatureIdentity.primitiveDerivedC4
        Q Q1 Q2 Q3 Q4 := by
  funext t
  unfold PF4.Advancement.CentralTransportIdentity.derivedC4
    PF4.Advancement.CentralTransportIdentity.primitiveRate
    PF4.Advancement.C4CurvatureIdentity.primitiveDerivedC4 curvature
  rfl

/-- Continuity needed by the positive transport theorem is derived from the
jet tower and strict curvature, not assumed for the numerator. -/
theorem primitiveDerivedC4_continuous
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ}
    (hQcont : Continuous Q) (hQ1cont : Continuous Q1)
    (hQ2cont : Continuous Q2) (hQ3cont : Continuous Q3)
    (hQ4cont : Continuous Q4)
    (hκpos : ∀ t, 0 < curvature Q2 t) :
    Continuous (PF4.Advancement.C4CurvatureIdentity.primitiveDerivedC4
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
  unfold PF4.Advancement.CentralTransportIdentity.derivedC4
    PF4.Advancement.CentralTransportIdentity.primitiveRate
  exact ((hQcont.pow 6).mul (hκcont.pow 2)).mul
    (((continuous_const.mul (continuous_const.sub hQ2cont)).sub
      (hQ1cont.mul hratio1)).sub (hQcont.mul hratio2))

/-- P000102 turns positivity of the primary determinant into positivity of
the exact P000101 transport numerator, pointwise and without a sign shortcut. -/
theorem derivedC4_pos_of_determinantC4_pos
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ}
    (hκpos : ∀ t, 0 < curvature Q2 t)
    (hdetpos : ∀ t,
      0 < PF4.Advancement.C4CurvatureIdentity.determinantC4Function
        Q Q1 Q2 Q3 Q4 t) :
    ∀ t, 0 < PF4.Advancement.CentralTransportIdentity.derivedC4
      Q Q1 Q2 (curvature Q2)
      (fun x => -Q3 x) (fun x => -Q4 x) t := by
  intro t
  rw [derivedC4_eq_primitiveDerivedC4,
    ← PF4.Advancement.C4CurvatureIdentity.determinantC4Function_eq_primitiveDerivedC4 (by
      intro x
      simpa [curvature] using hκpos x)]
  exact hdetpos t

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
      0 < PF4.Advancement.C4CurvatureIdentity.determinantC4Function
        Q Q1 Q2 Q3 Q4 t) :
    Q p * deriv (fun x =>
      PF4.Advancement.CoordinateSignBridge.coordinatePsi Q Q1 x z w) p < 0 := by
  let C4 := PF4.Advancement.CentralTransportIdentity.derivedC4
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
    exact PF4.Advancement.CentralTransportIdentity.expandedTransportK_eq_coordinateTransportIntegral
      hpz hzw hQ
      hQ1 hQ2 hQ3 hQ4cont hQpos hκpos hκcont
  exact PF4.Advancement.CoordinateSignBridge.coordinatePartialXiPsi_neg_of_centralIdentity hpz hzw
    (fun t _ => hQ t) (fun t _ => hQ1 t) hQcont hQ1cont
    (fun t _ => hQpos t) (fun t _ => hκpos t) hκcont hC4cont hC4pos hcentral

end PF4.Advancement.FinalDerivativeAssembly

#print axioms PF4.Advancement.FinalDerivativeAssembly.derivedC4_eq_primitiveDerivedC4
#print axioms PF4.Advancement.FinalDerivativeAssembly.primitiveDerivedC4_continuous
#print axioms PF4.Advancement.FinalDerivativeAssembly.derivedC4_pos_of_determinantC4_pos
#print axioms PF4.Advancement.FinalDerivativeAssembly.coordinatePartialXiPsi_neg_from_determinantC4
