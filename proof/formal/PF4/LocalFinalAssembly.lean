import PF4.RangeLocalFinalAssembly
import PF4.LocalGapClosure
import PF4.LocalCentralIntegration

set_option linter.style.header false

/-!
# Closed range-local coordinate assembly

This module composes the maintained actual-range coordinate realization, local
closed-gap proof, and direct central integration-by-parts identity.  The final
sign theorem has no gap-object premise and no central-identity premise.
-/

namespace PF4.LocalFinalAssembly

open Set
open PF4.Curvature PF4.Cumulative PF4.Transport PF4.TransportObject
open PF4.CoordinateSignBridge
open PF4.CurvatureCoordinateRealization
open PF4.TranslationQuotientPsi

/-- The compact-interval derivative sign with the closed-gap and central
identity premises discharged by their direct local proofs. -/
theorem coordinatePartialXiPsi_neg_on_Icc
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t ∈ Icc p w, HasDerivAt Q2 (Q3 t) t)
    (hQ3 : ∀ t ∈ Icc p w, HasDerivAt Q3 (Q4 t) t)
    (hQ4cont : ContinuousOn Q4 (Icc p w))
    (hQpos : ∀ t ∈ Icc p w, 0 < Q t)
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t)
    (hdetC4pos : ∀ t ∈ Icc p w,
      0 < PF4.C4Invariant.determinantC4Function Q Q1 Q2 Q3 Q4 t) :
    Q p * deriv (fun x => coordinatePsi Q Q1 x z w) p < 0 := by
  apply PF4.LocalGapClosure.coordinatePartialXiPsi_neg_on_Icc_of_centralIdentity
    hpz hzw hQ hQ1 hQ2 hQ3 hQ4cont hQpos hκpos hdetC4pos
  exact PF4.LocalCentralIntegration.expandedTransportK_eq_coordinateTransportIntegral_on_Icc
    hpz hzw hQ hQ1 hQ2 hQ3 hQ4cont hQpos hκpos

/-- Ordered original points discharge every local coordinate premise.  The
only analytic inputs are the literal derivative tower, continuity of its top
term, and the named positive `q`, `F₂`, and determinant signs. -/
theorem actualCoordinatePartialXiPsi_neg
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
    {x m r : ℝ} (hxm : x < m) (hmr : m < r) :
    coordinateQ S q (kernelCoordinate S x) *
      deriv (fun y => coordinatePsi (coordinateQ S q) (coordinateQ1 S q q1)
        y (kernelCoordinate S m) (kernelCoordinate S r))
        (kernelCoordinate S x) < 0 := by
  let p := kernelCoordinate S x
  let z := kernelCoordinate S m
  let w := kernelCoordinate S r
  let Q := coordinateQ S q
  let Q1 := coordinateQ1 S q q1
  let Q2 := coordinateQ2 S q q1 q2
  let Q3 := coordinateQ3 S q q1 q2 q3
  let Q4 := coordinateQ4 S q q1 q2 q3 q4
  have hmono := kernelCoordinate_strictMono hS hqpos
  have hpz : p < z := hmono hxm
  have hzw : z < w := hmono hmr
  have hdata : ∀ y ∈ Icc p w,
      (HasDerivAt Q (Q1 y) y ∧ HasDerivAt Q1 (Q2 y) y ∧
       HasDerivAt Q2 (Q3 y) y ∧ HasDerivAt Q3 (Q4 y) y) ∧
      (0 < Q y ∧ 0 < curvature Q2 y ∧
       0 < PF4.C4Invariant.determinantC4Function Q Q1 Q2 Q3 Q4 y) := by
    dsimp [p, w, Q, Q1, Q2, Q3, Q4]
    exact PF4.RangeLocalFinalAssembly.coordinateJetAndSigns_on_kernelCoordinate_Icc
      hS hq hq1 hq2 hq3 hqpos hF2pos hC4pos
  apply coordinatePartialXiPsi_neg_on_Icc hpz hzw
  · intro y hy
    exact (hdata y hy).1.1
  · intro y hy
    exact (hdata y hy).1.2.1
  · intro y hy
    exact (hdata y hy).1.2.2.1
  · intro y hy
    exact (hdata y hy).1.2.2.2
  · dsimp [p, w, Q4]
    exact PF4.RangeLocalFinalAssembly.coordinateQ4_continuousOn_kernelCoordinate_Icc
      hS hq hq1 hq2 hq3 hq4cont hqpos
  · intro y hy
    exact (hdata y hy).2.1
  · intro y hy
    exact (hdata y hy).2.2.1
  · intro y hy
    exact (hdata y hy).2.2.2

end PF4.LocalFinalAssembly
