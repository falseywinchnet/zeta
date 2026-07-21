import CurvatureCoordinateRealization
import PF4.FinalAssembly

set_option linter.style.header false

/-!
# Range-local final coordinate assembly

Advancement candidate.  The terminal sign theorem below consumes calculus and
sign data only on the compact coordinate interval.  The exact central identity
and closed-gap properties remain named object-level inputs; no sign conclusion
or free positive numerator is assumed.
-/

namespace PF4.Advancement.RangeLocalFinalAssembly

open Set
open PF4.Cumulative PF4.Curvature PF4.Transport PF4.TransportObject
open PF4.CoordinateSignBridge
open PF4.Advancement.CurvatureCoordinateRealization

/-- Every coordinate value between two ordered original points belongs to the
actual coordinate range.  This is the precise replacement for an unjustified
surjectivity claim. -/
theorem kernelCoordinate_Icc_subset_range
    {S q : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) {x r : ℝ} (hxr : x ≤ r) :
    Icc (kernelCoordinate S x) (kernelCoordinate S r) ⊆
      Set.range (kernelCoordinate S) := by
  have hmono := kernelCoordinate_strictMono hS hqpos
  have hcont : Continuous (kernelCoordinate S) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hasDerivAt_kernelCoordinate hS u).continuousAt
  have himage :
      kernelCoordinate S '' Icc x r =
        Icc (kernelCoordinate S x) (kernelCoordinate S r) :=
    hcont.image_Icc_of_strictMono hmono
  intro y hy
  rw [← himage] at hy
  rcases hy with ⟨u, _, rfl⟩
  exact Set.mem_range_self u

/-- The P000118 range packages restrict directly to every coordinate interval
coming from ordered original points. -/
theorem coordinateJetAndSigns_on_kernelCoordinate_Icc
    {S q q1 q2 q3 q4 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hq3 : ∀ u, HasDerivAt q3 (q4 u) u)
    (hqpos : ∀ u, 0 < q u)
    (hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u)
    (hC4pos : ∀ u, 0 < kernelDeterminantC4 q q1 q2 q3 q4 u)
    {x r : ℝ} (hxr : x ≤ r) :
    ∀ y ∈ Icc (kernelCoordinate S x) (kernelCoordinate S r),
      (HasDerivAt (coordinateQ S q) (coordinateQ1 S q q1 y) y ∧
       HasDerivAt (coordinateQ1 S q q1) (coordinateQ2 S q q1 q2 y) y ∧
       HasDerivAt (coordinateQ2 S q q1 q2)
         (coordinateQ3 S q q1 q2 q3 y) y ∧
       HasDerivAt (coordinateQ3 S q q1 q2 q3)
         (coordinateQ4 S q q1 q2 q3 q4 y) y) ∧
      (0 < coordinateQ S q y ∧
       0 < curvature (coordinateQ2 S q q1 q2) y ∧
       0 < PF4.C4Invariant.determinantC4Function
         (coordinateQ S q) (coordinateQ1 S q q1)
         (coordinateQ2 S q q1 q2) (coordinateQ3 S q q1 q2 q3)
         (coordinateQ4 S q q1 q2 q3 q4) y) := by
  intro y hy
  have hyrange := kernelCoordinate_Icc_subset_range hS hqpos hxr hy
  exact ⟨coordinateJet_on_range hS hq hq1 hq2 hq3 hqpos y hyrange,
    coordinateSigns_on_range hS hqpos hF2pos hC4pos y hyrange⟩

/-- Continuity of the top constructed coordinate jet is also range-local.
It follows from continuity of the actual top jet and the inverse theorem; no
behavior of `Function.invFun` outside the coordinate range is used. -/
theorem coordinateQ4_continuousAt_kernelCoordinate
    {S q q1 q2 q3 q4 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hq3 : ∀ u, HasDerivAt q3 (q4 u) u)
    (hq4cont : Continuous q4) (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    ContinuousAt (coordinateQ4 S q q1 q2 q3 q4)
      (kernelCoordinate S u) := by
  have hinv := (hasDerivAt_coordinateInverse hS hq hqpos u).continuousAt
  have hqcomp : ContinuousAt (fun y => q (coordinateInverse S y))
      (kernelCoordinate S u) := ContinuousAt.comp (hq u).continuousAt hinv
  have hq1comp : ContinuousAt (fun y => q1 (coordinateInverse S y))
      (kernelCoordinate S u) := ContinuousAt.comp (hq1 u).continuousAt hinv
  have hq2comp : ContinuousAt (fun y => q2 (coordinateInverse S y))
      (kernelCoordinate S u) := ContinuousAt.comp (hq2 u).continuousAt hinv
  have hq3comp : ContinuousAt (fun y => q3 (coordinateInverse S y))
      (kernelCoordinate S u) := ContinuousAt.comp (hq3 u).continuousAt hinv
  have hq4comp : ContinuousAt (fun y => q4 (coordinateInverse S y))
      (kernelCoordinate S u) := ContinuousAt.comp hq4cont.continuousAt hinv
  unfold coordinateQ4
  apply (((((hq4comp.mul (hqcomp.pow 3)).sub
    (((continuousAt_const.mul (hqcomp.pow 2)).mul hq1comp).mul hq3comp)).add
    ((((continuousAt_const.mul hqcomp).mul (hq1comp.pow 2)).mul hq2comp))).sub
    (((continuousAt_const.mul (hqcomp.pow 2)).mul (hq2comp.pow 2)))).sub
    (continuousAt_const.mul (hq1comp.pow 4))).div (hqcomp.pow 7)
  simpa [coordinateInverse_apply_kernelCoordinate hS hqpos] using
    pow_ne_zero 7 (hqpos u).ne'

/-- The top coordinate jet is continuous on every compact coordinate interval
constructed from ordered original points. -/
theorem coordinateQ4_continuousOn_kernelCoordinate_Icc
    {S q q1 q2 q3 q4 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hq3 : ∀ u, HasDerivAt q3 (q4 u) u)
    (hq4cont : Continuous q4) (hqpos : ∀ u, 0 < q u)
    {x r : ℝ} (hxr : x ≤ r) :
    ContinuousOn (coordinateQ4 S q q1 q2 q3 q4)
      (Icc (kernelCoordinate S x) (kernelCoordinate S r)) := by
  intro y hy
  rcases kernelCoordinate_Icc_subset_range hS hqpos hxr hy with ⟨u, rfl⟩
  exact (coordinateQ4_continuousAt_kernelCoordinate hS hq hq1 hq2 hq3
    hq4cont hqpos u).continuousWithinAt

/-- Interval-local terminal assembly.  All calculus, continuity, and sign
inputs are restricted to `Icc p w`.  `hcentral` is an equality between two
independently defined objects.  `hgapStrict` and `hgapcont` describe the actual
closed coordinate gap; neither assumes the desired derivative sign. -/
theorem coordinatePartialXiPsi_neg_from_determinantC4_on_interval
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
      0 < PF4.C4Invariant.determinantC4Function Q Q1 Q2 Q3 Q4 t)
    (hgapcont : ContinuousOn
      (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w)) (Icc p w))
    (hgapStrict : ∀ t ∈ Ioo p w,
      0 < coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w) t)
    (hcentral :
      expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
          (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
        transportIntegral
          (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
            (coordinateLambda Q p z w)) Q (curvature Q2)
          (PF4.CentralIdentity.derivedC4 Q Q1 Q2 (curvature Q2)
            (fun x => -Q3 x) (fun x => -Q4 x)) p w) :
    Q p * deriv (fun x => coordinatePsi Q Q1 x z w) p < 0 := by
  let C4 := PF4.CentralIdentity.derivedC4 Q Q1 Q2 (curvature Q2)
    (fun x => -Q3 x) (fun x => -Q4 x)
  have hQcont : ContinuousOn Q (Icc p w) :=
    fun t ht => (hQ t ht).continuousAt.continuousWithinAt
  have hQ1cont : ContinuousOn Q1 (Icc p w) :=
    fun t ht => (hQ1 t ht).continuousAt.continuousWithinAt
  have hQ2cont : ContinuousOn Q2 (Icc p w) :=
    fun t ht => (hQ2 t ht).continuousAt.continuousWithinAt
  have hQ3cont : ContinuousOn Q3 (Icc p w) :=
    fun t ht => (hQ3 t ht).continuousAt.continuousWithinAt
  have hκcont : ContinuousOn (curvature Q2) (Icc p w) := by
    unfold curvature
    exact continuousOn_const.sub hQ2cont
  have hC4cont : ContinuousOn C4 (Icc p w) := by
    dsimp [C4]
    unfold PF4.CentralIdentity.derivedC4 PF4.CentralIdentity.primitiveRate
    have hκ1cont : ContinuousOn (fun t => -Q3 t) (Icc p w) := hQ3cont.neg
    have hκ2cont : ContinuousOn (fun t => -Q4 t) (Icc p w) := hQ4cont.neg
    exact ((hQcont.pow 6).mul (hκcont.pow 2)).mul
      (((continuousOn_const.mul (continuousOn_const.sub hQ2cont)).sub
        (hQ1cont.mul (hκ1cont.div hκcont (by
          intro t ht
          exact (hκpos t ht).ne')))).sub
        (hQcont.mul (((hκ2cont.mul hκcont).sub (hκ1cont.pow 2)).div
          (hκcont.pow 2) (by
            intro t ht
            exact pow_ne_zero 2 (hκpos t ht).ne'))))
  have hC4pos : ∀ t ∈ Icc p w, 0 < C4 t := by
    intro t ht
    dsimp [C4]
    rw [PF4.FinalAssembly.derivedC4_eq_primitiveDerivedC4,
      ← PF4.C4Invariant.determinantC4Function_eq_primitiveDerivedC4 (by
        intro x
        simpa [curvature] using hκpos x ht)]
    exact hdetC4pos t ht
  have hδ : 0 < coordinateDelta Q Q1 p z :=
    coordinateDelta_pos hpz
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hQ1 t ⟨ht.1, ht.2.trans hzw.le⟩)
      (hκcont.mono fun _ ht => ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hκpos t ⟨ht.1, ht.2.trans hzw.le⟩)
  have hΛ : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw hQ hQ1 hκcont hκpos
  have hgap0 : ∀ t ∈ Icc p w,
      0 ≤ coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w) t := by
    intro t ht
    by_cases htp : t = p
    · subst t
      rw [coordinateGap_at_p hpz.le]
    by_cases htw : t = w
    · subst t
      rw [coordinateGap_at_w hzw]
    exact (hgapStrict t ⟨lt_of_le_of_ne ht.1 (Ne.symm htp),
      lt_of_le_of_ne ht.2 htw⟩).le
  have hdencont : ContinuousOn
      (fun t => Q t ^ 6 * curvature Q2 t ^ 2) (Icc p w) :=
    (hQcont.pow 6).mul (hκcont.pow 2)
  have hweightcont : ContinuousOn
      (curvatureWeight Q (curvature Q2) C4) (Icc p w) := by
    unfold curvatureWeight
    exact hC4cont.div hdencont (by
      intro t ht
      exact mul_ne_zero (pow_ne_zero 6 (hQpos t ht).ne')
        (pow_ne_zero 2 (hκpos t ht).ne'))
  have htransport : 0 < transportNumerator
      (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w)
      (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w)) Q (curvature Q2) C4 p w := by
    apply transportNumerator_pos hδ hΛ
    apply transportIntegral_pos (hpz.trans hzw) hgap0 hgapStrict hQpos hκpos hC4pos
    exact hgapcont.mul hweightcont
  have hN : 0 < coordinateNumerator Q Q1 Q2 p z w := by
    rw [coordinateNumerator_eq_transportNumerator_of_centralIdentity hpz
      hδ.ne' hΛ.ne' hcentral]
    exact htransport
  exact coordinatePartialXiPsi_neg hpz hΛ
    (hQpos p ⟨le_rfl, hpz.le.trans hzw.le⟩)
    (hQ p ⟨le_rfl, hpz.le.trans hzw.le⟩)
    (hQ1 p ⟨le_rfl, hpz.le.trans hzw.le⟩) hN

/-- The exact local objects which are not part of the P000118 inverse/jet/sign
construction.  This boundary contains no terminal derivative inequality and no
free positive transport scalar. -/
structure IntervalObjectBoundary
    (Q Q1 Q2 Q3 Q4 : ℝ → ℝ) (p z w : ℝ) : Prop where
  gap_continuousOn : ContinuousOn
    (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
      (coordinateLambda Q p z w)) (Icc p w)
  gap_strict : ∀ t ∈ Ioo p w,
    0 < coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
      (coordinateLambda Q p z w) t
  central_identity :
    expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
        (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
      transportIntegral
        (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
          (coordinateLambda Q p z w)) Q (curvature Q2)
        (PF4.CentralIdentity.derivedC4 Q Q1 Q2 (curvature Q2)
          (fun x => -Q3 x) (fun x => -Q4 x)) p w

/-- Ordered original points instantiate every P000118 coordinate derivative
and sign input.  The only remaining hypotheses are the four explicit local
object properties in `IntervalObjectBoundary`. -/
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
    {x m r : ℝ} (hxm : x < m) (hmr : m < r)
    (hobjects : IntervalObjectBoundary
      (coordinateQ S q) (coordinateQ1 S q q1)
      (coordinateQ2 S q q1 q2) (coordinateQ3 S q q1 q2 q3)
      (coordinateQ4 S q q1 q2 q3 q4)
      (kernelCoordinate S x) (kernelCoordinate S m) (kernelCoordinate S r)) :
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
    exact coordinateJetAndSigns_on_kernelCoordinate_Icc hS hq hq1 hq2 hq3
      hqpos hF2pos hC4pos (hxm.le.trans hmr.le)
  apply coordinatePartialXiPsi_neg_from_determinantC4_on_interval hpz hzw
  · intro y hy
    exact (hdata y hy).1.1
  · intro y hy
    exact (hdata y hy).1.2.1
  · intro y hy
    exact (hdata y hy).1.2.2.1
  · intro y hy
    exact (hdata y hy).1.2.2.2
  · dsimp [p, w, Q4]
    exact coordinateQ4_continuousOn_kernelCoordinate_Icc hS hq hq1 hq2 hq3
      hq4cont hqpos (hxm.le.trans hmr.le)
  · intro y hy
    exact (hdata y hy).2.1
  · intro y hy
    exact (hdata y hy).2.2.1
  · intro y hy
    exact (hdata y hy).2.2.2
  · simpa [p, z, w, Q, Q1] using hobjects.gap_continuousOn
  · simpa [p, z, w, Q, Q1] using hobjects.gap_strict
  · simpa [p, z, w, Q, Q1, Q2, Q3, Q4] using hobjects.central_identity

end PF4.Advancement.RangeLocalFinalAssembly

#print axioms PF4.Advancement.RangeLocalFinalAssembly.kernelCoordinate_Icc_subset_range
#print axioms PF4.Advancement.RangeLocalFinalAssembly.coordinateJetAndSigns_on_kernelCoordinate_Icc
#print axioms PF4.Advancement.RangeLocalFinalAssembly.coordinateQ4_continuousOn_kernelCoordinate_Icc
#print axioms PF4.Advancement.RangeLocalFinalAssembly.coordinatePartialXiPsi_neg_from_determinantC4_on_interval
#print axioms PF4.Advancement.RangeLocalFinalAssembly.actualCoordinatePartialXiPsi_neg
