import PF4.Transport
import PF4.TransportObject

set_option linter.style.header false

namespace PF4.Advancement.CentralTransportIdentity

open MeasureTheory Set
open scoped Interval
open PF4.CDF PF4.Cumulative PF4.Curvature PF4.Densities PF4.Measures
  PF4.Normalization PF4.Expectation PF4.Transport PF4.TransportObject

/-- The derivative rate of the paper primitive, kept independent of `C4`. -/
noncomputable def primitiveRate
    (Q Q1 Q2 κ κ1 κ2 : ℝ → ℝ) (y : ℝ) : ℝ :=
  3 * (1 - Q2 y) - Q1 y * (κ1 y / κ y) -
    Q y * ((κ2 y * κ y - κ1 y ^ 2) / κ y ^ 2)

/-- The curvature numerator obtained by clearing the exact primitive rate. -/
noncomputable def derivedC4
    (Q Q1 Q2 κ κ1 κ2 : ℝ → ℝ) (y : ℝ) : ℝ :=
  Q y ^ 6 * κ y ^ 2 * primitiveRate Q Q1 Q2 κ κ1 κ2 y

theorem paperPrimitive_hasDerivAt_primitiveRate
    {Q Q1 Q2 κ κ1 κ2 : ℝ → ℝ} {y : ℝ}
    (hQ : HasDerivAt Q (Q1 y) y)
    (hQ1 : HasDerivAt Q1 (Q2 y) y)
    (hκ : HasDerivAt κ (κ1 y) y)
    (hκ1 : HasDerivAt κ1 (κ2 y) y)
    (hκne : κ y ≠ 0) :
    HasDerivAt (paperPrimitive Q Q1 κ κ1)
      (primitiveRate Q Q1 Q2 κ κ1 κ2 y) y := by
  have hratio := hκ1.div hκ hκne
  have hraw := (((hasDerivAt_id y).sub hQ1).const_mul 3).sub (hQ.mul hratio)
  apply hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only [paperPrimitive, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id_eq])
      |>.congr_deriv
  unfold primitiveRate
  simp only [Pi.div_apply]
  field_simp [hκne]
  ring

theorem curvatureWeight_derivedC4
    {Q Q1 Q2 κ κ1 κ2 : ℝ → ℝ} {y : ℝ}
    (hQne : Q y ≠ 0) (hκne : κ y ≠ 0) :
    curvatureWeight Q κ (derivedC4 Q Q1 Q2 κ κ1 κ2) y =
      primitiveRate Q Q1 Q2 κ κ1 κ2 y := by
  unfold curvatureWeight derivedC4
  field_simp [hQne, hκne]

/-- The measure-backed gap and the deterministic closed gap agree pointwise
on the complete coordinate interval, with all normalizations derived. -/
theorem cdfGap_eq_coordinateGap
    {Q Q1 Q2 : ℝ → ℝ} {p z w y : ℝ}
    (hpz : p < z) (hzw : z < w) (hy : y ∈ Icc p w)
    (hQ : ∀ t, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t, HasDerivAt Q1 (Q2 t) t)
    (hκpos : ∀ t, 0 < curvature Q2 t)
    (hκcont : Continuous (curvature Q2)) :
    cdfGap (curvature Q2) p z w (z - p) (w - z)
        (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) y =
      coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w) y := by
  have hδ : 0 < coordinateDelta Q Q1 p z :=
    coordinateDelta_pos hpz (fun t _ => hQ t) (fun t _ => hQ1 t)
      hκcont.continuousOn (fun t _ => hκpos t)
  have hΛ : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw (fun t _ => hQ t) (fun t _ => hQ1 t)
      hκcont.continuousOn (fun t _ => hκpos t)
  have hμcont : Continuous (leftMuDensity (curvature Q2) z (z - p)
      (coordinateDelta Q Q1 p z)) := by
    unfold leftMuDensity
    fun_prop
  have hνleftcont : Continuous (leftNuDensity (curvature Q2) p (z - p)
      (coordinateLambda Q p z w)) := by
    unfold leftNuDensity
    fun_prop
  have hνrightcont : Continuous (rightNuDensity (curvature Q2) w (w - z)
      (coordinateLambda Q p z w)) := by
    unfold rightNuDensity
    fun_prop
  have hrawMu : Continuous (fun t => (z - t) * curvature Q2 t) := by fun_prop
  have hrawLeft : Continuous (fun t => (t - p) * curvature Q2 t) := by fun_prop
  have hrawRight : Continuous (fun t => (w - t) * curvature Q2 t) := by fun_prop
  have hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p)
        (coordinateDelta Q Q1 p z) t) = 1 := by
    apply leftMuDensity_intervalIntegral_eq_one (sub_pos.mpr hpz) hδ
    rw [coordinateDelta_eq_triangular hpz (fun t _ => hQ t)
      (fun t _ => hQ1 t) hκcont.continuousOn]
    field_simp [sub_ne_zero.mpr hpz.ne']
  have hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p)
        (coordinateLambda Q p z w) t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z)
          (coordinateLambda Q p z w) t) = 1 := by
    apply nuDensities_intervalIntegral_eq_one (sub_pos.mpr hpz)
      (sub_pos.mpr hzw) hΛ
    exact (coordinateLambda_eq_triangular hpz hzw (fun t _ => hQ t)
      (fun t _ => hQ1 t) hκcont.continuousOn).symm
  by_cases hyz : y ≤ z
  · rw [coordinateGap_of_le hyz]
    exact cdfGap_eq_closedGapLeft hpz hy.1 hyz
      (fun t _ => hκpos t) hδ hΛ
      (hμcont.intervalIntegrable p y) (hνleftcont.intervalIntegrable p y)
      (fun t _ => hQ t) (fun t _ => hQ1 t)
      (hrawMu.intervalIntegrable p y) (hrawLeft.intervalIntegrable p y)
  · have hzy : z ≤ y := le_of_not_ge hyz
    have hμmeasure : muMeasure (curvature Q2) p z (z - p)
        (coordinateDelta Q Q1 p z) Set.univ = 1 :=
      muMeasure_univ_eq_one hpz (fun t _ => hκpos t) (sub_pos.mpr hpz) hδ
        (hμcont.intervalIntegrable p z) hμmass
    rw [coordinateGap_of_ge (lt_of_not_ge hyz)]
    exact cdfGap_eq_closedGapRight hpz hzw hzy hy.2
      (fun t _ => hκpos t) hΛ hμmeasure
      (hνleftcont.intervalIntegrable p z)
      (hνrightcont.intervalIntegrable z y)
      (hνrightcont.intervalIntegrable y w) hνmass
      (fun t _ => hQ t) (fun t _ => hQ1 t)
      (hrawRight.intervalIntegrable y w)

/-- The two transport integrals are identical because their gap functions are
pointwise equal on the integration interval. -/
theorem cdfTransportIntegral_eq_coordinateTransportIntegral
    {Q Q1 Q2 C4 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t, HasDerivAt Q1 (Q2 t) t)
    (hκpos : ∀ t, 0 < curvature Q2 t)
    (hκcont : Continuous (curvature Q2)) :
    transportIntegral
        (cdfGap (curvature Q2) p z w (z - p) (w - z)
          (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w))
        Q (curvature Q2) C4 p w =
      transportIntegral
        (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
          (coordinateLambda Q p z w)) Q (curvature Q2) C4 p w := by
  unfold transportIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc p w := by
    simpa [uIcc_of_le (hpz.trans hzw).le] using ht
  change cdfGap (curvature Q2) p z w (z - p) (w - z)
      (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) t * _ =
    coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
      (coordinateLambda Q p z w) t * _
  rw [cdfGap_eq_coordinateGap hpz hzw ht' hQ hQ1 hκpos hκcont]

/-- Full central-identity candidate for the curvature numerator derived from
the paper primitive. Every intermediate object is independently defined. -/
theorem expandedTransportK_eq_coordinateTransportIntegral
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t, HasDerivAt Q2 (Q3 t) t)
    (hQ3 : ∀ t, HasDerivAt Q3 (Q4 t) t)
    (hQ4cont : Continuous Q4)
    (hQpos : ∀ t, 0 < Q t)
    (hκpos : ∀ t, 0 < curvature Q2 t)
    (hκcont : Continuous (curvature Q2)) :
    expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
        (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
      transportIntegral
        (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
          (coordinateLambda Q p z w)) Q (curvature Q2)
        (derivedC4 Q Q1 Q2 (curvature Q2) (fun t => -Q3 t)
          (fun t => -Q4 t)) p w := by
  let κ := curvature Q2
  let κ1 : ℝ → ℝ := fun t => -Q3 t
  let κ2 : ℝ → ℝ := fun t => -Q4 t
  let A := paperPrimitive Q Q1 κ κ1
  let C4 := derivedC4 Q Q1 Q2 κ κ1 κ2
  have hκ : ∀ t, HasDerivAt κ (κ1 t) t := by
    intro t
    dsimp [κ, κ1]
    unfold curvature
    simpa only [id_eq] using (hQ2 t).const_sub 2
  have hκ1 : ∀ t, HasDerivAt κ1 (κ2 t) t := by
    intro t
    have hraw := (hQ3 t).neg
    have heq : Filter.EventuallyEq (nhds t) (fun x => -Q3 x) (-Q3) :=
      Filter.Eventually.of_forall fun _ => rfl
    exact hraw.congr_of_eventuallyEq heq
  have hA : ∀ t, HasDerivAt A (primitiveRate Q Q1 Q2 κ κ1 κ2 t) t := by
    intro t
    exact paperPrimitive_hasDerivAt_primitiveRate (hQ t) (hQ1 t)
      (hκ t) (hκ1 t) (hκpos t).ne'
  have hAweight : ∀ t, HasDerivAt A (curvatureWeight Q κ C4 t) t := by
    intro t
    apply (hA t).congr_deriv
    exact (curvatureWeight_derivedC4
      (Q1 := Q1) (Q2 := Q2) (κ1 := κ1) (κ2 := κ2)
      (hQpos t).ne' (hκpos t).ne').symm
  have hAcont : Continuous A := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hA t).continuousAt
  have hQcont : Continuous Q := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hQ t).continuousAt
  have hQ1cont : Continuous Q1 := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hQ1 t).continuousAt
  have hQ2cont : Continuous Q2 := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hQ2 t).continuousAt
  have hQ3cont : Continuous Q3 := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hQ3 t).continuousAt
  have hκ1cont : Continuous κ1 := by
    dsimp [κ1]
    exact hQ3cont.neg
  have hκ2cont : Continuous κ2 := by
    dsimp [κ2]
    exact hQ4cont.neg
  have hratecont : Continuous (primitiveRate Q Q1 Q2 κ κ1 κ2) := by
    unfold primitiveRate
    exact ((continuous_const.mul (continuous_const.sub hQ2cont)).sub
      (hQ1cont.mul (hκ1cont.div hκcont fun t => (hκpos t).ne'))).sub
      (hQcont.mul (((hκ2cont.mul hκcont).sub (hκ1cont.pow 2)).div
        (hκcont.pow 2) fun t => pow_ne_zero 2 (hκpos t).ne'))
  have hweighteq : curvatureWeight Q κ C4 =
      primitiveRate Q Q1 Q2 κ κ1 κ2 := by
    funext t
    exact curvatureWeight_derivedC4 (hQpos t).ne' (hκpos t).ne'
  have hweight : IntervalIntegrable (curvatureWeight Q κ C4) volume p w := by
    rw [hweighteq]
    exact hratecont.intervalIntegrable p w
  have hδ : 0 < coordinateDelta Q Q1 p z :=
    coordinateDelta_pos hpz (fun t _ => hQ t) (fun t _ => hQ1 t)
      hκcont.continuousOn (fun t _ => hκpos t)
  have hΛ : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw (fun t _ => hQ t) (fun t _ => hQ1 t)
      hκcont.continuousOn (fun t _ => hκpos t)
  have hμmass :
      (∫ t in p..z, leftMuDensity κ z (z - p)
        (coordinateDelta Q Q1 p z) t) = 1 := by
    dsimp [κ]
    apply leftMuDensity_intervalIntegral_eq_one (sub_pos.mpr hpz) hδ
    rw [coordinateDelta_eq_triangular hpz (fun t _ => hQ t)
      (fun t _ => hQ1 t) hκcont.continuousOn]
    field_simp [sub_ne_zero.mpr hpz.ne']
  have hνmass :
      (∫ t in p..z, leftNuDensity κ p (z - p)
        (coordinateLambda Q p z w) t) +
        (∫ t in z..w, rightNuDensity κ w (w - z)
          (coordinateLambda Q p z w) t) = 1 := by
    dsimp [κ]
    apply nuDensities_intervalIntegral_eq_one (sub_pos.mpr hpz)
      (sub_pos.mpr hzw) hΛ
    exact (coordinateLambda_eq_triangular hpz hzw (fun t _ => hQ t)
      (fun t _ => hQ1 t) hκcont.continuousOn).symm
  have hKexpectation :
      expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
          (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
        measureExpectation
            (nuMeasure κ p z w (z - p) (w - z)
              (coordinateLambda Q p z w)) A -
          measureExpectation
            (muMeasure κ p z (z - p) (coordinateDelta Q Q1 p z)) A := by
    apply derived_expandedTransportK_eq_concrete_expectationDifference hpz hzw
      hQ hQ1 hQ2
    · intro t
      rfl
    · exact hκpos
    · exact hκcont
    · exact hAcont
  have hexpectationTransport :
      measureExpectation
            (nuMeasure κ p z w (z - p) (w - z)
              (coordinateLambda Q p z w)) A -
          measureExpectation
            (muMeasure κ p z (z - p) (coordinateDelta Q Q1 p z)) A =
        transportIntegral
          (cdfGap κ p z w (z - p) (w - z)
            (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w))
          Q κ C4 p w := by
    exact concrete_expectationDifference_eq_transportIntegral hpz hzw
      (fun t _ => hκpos t) hκcont hAcont hAweight hweight
      (sub_pos.mpr hpz) (sub_pos.mpr hzw) hδ hΛ hμmass hνmass
  change expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
      (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
    transportIntegral
      (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w)) Q κ C4 p w
  rw [hKexpectation, hexpectationTransport]
  exact cdfTransportIntegral_eq_coordinateTransportIntegral hpz hzw hQ hQ1
    hκpos hκcont

/-- Central identity for an independently supplied `C4`. The only additional
interface is the exact pointwise identification with the primitive-derived
curvature numerator; no inequality or sign is assumed. -/
theorem expandedTransportK_eq_coordinateTransportIntegral_of_C4_eq
    {Q Q1 Q2 Q3 Q4 C4 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t, HasDerivAt Q2 (Q3 t) t)
    (hQ3 : ∀ t, HasDerivAt Q3 (Q4 t) t)
    (hQ4cont : Continuous Q4)
    (hQpos : ∀ t, 0 < Q t)
    (hκpos : ∀ t, 0 < curvature Q2 t)
    (hκcont : Continuous (curvature Q2))
    (hC4eq : ∀ t ∈ Icc p w,
      C4 t = derivedC4 Q Q1 Q2 (curvature Q2) (fun x => -Q3 x)
        (fun x => -Q4 x) t) :
    expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
        (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
      transportIntegral
        (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
          (coordinateLambda Q p z w)) Q (curvature Q2) C4 p w := by
  rw [expandedTransportK_eq_coordinateTransportIntegral hpz hzw hQ hQ1 hQ2
    hQ3 hQ4cont hQpos hκpos hκcont]
  unfold transportIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc p w := by
    simpa [uIcc_of_le (hpz.trans hzw).le] using ht
  change _ * curvatureWeight Q (curvature Q2)
      (derivedC4 Q Q1 Q2 (curvature Q2) (fun x => -Q3 x)
        (fun x => -Q4 x)) t = _ * curvatureWeight Q (curvature Q2) C4 t
  simp only [curvatureWeight, hC4eq t ht']

end PF4.Advancement.CentralTransportIdentity

#print axioms PF4.Advancement.CentralTransportIdentity.paperPrimitive_hasDerivAt_primitiveRate
#print axioms PF4.Advancement.CentralTransportIdentity.curvatureWeight_derivedC4
#print axioms PF4.Advancement.CentralTransportIdentity.cdfGap_eq_coordinateGap
#print axioms PF4.Advancement.CentralTransportIdentity.cdfTransportIntegral_eq_coordinateTransportIntegral
#print axioms PF4.Advancement.CentralTransportIdentity.expandedTransportK_eq_coordinateTransportIntegral
#print axioms PF4.Advancement.CentralTransportIdentity.expandedTransportK_eq_coordinateTransportIntegral_of_C4_eq
