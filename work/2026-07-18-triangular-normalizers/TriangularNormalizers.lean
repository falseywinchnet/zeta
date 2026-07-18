import PF4.TransportObject
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Curvature-coordinate triangular normalizers

Advancement candidate for PO-0023 and PO-0024.  The central point is that the
normalizers are derived from a genuine twice-differentiable coordinate
function; they are not free positive parameters.
-/

namespace PF4.Advancement.TriangularNormalizers

open MeasureTheory Set
open scoped Interval
open PF4.Densities PF4.Normalization PF4.Measures

noncomputable def chordSlope (Q : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (Q b - Q a) / (b - a)

noncomputable def coordinateLambda (Q : ℝ → ℝ) (p z w : ℝ) : ℝ :=
  (w - p) + chordSlope Q p z - chordSlope Q z w

noncomputable def coordinateDelta
    (Q Q' : ℝ → ℝ) (p z : ℝ) : ℝ :=
  ((z - p) + Q' p - chordSlope Q p z) / (z - p)

def curvature (Q'' : ℝ → ℝ) (t : ℝ) : ℝ := 2 - Q'' t

private noncomputable def leftIncreasingPrimitive
    (Q Q' : ℝ → ℝ) (p t : ℝ) : ℝ :=
  (t - p) ^ 2 - (t - p) * Q' t + Q t

private noncomputable def leftDecreasingPrimitive
    (Q Q' : ℝ → ℝ) (z t : ℝ) : ℝ :=
  -(z - t) ^ 2 - (z - t) * Q' t - Q t

theorem hasDerivAt_leftIncreasingPrimitive
    {Q Q' Q'' : ℝ → ℝ} {p t : ℝ}
    (hQ : HasDerivAt Q (Q' t) t)
    (hQ' : HasDerivAt Q' (Q'' t) t) :
    HasDerivAt (leftIncreasingPrimitive Q Q' p)
      ((t - p) * curvature Q'' t) t := by
  unfold leftIncreasingPrimitive curvature
  convert (((hasDerivAt_id t).sub_const p).pow 2).sub
      (((hasDerivAt_id t).sub_const p).mul hQ') |>.add hQ using 1 <;>
    ring

theorem hasDerivAt_leftDecreasingPrimitive
    {Q Q' Q'' : ℝ → ℝ} {z t : ℝ}
    (hQ : HasDerivAt Q (Q' t) t)
    (hQ' : HasDerivAt Q' (Q'' t) t) :
    HasDerivAt (leftDecreasingPrimitive Q Q' z)
      ((z - t) * curvature Q'' t) t := by
  unfold leftDecreasingPrimitive curvature
  convert ((((hasDerivAt_id t).const_sub z).pow 2).neg.sub
      (((hasDerivAt_id t).const_sub z).mul hQ')).sub hQ using 1 <;>
    ring

theorem leftIncreasing_integral
    {Q Q' Q'' : ℝ → ℝ} {p z : ℝ}
    (hpz : p ≤ z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p z, HasDerivAt Q' (Q'' t) t) :
    (∫ t in p..z, (t - p) * curvature Q'' t) =
      (z - p) ^ 2 - (z - p) * Q' z + Q z - Q p := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_leftIncreasingPrimitive (hQ t ht) (hQ' t ht))]
  simp [leftIncreasingPrimitive]

theorem leftDecreasing_integral
    {Q Q' Q'' : ℝ → ℝ} {p z : ℝ}
    (hpz : p ≤ z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p z, HasDerivAt Q' (Q'' t) t) :
    (∫ t in p..z, (z - t) * curvature Q'' t) =
      (z - p) ^ 2 + (z - p) * Q' p + Q p - Q z := by
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_leftDecreasingPrimitive (hQ t ht) (hQ' t ht))]
  simp [leftDecreasingPrimitive]
  ring

/-- PO-0023: the coordinate normalizer is the sum of the two triangular
curvature integrals. -/
theorem coordinateLambda_eq_triangular
    {Q Q' Q'' : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p w, HasDerivAt Q' (Q'' t) t) :
    coordinateLambda Q p z w =
      (∫ t in p..z, (t - p) * curvature Q'' t) / (z - p) +
      (∫ t in z..w, (w - t) * curvature Q'' t) / (w - z) := by
  have hleft := leftIncreasing_integral hpz.le
    (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
    (fun t ht => hQ' t ⟨ht.1, ht.2.trans hzw.le⟩)
  have hright := leftDecreasing_integral hzw.le
    (fun t ht => hQ t ⟨hpz.le.trans ht.1, ht.2⟩)
    (fun t ht => hQ' t ⟨hpz.le.trans ht.1, ht.2⟩)
  rw [hleft, hright]
  unfold coordinateLambda chordSlope
  field_simp [sub_ne_zero.mpr hpz.ne, sub_ne_zero.mpr hzw.ne]
  ring

/-- PO-0024, algebraic half: the left endpoint derivative of `Lambda` is
the negative coordinate `delta`. -/
theorem hasDerivAt_coordinateLambda_left
    {Q Q' : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hQ : HasDerivAt Q (Q' p) p) :
    HasDerivAt (fun x => coordinateLambda Q x z w)
      (-coordinateDelta Q Q' p z) p := by
  have hnum : HasDerivAt (fun x => Q z - Q x) (-Q' p) p :=
    (hasDerivAt_const p (Q z)).sub hQ
  have hden : HasDerivAt (fun x : ℝ => z - x) (-1) p :=
    (hasDerivAt_id p).const_sub z
  have hquot := hnum.div hden (sub_ne_zero.mpr hpz.ne)
  have hmain : HasDerivAt
      (fun x : ℝ => (w - x) + (Q z - Q x) / (z - x) -
        (Q w - Q z) / (w - z))
      (-1 + ((-Q' p) * (z - p) - (Q z - Q p) * (-1)) /
        (z - p) ^ 2 - 0) p :=
    ((hasDerivAt_id p).const_sub w).add hquot |>.sub_const
      ((Q w - Q z) / (w - z))
  convert hmain using 1
  · ext x
    rfl
  · unfold coordinateDelta chordSlope
    field_simp [sub_ne_zero.mpr hpz.ne]
    ring

/-- PO-0024, integral half: the endpoint derivative coordinate has the
decreasing triangular representation. -/
theorem coordinateDelta_eq_triangular
    {Q Q' Q'' : ℝ → ℝ} {p z : ℝ}
    (hpz : p < z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p z, HasDerivAt Q' (Q'' t) t) :
    coordinateDelta Q Q' p z =
      (∫ t in p..z, (z - t) * curvature Q'' t) / (z - p) ^ 2 := by
  rw [leftDecreasing_integral hpz.le hQ hQ']
  unfold coordinateDelta chordSlope
  field_simp [sub_ne_zero.mpr hpz.ne]
  ring

theorem coordinateDelta_pos
    {Q Q' Q'' : ℝ → ℝ} {p z : ℝ}
    (hpz : p < z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p z, HasDerivAt Q' (Q'' t) t)
    (hcurv : ContinuousOn (curvature Q'') (Icc p z))
    (hcurvpos : ∀ t ∈ Icc p z, 0 < curvature Q'' t) :
    0 < coordinateDelta Q Q' p z := by
  have hcont : ContinuousOn (fun t => (z - t) * curvature Q'' t) (Icc p z) :=
    (continuous_const.sub continuous_id).continuousOn.mul hcurv
  have hnonneg : ∀ t ∈ Icc p z, 0 ≤ (z - t) * curvature Q'' t := by
    intro t ht
    exact mul_nonneg (sub_nonneg.mpr ht.2) (hcurvpos t ht).le
  have hraw : 0 < ∫ t in p..z, (z - t) * curvature Q'' t :=
    intervalIntegral.integral_pos hpz hcont hnonneg
      ⟨(p + z) / 2, by constructor <;> linarith,
        mul_pos (by linarith)
          (hcurvpos ((p + z) / 2) (by constructor <;> linarith))⟩
  rw [coordinateDelta_eq_triangular hpz hQ hQ']
  exact div_pos hraw (sq_pos_of_pos (sub_pos.mpr hpz))

theorem coordinateLambda_pos
    {Q Q' Q'' : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p w, HasDerivAt Q' (Q'' t) t)
    (hcurv : ContinuousOn (curvature Q'') (Icc p w))
    (hcurvpos : ∀ t ∈ Icc p w, 0 < curvature Q'' t) :
    0 < coordinateLambda Q p z w := by
  have hleftcont : ContinuousOn
      (fun t => (t - p) * curvature Q'' t) (Icc p z) :=
    (continuous_id.sub continuous_const).continuousOn.mul
      (hcurv.mono fun t ht => ⟨ht.1, ht.2.trans hzw.le⟩)
  have hrightcont : ContinuousOn
      (fun t => (w - t) * curvature Q'' t) (Icc z w) :=
    (continuous_const.sub continuous_id).continuousOn.mul
      (hcurv.mono fun t ht => ⟨hpz.le.trans ht.1, ht.2⟩)
  have hleft : 0 < ∫ t in p..z, (t - p) * curvature Q'' t :=
    intervalIntegral.integral_pos hpz hleftcont
      (fun t ht => mul_nonneg (sub_nonneg.mpr ht.1)
        (hcurvpos t ⟨ht.1, ht.2.trans hzw.le⟩).le)
      ⟨(p + z) / 2, by constructor <;> linarith,
        mul_pos (by linarith)
          (hcurvpos ((p + z) / 2) (by constructor <;> linarith))⟩
  have hright : 0 < ∫ t in z..w, (w - t) * curvature Q'' t :=
    intervalIntegral.integral_pos hzw hrightcont
      (fun t ht => mul_nonneg (sub_nonneg.mpr ht.2)
        (hcurvpos t ⟨hpz.le.trans ht.1, ht.2⟩).le)
      ⟨(z + w) / 2, by constructor <;> linarith,
        mul_pos (by linarith)
          (hcurvpos ((z + w) / 2) (by constructor <;> linarith))⟩
  rw [coordinateLambda_eq_triangular hpz hzw hQ hQ']
  exact add_pos (div_pos hleft (sub_pos.mpr hpz))
    (div_pos hright (sub_pos.mpr hzw))

theorem coordinate_leftMuDensity_mass
    {Q Q' Q'' : ℝ → ℝ} {p z : ℝ}
    (hpz : p < z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p z, HasDerivAt Q' (Q'' t) t)
    (hcurv : ContinuousOn (curvature Q'') (Icc p z))
    (hcurvpos : ∀ t ∈ Icc p z, 0 < curvature Q'' t) :
    (∫ t in p..z, leftMuDensity (curvature Q'') z (z - p)
      (coordinateDelta Q Q' p z) t) = 1 := by
  apply leftMuDensity_intervalIntegral_eq_one (sub_pos.mpr hpz)
    (coordinateDelta_pos hpz hQ hQ' hcurv hcurvpos)
  rw [coordinateDelta_eq_triangular hpz hQ hQ']
  field_simp [sub_ne_zero.mpr hpz.ne]

theorem coordinate_nuDensities_mass
    {Q Q' Q'' : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p w, HasDerivAt Q' (Q'' t) t)
    (hcurv : ContinuousOn (curvature Q'') (Icc p w))
    (hcurvpos : ∀ t ∈ Icc p w, 0 < curvature Q'' t) :
    (∫ t in p..z, leftNuDensity (curvature Q'') p (z - p)
      (coordinateLambda Q p z w) t) +
      (∫ t in z..w, rightNuDensity (curvature Q'') w (w - z)
        (coordinateLambda Q p z w) t) = 1 := by
  apply nuDensities_intervalIntegral_eq_one (sub_pos.mpr hpz)
    (sub_pos.mpr hzw)
    (coordinateLambda_pos hpz hzw hQ hQ' hcurv hcurvpos)
  exact (coordinateLambda_eq_triangular hpz hzw hQ hQ').symm

theorem coordinate_leftMuDensity_continuousOn
    {Q Q' Q'' : ℝ → ℝ} {p z : ℝ}
    (hpz : p < z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p z, HasDerivAt Q' (Q'' t) t)
    (hcurv : ContinuousOn (curvature Q'') (Icc p z))
    (hcurvpos : ∀ t ∈ Icc p z, 0 < curvature Q'' t) :
    ContinuousOn (leftMuDensity (curvature Q'') z (z - p)
      (coordinateDelta Q Q' p z)) (Icc p z) := by
  unfold leftMuDensity
  apply ((continuous_const.sub continuous_id).continuousOn.mul hcurv).div
    continuousOn_const
  intro t ht
  exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hpz.ne))
    (coordinateDelta_pos hpz hQ hQ' hcurv hcurvpos).ne'

theorem coordinate_leftNuDensity_continuousOn
    {Q Q' Q'' : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p w, HasDerivAt Q' (Q'' t) t)
    (hcurv : ContinuousOn (curvature Q'') (Icc p w))
    (hcurvpos : ∀ t ∈ Icc p w, 0 < curvature Q'' t) :
    ContinuousOn (leftNuDensity (curvature Q'') p (z - p)
      (coordinateLambda Q p z w)) (Icc p z) := by
  unfold leftNuDensity
  apply ((continuous_id.sub continuous_const).continuousOn.mul
    (hcurv.mono fun t ht => ⟨ht.1, ht.2.trans hzw.le⟩)).div continuousOn_const
  intro t ht
  exact mul_ne_zero (sub_ne_zero.mpr hpz.ne)
    (coordinateLambda_pos hpz hzw hQ hQ' hcurv hcurvpos).ne'

theorem coordinate_rightNuDensity_continuousOn
    {Q Q' Q'' : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p w, HasDerivAt Q' (Q'' t) t)
    (hcurv : ContinuousOn (curvature Q'') (Icc p w))
    (hcurvpos : ∀ t ∈ Icc p w, 0 < curvature Q'' t) :
    ContinuousOn (rightNuDensity (curvature Q'') w (w - z)
      (coordinateLambda Q p z w)) (Icc z w) := by
  unfold rightNuDensity
  apply ((continuous_const.sub continuous_id).continuousOn.mul
    (hcurv.mono fun t ht => ⟨hpz.le.trans ht.1, ht.2⟩)).div continuousOn_const
  intro t ht
  exact mul_ne_zero (sub_ne_zero.mpr hzw.ne)
    (coordinateLambda_pos hpz hzw hQ hQ' hcurv hcurvpos).ne'

/-- The derived `delta`, rather than an assumed normalizer, makes the concrete
left triangular measure a probability measure. -/
theorem coordinate_mu_isProbabilityMeasure
    {Q Q' Q'' : ℝ → ℝ} {p z : ℝ}
    (hpz : p < z)
    (hQ : ∀ t ∈ Icc p z, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p z, HasDerivAt Q' (Q'' t) t)
    (hcurv : ContinuousOn (curvature Q'') (Icc p z))
    (hcurvpos : ∀ t ∈ Icc p z, 0 < curvature Q'' t) :
    IsProbabilityMeasure
      (muMeasure (curvature Q'') p z (z - p) (coordinateDelta Q Q' p z)) := by
  apply mu_isProbabilityMeasure
  apply muMeasure_univ_eq_one hpz hcurvpos (sub_pos.mpr hpz)
    (coordinateDelta_pos hpz hQ hQ' hcurv hcurvpos)
  · exact (coordinate_leftMuDensity_continuousOn hpz hQ hQ' hcurv hcurvpos)
      |>.intervalIntegrable_of_Icc hpz.le
  · exact coordinate_leftMuDensity_mass hpz hQ hQ' hcurv hcurvpos

/-- The two derived triangular pieces make the concrete two-interval measure
a probability measure. -/
theorem coordinate_nu_isProbabilityMeasure
    {Q Q' Q'' : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t ∈ Icc p w, HasDerivAt Q' (Q'' t) t)
    (hcurv : ContinuousOn (curvature Q'') (Icc p w))
    (hcurvpos : ∀ t ∈ Icc p w, 0 < curvature Q'' t) :
    IsProbabilityMeasure
      (nuMeasure (curvature Q'') p z w (z - p) (w - z)
        (coordinateLambda Q p z w)) := by
  apply nu_isProbabilityMeasure
  apply nuMeasure_univ_eq_one hpz hzw
    (fun t ht => hcurvpos t ⟨ht.1, ht.2.trans hzw.le⟩)
    (fun t ht => hcurvpos t ⟨hpz.le.trans ht.1, ht.2⟩)
    (sub_pos.mpr hpz) (sub_pos.mpr hzw)
    (coordinateLambda_pos hpz hzw hQ hQ' hcurv hcurvpos)
  · exact (coordinate_leftNuDensity_continuousOn hpz hzw hQ hQ' hcurv hcurvpos)
      |>.intervalIntegrable_of_Icc hpz.le
  · exact (coordinate_rightNuDensity_continuousOn hpz hzw hQ hQ' hcurv hcurvpos)
      |>.intervalIntegrable_of_Icc hzw.le
  · exact coordinate_nuDensities_mass hpz hzw hQ hQ' hcurv hcurvpos

theorem coordinateDelta_eq_transport_endpoint
    {Q Q' : ℝ → ℝ} {p z : ℝ} :
    coordinateDelta Q Q' p z =
      ((z - p) + Q' p - PF4.TransportObject.chordSlope Q p z) / (z - p) := by
  rfl

theorem coordinateLambda_eq_transport_endpoint
    {Q : ℝ → ℝ} {p z w : ℝ} :
    coordinateLambda Q p z w =
      (z - p) + (w - z) + PF4.TransportObject.chordSlope Q p z -
        PF4.TransportObject.chordSlope Q z w := by
  unfold coordinateLambda chordSlope PF4.TransportObject.chordSlope
  ring

/-- Handoff to PO-0038: the normalizers required by the transport theorem are
now constructed from `Q`; their endpoint identities and positivity no longer
appear as independent hypotheses. -/
theorem derived_expandedTransportK_eq_concrete_expectationDifference
    {Q Q' Q'' Q''' κ' : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t, HasDerivAt Q (Q' t) t)
    (hQ' : ∀ t, HasDerivAt Q' (Q'' t) t)
    (hQ'' : ∀ t, HasDerivAt Q'' (Q''' t) t)
    (hκ' : ∀ t, κ' t = -Q''' t)
    (hcurvpos : ∀ t, 0 < curvature Q'' t)
    (hcurvcont : Continuous (curvature Q''))
    (hAcont : Continuous
      (PF4.TransportObject.paperPrimitive Q Q' (curvature Q'') κ')) :
    PF4.TransportObject.expandedTransportK Q Q' Q'' p z w
        (z - p) (w - z) (coordinateDelta Q Q' p z)
        (coordinateLambda Q p z w) =
      PF4.Expectation.measureExpectation
          (nuMeasure (curvature Q'') p z w (z - p) (w - z)
            (coordinateLambda Q p z w))
          (PF4.TransportObject.paperPrimitive Q Q' (curvature Q'') κ') -
        PF4.Expectation.measureExpectation
          (muMeasure (curvature Q'') p z (z - p)
            (coordinateDelta Q Q' p z))
          (PF4.TransportObject.paperPrimitive Q Q' (curvature Q'') κ') := by
  apply PF4.TransportObject.expandedTransportK_eq_concrete_expectationDifference
    hpz hzw rfl rfl
  · exact coordinateDelta_eq_transport_endpoint
  · exact coordinateLambda_eq_transport_endpoint
  · exact hQ
  · exact hQ'
  · exact hQ''
  · intro t
    rfl
  · exact hκ'
  · exact hcurvpos
  · exact hcurvcont
  · exact hAcont
  · exact sub_pos.mpr hpz
  · exact sub_pos.mpr hzw
  · exact coordinateDelta_pos hpz
      (fun t _ => hQ t) (fun t _ => hQ' t) hcurvcont.continuousOn
      (fun t _ => hcurvpos t)
  · exact coordinateLambda_pos hpz hzw
      (fun t _ => hQ t) (fun t _ => hQ' t) hcurvcont.continuousOn
      (fun t _ => hcurvpos t)

end PF4.Advancement.TriangularNormalizers
