import PF4.PaperObjectClosure
import Mathlib.Topology.Order.Compact

set_option linter.style.header false

/-!
# Weighted-mean and positive-variation closure

This module formalizes the S04 proof of PO-0014 for the literal Riemann-kernel
objects.  It does not use the independently maintained theorem that the final
`Lambda` is already positive.
-/

namespace PF4.WeightedMeanVariation

open MeasureTheory Set
open PF4.CurvatureCoordinateRealization PF4.PaperObjectClosure
open PF4.TranslationQuotientSigns

/-- The paper's `f₀=q'/q` for the literal curvature jet. -/
noncomputable def actualF0 (t : ℝ) : ℝ :=
  actualKernelCurvature1 t / actualKernelCurvature t

/-- The numerator `F₁=qq''-(q')²`, so that `f₀'=F₁/q²`. -/
noncomputable def actualF1 (t : ℝ) : ℝ :=
  actualKernelCurvature t * actualKernelCurvature2 t -
    actualKernelCurvature1 t ^ 2

theorem hasDerivAt_actualF0 (t : ℝ) :
    HasDerivAt actualF0
      (actualF1 t / actualKernelCurvature t ^ 2) t := by
  unfold actualF0 actualF1
  have hq := actualKernelCurvature_derivativeTower.1 t
  have hq1 := actualKernelCurvature_derivativeTower.2.1 t
  apply (hq1.fun_div hq (actualKernelCurvature_pos t).ne').congr_deriv
  ring

theorem continuous_actualF0 : Continuous actualF0 :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_actualF0 t).continuousAt

theorem continuous_actualF1 : Continuous actualF1 := by
  unfold actualF1
  exact continuous_actualKernelCurvature.mul
      (continuous_iff_continuousAt.mpr fun t =>
        (actualKernelCurvature_derivativeTower.2.2.1 t).continuousAt) |>.sub
    ((continuous_iff_continuousAt.mpr fun t =>
      (actualKernelCurvature_derivativeTower.2.1 t).continuousAt).pow 2)

/-- The actual quotient `M` is exactly the `q`-weighted average of `f₀`. -/
theorem actualM_eq_weightedMean {a b : ℝ} (_hab : a < b) :
    actualM a b =
      (∫ t in a..b, actualF0 t * actualKernelCurvature t) /
        (∫ t in a..b, actualKernelCurvature t) := by
  have hq1cont : Continuous actualKernelCurvature1 :=
    continuous_iff_continuousAt.mpr fun t =>
      (actualKernelCurvature_derivativeTower.2.1 t).continuousAt
  have hq1FTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := actualKernelCurvature)
    (f' := actualKernelCurvature1)
    (fun t _ => actualKernelCurvature_derivativeTower.1 t)
    (hq1cont.intervalIntegrable a b)
  rw [show (∫ t in a..b, actualF0 t * actualKernelCurvature t) =
      ∫ t in a..b, actualKernelCurvature1 t by
    apply intervalIntegral.integral_congr
    intro t _
    unfold actualF0
    field_simp [(actualKernelCurvature_pos t).ne']]
  rw [hq1FTC, ← actualA_eq_intervalIntegral]
  rfl

/-- A positive weighted mean lies above any pointwise lower bound. -/
theorem weightedMean_ge
    {q f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hqcont : Continuous q) (hfcont : Continuous f)
    (hqpos : ∀ t ∈ Icc a b, 0 < q t)
    (hc : ∀ t ∈ Icc a b, f c ≤ f t) :
    f c ≤ (∫ t in a..b, f t * q t) / (∫ t in a..b, q t) := by
  have hfqint : IntervalIntegrable (fun t => f t * q t) volume a b :=
    (hfcont.mul hqcont).intervalIntegrable a b
  have hcqint : IntervalIntegrable (fun t => f c * q t) volume a b :=
    (continuous_const.mul hqcont).intervalIntegrable a b
  have hmass : 0 < ∫ t in a..b, q t :=
    intervalIntegral.integral_pos hab hqcont.continuousOn
      (fun t ht => (hqpos t ⟨ht.1.le, ht.2⟩).le)
      ⟨(a + b) / 2, by constructor <;> linarith,
        hqpos ((a + b) / 2) (by constructor <;> linarith)⟩
  apply (le_div_iff₀ hmass).2
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hab.le hcqint hfqint
    (fun t ht => mul_le_mul_of_nonneg_right (hc t ht) (hqpos t ht).le)

/-- A positive weighted mean lies below any pointwise upper bound. -/
theorem weightedMean_le
    {q f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hqcont : Continuous q) (hfcont : Continuous f)
    (hqpos : ∀ t ∈ Icc a b, 0 < q t)
    (hc : ∀ t ∈ Icc a b, f t ≤ f c) :
    (∫ t in a..b, f t * q t) / (∫ t in a..b, q t) ≤ f c := by
  have hfqint : IntervalIntegrable (fun t => f t * q t) volume a b :=
    (hfcont.mul hqcont).intervalIntegrable a b
  have hcqint : IntervalIntegrable (fun t => f c * q t) volume a b :=
    (continuous_const.mul hqcont).intervalIntegrable a b
  have hmass : 0 < ∫ t in a..b, q t :=
    intervalIntegral.integral_pos hab hqcont.continuousOn
      (fun t ht => (hqpos t ⟨ht.1.le, ht.2⟩).le)
      ⟨(a + b) / 2, by constructor <;> linarith,
        hqpos ((a + b) / 2) (by constructor <;> linarith)⟩
  apply (div_le_iff₀ hmass).2
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_mono_on hab.le hfqint hcqint
    (fun t ht => mul_le_mul_of_nonneg_right (hc t ht) (hqpos t ht).le)

/-- A function's net increase is bounded by the integral of its positive
derivative part over any containing interval. -/
theorem sub_le_integral_max_deriv
    {f f' : ℝ → ℝ} {a u v b : ℝ}
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf'cont : Continuous f') :
    f v - f u ≤ ∫ t in a..b, max (f' t) 0 := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := u) (b := v) (f := f) (f' := f')
    (fun t _ => hf t) (hf'cont.intervalIntegrable u v)
  rw [← hftc]
  calc
    (∫ t in u..v, f' t) ≤ ∫ t in u..v, max (f' t) 0 := by
      exact intervalIntegral.integral_mono_on huv
        (hf'cont.intervalIntegrable u v)
        ((hf'cont.max continuous_const).intervalIntegrable u v)
        (fun t _ => le_max_left _ _)
    _ ≤ ∫ t in a..b, max (f' t) 0 := by
      exact intervalIntegral.integral_mono_interval hau huv hvb
        (Filter.Eventually.of_forall fun t => le_max_right (f' t) 0)
        ((hf'cont.max continuous_const).intervalIntegrable a b)

/-- Compact extrema and the two weighted-mean bounds used in S04. -/
theorem actual_weightedMean_extrema {ξ m r : ℝ}
    (hξm : ξ < m) (hmr : m < r) :
    ∃ u ∈ Icc ξ m, ∃ v ∈ Icc m r,
      IsMinOn actualF0 (Icc ξ m) u ∧
      IsMaxOn actualF0 (Icc m r) v ∧
      actualF0 u ≤ actualM ξ m ∧ actualM m r ≤ actualF0 v := by
  obtain ⟨u, hu, humin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hξm.le) continuous_actualF0.continuousOn
  obtain ⟨v, hv, hvmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hmr.le) continuous_actualF0.continuousOn
  refine ⟨u, hu, v, hv, humin, hvmax, ?_, ?_⟩
  · rw [actualM_eq_weightedMean hξm]
    exact weightedMean_ge hξm continuous_actualKernelCurvature
      continuous_actualF0 (fun t _ => actualKernelCurvature_pos t) humin
  · rw [actualM_eq_weightedMean hmr]
    exact weightedMean_le hmr continuous_actualKernelCurvature
      continuous_actualF0 (fun t _ => actualKernelCurvature_pos t) hvmax

/-- The paper's exact positive-variation estimate between the two adjacent
weighted means. -/
theorem actual_weightedMean_difference_le_variation {ξ m r : ℝ}
    (hξm : ξ < m) (hmr : m < r) :
    actualM m r - actualM ξ m ≤
      ∫ t in ξ..r,
        max (actualF1 t / actualKernelCurvature t ^ 2) 0 := by
  obtain ⟨u, hu, v, hv, _humin, _hvmax, hleft, hright⟩ :=
    actual_weightedMean_extrema hξm hmr
  calc
    actualM m r - actualM ξ m ≤ actualF0 v - actualF0 u := by linarith
    _ ≤ ∫ t in ξ..r,
        max (actualF1 t / actualKernelCurvature t ^ 2) 0 := by
      apply sub_le_integral_max_deriv hu.1 (hu.2.trans hv.1) hv.2
        hasDerivAt_actualF0
      exact continuous_actualF1.div
        (continuous_actualKernelCurvature.pow 2)
        (fun t => pow_ne_zero 2 (actualKernelCurvature_pos t).ne')

/-! ## The displayed S04 lower bound -/

/-- The exact strictly positive integrand printed in S04. -/
noncomputable def actualLambdaLowerIntegrand (t : ℝ) : ℝ :=
  min (actualKernelCurvature t ^ 3)
      (kernelF2 actualKernelCurvature actualKernelCurvature1
        actualKernelCurvature2 t) /
    actualKernelCurvature t ^ 2

theorem actualF2_eq_q_cubed_sub_F1 (t : ℝ) :
    kernelF2 actualKernelCurvature actualKernelCurvature1
        actualKernelCurvature2 t =
      actualKernelCurvature t ^ 3 - actualF1 t := by
  rfl

/-- Pointwise algebra converting the positive variation into the paper's
`min(q³,F₂)/q²` remainder. -/
theorem q_sub_positiveVariation_eq_lowerIntegrand (t : ℝ) :
    actualKernelCurvature t -
        max (actualF1 t / actualKernelCurvature t ^ 2) 0 =
      actualLambdaLowerIntegrand t := by
  have hq : 0 < actualKernelCurvature t := actualKernelCurvature_pos t
  rw [actualLambdaLowerIntegrand, actualF2_eq_q_cubed_sub_F1]
  by_cases hF : actualF1 t ≤ 0
  · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg hF (sq_nonneg _)),
      min_eq_left]
    · field_simp [hq.ne']
      ring
    · linarith
  · have hFpos : 0 < actualF1 t := lt_of_not_ge hF
    rw [max_eq_left (div_nonneg hFpos.le (sq_nonneg _)), min_eq_right]
    · field_simp [hq.ne']
    · linarith

theorem continuous_actualLambdaLowerIntegrand :
    Continuous actualLambdaLowerIntegrand := by
  unfold actualLambdaLowerIntegrand kernelF2
  apply (continuous_actualKernelCurvature.pow 3).min
    (continuous_actualKernelCurvature.pow 3 |>.sub
      (continuous_actualKernelCurvature.mul
        (continuous_iff_continuousAt.mpr fun t =>
          (actualKernelCurvature_derivativeTower.2.2.1 t).continuousAt) |>.sub
        ((continuous_iff_continuousAt.mpr fun t =>
          (actualKernelCurvature_derivativeTower.2.1 t).continuousAt).pow 2))) |>.div
    (continuous_actualKernelCurvature.pow 2)
    (fun t => pow_ne_zero 2 (actualKernelCurvature_pos t).ne')

theorem actualLambdaLowerIntegrand_pos (t : ℝ) :
    0 < actualLambdaLowerIntegrand t := by
  unfold actualLambdaLowerIntegrand
  exact div_pos
    (lt_min (pow_pos (actualKernelCurvature_pos t) 3)
      (actualKernelF2_pos t))
    (pow_pos (actualKernelCurvature_pos t) 2)

/-- PO-0014's displayed lower bound, derived through the weighted means and
positive variation rather than through the independently proved positivity of
`lowerLambda`. -/
theorem actual_lowerLambda_ge_integral_min {ξ m r : ℝ}
    (hξm : ξ < m) (hmr : m < r) :
    (∫ t in ξ..r, actualLambdaLowerIntegrand t) ≤
      lowerLambda actualKernelSlope actualKernelCurvature ξ m r := by
  have hξr : ξ < r := hξm.trans hmr
  have hvar := actual_weightedMean_difference_le_variation hξm hmr
  have hVcont : Continuous
      (fun t => max (actualF1 t / actualKernelCurvature t ^ 2) 0) :=
    (continuous_actualF1.div (continuous_actualKernelCurvature.pow 2)
      (fun t => pow_ne_zero 2 (actualKernelCurvature_pos t).ne')).max
      continuous_const
  have hlowerEq : (∫ t in ξ..r, actualLambdaLowerIntegrand t) =
      (∫ t in ξ..r, actualKernelCurvature t) -
        ∫ t in ξ..r,
          max (actualF1 t / actualKernelCurvature t ^ 2) 0 := by
    rw [← intervalIntegral.integral_sub
      (continuous_actualKernelCurvature.intervalIntegrable ξ r)
      (hVcont.intervalIntegrable ξ r)]
    apply intervalIntegral.integral_congr
    intro t _
    exact (q_sub_positiveVariation_eq_lowerIntegrand t).symm
  rw [hlowerEq, ← actualA_eq_intervalIntegral]
  change actualA ξ r -
      (∫ t in ξ..r, max (actualF1 t / actualKernelCurvature t ^ 2) 0) ≤
    actualA ξ r + actualM ξ m - actualM m r
  linarith

/-- PO-0014 in one public actual-kernel statement: the displayed integral is
strictly positive and is a lower bound for the maintained `Lambda`. -/
theorem actual_weightedMeanVariation_lowerLambda {ξ m r : ℝ}
    (hξm : ξ < m) (hmr : m < r) :
    0 < (∫ t in ξ..r, actualLambdaLowerIntegrand t) ∧
    (∫ t in ξ..r, actualLambdaLowerIntegrand t) ≤
      lowerLambda actualKernelSlope actualKernelCurvature ξ m r ∧
    0 < lowerLambda actualKernelSlope actualKernelCurvature ξ m r := by
  have hξr : ξ < r := hξm.trans hmr
  have hint : 0 < ∫ t in ξ..r, actualLambdaLowerIntegrand t :=
    intervalIntegral.integral_pos hξr
      continuous_actualLambdaLowerIntegrand.continuousOn
      (fun t _ => (actualLambdaLowerIntegrand_pos t).le)
      ⟨(ξ + r) / 2, by constructor <;> linarith,
        actualLambdaLowerIntegrand_pos ((ξ + r) / 2)⟩
  have hlower := actual_lowerLambda_ge_integral_min hξm hmr
  exact ⟨hint, hlower, hint.trans_le hlower⟩

end PF4.WeightedMeanVariation
