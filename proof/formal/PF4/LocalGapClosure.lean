import PF4.CurvatureCoordinateRealization
import PF4.FinalAssembly

set_option linter.style.header false

/-!
# Compact-interval closed-gap closure

Maintained compact-interval layer.  These are local counterparts of the maintained
closed-gap theorems.  Continuity is required only on `Icc p w`.
-/

namespace PF4.LocalGapClosure

open MeasureTheory Set
open scoped Interval
open PF4.Crossing PF4.Curvature PF4.Cumulative PF4.Densities PF4.Normalization
open PF4.Transport PF4.TransportObject PF4.CoordinateSignBridge
open PF4.CurvatureCoordinateRealization
open PF4.TranslationQuotientPsi

/-- Strict positivity of the normalized closed coordinate gap from continuity
of curvature only on the integration interval. -/
theorem coordinateGap_pos_of_normalized_on_Icc
    {Q Q1 Q2 : ℝ → ℝ} {p z w δ Λ y : ℝ}
    (hpz : p < z) (hzw : z < w) (hpy : p < y) (hyw : y < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w))
    (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p) δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p) Λ t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z) Λ t) = 1) :
    0 < coordinateGap Q Q1 p z w δ Λ y := by
  have hL : 0 < z - p := sub_pos.mpr hpz
  have hR : 0 < w - z := sub_pos.mpr hzw
  have hμcont : ContinuousOn
      (leftMuDensity (curvature Q2) z (z - p) δ) (Icc p w) := by
    unfold leftMuDensity
    fun_prop
  have hνleftcont : ContinuousOn
      (leftNuDensity (curvature Q2) p (z - p) Λ) (Icc p w) := by
    unfold leftNuDensity
    fun_prop
  have hνrightcont : ContinuousOn
      (rightNuDensity (curvature Q2) w (w - z) Λ) (Icc p w) := by
    unfold rightNuDensity
    fun_prop
  have hrawMuCont : ContinuousOn
      (fun t => (z - t) * curvature Q2 t) (Icc p w) := by fun_prop
  have hrawNuLeftCont : ContinuousOn
      (fun t => (t - p) * curvature Q2 t) (Icc p w) := by fun_prop
  have hrawNuRightCont : ContinuousOn
      (fun t => (w - t) * curvature Q2 t) (Icc p w) := by fun_prop
  have hIcc_py : Icc p y ⊆ Icc p w := fun _ ht =>
    ⟨ht.1, ht.2.trans hyw.le⟩
  have hIcc_yw : Icc y w ⊆ Icc p w := fun _ ht =>
    ⟨hpy.le.trans ht.1, ht.2⟩
  have hIcc_pz : Icc p z ⊆ Icc p w := fun _ ht =>
    ⟨ht.1, ht.2.trans hzw.le⟩
  have hIcc_yz (hyz : y ≤ z) : Icc y z ⊆ Icc p w := fun _ ht =>
    ⟨hpy.le.trans ht.1, ht.2.trans hzw.le⟩
  have hIcc_zw : Icc z w ⊆ Icc p w := fun _ ht =>
    ⟨hpz.le.trans ht.1, ht.2⟩
  have hQpy : ∀ t ∈ uIcc p y, HasDerivAt Q (Q1 t) t := by
    intro t ht
    have ht' : t ∈ Icc p y := by simpa [uIcc_of_le hpy.le] using ht
    exact hQ t (hIcc_py ht')
  have hQ1py : ∀ t ∈ uIcc p y, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    have ht' : t ∈ Icc p y := by simpa [uIcc_of_le hpy.le] using ht
    exact hQ1 t (hIcc_py ht')
  have hQyw : ∀ t ∈ uIcc y w, HasDerivAt Q (Q1 t) t := by
    intro t ht
    have ht' : t ∈ Icc y w := by simpa [uIcc_of_le hyw.le] using ht
    exact hQ t (hIcc_yw ht')
  have hQ1yw : ∀ t ∈ uIcc y w, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    have ht' : t ∈ Icc y w := by simpa [uIcc_of_le hyw.le] using ht
    exact hQ1 t (hIcc_yw ht')
  have hrawMuInt : IntervalIntegrable
      (fun t => (z - t) * curvature Q2 t) volume p y :=
    (hrawMuCont.mono hIcc_py).intervalIntegrable_of_Icc hpy.le
  have hrawNuLeftInt : IntervalIntegrable
      (fun t => (t - p) * curvature Q2 t) volume p y :=
    (hrawNuLeftCont.mono hIcc_py).intervalIntegrable_of_Icc hpy.le
  have hrawNuRightInt : IntervalIntegrable
      (fun t => (w - t) * curvature Q2 t) volume y w :=
    (hrawNuRightCont.mono hIcc_yw).intervalIntegrable_of_Icc hyw.le
  by_cases hyz : y ≤ z
  · rw [coordinateGap_of_le hyz,
      closedGapLeft_eq_integral_difference hQpy hQ1py hrawMuInt hrawNuLeftInt]
    have hcp := crossingPoint_mem hpz hΛ (mul_pos hL hδ)
    by_cases hyc : y < crossingPoint p z (z - p) δ Λ
    · have hμint : IntervalIntegrable
          (leftMuDensity (curvature Q2) z (z - p) δ) volume p y :=
        (hμcont.mono hIcc_py).intervalIntegrable_of_Icc hpy.le
      have hνint : IntervalIntegrable
          (leftNuDensity (curvature Q2) p (z - p) Λ) volume p y :=
        (hνleftcont.mono hIcc_py).intervalIntegrable_of_Icc hpy.le
      rw [← intervalIntegral.integral_sub hμint hνint]
      apply intervalIntegral.integral_pos hpy
        ((hμcont.sub hνleftcont).mono hIcc_py)
      · intro t ht
        exact (leftDensity_difference_pos_iff ht.1
          (lt_of_le_of_lt ht.2 (hyc.trans hcp.2))
          (hκpos t ⟨ht.1.le, ht.2.trans hyz |>.trans hzw.le⟩)
          hΛ hL hδ).2 (lt_of_le_of_lt ht.2 hyc) |>.le
      · refine ⟨(p + y) / 2, by constructor <;> linarith, ?_⟩
        exact (leftDensity_difference_pos_iff (by linarith) (by linarith)
          (hκpos ((p + y) / 2) (by constructor <;> linarith))
          hΛ hL hδ).2 (by linarith)
    · have hcy : crossingPoint p z (z - p) δ Λ ≤ y := le_of_not_gt hyc
      have hμprefix : IntervalIntegrable
          (leftMuDensity (curvature Q2) z (z - p) δ) volume p y :=
        (hμcont.mono hIcc_py).intervalIntegrable_of_Icc hpy.le
      have hνprefix : IntervalIntegrable
          (leftNuDensity (curvature Q2) p (z - p) Λ) volume p y :=
        (hνleftcont.mono hIcc_py).intervalIntegrable_of_Icc hpy.le
      have hμsuffix : IntervalIntegrable
          (leftMuDensity (curvature Q2) z (z - p) δ) volume y z :=
        (hμcont.mono (hIcc_yz hyz)).intervalIntegrable_of_Icc hyz
      have hνsuffix : IntervalIntegrable
          (leftNuDensity (curvature Q2) p (z - p) Λ) volume y z :=
        (hνleftcont.mono (hIcc_yz hyz)).intervalIntegrable_of_Icc hyz
      have hμsplit := intervalIntegral.integral_add_adjacent_intervals
        hμprefix hμsuffix
      have hνsplit := intervalIntegral.integral_add_adjacent_intervals
        hνprefix hνsuffix
      have htailpos :
          0 < ∫ t in z..w, rightNuDensity (curvature Q2) w (w - z) Λ t := by
        apply intervalIntegral.integral_pos hzw (hνrightcont.mono hIcc_zw)
        · intro t ht
          by_cases htw : t = w
          · simp [rightNuDensity, htw]
          · exact (rightNuDensity_pos (lt_of_le_of_ne ht.2 htw)
              (hκpos t ⟨hpz.le.trans ht.1.le, ht.2⟩) hR hΛ).le
        · refine ⟨(z + w) / 2, by constructor <;> linarith, ?_⟩
          exact rightNuDensity_pos (by linarith)
            (hκpos ((z + w) / 2) (by constructor <;> linarith)) hR hΛ
      have hreverse :
          0 ≤ ∫ t in y..z,
            (leftNuDensity (curvature Q2) p (z - p) Λ t -
              leftMuDensity (curvature Q2) z (z - p) δ t) := by
        apply intervalIntegral.integral_nonneg hyz
        intro t ht
        by_cases htz : t = z
        · subst t
          simp only [leftMuDensity, sub_self, zero_mul, zero_div, sub_zero]
          exact (leftNuDensity_pos hpz (hκpos z ⟨hpz.le, hzw.le⟩) hL hΛ).le
        by_cases htc : t = crossingPoint p z (z - p) δ Λ
        · subst t
          have heq := (leftDensity_eq_iff_crossingPoint hcp.1 hcp.2
            (hκpos _ ⟨hcp.1.le, hcp.2.le.trans hzw.le⟩) hΛ hL hδ).2 rfl
          linarith
        · have hct : crossingPoint p z (z - p) δ Λ < t :=
            lt_of_le_of_ne (hcy.trans ht.1) (Ne.symm htc)
          have hneg := (leftDensity_difference_neg_iff
            (hcp.1.trans_le (hcy.trans ht.1)) (lt_of_le_of_ne ht.2 htz)
            (hκpos t ⟨(hcp.1.trans_le (hcy.trans ht.1)).le,
              ht.2.trans hzw.le⟩) hΛ hL hδ).2 hct
          linarith
      rw [intervalIntegral.integral_sub hνsuffix hμsuffix] at hreverse
      linarith
  · have hzy : z < y := lt_of_not_ge hyz
    rw [coordinateGap_of_ge hzy,
      closedGapRight_eq_tail_integral hQyw hQ1yw hrawNuRightInt]
    apply intervalIntegral.integral_pos hyw (hνrightcont.mono hIcc_yw)
    · intro t ht
      by_cases htw : t = w
      · simp [rightNuDensity, htw]
      · exact (rightNuDensity_pos (lt_of_le_of_ne ht.2 htw)
          (hκpos t ⟨hpy.le.trans ht.1.le, ht.2⟩) hR hΛ).le
    · refine ⟨(y + w) / 2, by constructor <;> linarith, ?_⟩
      exact rightNuDensity_pos (by linarith)
        (hκpos ((y + w) / 2) (by constructor <;> linarith)) hR hΛ

/-- Local continuity of the normalized closed coordinate gap. -/
theorem coordinateGap_continuousOn_of_normalized
    {Q Q1 Q2 : ℝ → ℝ} {p z w δ Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hQcont : ContinuousOn Q (Icc p w))
    (hQ1cont : ContinuousOn Q1 (Icc p w))
    (hκcont : ContinuousOn (curvature Q2) (Icc p w))
    (hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p) δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p) Λ t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z) Λ t) = 1) :
    ContinuousOn (coordinateGap Q Q1 p z w δ Λ) (Icc p w) := by
  have hIcc_pz : Icc p z ⊆ Icc p w := fun _ ht =>
    ⟨ht.1, ht.2.trans hzw.le⟩
  have hIcc_zw : Icc z w ⊆ Icc p w := fun _ ht =>
    ⟨hpz.le.trans ht.1, ht.2⟩
  have hrawMuCont : ContinuousOn
      (fun t => (z - t) * curvature Q2 t) (Icc p w) := by fun_prop
  have hrawNuLeftCont : ContinuousOn
      (fun t => (t - p) * curvature Q2 t) (Icc p w) := by fun_prop
  have hrawNuRightCont : ContinuousOn
      (fun t => (w - t) * curvature Q2 t) (Icc p w) := by fun_prop
  have hQpz : ∀ t ∈ uIcc p z, HasDerivAt Q (Q1 t) t := by
    intro t ht
    have ht' : t ∈ Icc p z := by simpa [uIcc_of_le hpz.le] using ht
    exact hQ t (hIcc_pz ht')
  have hQ1pz : ∀ t ∈ uIcc p z, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    have ht' : t ∈ Icc p z := by simpa [uIcc_of_le hpz.le] using ht
    exact hQ1 t (hIcc_pz ht')
  have hQzw : ∀ t ∈ uIcc z w, HasDerivAt Q (Q1 t) t := by
    intro t ht
    have ht' : t ∈ Icc z w := by simpa [uIcc_of_le hzw.le] using ht
    exact hQ t (hIcc_zw ht')
  have hQ1zw : ∀ t ∈ uIcc z w, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    have ht' : t ∈ Icc z w := by simpa [uIcc_of_le hzw.le] using ht
    exact hQ1 t (hIcc_zw ht')
  have hmatch : closedGapLeft Q Q1 p z δ Λ z =
      closedGapRight Q Q1 z w Λ z := by
    rw [closedGapLeft_eq_integral_difference hQpz hQ1pz
      ((hrawMuCont.mono hIcc_pz).intervalIntegrable_of_Icc hpz.le)
      ((hrawNuLeftCont.mono hIcc_pz).intervalIntegrable_of_Icc hpz.le)]
    rw [closedGapRight_eq_tail_integral hQzw hQ1zw
      ((hrawNuRightCont.mono hIcc_zw).intervalIntegrable_of_Icc hzw.le)]
    linarith
  have hleft : ContinuousOn (closedGapLeft Q Q1 p z δ Λ) (Icc p w) := by
    unfold closedGapLeft closedMuLeft closedNuLeft
      increasingBoundary decreasingBoundary
    fun_prop
  have hright : ContinuousOn (closedGapRight Q Q1 z w Λ) (Icc p w) := by
    unfold closedGapRight
    fun_prop
  unfold coordinateGap
  apply ContinuousOn.if (s := Icc p w) (p := fun y => y ≤ z)
  · intro a ha
    have haz : a = z := frontier_Iic_subset z ha.2
    subst a
    exact hmatch
  · exact hleft.mono inter_subset_left
  · exact hright.mono inter_subset_left

/-- The derived coordinate gap is strictly positive with only local curvature
continuity. -/
theorem coordinateGap_pos_on_Icc
    {Q Q1 Q2 : ℝ → ℝ} {p z w y : ℝ}
    (hpz : p < z) (hzw : z < w) (hpy : p < y) (hyw : y < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w)) :
    0 < coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
      (coordinateLambda Q p z w) y := by
  have hδ : 0 < coordinateDelta Q Q1 p z :=
    coordinateDelta_pos hpz
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hQ1 t ⟨ht.1, ht.2.trans hzw.le⟩)
      (hκcont.mono fun _ ht => ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hκpos t ⟨ht.1, ht.2.trans hzw.le⟩)
  have hΛ : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw hQ hQ1 hκcont hκpos
  have hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p)
        (coordinateDelta Q Q1 p z) t) = 1 := by
    apply leftMuDensity_intervalIntegral_eq_one (sub_pos.mpr hpz) hδ
    rw [coordinateDelta_eq_triangular hpz
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hQ1 t ⟨ht.1, ht.2.trans hzw.le⟩)
      (hκcont.mono fun _ ht => ⟨ht.1, ht.2.trans hzw.le⟩)]
    field_simp [sub_ne_zero.mpr hpz.ne']
  have hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p)
        (coordinateLambda Q p z w) t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z)
          (coordinateLambda Q p z w) t) = 1 := by
    apply nuDensities_intervalIntegral_eq_one (sub_pos.mpr hpz)
      (sub_pos.mpr hzw) hΛ
    exact (coordinateLambda_eq_triangular hpz hzw hQ hQ1 hκcont).symm
  exact coordinateGap_pos_of_normalized_on_Icc hpz hzw hpy hyw hQ hQ1
    hκpos hκcont hδ hΛ hμmass hνmass

/-- The derived coordinate gap is continuous on its compact interval from the
same local jet. -/
theorem coordinateGap_continuousOn_Icc
    {Q Q1 Q2 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w)) :
    ContinuousOn
      (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w)) (Icc p w) := by
  have hQcont : ContinuousOn Q (Icc p w) := fun t ht =>
    (hQ t ht).continuousAt.continuousWithinAt
  have hQ1cont : ContinuousOn Q1 (Icc p w) := fun t ht =>
    (hQ1 t ht).continuousAt.continuousWithinAt
  have hδ : 0 < coordinateDelta Q Q1 p z :=
    coordinateDelta_pos hpz
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hQ1 t ⟨ht.1, ht.2.trans hzw.le⟩)
      (hκcont.mono fun _ ht => ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hκpos t ⟨ht.1, ht.2.trans hzw.le⟩)
  have hΛ : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw hQ hQ1 hκcont hκpos
  have hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p)
        (coordinateDelta Q Q1 p z) t) = 1 := by
    apply leftMuDensity_intervalIntegral_eq_one (sub_pos.mpr hpz) hδ
    rw [coordinateDelta_eq_triangular hpz
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hQ1 t ⟨ht.1, ht.2.trans hzw.le⟩)
      (hκcont.mono fun _ ht => ⟨ht.1, ht.2.trans hzw.le⟩)]
    field_simp [sub_ne_zero.mpr hpz.ne']
  have hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p)
        (coordinateLambda Q p z w) t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z)
          (coordinateLambda Q p z w) t) = 1 := by
    apply nuDensities_intervalIntegral_eq_one (sub_pos.mpr hpz)
      (sub_pos.mpr hzw) hΛ
    exact (coordinateLambda_eq_triangular hpz hzw hQ hQ1 hκcont).symm
  exact coordinateGap_continuousOn_of_normalized hpz hzw hQ hQ1
    hQcont hQ1cont hκcont hμmass hνmass

/-- Ordered original points put their whole coordinate interval in the actual
range.  This local copy keeps the present candidate independent of the
P000119 work module while using the same argument. -/
theorem kernelCoordinate_Icc_subset_range
    {S q : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) {x r : ℝ} :
    Icc (kernelCoordinate S x) (kernelCoordinate S r) ⊆
      Set.range (kernelCoordinate S) := by
  have hmono := kernelCoordinate_strictMono hS hqpos
  have hcont : Continuous (kernelCoordinate S) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (hasDerivAt_kernelCoordinate hS u).continuousAt
  have himage : kernelCoordinate S '' Icc x r =
      Icc (kernelCoordinate S x) (kernelCoordinate S r) :=
    hcont.image_Icc_of_strictMono hmono
  intro y hy
  rw [← himage] at hy
  rcases hy with ⟨u, _, rfl⟩
  exact Set.mem_range_self u

/-- The actual curvature-coordinate construction discharges both local
closed-gap fields.  Only the original `q` derivative tower through `q3`,
`q > 0`, and `F2 > 0` are used. -/
theorem actualCoordinateGap_properties
    {S q q1 q2 q3 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hqpos : ∀ u, 0 < q u)
    (hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u)
    {x m r : ℝ} (hxm : x < m) (hmr : m < r) :
    let Q := coordinateQ S q
    let Q1 := coordinateQ1 S q q1
    let p := kernelCoordinate S x
    let z := kernelCoordinate S m
    let w := kernelCoordinate S r
    ContinuousOn
        (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
          (coordinateLambda Q p z w)) (Icc p w) ∧
      ∀ y ∈ Ioo p w,
        0 < coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
          (coordinateLambda Q p z w) y := by
  dsimp only
  let Q := coordinateQ S q
  let Q1 := coordinateQ1 S q q1
  let Q2 := coordinateQ2 S q q1 q2
  let Q3 := coordinateQ3 S q q1 q2 q3
  let p := kernelCoordinate S x
  let z := kernelCoordinate S m
  let w := kernelCoordinate S r
  have hmono := kernelCoordinate_strictMono hS hqpos
  have hpz : p < z := hmono hxm
  have hzw : z < w := hmono hmr
  have hrange : Icc p w ⊆ Set.range (kernelCoordinate S) := by
    dsimp [p, w]
    exact kernelCoordinate_Icc_subset_range hS hqpos
  have hQ : ∀ y ∈ Icc p w, HasDerivAt Q (Q1 y) y := by
    rintro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q, Q1]
    rw [coordinateQ1_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ hS hq hqpos u
  have hQ1 : ∀ y ∈ Icc p w, HasDerivAt Q1 (Q2 y) y := by
    rintro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q1, Q2]
    rw [coordinateQ2_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ1 hS hq hq1 hqpos u
  have hQ2 : ∀ y ∈ Icc p w, HasDerivAt Q2 (Q3 y) y := by
    rintro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q2, Q3]
    rw [coordinateQ3_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ2 hS hq hq1 hq2 hqpos u
  have hκpos : ∀ y ∈ Icc p w, 0 < curvature Q2 y := by
    rintro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q2]
    exact curvature_coordinateQ2_pos_on_range hS hqpos hF2pos u
  have hQ2cont : ContinuousOn Q2 (Icc p w) := fun y hy =>
    (hQ2 y hy).continuousAt.continuousWithinAt
  have hκcont : ContinuousOn (curvature Q2) (Icc p w) := by
    unfold curvature
    exact continuousOn_const.sub hQ2cont
  constructor
  · exact coordinateGap_continuousOn_Icc hpz hzw hQ hQ1 hκpos hκcont
  · intro y hy
    exact coordinateGap_pos_on_Icc hpz hzw hy.1 hy.2 hQ hQ1 hκpos hκcont

/-- With the two gap fields now derived, the interval-local terminal assembly
has exactly one remaining object premise: the central identity. -/
theorem coordinatePartialXiPsi_neg_on_Icc_of_centralIdentity
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
  have hQcont : ContinuousOn Q (Icc p w) := fun t ht =>
    (hQ t ht).continuousAt.continuousWithinAt
  have hQ1cont : ContinuousOn Q1 (Icc p w) := fun t ht =>
    (hQ1 t ht).continuousAt.continuousWithinAt
  have hQ2cont : ContinuousOn Q2 (Icc p w) := fun t ht =>
    (hQ2 t ht).continuousAt.continuousWithinAt
  have hQ3cont : ContinuousOn Q3 (Icc p w) := fun t ht =>
    (hQ3 t ht).continuousAt.continuousWithinAt
  have hκcont : ContinuousOn (curvature Q2) (Icc p w) := by
    unfold curvature
    exact continuousOn_const.sub hQ2cont
  have hgapcont : ContinuousOn
      (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w)) (Icc p w) :=
    coordinateGap_continuousOn_Icc hpz hzw hQ hQ1 hκpos hκcont
  have hgapStrict : ∀ t ∈ Ioo p w,
      0 < coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
        (coordinateLambda Q p z w) t := by
    intro t ht
    exact coordinateGap_pos_on_Icc hpz hzw ht.1 ht.2 hQ hQ1 hκpos hκcont
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
    have heq := PF4.C4Invariant.coordinateDeterminantC4_eq_derivedC4
      (Q t) (Q1 t) (Q2 t) (Q3 t) (Q4 t) (hκpos t ht).ne'
    dsimp [C4]
    unfold PF4.CentralIdentity.derivedC4 PF4.CentralIdentity.primitiveRate
    unfold PF4.C4Invariant.determinantC4Function at hdetC4pos
    simp only [curvature]
    rw [← heq]
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

end PF4.LocalGapClosure
