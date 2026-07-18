/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.Curvature

set_option linter.style.header false

/-!
# Closed cumulative triangular weights

The primary objects are deterministic normalized integrals and their endpoint
closed forms. No measure or probability-CDF definition is used here.
-/

namespace PF4.Cumulative

open MeasureTheory Set
open scoped Interval
open PF4.Crossing PF4.Curvature PF4.Densities PF4.Normalization

noncomputable def increasingBoundary (Q Q1 : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (x - a) ^ 2 - (x - a) * Q1 x + Q x

noncomputable def decreasingBoundary (Q Q1 : ℝ → ℝ) (a x : ℝ) : ℝ :=
  -(a - x) ^ 2 - (a - x) * Q1 x - Q x

theorem hasDerivAt_increasingBoundary
    {Q Q1 Q2 : ℝ → ℝ} {a x : ℝ}
    (hQ : HasDerivAt Q (Q1 x) x) (hQ1 : HasDerivAt Q1 (Q2 x) x) :
    HasDerivAt (increasingBoundary Q Q1 a) ((x - a) * curvature Q2 x) x := by
  unfold increasingBoundary curvature
  have hx : HasDerivAt (fun t : ℝ => t - a) 1 x := by
    simpa only [id_eq] using (hasDerivAt_id x).sub_const a
  apply ((hx.pow 2).sub (hx.mul hQ1) |>.add hQ).congr_deriv
  ring

theorem hasDerivAt_decreasingBoundary
    {Q Q1 Q2 : ℝ → ℝ} {a x : ℝ}
    (hQ : HasDerivAt Q (Q1 x) x) (hQ1 : HasDerivAt Q1 (Q2 x) x) :
    HasDerivAt (decreasingBoundary Q Q1 a) ((a - x) * curvature Q2 x) x := by
  unfold decreasingBoundary curvature
  have hx : HasDerivAt (fun t : ℝ => a - t) (-1) x := by
    simpa only [id_eq] using (hasDerivAt_id x).const_sub a
  apply (((hx.pow 2).neg.sub (hx.mul hQ1)).sub hQ).congr_deriv
  ring

theorem increasing_integral_closed
    {Q Q1 Q2 : ℝ → ℝ} {a x y : ℝ}
    (hQ : ∀ t ∈ uIcc x y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc x y, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (t - a) * curvature Q2 t) volume x y) :
    (∫ t in x..y, (t - a) * curvature Q2 t) =
      increasingBoundary Q Q1 a y - increasingBoundary Q Q1 a x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_increasingBoundary (hQ t ht) (hQ1 t ht)) hint]

theorem decreasing_integral_closed
    {Q Q1 Q2 : ℝ → ℝ} {a x y : ℝ}
    (hQ : ∀ t ∈ uIcc x y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc x y, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (a - t) * curvature Q2 t) volume x y) :
    (∫ t in x..y, (a - t) * curvature Q2 t) =
      decreasingBoundary Q Q1 a y - decreasingBoundary Q Q1 a x := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_decreasingBoundary (hQ t ht) (hQ1 t ht)) hint]

noncomputable def closedMuLeft
    (Q Q1 : ℝ → ℝ) (p z δ y : ℝ) : ℝ :=
  (decreasingBoundary Q Q1 z y - decreasingBoundary Q Q1 z p) /
    ((z - p) ^ 2 * δ)

noncomputable def closedNuLeft
    (Q Q1 : ℝ → ℝ) (p z Λ y : ℝ) : ℝ :=
  (increasingBoundary Q Q1 p y - increasingBoundary Q Q1 p p) /
    ((z - p) * Λ)

/-- The deterministic closed cumulative gap on `[p,z]`. -/
noncomputable def closedGapLeft
    (Q Q1 : ℝ → ℝ) (p z δ Λ y : ℝ) : ℝ :=
  closedMuLeft Q Q1 p z δ y - closedNuLeft Q Q1 p z Λ y

/-- The deterministic closed right-tail gap on `[z,w]`. -/
noncomputable def closedGapRight
    (Q Q1 : ℝ → ℝ) (z w Λ y : ℝ) : ℝ :=
  ((w - y) ^ 2 + (w - y) * Q1 y + Q y - Q w) / ((w - z) * Λ)

/-- The proof-facing cumulative gap, defined entirely by endpoint data. -/
noncomputable def coordinateGap
    (Q Q1 : ℝ → ℝ) (p z w δ Λ y : ℝ) : ℝ :=
  if y ≤ z then closedGapLeft Q Q1 p z δ Λ y
  else closedGapRight Q Q1 z w Λ y

theorem coordinateGap_of_le
    {Q Q1 : ℝ → ℝ} {p z w δ Λ y : ℝ} (hyz : y ≤ z) :
    coordinateGap Q Q1 p z w δ Λ y = closedGapLeft Q Q1 p z δ Λ y := by
  simp [coordinateGap, hyz]

theorem coordinateGap_of_ge
    {Q Q1 : ℝ → ℝ} {p z w δ Λ y : ℝ} (hzy : z < y) :
    coordinateGap Q Q1 p z w δ Λ y = closedGapRight Q Q1 z w Λ y := by
  simp [coordinateGap, not_le_of_gt hzy]

theorem closedGapLeft_expanded
    {Q Q1 : ℝ → ℝ} {p z δ Λ y : ℝ} :
    closedGapLeft Q Q1 p z δ Λ y =
      (-(z - y) ^ 2 - (z - y) * Q1 y - Q y +
          (z - p) ^ 2 + (z - p) * Q1 p + Q p) / ((z - p) ^ 2 * δ) -
      ((y - p) ^ 2 - (y - p) * Q1 y + Q y - Q p) / ((z - p) * Λ) := by
  unfold closedGapLeft closedMuLeft closedNuLeft
    increasingBoundary decreasingBoundary
  ring

theorem closedMuLeft_eq_integral
    {Q Q1 Q2 : ℝ → ℝ} {p z δ y : ℝ}
    (hQ : ∀ t ∈ uIcc p y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc p y, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (z - t) * curvature Q2 t) volume p y) :
    closedMuLeft Q Q1 p z δ y =
      ∫ t in p..y, leftMuDensity (curvature Q2) z (z - p) δ t := by
  change _ = ∫ t in p..y, ((z - t) * curvature Q2 t) / ((z - p) ^ 2 * δ)
  rw [closedMuLeft, intervalIntegral.integral_div,
    decreasing_integral_closed hQ hQ1 hint]

theorem closedNuLeft_eq_integral
    {Q Q1 Q2 : ℝ → ℝ} {p z Λ y : ℝ}
    (hQ : ∀ t ∈ uIcc p y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc p y, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (t - p) * curvature Q2 t) volume p y) :
    closedNuLeft Q Q1 p z Λ y =
      ∫ t in p..y, leftNuDensity (curvature Q2) p (z - p) Λ t := by
  change _ = ∫ t in p..y, ((t - p) * curvature Q2 t) / ((z - p) * Λ)
  rw [closedNuLeft, intervalIntegral.integral_div,
    increasing_integral_closed hQ hQ1 hint]

theorem closedGapLeft_eq_integral_difference
    {Q Q1 Q2 : ℝ → ℝ} {p z δ Λ y : ℝ}
    (hQ : ∀ t ∈ uIcc p y, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc p y, HasDerivAt Q1 (Q2 t) t)
    (hmu : IntervalIntegrable (fun t => (z - t) * curvature Q2 t) volume p y)
    (hnu : IntervalIntegrable (fun t => (t - p) * curvature Q2 t) volume p y) :
    closedGapLeft Q Q1 p z δ Λ y =
      (∫ t in p..y, leftMuDensity (curvature Q2) z (z - p) δ t) -
      ∫ t in p..y, leftNuDensity (curvature Q2) p (z - p) Λ t := by
  rw [closedGapLeft, closedMuLeft_eq_integral hQ hQ1 hmu,
    closedNuLeft_eq_integral hQ hQ1 hnu]

theorem closedGapRight_eq_tail_integral
    {Q Q1 Q2 : ℝ → ℝ} {z w Λ y : ℝ}
    (hQ : ∀ t ∈ uIcc y w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ uIcc y w, HasDerivAt Q1 (Q2 t) t)
    (hint : IntervalIntegrable (fun t => (w - t) * curvature Q2 t) volume y w) :
    closedGapRight Q Q1 z w Λ y =
      ∫ t in y..w, rightNuDensity (curvature Q2) w (w - z) Λ t := by
  change _ = ∫ t in y..w, ((w - t) * curvature Q2 t) / ((w - z) * Λ)
  rw [intervalIntegral.integral_div, decreasing_integral_closed hQ hQ1 hint]
  unfold closedGapRight decreasingBoundary
  ring

theorem closedGapLeft_at_p
    {Q Q1 : ℝ → ℝ} {p z δ Λ : ℝ} : closedGapLeft Q Q1 p z δ Λ p = 0 := by
  simp [closedGapLeft, closedMuLeft, closedNuLeft]

theorem closedGapRight_at_w
    {Q Q1 : ℝ → ℝ} {z w Λ : ℝ} : closedGapRight Q Q1 z w Λ w = 0 := by
  simp [closedGapRight]

theorem coordinateGap_at_p
    {Q Q1 : ℝ → ℝ} {p z w δ Λ : ℝ} (hpz : p ≤ z) :
    coordinateGap Q Q1 p z w δ Λ p = 0 := by
  rw [coordinateGap_of_le hpz, closedGapLeft_at_p]

theorem coordinateGap_at_w
    {Q Q1 : ℝ → ℝ} {p z w δ Λ : ℝ} (hzw : z < w) :
    coordinateGap Q Q1 p z w δ Λ w = 0 := by
  rw [coordinateGap_of_ge hzw, closedGapRight_at_w]

/-- Strict positivity of the closed coordinate gap from exact density
normalization. No measure, probability CDF, or complement identity is used. -/
theorem coordinateGap_pos_of_normalized
    {Q Q1 Q2 : ℝ → ℝ} {p z w δ Λ y : ℝ}
    (hpz : p < z) (hzw : z < w) (hpy : p < y) (hyw : y < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t)
    (hκcont : Continuous (curvature Q2))
    (hδ : 0 < δ) (hΛ : 0 < Λ)
    (hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p) δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p) Λ t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z) Λ t) = 1) :
    0 < coordinateGap Q Q1 p z w δ Λ y := by
  have hL : 0 < z - p := sub_pos.mpr hpz
  have hR : 0 < w - z := sub_pos.mpr hzw
  have hμcont : Continuous (leftMuDensity (curvature Q2) z (z - p) δ) := by
    unfold leftMuDensity
    fun_prop
  have hνleftcont : Continuous (leftNuDensity (curvature Q2) p (z - p) Λ) := by
    unfold leftNuDensity
    fun_prop
  have hνrightcont : Continuous (rightNuDensity (curvature Q2) w (w - z) Λ) := by
    unfold rightNuDensity
    fun_prop
  have hrawMuCont : Continuous (fun t => (z - t) * curvature Q2 t) := by
    fun_prop
  have hrawNuLeftCont : Continuous (fun t => (t - p) * curvature Q2 t) := by
    fun_prop
  have hrawNuRightCont : Continuous (fun t => (w - t) * curvature Q2 t) := by
    fun_prop
  have hQpy : ∀ t ∈ uIcc p y, HasDerivAt Q (Q1 t) t := by
    intro t ht
    have ht' : t ∈ Icc p y := by simpa [uIcc_of_le hpy.le] using ht
    exact hQ t ⟨ht'.1, ht'.2.trans hyw.le⟩
  have hQ1py : ∀ t ∈ uIcc p y, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    have ht' : t ∈ Icc p y := by simpa [uIcc_of_le hpy.le] using ht
    exact hQ1 t ⟨ht'.1, ht'.2.trans hyw.le⟩
  have hQyw : ∀ t ∈ uIcc y w, HasDerivAt Q (Q1 t) t := by
    intro t ht
    have ht' : t ∈ Icc y w := by simpa [uIcc_of_le hyw.le] using ht
    exact hQ t ⟨hpy.le.trans ht'.1, ht'.2⟩
  have hQ1yw : ∀ t ∈ uIcc y w, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    have ht' : t ∈ Icc y w := by simpa [uIcc_of_le hyw.le] using ht
    exact hQ1 t ⟨hpy.le.trans ht'.1, ht'.2⟩
  by_cases hyz : y ≤ z
  · rw [coordinateGap_of_le hyz,
      closedGapLeft_eq_integral_difference hQpy hQ1py
        (hrawMuCont.intervalIntegrable p y)
        (hrawNuLeftCont.intervalIntegrable p y)]
    have hcp := crossingPoint_mem hpz hΛ (mul_pos hL hδ)
    by_cases hyc : y < crossingPoint p z (z - p) δ Λ
    · rw [← intervalIntegral.integral_sub
        (hμcont.intervalIntegrable p y) (hνleftcont.intervalIntegrable p y)]
      apply intervalIntegral.integral_pos hpy (hμcont.sub hνleftcont).continuousOn
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
        hμcont.intervalIntegrable p y
      have hνprefix : IntervalIntegrable
          (leftNuDensity (curvature Q2) p (z - p) Λ) volume p y :=
        hνleftcont.intervalIntegrable p y
      have hμsuffix : IntervalIntegrable
          (leftMuDensity (curvature Q2) z (z - p) δ) volume y z :=
        hμcont.intervalIntegrable y z
      have hνsuffix : IntervalIntegrable
          (leftNuDensity (curvature Q2) p (z - p) Λ) volume y z :=
        hνleftcont.intervalIntegrable y z
      have hμsplit := intervalIntegral.integral_add_adjacent_intervals
        hμprefix hμsuffix
      have hνsplit := intervalIntegral.integral_add_adjacent_intervals
        hνprefix hνsuffix
      have htailpos :
          0 < ∫ t in z..w, rightNuDensity (curvature Q2) w (w - z) Λ t := by
        apply intervalIntegral.integral_pos hzw hνrightcont.continuousOn
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
      closedGapRight_eq_tail_integral hQyw hQ1yw
        (hrawNuRightCont.intervalIntegrable y w)]
    apply intervalIntegral.integral_pos hyw hνrightcont.continuousOn
    · intro t ht
      by_cases htw : t = w
      · simp [rightNuDensity, htw]
      · exact (rightNuDensity_pos (lt_of_le_of_ne ht.2 htw)
          (hκpos t ⟨hpy.le.trans ht.1.le, ht.2⟩) hR hΛ).le
    · refine ⟨(y + w) / 2, by constructor <;> linarith, ?_⟩
      exact rightNuDensity_pos (by linarith)
        (hκpos ((y + w) / 2) (by constructor <;> linarith)) hR hΛ

/-- Exact normalized mass cancellation makes the two closed cumulative
branches meet at `z`; consequently the proof-facing gap is continuous. -/
theorem coordinateGap_continuous_of_normalized
    {Q Q1 Q2 : ℝ → ℝ} {p z w δ Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hQcont : Continuous Q) (hQ1cont : Continuous Q1)
    (hκcont : Continuous (curvature Q2))
    (hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p) δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p) Λ t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z) Λ t) = 1) :
    Continuous (coordinateGap Q Q1 p z w δ Λ) := by
  have hrawMuCont : Continuous (fun t => (z - t) * curvature Q2 t) := by
    fun_prop
  have hrawNuLeftCont : Continuous (fun t => (t - p) * curvature Q2 t) := by
    fun_prop
  have hrawNuRightCont : Continuous (fun t => (w - t) * curvature Q2 t) := by
    fun_prop
  have hQpz : ∀ t ∈ uIcc p z, HasDerivAt Q (Q1 t) t := by
    intro t ht
    have ht' : t ∈ Icc p z := by simpa [uIcc_of_le hpz.le] using ht
    exact hQ t ⟨ht'.1, ht'.2.trans hzw.le⟩
  have hQ1pz : ∀ t ∈ uIcc p z, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    have ht' : t ∈ Icc p z := by simpa [uIcc_of_le hpz.le] using ht
    exact hQ1 t ⟨ht'.1, ht'.2.trans hzw.le⟩
  have hQzw : ∀ t ∈ uIcc z w, HasDerivAt Q (Q1 t) t := by
    intro t ht
    have ht' : t ∈ Icc z w := by simpa [uIcc_of_le hzw.le] using ht
    exact hQ t ⟨hpz.le.trans ht'.1, ht'.2⟩
  have hQ1zw : ∀ t ∈ uIcc z w, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    have ht' : t ∈ Icc z w := by simpa [uIcc_of_le hzw.le] using ht
    exact hQ1 t ⟨hpz.le.trans ht'.1, ht'.2⟩
  have hmatch : closedGapLeft Q Q1 p z δ Λ z =
      closedGapRight Q Q1 z w Λ z := by
    rw [closedGapLeft_eq_integral_difference hQpz hQ1pz
      (hrawMuCont.intervalIntegrable p z)
      (hrawNuLeftCont.intervalIntegrable p z)]
    rw [closedGapRight_eq_tail_integral hQzw hQ1zw
      (hrawNuRightCont.intervalIntegrable z w)]
    linarith
  have hleft : Continuous (closedGapLeft Q Q1 p z δ Λ) := by
    unfold closedGapLeft closedMuLeft closedNuLeft
      increasingBoundary decreasingBoundary
    fun_prop
  have hright : Continuous (closedGapRight Q Q1 z w Λ) := by
    unfold closedGapRight
    fun_prop
  unfold coordinateGap
  apply continuous_if_le continuous_id continuous_const
    hleft.continuousOn hright.continuousOn
  intro y hyz
  change y = z at hyz
  subst y
  exact hmatch

/-- PO-0037 candidate: the actual coordinate-derived closed gap is strictly
positive at every interior point. All normalizations are derived here. -/
theorem coordinateGap_pos
    {Q Q1 Q2 : ℝ → ℝ} {p z w y : ℝ}
    (hpz : p < z) (hzw : z < w) (hpy : p < y) (hyw : y < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t)
    (hκcont : Continuous (curvature Q2)) :
    0 < coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
      (coordinateLambda Q p z w) y := by
  have hδ : 0 < coordinateDelta Q Q1 p z :=
    coordinateDelta_pos hpz
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hQ1 t ⟨ht.1, ht.2.trans hzw.le⟩)
      hκcont.continuousOn
      (fun t ht => hκpos t ⟨ht.1, ht.2.trans hzw.le⟩)
  have hΛ : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw hQ hQ1 hκcont.continuousOn hκpos
  have hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p)
        (coordinateDelta Q Q1 p z) t) = 1 := by
    apply leftMuDensity_intervalIntegral_eq_one (sub_pos.mpr hpz) hδ
    rw [coordinateDelta_eq_triangular hpz
      (fun t ht => hQ t ⟨ht.1, ht.2.trans hzw.le⟩)
      (fun t ht => hQ1 t ⟨ht.1, ht.2.trans hzw.le⟩)
      hκcont.continuousOn]
    field_simp [sub_ne_zero.mpr hpz.ne']
  have hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p)
        (coordinateLambda Q p z w) t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z)
          (coordinateLambda Q p z w) t) = 1 := by
    apply nuDensities_intervalIntegral_eq_one (sub_pos.mpr hpz)
      (sub_pos.mpr hzw) hΛ
    exact (coordinateLambda_eq_triangular hpz hzw hQ hQ1
      hκcont.continuousOn).symm
  exact coordinateGap_pos_of_normalized hpz hzw hpy hyw hQ hQ1 hκpos hκcont
    hδ hΛ hμmass hνmass

end PF4.Cumulative
