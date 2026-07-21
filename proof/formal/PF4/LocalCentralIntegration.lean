import PF4.FinalAssembly

set_option linter.style.header false

/-!
# Range-local central integration by parts

The central identity is reconstructed directly from the two deterministic
closed-gap branches.  No measure-valued object is used.
-/

namespace PF4.LocalCentralIntegration

open MeasureTheory Set
open scoped Interval
open PF4.Curvature PF4.Cumulative PF4.Densities PF4.Normalization
open PF4.Transport PF4.TransportObject PF4.CoordinateSignBridge

/-- The left closed gap has the literal density-difference derivative. -/
theorem closedGapLeft_hasDerivAt_densityDifference
    {Q Q1 Q2 : ℝ → ℝ} {p z δ Λ y : ℝ}
    (hQ : HasDerivAt Q (Q1 y) y)
    (hQ1 : HasDerivAt Q1 (Q2 y) y) :
    HasDerivAt (closedGapLeft Q Q1 p z δ Λ)
      (leftMuDensity (curvature Q2) z (z - p) δ y -
        leftNuDensity (curvature Q2) p (z - p) Λ y) y := by
  have hdec := hasDerivAt_decreasingBoundary (a := z) hQ hQ1
  have hinc := hasDerivAt_increasingBoundary (a := p) hQ hQ1
  unfold closedGapLeft closedMuLeft closedNuLeft
  have hmu := (hdec.sub_const (decreasingBoundary Q Q1 z p)).div_const
    ((z - p) ^ 2 * δ)
  have hnu := (hinc.sub_const (increasingBoundary Q Q1 p p)).div_const
    ((z - p) * Λ)
  apply (hmu.sub hnu).congr_deriv
  rfl

/-- The right closed gap is a tail; its derivative is the negative right
density. -/
theorem closedGapRight_hasDerivAt_negDensity
    {Q Q1 Q2 : ℝ → ℝ} {z w Λ y : ℝ}
    (hQ : HasDerivAt Q (Q1 y) y)
    (hQ1 : HasDerivAt Q1 (Q2 y) y) :
    HasDerivAt (closedGapRight Q Q1 z w Λ)
      (-rightNuDensity (curvature Q2) w (w - z) Λ y) y := by
  have hwy : HasDerivAt (fun t : ℝ => w - t) (-1) y := by
    simpa only [id_eq] using (hasDerivAt_id y).const_sub w
  have hnum := (((hwy.pow 2).add (hwy.mul hQ1)).add hQ).sub_const (Q w)
  unfold closedGapRight
  apply (hnum.div_const ((w - z) * Λ)).congr_deriv
  unfold rightNuDensity curvature
  ring

/-- Exact meeting of the two closed branches from local integrability and the
two normalized masses. -/
theorem closedGap_match_on_Icc
    {Q Q1 Q2 : ℝ → ℝ} {p z w δ Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w))
    (hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p) δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p) Λ t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z) Λ t) = 1) :
    closedGapLeft Q Q1 p z δ Λ z = closedGapRight Q Q1 z w Λ z := by
  have hIcc_pz : Icc p z ⊆ Icc p w := fun _ ht =>
    ⟨ht.1, ht.2.trans hzw.le⟩
  have hIcc_zw : Icc z w ⊆ Icc p w := fun _ ht =>
    ⟨hpz.le.trans ht.1, ht.2⟩
  have hQpz : ∀ t ∈ uIcc p z, HasDerivAt Q (Q1 t) t := by
    intro t ht
    exact hQ t (hIcc_pz (by simpa [uIcc_of_le hpz.le] using ht))
  have hQ1pz : ∀ t ∈ uIcc p z, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    exact hQ1 t (hIcc_pz (by simpa [uIcc_of_le hpz.le] using ht))
  have hQzw : ∀ t ∈ uIcc z w, HasDerivAt Q (Q1 t) t := by
    intro t ht
    exact hQ t (hIcc_zw (by simpa [uIcc_of_le hzw.le] using ht))
  have hQ1zw : ∀ t ∈ uIcc z w, HasDerivAt Q1 (Q2 t) t := by
    intro t ht
    exact hQ1 t (hIcc_zw (by simpa [uIcc_of_le hzw.le] using ht))
  have hrawMu : ContinuousOn
      (fun t => (z - t) * curvature Q2 t) (Icc p z) := by
    exact ((continuous_const.sub continuous_id).continuousOn.mul
      (hκcont.mono hIcc_pz))
  have hrawLeft : ContinuousOn
      (fun t => (t - p) * curvature Q2 t) (Icc p z) := by
    exact ((continuous_id.sub continuous_const).continuousOn.mul
      (hκcont.mono hIcc_pz))
  have hrawRight : ContinuousOn
      (fun t => (w - t) * curvature Q2 t) (Icc z w) := by
    exact ((continuous_const.sub continuous_id).continuousOn.mul
      (hκcont.mono hIcc_zw))
  rw [closedGapLeft_eq_integral_difference hQpz hQ1pz
    (hrawMu.intervalIntegrable_of_Icc hpz.le)
    (hrawLeft.intervalIntegrable_of_Icc hpz.le)]
  rw [closedGapRight_eq_tail_integral hQzw hQ1zw
    (hrawRight.intervalIntegrable_of_Icc hzw.le)]
  linarith

/-- Direct compact-interval integration by parts.  The deterministic
closed-gap integral is exactly the right-density contributions minus the
left-mu contribution. -/
theorem coordinateGap_integral_eq_densityDifference
    {Q Q1 Q2 A D : ℝ → ℝ} {p z w δ Λ : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w))
    (hA : ∀ t ∈ Icc p w, HasDerivAt A (D t) t)
    (hDcont : ContinuousOn D (Icc p w))
    (hμmass :
      (∫ t in p..z, leftMuDensity (curvature Q2) z (z - p) δ t) = 1)
    (hνmass :
      (∫ t in p..z, leftNuDensity (curvature Q2) p (z - p) Λ t) +
        (∫ t in z..w, rightNuDensity (curvature Q2) w (w - z) Λ t) = 1) :
    (∫ t in p..w, coordinateGap Q Q1 p z w δ Λ t * D t) =
      (∫ t in p..z,
        A t * leftNuDensity (curvature Q2) p (z - p) Λ t) +
      (∫ t in z..w,
        A t * rightNuDensity (curvature Q2) w (w - z) Λ t) -
      (∫ t in p..z,
        A t * leftMuDensity (curvature Q2) z (z - p) δ t) := by
  have hpw : p < w := hpz.trans hzw
  have hIcc_pz : Icc p z ⊆ Icc p w := fun _ ht =>
    ⟨ht.1, ht.2.trans hzw.le⟩
  have hIcc_zw : Icc z w ⊆ Icc p w := fun _ ht =>
    ⟨hpz.le.trans ht.1, ht.2⟩
  have hAcont : ContinuousOn A (Icc p w) := fun t ht =>
    (hA t ht).continuousAt.continuousWithinAt
  have hμcont : ContinuousOn
      (leftMuDensity (curvature Q2) z (z - p) δ) (Icc p w) := by
    unfold leftMuDensity
    fun_prop
  have hνLcont : ContinuousOn
      (leftNuDensity (curvature Q2) p (z - p) Λ) (Icc p w) := by
    unfold leftNuDensity
    fun_prop
  have hνRcont : ContinuousOn
      (rightNuDensity (curvature Q2) w (w - z) Λ) (Icc p w) := by
    unfold rightNuDensity
    fun_prop
  have hleftRateInt : IntervalIntegrable
      (fun t => leftMuDensity (curvature Q2) z (z - p) δ t -
        leftNuDensity (curvature Q2) p (z - p) Λ t) volume p z :=
    ((hμcont.sub hνLcont).mono hIcc_pz).intervalIntegrable_of_Icc hpz.le
  have hrightRateInt : IntervalIntegrable
      (fun t => -rightNuDensity (curvature Q2) w (w - z) Λ t) volume z w :=
    (hνRcont.neg.mono hIcc_zw).intervalIntegrable_of_Icc hzw.le
  have hDleft : IntervalIntegrable D volume p z :=
    (hDcont.mono hIcc_pz).intervalIntegrable_of_Icc hpz.le
  have hDright : IntervalIntegrable D volume z w :=
    (hDcont.mono hIcc_zw).intervalIntegrable_of_Icc hzw.le
  have hleftParts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := closedGapLeft Q Q1 p z δ Λ) (v := A)
    (u' := fun t => leftMuDensity (curvature Q2) z (z - p) δ t -
      leftNuDensity (curvature Q2) p (z - p) Λ t) (v' := D)
    (a := p) (b := z)
    (fun t ht => closedGapLeft_hasDerivAt_densityDifference
      (hQ t (hIcc_pz (by simpa [uIcc_of_le hpz.le] using ht)))
      (hQ1 t (hIcc_pz (by simpa [uIcc_of_le hpz.le] using ht))))
    (fun t ht => hA t (hIcc_pz (by simpa [uIcc_of_le hpz.le] using ht)))
    hleftRateInt hDleft
  have hrightParts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := closedGapRight Q Q1 z w Λ) (v := A)
    (u' := fun t => -rightNuDensity (curvature Q2) w (w - z) Λ t)
    (v' := D) (a := z) (b := w)
    (fun t ht => closedGapRight_hasDerivAt_negDensity
      (hQ t (hIcc_zw (by simpa [uIcc_of_le hzw.le] using ht)))
      (hQ1 t (hIcc_zw (by simpa [uIcc_of_le hzw.le] using ht))))
    (fun t ht => hA t (hIcc_zw (by simpa [uIcc_of_le hzw.le] using ht)))
    hrightRateInt hDright
  have hmatch := closedGap_match_on_Icc hpz hzw hQ hQ1 hκcont hμmass hνmass
  have hQcont : ContinuousOn Q (Icc p w) := fun t ht =>
    (hQ t ht).continuousAt.continuousWithinAt
  have hQ1cont : ContinuousOn Q1 (Icc p w) := fun t ht =>
    (hQ1 t ht).continuousAt.continuousWithinAt
  have hclosedLeft : ContinuousOn (closedGapLeft Q Q1 p z δ Λ) (Icc p w) := by
    unfold closedGapLeft closedMuLeft closedNuLeft
      increasingBoundary decreasingBoundary
    fun_prop
  have hclosedRight : ContinuousOn (closedGapRight Q Q1 z w Λ) (Icc p w) := by
    unfold closedGapRight
    fun_prop
  have hgapcont : ContinuousOn (coordinateGap Q Q1 p z w δ Λ) (Icc p w) := by
    unfold coordinateGap
    apply ContinuousOn.if (s := Icc p w) (p := fun y => y ≤ z)
    · intro a ha
      have haz : a = z := frontier_Iic_subset z ha.2
      subst a
      exact hmatch
    · exact hclosedLeft.mono inter_subset_left
    · exact hclosedRight.mono inter_subset_left
  have hfullInt : IntervalIntegrable
      (fun t => coordinateGap Q Q1 p z w δ Λ t * D t) volume p w :=
    (hgapcont.mul hDcont).intervalIntegrable_of_Icc hpw.le
  have hleftInt : IntervalIntegrable
      (fun t => coordinateGap Q Q1 p z w δ Λ t * D t) volume p z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpz.le).2 <|
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpw.le).1 hfullInt).mono_set
        fun t ht => ⟨ht.1, ht.2.trans hzw.le⟩
  have hrightInt : IntervalIntegrable
      (fun t => coordinateGap Q Q1 p z w δ Λ t * D t) volume z w :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hzw.le).2 <|
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpw.le).1 hfullInt).mono_set
        fun t ht => ⟨hpz.trans ht.1, ht.2⟩
  have hμAInt : IntervalIntegrable
      (fun t => leftMuDensity (curvature Q2) z (z - p) δ t * A t)
      volume p z :=
    ((hμcont.mul hAcont).mono hIcc_pz).intervalIntegrable_of_Icc hpz.le
  have hνLAInt : IntervalIntegrable
      (fun t => leftNuDensity (curvature Q2) p (z - p) Λ t * A t)
      volume p z :=
    ((hνLcont.mul hAcont).mono hIcc_pz).intervalIntegrable_of_Icc hpz.le
  have hleftRateExpand :
      (∫ t in p..z,
        (leftMuDensity (curvature Q2) z (z - p) δ t -
          leftNuDensity (curvature Q2) p (z - p) Λ t) * A t) =
        (∫ t in p..z,
          leftMuDensity (curvature Q2) z (z - p) δ t * A t) -
        (∫ t in p..z,
          leftNuDensity (curvature Q2) p (z - p) Λ t * A t) := by
    rw [← intervalIntegral.integral_sub hμAInt hνLAInt]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hμAComm :
      (∫ t in p..z,
        leftMuDensity (curvature Q2) z (z - p) δ t * A t) =
        ∫ t in p..z,
          A t * leftMuDensity (curvature Q2) z (z - p) δ t := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hνLAComm :
      (∫ t in p..z,
        leftNuDensity (curvature Q2) p (z - p) Λ t * A t) =
        ∫ t in p..z,
          A t * leftNuDensity (curvature Q2) p (z - p) Λ t := by
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hrightRateNeg :
      (∫ t in z..w,
        -rightNuDensity (curvature Q2) w (w - z) Λ t * A t) =
        -(∫ t in z..w,
          A t * rightNuDensity (curvature Q2) w (w - z) Λ t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hleftActual :
      (∫ t in p..z, coordinateGap Q Q1 p z w δ Λ t * D t) =
        ∫ t in p..z, closedGapLeft Q Q1 p z δ Λ t * D t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hpz.le] at ht
    change coordinateGap Q Q1 p z w δ Λ t * D t =
      closedGapLeft Q Q1 p z δ Λ t * D t
    rw [coordinateGap_of_le ht.2]
  have hrightActual :
      (∫ t in z..w, coordinateGap Q Q1 p z w δ Λ t * D t) =
        ∫ t in z..w, closedGapRight Q Q1 z w Λ t * D t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hzw.le] at ht
    by_cases htz : t = z
    · subst t
      change coordinateGap Q Q1 p z w δ Λ z * D z =
        closedGapRight Q Q1 z w Λ z * D z
      rw [coordinateGap_of_le le_rfl, hmatch]
    · change coordinateGap Q Q1 p z w δ Λ t * D t =
        closedGapRight Q Q1 z w Λ t * D t
      rw [coordinateGap_of_ge (lt_of_le_of_ne ht.1 (Ne.symm htz))]
  rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt,
    hleftActual, hrightActual, hleftParts, hrightParts,
    closedGapLeft_at_p, closedGapRight_at_w, hleftRateExpand,
    hrightRateNeg, hmatch, hμAComm, hνLAComm]
  ring

/-- Local FTC reduction for a decreasing triangular factor. -/
theorem integral_decreasing_linear_mul_deriv_on_Icc
    {G H J : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt H (G t) t)
    (hJ : ∀ t ∈ Icc a b, HasDerivAt J (H t) t)
    (hGcont : ContinuousOn G (Icc a b)) :
    (∫ t in a..b, (b - t) * G t) =
      (J b - J a) - (b - a) * H a := by
  have hP : ∀ t ∈ uIcc a b,
      HasDerivAt (fun x => (b - x) * H x + J x) ((b - t) * G t) t := by
    intro t ht
    have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab] using ht
    convert! (((hasDerivAt_id t).const_sub b).mul (hH t ht')).add
      (hJ t ht') using 1
    simp [id_eq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP
    (((continuous_const.sub continuous_id).continuousOn.mul hGcont)
      |>.intervalIntegrable_of_Icc hab)]
  ring

/-- Local FTC reduction for an increasing triangular factor. -/
theorem integral_increasing_linear_mul_deriv_on_Icc
    {G H J : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hH : ∀ t ∈ Icc a b, HasDerivAt H (G t) t)
    (hJ : ∀ t ∈ Icc a b, HasDerivAt J (H t) t)
    (hGcont : ContinuousOn G (Icc a b)) :
    (∫ t in a..b, (t - a) * G t) =
      (b - a) * H b - (J b - J a) := by
  have hP : ∀ t ∈ uIcc a b,
      HasDerivAt (fun x => (x - a) * H x - J x) ((t - a) * G t) t := by
    intro t ht
    have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab] using ht
    convert! (((hasDerivAt_id t).sub_const a).mul (hH t ht')).sub
      (hJ t ht') using 1
    simp [id_eq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP
    (((continuous_id.sub continuous_const).continuousOn.mul hGcont)
      |>.intervalIntegrable_of_Icc hab)]
  ring

/-- The direct triangular density integrals reduce to the independently
expanded endpoint object using only local derivatives. -/
theorem expandedTransportK_eq_densityDifference_on_Icc
    {Q Q1 Q2 Q3 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t ∈ Icc p w, HasDerivAt Q2 (Q3 t) t)
    (hQ3cont : ContinuousOn Q3 (Icc p w))
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t)
    (hκcont : ContinuousOn (curvature Q2) (Icc p w)) :
    expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
        (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
      (∫ t in p..z, paperPrimitive Q Q1 (curvature Q2) (fun x => -Q3 x) t *
        leftNuDensity (curvature Q2) p (z - p)
          (coordinateLambda Q p z w) t) +
      (∫ t in z..w, paperPrimitive Q Q1 (curvature Q2) (fun x => -Q3 x) t *
        rightNuDensity (curvature Q2) w (w - z)
          (coordinateLambda Q p z w) t) -
      (∫ t in p..z, paperPrimitive Q Q1 (curvature Q2) (fun x => -Q3 x) t *
        leftMuDensity (curvature Q2) z (z - p)
          (coordinateDelta Q Q1 p z) t) := by
  let κ := curvature Q2
  let κ1 : ℝ → ℝ := fun t => -Q3 t
  let A := paperPrimitive Q Q1 κ κ1
  let H := transportH Q Q1 Q2
  let J := transportJ Q Q1
  let G : ℝ → ℝ := fun t => κ t * A t
  have hpw : p < w := hpz.trans hzw
  have hIcc_pz : Icc p z ⊆ Icc p w := fun _ ht =>
    ⟨ht.1, ht.2.trans hzw.le⟩
  have hIcc_zw : Icc z w ⊆ Icc p w := fun _ ht =>
    ⟨hpz.le.trans ht.1, ht.2⟩
  have hH : ∀ t ∈ Icc p w, HasDerivAt H (G t) t := by
    intro t ht
    dsimp [H, G, κ, κ1, A]
    exact transportH_hasDerivAt (hQ t ht) (hQ1 t ht) (hQ2 t ht)
      rfl rfl (hκpos t ht).ne'
  have hJ : ∀ t ∈ Icc p w, HasDerivAt J (H t) t := by
    intro t ht
    dsimp [J, H]
    exact transportJ_hasDerivAt (hQ t ht) (hQ1 t ht)
  have hQcont : ContinuousOn Q (Icc p w) := fun t ht =>
    (hQ t ht).continuousAt.continuousWithinAt
  have hQ1cont : ContinuousOn Q1 (Icc p w) := fun t ht =>
    (hQ1 t ht).continuousAt.continuousWithinAt
  have hAcont : ContinuousOn A (Icc p w) := by
    dsimp [A, κ1, κ]
    unfold paperPrimitive
    exact (continuousOn_const.mul (continuousOn_id.sub hQ1cont)).sub
      (hQcont.mul (hQ3cont.neg.div hκcont (by
        intro t ht
        exact (hκpos t ht).ne')))
  have hGcont : ContinuousOn G (Icc p w) := by
    dsimp [G, κ]
    exact hκcont.mul hAcont
  have hdecLeft :
      (∫ t in p..z, (z - t) * G t) =
        (J z - J p) - (z - p) * H p :=
    integral_decreasing_linear_mul_deriv_on_Icc hpz.le
      (fun t ht => hH t (hIcc_pz ht)) (fun t ht => hJ t (hIcc_pz ht))
      (hGcont.mono hIcc_pz)
  have hincLeft :
      (∫ t in p..z, (t - p) * G t) =
        (z - p) * H z - (J z - J p) :=
    integral_increasing_linear_mul_deriv_on_Icc hpz.le
      (fun t ht => hH t (hIcc_pz ht)) (fun t ht => hJ t (hIcc_pz ht))
      (hGcont.mono hIcc_pz)
  have hdecRight :
      (∫ t in z..w, (w - t) * G t) =
        (J w - J z) - (w - z) * H z :=
    integral_decreasing_linear_mul_deriv_on_Icc hzw.le
      (fun t ht => hH t (hIcc_zw ht)) (fun t ht => hJ t (hIcc_zw ht))
      (hGcont.mono hIcc_zw)
  have hδ : 0 < coordinateDelta Q Q1 p z :=
    coordinateDelta_pos hpz
      (fun t ht => hQ t (hIcc_pz ht))
      (fun t ht => hQ1 t (hIcc_pz ht))
      (hκcont.mono hIcc_pz) (fun t ht => hκpos t (hIcc_pz ht))
  have hΛ : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw hQ hQ1 hκcont hκpos
  have hμIntegral :
      (∫ t in p..z, A t * leftMuDensity κ z (z - p)
        (coordinateDelta Q Q1 p z) t) =
        (∫ t in p..z, (z - t) * G t) /
          ((z - p) ^ 2 * coordinateDelta Q Q1 p z) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [leftMuDensity, G]
    ring
  have hνLeftIntegral :
      (∫ t in p..z, A t * leftNuDensity κ p (z - p)
        (coordinateLambda Q p z w) t) =
        (∫ t in p..z, (t - p) * G t) /
          ((z - p) * coordinateLambda Q p z w) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [leftNuDensity, G]
    ring
  have hνRightIntegral :
      (∫ t in z..w, A t * rightNuDensity κ w (w - z)
        (coordinateLambda Q p z w) t) =
        (∫ t in z..w, (w - t) * G t) /
          ((w - z) * coordinateLambda Q p z w) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [rightNuDensity, G]
    ring
  have hendpoint : expectationEndpoint H J p z w (z - p) (w - z)
      (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
      expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
        (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) := by
    apply expectationEndpoint_eq_expandedTransportK rfl rfl
    · rfl
    · unfold coordinateLambda
      ring
    · exact sub_pos.mpr hpz
    · exact sub_pos.mpr hzw
    · exact hδ
    · exact hΛ
  change expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
      (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
    (∫ t in p..z, A t * leftNuDensity κ p (z - p)
      (coordinateLambda Q p z w) t) +
    (∫ t in z..w, A t * rightNuDensity κ w (w - z)
      (coordinateLambda Q p z w) t) -
    (∫ t in p..z, A t * leftMuDensity κ z (z - p)
      (coordinateDelta Q Q1 p z) t)
  rw [← hendpoint, hμIntegral, hνLeftIntegral, hνRightIntegral,
    hdecLeft, hincLeft, hdecRight]
  unfold expectationEndpoint
  field_simp [sub_ne_zero.mpr hpz.ne', sub_ne_zero.mpr hzw.ne', hδ.ne', hΛ.ne']
  ring

/-- Range-local central identity obtained by composing the direct integration
by parts with the endpoint primitive reduction. -/
theorem expandedTransportK_eq_coordinateTransportIntegral_on_Icc
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ} {p z w : ℝ}
    (hpz : p < z) (hzw : z < w)
    (hQ : ∀ t ∈ Icc p w, HasDerivAt Q (Q1 t) t)
    (hQ1 : ∀ t ∈ Icc p w, HasDerivAt Q1 (Q2 t) t)
    (hQ2 : ∀ t ∈ Icc p w, HasDerivAt Q2 (Q3 t) t)
    (hQ3 : ∀ t ∈ Icc p w, HasDerivAt Q3 (Q4 t) t)
    (hQ4cont : ContinuousOn Q4 (Icc p w))
    (hQpos : ∀ t ∈ Icc p w, 0 < Q t)
    (hκpos : ∀ t ∈ Icc p w, 0 < curvature Q2 t) :
    expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
        (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
      transportIntegral
        (coordinateGap Q Q1 p z w (coordinateDelta Q Q1 p z)
          (coordinateLambda Q p z w)) Q (curvature Q2)
        (PF4.CentralIdentity.derivedC4 Q Q1 Q2 (curvature Q2)
          (fun x => -Q3 x) (fun x => -Q4 x)) p w := by
  let κ := curvature Q2
  let κ1 : ℝ → ℝ := fun t => -Q3 t
  let κ2 : ℝ → ℝ := fun t => -Q4 t
  let A := paperPrimitive Q Q1 κ κ1
  let C4 := PF4.CentralIdentity.derivedC4 Q Q1 Q2 κ κ1 κ2
  let D := curvatureWeight Q κ C4
  have hpw : p < w := hpz.trans hzw
  have hIcc_pz : Icc p z ⊆ Icc p w := fun _ ht =>
    ⟨ht.1, ht.2.trans hzw.le⟩
  have hQcont : ContinuousOn Q (Icc p w) := fun t ht =>
    (hQ t ht).continuousAt.continuousWithinAt
  have hQ1cont : ContinuousOn Q1 (Icc p w) := fun t ht =>
    (hQ1 t ht).continuousAt.continuousWithinAt
  have hQ2cont : ContinuousOn Q2 (Icc p w) := fun t ht =>
    (hQ2 t ht).continuousAt.continuousWithinAt
  have hQ3cont : ContinuousOn Q3 (Icc p w) := fun t ht =>
    (hQ3 t ht).continuousAt.continuousWithinAt
  have hκcont : ContinuousOn κ (Icc p w) := by
    dsimp [κ]
    unfold curvature
    exact continuousOn_const.sub hQ2cont
  have hκ : ∀ t ∈ Icc p w, HasDerivAt κ (κ1 t) t := by
    intro t ht
    dsimp [κ, κ1]
    unfold curvature
    simpa only [id_eq] using (hQ2 t ht).const_sub 2
  have hκ1 : ∀ t ∈ Icc p w, HasDerivAt κ1 (κ2 t) t := by
    intro t ht
    dsimp [κ1, κ2]
    exact (hQ3 t ht).neg.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  have hA : ∀ t ∈ Icc p w, HasDerivAt A (D t) t := by
    intro t ht
    have hraw := PF4.CentralIdentity.paperPrimitive_hasDerivAt_primitiveRate
      (hQ t ht) (hQ1 t ht) (hκ t ht) (hκ1 t ht) (hκpos t ht).ne'
    apply hraw.congr_deriv
    dsimp [D, C4]
    exact (PF4.CentralIdentity.curvatureWeight_derivedC4
      (Q1 := Q1) (Q2 := Q2) (κ1 := κ1) (κ2 := κ2)
      (hQpos t ht).ne' (hκpos t ht).ne').symm
  have hC4cont : ContinuousOn C4 (Icc p w) := by
    dsimp [C4]
    unfold PF4.CentralIdentity.derivedC4 PF4.CentralIdentity.primitiveRate
    have hκ1cont : ContinuousOn κ1 (Icc p w) := by
      dsimp [κ1]
      exact hQ3cont.neg
    have hκ2cont : ContinuousOn κ2 (Icc p w) := by
      dsimp [κ2]
      exact hQ4cont.neg
    exact ((hQcont.pow 6).mul (hκcont.pow 2)).mul
      (((continuousOn_const.mul (continuousOn_const.sub hQ2cont)).sub
        (hQ1cont.mul (hκ1cont.div hκcont (by
          intro t ht
          exact (hκpos t ht).ne')))).sub
        (hQcont.mul (((hκ2cont.mul hκcont).sub (hκ1cont.pow 2)).div
          (hκcont.pow 2) (by
            intro t ht
            exact pow_ne_zero 2 (hκpos t ht).ne'))))
  have hDcont : ContinuousOn D (Icc p w) := by
    dsimp [D]
    unfold curvatureWeight
    exact hC4cont.div ((hQcont.pow 6).mul (hκcont.pow 2)) (by
      intro t ht
      exact mul_ne_zero (pow_ne_zero 6 (hQpos t ht).ne')
        (pow_ne_zero 2 (hκpos t ht).ne'))
  have hδ : 0 < coordinateDelta Q Q1 p z :=
    coordinateDelta_pos hpz
      (fun t ht => hQ t (hIcc_pz ht))
      (fun t ht => hQ1 t (hIcc_pz ht))
      (hκcont.mono hIcc_pz) (fun t ht => hκpos t (hIcc_pz ht))
  have hΛ : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw hQ hQ1 hκcont hκpos
  have hμmass :
      (∫ t in p..z, leftMuDensity κ z (z - p)
        (coordinateDelta Q Q1 p z) t) = 1 := by
    dsimp [κ]
    apply leftMuDensity_intervalIntegral_eq_one (sub_pos.mpr hpz) hδ
    rw [coordinateDelta_eq_triangular hpz
      (fun t ht => hQ t (hIcc_pz ht))
      (fun t ht => hQ1 t (hIcc_pz ht)) (hκcont.mono hIcc_pz)]
    field_simp [sub_ne_zero.mpr hpz.ne']
  have hνmass :
      (∫ t in p..z, leftNuDensity κ p (z - p)
        (coordinateLambda Q p z w) t) +
        (∫ t in z..w, rightNuDensity κ w (w - z)
          (coordinateLambda Q p z w) t) = 1 := by
    dsimp [κ]
    apply nuDensities_intervalIntegral_eq_one (sub_pos.mpr hpz)
      (sub_pos.mpr hzw) hΛ
    exact (coordinateLambda_eq_triangular hpz hzw hQ hQ1 hκcont).symm
  have hparts := coordinateGap_integral_eq_densityDifference hpz hzw hQ hQ1
    hκcont hA hDcont hμmass hνmass
  have hendpoint := expandedTransportK_eq_densityDifference_on_Icc hpz hzw
    hQ hQ1 hQ2 hQ3cont hκpos hκcont
  change expandedTransportK Q Q1 Q2 p z w (z - p) (w - z)
      (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) =
    ∫ t in p..w, coordinateGap Q Q1 p z w
      (coordinateDelta Q Q1 p z) (coordinateLambda Q p z w) t * D t
  rw [hparts]
  exact hendpoint

end PF4.LocalCentralIntegration
