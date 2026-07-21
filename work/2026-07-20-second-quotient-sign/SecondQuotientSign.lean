import PF4.TranslationQuotientTower
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Closed second translation-quotient sign

The maintained second quotient derivative is factored through the exact
lower-order `Lambda` object. Its sign is never assumed.
-/

namespace PF4.Advancement.SecondQuotientSign

open PF4.TranslationQuotientTower

noncomputable def logSlope (Φ Φ1 : ℝ → ℝ) : ℝ → ℝ :=
  fun t => Φ1 t / Φ t

noncomputable def kernelCurvature (Φ Φ1 Φ2 : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (Φ1 t ^ 2 - Φ t * Φ2 t) / Φ t ^ 2

noncomputable def slopeChord (S : ℝ → ℝ) (x r : ℝ) : ℝ :=
  S x - S r

noncomputable def curvatureMean (S q : ℝ → ℝ) (x r : ℝ) : ℝ :=
  (q r - q x) / slopeChord S x r

/-- The same three-point lower-order object denoted `Lambda` in the paper. -/
noncomputable def lowerLambda (S q : ℝ → ℝ) (x m r : ℝ) : ℝ :=
  slopeChord S x r + curvatureMean S q x m - curvatureMean S q m r

/-- The logarithmic rate appearing directly after differentiating `v_b/v_c`. -/
noncomputable def orderThreeRate (S q : ℝ → ℝ) (x m r : ℝ) : ℝ :=
  slopeChord S x m + curvatureMean S q x r - curvatureMean S q m r

theorem hasDerivAt_logSlope
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t) (t : ℝ) :
    HasDerivAt (logSlope Φ Φ1) (-(kernelCurvature Φ Φ1 Φ2 t)) t := by
  unfold logSlope
  have h := (hΦ1 t).fun_div (hΦ t) (hΦpos t).ne'
  exact h.congr_deriv (by unfold kernelCurvature; ring)

theorem logSlope_strictAnti_of_kernelCurvature_pos
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t)
    (hqpos : ∀ t, 0 < kernelCurvature Φ Φ1 Φ2 t) :
    StrictAnti (logSlope Φ Φ1) := by
  apply strictAnti_of_hasDerivAt_neg
    (fun t => hasDerivAt_logSlope hΦ hΦ1 hΦpos t)
  intro t
  exact neg_neg_of_pos (hqpos t)

theorem slopeChord_pos_of_lt
    {S : ℝ → ℝ} (hS : StrictAnti S) {x r : ℝ} (hxr : x < r) :
    0 < slopeChord S x r := by
  unfold slopeChord
  exact sub_pos.mpr (hS hxr)

theorem firstQuotD_eq_firstQuot_mul_slopeChord
    {Φ Φ1 : ℝ → ℝ} (hΦpos : ∀ t, 0 < Φ t) (a b t : ℝ) :
    firstQuotD Φ Φ1 a b t = firstQuot Φ a b t *
      slopeChord (logSlope Φ Φ1) (t - b) (t - a) := by
  unfold firstQuotD firstQuot logSlope slopeChord
  field_simp [(hΦpos (t - a)).ne', (hΦpos (t - b)).ne']

theorem firstQuotD_pos
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t)
    (hqpos : ∀ t, 0 < kernelCurvature Φ Φ1 Φ2 t)
    {a b : ℝ} (hab : a < b) :
    ∀ t, 0 < firstQuotD Φ Φ1 a b t := by
  have hanti := logSlope_strictAnti_of_kernelCurvature_pos hΦ hΦ1 hΦpos hqpos
  intro t
  rw [firstQuotD_eq_firstQuot_mul_slopeChord hΦpos]
  have hp : t - b < t - a := by linarith
  exact mul_pos (div_pos (hΦpos (t - b)) (hΦpos (t - a)))
    (slopeChord_pos_of_lt hanti hp)

/-- Exact first-level logarithmic-rate factorization. -/
theorem firstQuotD2_eq_firstQuotD_mul_rate
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t)
    (a b t : ℝ)
    (hA : slopeChord (logSlope Φ Φ1) (t - b) (t - a) ≠ 0) :
    firstQuotD2 Φ Φ1 Φ2 a b t = firstQuotD Φ Φ1 a b t *
      (slopeChord (logSlope Φ Φ1) (t - b) (t - a) +
        curvatureMean (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2)
          (t - b) (t - a)) := by
  let S := logSlope Φ Φ1
  let q := kernelCurvature Φ Φ1 Φ2
  let A := slopeChord S (t - b) (t - a)
  let M := curvatureMean S q (t - b) (t - a)
  have hSb : HasDerivAt (fun s => S (s - b)) (-q (t - b)) t := by
    have h := (hasDerivAt_logSlope hΦ hΦ1 hΦpos (t - b)).comp t
      ((hasDerivAt_id t).sub_const b)
    simpa [S, q, Function.comp_def] using h
  have hSa : HasDerivAt (fun s => S (s - a)) (-q (t - a)) t := by
    have h := (hasDerivAt_logSlope hΦ hΦ1 hΦpos (t - a)).comp t
      ((hasDerivAt_id t).sub_const a)
    simpa [S, q, Function.comp_def] using h
  have hChordRaw : HasDerivAt
      ((fun s => S (s - b)) - fun s => S (s - a))
      (q (t - a) - q (t - b)) t :=
    (hSb.sub hSa).congr_deriv (by ring)
  have hChord : HasDerivAt
      (fun s => slopeChord S (s - b) (s - a))
      (q (t - a) - q (t - b)) t := by
    apply hChordRaw.congr_of_eventuallyEq
    filter_upwards [] with s
    rfl
  have hProduct := (hasDerivAt_firstQuot hΦ hΦpos a b t).mul hChord
  have hANe : A ≠ 0 := by
    simpa [A, S] using hA
  have hFactor : firstQuotD Φ Φ1 a b t = firstQuot Φ a b t * A := by
    simpa [A, S] using firstQuotD_eq_firstQuot_mul_slopeChord hΦpos a b t
  have hMean : q (t - a) - q (t - b) = A * M := by
    change q (t - a) - q (t - b) =
      A * ((q (t - a) - q (t - b)) / A)
    field_simp [hANe]
  have hProductRate : HasDerivAt
      (fun s => firstQuot Φ a b s * slopeChord S (s - b) (s - a))
      (firstQuotD Φ Φ1 a b t * (A + M)) t := by
    exact hProduct.congr_deriv (by
      rw [hMean]
      calc
        firstQuotD Φ Φ1 a b t * A + firstQuot Φ a b t * (A * M) =
            firstQuotD Φ Φ1 a b t * A +
              (firstQuot Φ a b t * A) * M := by ring
        _ = firstQuotD Φ Φ1 a b t * (A + M) := by rw [← hFactor]; ring)
  have hFactored : HasDerivAt (firstQuotD Φ Φ1 a b)
      (firstQuotD Φ Φ1 a b t * (A + M)) t := by
    apply hProductRate.congr_of_eventuallyEq
    filter_upwards [] with s
    exact firstQuotD_eq_firstQuot_mul_slopeChord hΦpos a b s
  have hMaintained := hasDerivAt_firstQuotD hΦ hΦ1 hΦpos a b t
  have hUnique := hMaintained.unique hFactored
  simpa [S, q, A, M] using hUnique

/-- The direct rate difference is exactly the paper's order-three rate. -/
theorem levelOneRate_sub_eq_orderThreeRate
    (S q : ℝ → ℝ) (x m r : ℝ) :
    (slopeChord S x r + curvatureMean S q x r) -
        (slopeChord S m r + curvatureMean S q m r) =
      orderThreeRate S q x m r := by
  unfold orderThreeRate slopeChord
  ring

/-- The weighted-mean split exposes the exact positive `Lambda` factor. -/
theorem orderThreeRate_eq_lambdaFactor
    (S q : ℝ → ℝ) (x m r : ℝ)
    (hAxm : slopeChord S x m ≠ 0)
    (hAmr : slopeChord S m r ≠ 0)
    (hAxr : slopeChord S x r ≠ 0) :
    orderThreeRate S q x m r =
      slopeChord S x m / slopeChord S x r * lowerLambda S q x m r := by
  unfold slopeChord at hAxm hAmr hAxr
  unfold orderThreeRate lowerLambda curvatureMean slopeChord
  field_simp [hAxm, hAmr, hAxr]
  ring

/-- Exact maintained second-quotient derivative factorization through the
paper's lower-order `Lambda`. -/
theorem secondQuotD_eq_lambdaProduct
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t)
    (a c b : ℝ)
    (hfirst : ∀ t, 0 < firstQuotD Φ Φ1 a c t)
    (hAb : ∀ t, slopeChord (logSlope Φ Φ1) (t - b) (t - a) ≠ 0)
    (hAc : ∀ t, slopeChord (logSlope Φ Φ1) (t - c) (t - a) ≠ 0)
    (hAbc : ∀ t, slopeChord (logSlope Φ Φ1) (t - b) (t - c) ≠ 0)
    (t : ℝ) :
    secondQuotD Φ Φ1 Φ2 a c b t =
      secondQuot Φ Φ1 a c b t *
        (slopeChord (logSlope Φ Φ1) (t - b) (t - c) /
          slopeChord (logSlope Φ Φ1) (t - b) (t - a)) *
        lowerLambda (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2)
          (t - b) (t - c) (t - a) := by
  rw [show secondQuotD Φ Φ1 Φ2 a c b t =
      secondQuot Φ Φ1 a c b t *
        ((slopeChord (logSlope Φ Φ1) (t - b) (t - a) +
            curvatureMean (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2)
              (t - b) (t - a)) -
          (slopeChord (logSlope Φ Φ1) (t - c) (t - a) +
            curvatureMean (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2)
              (t - c) (t - a))) by
    unfold secondQuotD secondQuot
    rw [firstQuotD2_eq_firstQuotD_mul_rate hΦ hΦ1 hΦpos a b t (hAb t),
      firstQuotD2_eq_firstQuotD_mul_rate hΦ hΦ1 hΦpos a c t (hAc t)]
    field_simp [(hfirst t).ne']]
  rw [levelOneRate_sub_eq_orderThreeRate]
  rw [orderThreeRate_eq_lambdaFactor _ _ _ _ _ (hAbc t) (hAc t) (hAb t)]
  ring

/-- Ordered columns, positive kernel curvature, and the literal lower-order
`Lambda>0` theorem discharge the maintained second quotient sign premise. -/
theorem secondQuotD_pos_of_lowerLambda_pos
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t)
    (hqpos : ∀ t, 0 < kernelCurvature Φ Φ1 Φ2 t)
    (hLambda : ∀ x m r, x < m → m < r →
      0 < lowerLambda (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2) x m r)
    {a c b : ℝ} (hac : a < c) (hcb : c < b) :
    ∀ t, 0 < secondQuotD Φ Φ1 Φ2 a c b t := by
  have hanti := logSlope_strictAnti_of_kernelCurvature_pos hΦ hΦ1 hΦpos hqpos
  have hfirstC := firstQuotD_pos hΦ hΦ1 hΦpos hqpos hac
  have hfirstB := firstQuotD_pos hΦ hΦ1 hΦpos hqpos (hac.trans hcb)
  have hAb : ∀ s,
      slopeChord (logSlope Φ Φ1) (s - b) (s - a) ≠ 0 := by
    intro s
    exact (slopeChord_pos_of_lt hanti (by linarith)).ne'
  have hAc : ∀ s,
      slopeChord (logSlope Φ Φ1) (s - c) (s - a) ≠ 0 := by
    intro s
    exact (slopeChord_pos_of_lt hanti (by linarith)).ne'
  have hAbc : ∀ s,
      slopeChord (logSlope Φ Φ1) (s - b) (s - c) ≠ 0 := by
    intro s
    exact (slopeChord_pos_of_lt hanti (by linarith)).ne'
  intro t
  have hpbc : t - b < t - c := by linarith
  have hpca : t - c < t - a := by linarith
  have hpba : t - b < t - a := hpbc.trans hpca
  have hAbcPos := slopeChord_pos_of_lt hanti hpbc
  have hAcaPos := slopeChord_pos_of_lt hanti hpca
  have hAbaPos := slopeChord_pos_of_lt hanti hpba
  rw [secondQuotD_eq_lambdaProduct hΦ hΦ1 hΦpos a c b hfirstC hAb hAc hAbc]
  have hsecondQuot : 0 < secondQuot Φ Φ1 a c b t := by
    unfold secondQuot
    exact div_pos (hfirstB t) (hfirstC t)
  have hLam := hLambda (t - b) (t - c) (t - a) hpbc hpca
  positivity

end PF4.Advancement.SecondQuotientSign

#print axioms PF4.Advancement.SecondQuotientSign.firstQuotD2_eq_firstQuotD_mul_rate
#print axioms PF4.Advancement.SecondQuotientSign.secondQuotD_eq_lambdaProduct
#print axioms PF4.Advancement.SecondQuotientSign.secondQuotD_pos_of_lowerLambda_pos
