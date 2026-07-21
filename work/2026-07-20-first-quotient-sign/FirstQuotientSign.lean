import PF4.TranslationQuotientTower
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Closed first translation-quotient sign

This file derives the first strict quotient sign from the literal kernel
curvature `q=(Φ1²-Φ*Φ2)/Φ²`. It does not assume monotonicity of the logarithmic
slope or positivity of `firstQuotD`.
-/

namespace PF4.Advancement.FirstQuotientSign

open PF4.TranslationQuotientTower

/-- The logarithmic slope, defined without introducing a logarithm object. -/
noncomputable def logSlope (Φ Φ1 : ℝ → ℝ) : ℝ → ℝ :=
  fun t => Φ1 t / Φ t

/-- The exact positive curvature boundary in kernel jets. -/
noncomputable def kernelCurvature (Φ Φ1 Φ2 : ℝ → ℝ) : ℝ → ℝ :=
  fun t => (Φ1 t ^ 2 - Φ t * Φ2 t) / Φ t ^ 2

/-- Exact closed derivative identity `S'=-q`. -/
theorem hasDerivAt_logSlope
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t) (t : ℝ) :
    HasDerivAt (logSlope Φ Φ1) (-(kernelCurvature Φ Φ1 Φ2 t)) t := by
  unfold logSlope
  have h := (hΦ1 t).fun_div (hΦ t) (hΦpos t).ne'
  exact h.congr_deriv (by unfold kernelCurvature; ring)

/-- Positive exact curvature makes the actual logarithmic slope strictly
decreasing; monotonicity is a conclusion, not a premise. -/
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

/-- Exact factorization of the maintained first quotient derivative into a
positive kernel ratio and an oriented logarithmic-slope difference. -/
theorem firstQuotD_eq_firstQuot_mul_logSlopeDiff
    {Φ Φ1 : ℝ → ℝ} (hΦpos : ∀ t, 0 < Φ t) (a b t : ℝ) :
    firstQuotD Φ Φ1 a b t =
      firstQuot Φ a b t *
        (logSlope Φ Φ1 (t - b) - logSlope Φ Φ1 (t - a)) := by
  unfold firstQuotD firstQuot logSlope
  field_simp [(hΦpos (t - a)).ne', (hΦpos (t - b)).ne']

/-- The first open sign premise of the translation quotient tower follows
globally from ordered columns, positive `Φ`, and positive exact curvature. -/
theorem firstQuotD_pos_of_kernelCurvature_pos
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t)
    (hqpos : ∀ t, 0 < kernelCurvature Φ Φ1 Φ2 t)
    {a b : ℝ} (hab : a < b) :
    ∀ t, 0 < firstQuotD Φ Φ1 a b t := by
  have hanti :=
    logSlope_strictAnti_of_kernelCurvature_pos hΦ hΦ1 hΦpos hqpos
  intro t
  rw [firstQuotD_eq_firstQuot_mul_logSlopeDiff hΦpos]
  have hpoints : t - b < t - a := by linarith
  have hslope :
      0 < logSlope Φ Φ1 (t - b) - logSlope Φ Φ1 (t - a) :=
    sub_pos.mpr (hanti hpoints)
  have hquot : 0 < firstQuot Φ a b t := by
    unfold firstQuot
    exact div_pos (hΦpos (t - b)) (hΦpos (t - a))
  exact mul_pos hquot hslope

end PF4.Advancement.FirstQuotientSign

#print axioms PF4.Advancement.FirstQuotientSign.hasDerivAt_logSlope
#print axioms PF4.Advancement.FirstQuotientSign.firstQuotD_pos_of_kernelCurvature_pos
