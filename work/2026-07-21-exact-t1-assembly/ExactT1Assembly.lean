import PF4.CERT12OuterClosure
import PF4.TranslationQuotientAssembly

set_option linter.style.header false
set_option linter.unusedVariables false

namespace PF4.ExactT1Candidate

open PF4.ClearedJetCertificateBridge
open PF4.ContinuousQuotientBox
open PF4.CurvatureCoordinateRealization
open PF4.GlobalKernelJetIdentification
open PF4.TranslationQuotientSigns
open PF4.TranslationQuotientTower

private theorem normalizedQ_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < clearedQ (normalizedThetaSeriesJet 0 t)
      (normalizedThetaSeriesJet 1 t) (normalizedThetaSeriesJet 2 t) := by
  simpa only [← PF4.CERT12OuterClosure.normalizedSeriesJet_eq_globalNormalized] using
    PF4.CERT12OuterClosure.normalized_clearedQ_pos ht

private theorem normalizedF2_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < clearedF2 (normalizedThetaSeriesJet 0 t)
      (normalizedThetaSeriesJet 1 t) (normalizedThetaSeriesJet 2 t)
      (normalizedThetaSeriesJet 3 t) (normalizedThetaSeriesJet 4 t) := by
  simpa only [← PF4.CERT12OuterClosure.normalizedSeriesJet_eq_globalNormalized] using
    PF4.CERT12OuterClosure.normalized_clearedF2_pos ht

private theorem normalizedC4_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < clearedC4 (normalizedThetaSeriesJet 0 t)
      (normalizedThetaSeriesJet 1 t) (normalizedThetaSeriesJet 2 t)
      (normalizedThetaSeriesJet 3 t) (normalizedThetaSeriesJet 4 t)
      (normalizedThetaSeriesJet 5 t) (normalizedThetaSeriesJet 6 t) := by
  simpa only [← PF4.CERT12OuterClosure.normalizedSeriesJet_eq_globalNormalized] using
    PF4.CERT12OuterClosure.normalized_clearedC4_pos ht

private theorem global_clearedQ_pos : ∀ t, 0 <
    clearedQ (kernelJet 0 t) (kernelJet 1 t) (kernelJet 2 t) :=
  clearedQ_kernelJet_pos_of_nonneg fun t ht =>
    (clearedQ_thetaSeriesJet_pos_iff_normalized ht).2 (normalizedQ_pos ht)

private theorem global_clearedF2_pos : ∀ t, 0 <
    clearedF2 (kernelJet 0 t) (kernelJet 1 t) (kernelJet 2 t)
      (kernelJet 3 t) (kernelJet 4 t) :=
  clearedF2_kernelJet_pos_of_nonneg fun t ht =>
    (clearedF2_thetaSeriesJet_pos_iff_normalized ht).2 (normalizedF2_pos ht)

private theorem global_clearedC4_pos : ∀ t, 0 <
    clearedC4 (kernelJet 0 t) (kernelJet 1 t) (kernelJet 2 t)
      (kernelJet 3 t) (kernelJet 4 t) (kernelJet 5 t) (kernelJet 6 t) :=
  clearedC4_kernelJet_pos_of_nonneg fun t ht =>
    (clearedC4_thetaSeriesJet_pos_iff_normalized ht).2 (normalizedC4_pos ht)

private theorem kernel0_pos : ∀ t, 0 < kernelJet 0 t := by
  intro t
  simpa [kernelJet, iteratedDeriv_zero] using globalRiemannKernel_pos t

private theorem actualKernelSigns :
    (∀ t, 0 < kernelCurvature (kernelJet 0) (kernelJet 1) (kernelJet 2) t) ∧
    (∀ t, 0 < kernelF2
      (kernelCurvature (kernelJet 0) (kernelJet 1) (kernelJet 2))
      (jetQ1 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3))
      (jetQ2 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
        (kernelJet 4)) t) ∧
    (∀ t, 0 < kernelDeterminantC4
      (kernelCurvature (kernelJet 0) (kernelJet 1) (kernelJet 2))
      (jetQ1 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3))
      (jetQ2 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
        (kernelJet 4))
      (jetQ3 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
        (kernelJet 4) (kernelJet 5))
      (jetQ4 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
        (kernelJet 4) (kernelJet 5) (kernelJet 6)) t) :=
  kernelSigns_of_clearedSigns kernel0_pos global_clearedQ_pos
    global_clearedF2_pos global_clearedC4_pos

private theorem actual_lowerLambda_pos : ∀ x m r, x < m → m < r →
    0 < lowerLambda
      (logSlope (kernelJet 0) (kernelJet 1))
      (kernelCurvature (kernelJet 0) (kernelJet 1) (kernelJet 2)) x m r := by
  let q := kernelCurvature (kernelJet 0) (kernelJet 1) (kernelJet 2)
  let q1 := jetQ1 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
  let q2 := jetQ2 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
    (kernelJet 4)
  have htower := curvatureDerivativeTower_of_rawJet
    (hasDerivAt_kernelJet 0) (hasDerivAt_kernelJet 1)
    (hasDerivAt_kernelJet 2) (hasDerivAt_kernelJet 3)
    (hasDerivAt_kernelJet 4) (hasDerivAt_kernelJet 5) kernel0_pos
  have hS : ∀ u, HasDerivAt (logSlope (kernelJet 0) (kernelJet 1))
      (-q u) u := fun u =>
    hasDerivAt_logSlope (hasDerivAt_kernelJet 0) (hasDerivAt_kernelJet 1)
      kernel0_pos u
  intro x m r hxm hmr
  exact lowerLambda_pos_of_actualCoordinate hS htower.1 htower.2.1
    htower.2.2.1 actualKernelSigns.1 actualKernelSigns.2.1 hxm hmr

theorem actual_firstQuotD_pos {a b : ℝ} (hab : a < b) : ∀ t, 0 <
    firstQuotD (kernelJet 0) (kernelJet 1) a b t :=
  firstQuotD_pos_of_kernelCurvature_pos
    (hasDerivAt_kernelJet 0) (hasDerivAt_kernelJet 1) kernel0_pos
    actualKernelSigns.1 hab

theorem actual_secondQuotD_pos {a c b : ℝ} (hac : a < c) (hcb : c < b) :
    ∀ t, 0 < secondQuotD (kernelJet 0) (kernelJet 1) (kernelJet 2)
      a c b t :=
  secondQuotD_pos_of_lowerLambda_pos
    (hasDerivAt_kernelJet 0) (hasDerivAt_kernelJet 1) kernel0_pos
    actualKernelSigns.1 actual_lowerLambda_pos hac hcb

private theorem translationMinor_two_factor
    {Φ : ℝ → ℝ} (hΦpos : ∀ t, 0 < Φ t)
    (t₁ t₂ y₁ y₂ : ℝ) :
    PF4.translationMinor Φ ![t₁, t₂] ![y₁, y₂] =
      Φ (t₁ - y₁) * Φ (t₂ - y₁) *
        (firstQuot Φ y₁ y₂ t₂ - firstQuot Φ y₁ y₂ t₁) := by
  unfold PF4.translationMinor PF4.translationMatrix firstQuot
  simp [Matrix.det_fin_two]
  field_simp [(hΦpos (t₁ - y₁)).ne', (hΦpos (t₂ - y₁)).ne']

private theorem translationMinor_three_factor
    {Φ : ℝ → ℝ} (hΦpos : ∀ t, 0 < Φ t)
    (t₁ t₂ t₃ y₁ y₂ y₃ : ℝ) :
    PF4.translationMinor Φ ![t₁, t₂, t₃] ![y₁, y₂, y₃] =
      Φ (t₁ - y₁) * Φ (t₂ - y₁) * Φ (t₃ - y₁) *
        normalizedDet3
          (firstQuot Φ y₁ y₂ t₁) (firstQuot Φ y₁ y₃ t₁)
          (firstQuot Φ y₁ y₂ t₂) (firstQuot Φ y₁ y₃ t₂)
          (firstQuot Φ y₁ y₂ t₃) (firstQuot Φ y₁ y₃ t₃) := by
  unfold PF4.translationMinor PF4.translationMatrix firstQuot normalizedDet3
  simp [Matrix.det_fin_three]
  field_simp [(hΦpos (t₁ - y₁)).ne', (hΦpos (t₂ - y₁)).ne',
    (hΦpos (t₃ - y₁)).ne']

theorem translationMinor_one_pos (t y : ℝ) :
    0 < PF4.translationMinor PF4.globalRiemannKernel ![t] ![y] := by
  simpa [PF4.translationMinor, PF4.translationMatrix] using
    globalRiemannKernel_pos (t - y)

theorem translationMinor_two_pos
    {t₁ t₂ y₁ y₂ : ℝ} (ht₁₂ : t₁ < t₂) (hy₁₂ : y₁ < y₂) :
    0 < PF4.translationMinor PF4.globalRiemannKernel
      ![t₁, t₂] ![y₁, y₂] := by
  let Φ := kernelJet 0
  let Φ1 := kernelJet 1
  have hdiff : 0 < firstQuot Φ y₁ y₂ t₂ - firstQuot Φ y₁ y₂ t₁ :=
    forwardDiff_pos_of_global_deriv_pos ht₁₂
      (fun t => hasDerivAt_firstQuot (hasDerivAt_kernelJet 0) kernel0_pos y₁ y₂ t)
      (continuous_firstQuotD (continuous_kernelJet 0) (continuous_kernelJet 1)
        kernel0_pos y₁ y₂)
      (actual_firstQuotD_pos hy₁₂)
  have hfactor := translationMinor_two_factor kernel0_pos t₁ t₂ y₁ y₂
  have hpos : 0 < Φ (t₁ - y₁) * Φ (t₂ - y₁) *
      (firstQuot Φ y₁ y₂ t₂ - firstQuot Φ y₁ y₂ t₁) :=
    mul_pos (mul_pos (kernel0_pos (t₁ - y₁)) (kernel0_pos (t₂ - y₁))) hdiff
  simpa [Φ, kernelJet, iteratedDeriv_zero] using hfactor.symm ▸ hpos

theorem translationMinor_three_pos
    {t₁ t₂ t₃ y₁ y₂ y₃ : ℝ}
    (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃)
    (hy₁₂ : y₁ < y₂) (hy₂₃ : y₂ < y₃) :
    0 < PF4.translationMinor PF4.globalRiemannKernel
      ![t₁, t₂, t₃] ![y₁, y₂, y₃] := by
  let Φ := kernelJet 0
  let Φ1 := kernelJet 1
  let Φ2 := kernelJet 2
  have hfirst : ∀ t, 0 < firstQuotD Φ Φ1 y₁ y₂ t :=
    actual_firstQuotD_pos hy₁₂
  have hsecond : ∀ t, 0 < secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t :=
    actual_secondQuotD_pos hy₁₂ hy₂₃
  have hnorm : 0 < normalizedDet3
      (firstQuot Φ y₁ y₂ t₁) (firstQuot Φ y₁ y₃ t₁)
      (firstQuot Φ y₁ y₂ t₂) (firstQuot Φ y₁ y₃ t₂)
      (firstQuot Φ y₁ y₂ t₃) (firstQuot Φ y₁ y₃ t₃) := by
    apply normalizedDet3_pos_of_derivativeDet_pos ht₁₂ ht₂₃
      (fun t => hasDerivAt_firstQuot (hasDerivAt_kernelJet 0) kernel0_pos y₁ y₂ t)
      (fun t => hasDerivAt_firstQuot (hasDerivAt_kernelJet 0) kernel0_pos y₁ y₃ t)
      (continuous_firstQuotD (continuous_kernelJet 0) (continuous_kernelJet 1)
        kernel0_pos y₁ y₂)
      (continuous_firstQuotD (continuous_kernelJet 0) (continuous_kernelJet 1)
        kernel0_pos y₁ y₃)
    intro s₀ hs₀ s₁ hs₁
    rw [firstQuotD_factor hfirst y₃ s₀, firstQuotD_factor hfirst y₃ s₁,
      rowDet2_factored]
    exact mul_pos (mul_pos (hfirst s₀) (hfirst s₁))
      (forwardDiff_pos_of_global_deriv_pos (lt_trans hs₀.2 hs₁.1)
        (fun t => hasDerivAt_secondQuot
          (hasDerivAt_kernelJet 0) (hasDerivAt_kernelJet 1)
          kernel0_pos hfirst y₃ t)
        (continuous_secondQuotD
          (continuous_kernelJet 0) (continuous_kernelJet 1) (continuous_kernelJet 2)
          kernel0_pos hfirst y₃)
        hsecond)
  have hfactor := translationMinor_three_factor kernel0_pos t₁ t₂ t₃ y₁ y₂ y₃
  have hpos : 0 < Φ (t₁ - y₁) * Φ (t₂ - y₁) * Φ (t₃ - y₁) *
      normalizedDet3
        (firstQuot Φ y₁ y₂ t₁) (firstQuot Φ y₁ y₃ t₁)
        (firstQuot Φ y₁ y₂ t₂) (firstQuot Φ y₁ y₃ t₂)
        (firstQuot Φ y₁ y₂ t₃) (firstQuot Φ y₁ y₃ t₃) :=
    mul_pos
      (mul_pos (mul_pos (kernel0_pos (t₁ - y₁)) (kernel0_pos (t₂ - y₁)))
        (kernel0_pos (t₃ - y₁))) hnorm
  simpa [Φ, kernelJet, iteratedDeriv_zero] using hfactor.symm ▸ hpos

theorem translationMinor_four_pos
    {t₁ t₂ t₃ t₄ y₁ y₂ y₃ y₄ : ℝ}
    (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃) (ht₃₄ : t₃ < t₄)
    (hy₁₂ : y₁ < y₂) (hy₂₃ : y₂ < y₃) (hy₃₄ : y₃ < y₄) :
    0 < PF4.translationMinor PF4.globalRiemannKernel
      ![t₁, t₂, t₃, t₄] ![y₁, y₂, y₃, y₄] := by
  have h := translationMinor_pos_of_quotient_tower_signs
    ht₁₂ ht₂₃ ht₃₄
    (hasDerivAt_kernelJet 0) (hasDerivAt_kernelJet 1)
    (hasDerivAt_kernelJet 2) (continuous_kernelJet 3) kernel0_pos
    (actual_firstQuotD_pos hy₁₂)
    (actual_secondQuotD_pos hy₁₂ hy₂₃)
    (PF4.CERT12OuterClosure.terminalQuotD_global_kernel_pos
      hy₁₂ hy₂₃ hy₃₄)
  simpa [kernelJet, iteratedDeriv_zero] using h

/-- Exact target T1: every translation minor of the global Riemann kernel at
orders one through four is strictly positive for arbitrary strictly increasing
real row and column nodes. -/
theorem strictPFUpTo_four :
    PF4.StrictPFUpTo PF4.globalRiemannKernel 4 := by
  intro k hk₁ hk₄ x y hx hy
  have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · have hxv : x = ![x 0] := by
      funext i
      fin_cases i
      rfl
    have hyv : y = ![y 0] := by
      funext i
      fin_cases i
      rfl
    rw [hxv, hyv]
    exact translationMinor_one_pos (x 0) (y 0)
  · have hx₁₂ : x 0 < x 1 := hx (by decide)
    have hy₁₂ : y 0 < y 1 := hy (by decide)
    have hxv : x = ![x 0, x 1] := by
      funext i
      fin_cases i <;> rfl
    have hyv : y = ![y 0, y 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hxv, hyv]
    exact translationMinor_two_pos hx₁₂ hy₁₂
  · have hx₁₂ : x 0 < x 1 := hx (by decide)
    have hx₂₃ : x 1 < x 2 := hx (by decide)
    have hy₁₂ : y 0 < y 1 := hy (by decide)
    have hy₂₃ : y 1 < y 2 := hy (by decide)
    have hxv : x = ![x 0, x 1, x 2] := by
      funext i
      fin_cases i <;> rfl
    have hyv : y = ![y 0, y 1, y 2] := by
      funext i
      fin_cases i <;> rfl
    rw [hxv, hyv]
    exact translationMinor_three_pos hx₁₂ hx₂₃ hy₁₂ hy₂₃
  · have hx₁₂ : x 0 < x 1 := hx (by decide)
    have hx₂₃ : x 1 < x 2 := hx (by decide)
    have hx₃₄ : x 2 < x 3 := hx (by decide)
    have hy₁₂ : y 0 < y 1 := hy (by decide)
    have hy₂₃ : y 1 < y 2 := hy (by decide)
    have hy₃₄ : y 2 < y 3 := hy (by decide)
    have hxv : x = ![x 0, x 1, x 2, x 3] := by
      funext i
      fin_cases i <;> rfl
    have hyv : y = ![y 0, y 1, y 2, y 3] := by
      funext i
      fin_cases i <;> rfl
    rw [hxv, hyv]
    exact translationMinor_four_pos hx₁₂ hx₂₃ hx₃₄ hy₁₂ hy₂₃ hy₃₄

#print axioms PF4.ExactT1Candidate.strictPFUpTo_four

end PF4.ExactT1Candidate
