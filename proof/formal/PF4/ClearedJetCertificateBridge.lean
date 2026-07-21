import PF4.LocalFinalAssembly
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Cleared raw-jet interface for the exact Riemann sign certificate

The certificate works with raw derivatives `a0,...,a6`; the maintained
coordinate proof works with logarithmic curvature and its derivatives.  This
file gives an exact algebraic and differential bridge between those forms.
-/

namespace PF4.ClearedJetCertificateBridge

open PF4.C4Invariant PF4.CurvatureCoordinateRealization
open PF4.CoordinateSignBridge
open PF4.Curvature
open PF4.TranslationQuotientPsi PF4.TranslationQuotientSigns
open PF4.TranslationQuotientTower
open Set

/-- A raw derivative normalized by the positive zeroth kernel jet. -/
noncomputable def normalizedJet (f0 fj : ℝ → ℝ) : ℝ → ℝ :=
  fun u => fj u / f0 u

/-- Logarithmic cumulants as polynomials in normalized raw moments. -/
def cumulant2 (m1 m2 : ℝ) : ℝ := m2 - m1 ^ 2
def cumulant3 (m1 m2 m3 : ℝ) : ℝ :=
  m3 - 3 * m2 * m1 + 2 * m1 ^ 3
def cumulant4 (m1 m2 m3 m4 : ℝ) : ℝ :=
  m4 - 4 * m3 * m1 - 3 * m2 ^ 2 + 12 * m2 * m1 ^ 2 - 6 * m1 ^ 4
def cumulant5 (m1 m2 m3 m4 m5 : ℝ) : ℝ :=
  m5 - 5 * m1 * m4 - 10 * m2 * m3 + 20 * m1 ^ 2 * m3 +
    30 * m1 * m2 ^ 2 - 60 * m1 ^ 3 * m2 + 24 * m1 ^ 5
def cumulant6 (m1 m2 m3 m4 m5 m6 : ℝ) : ℝ :=
  m6 - 6 * m1 * m5 - 15 * m2 * m4 - 10 * m3 ^ 2 +
    30 * m1 ^ 2 * m4 + 120 * m1 * m2 * m3 + 30 * m2 ^ 3 -
    120 * m1 ^ 3 * m3 - 270 * m1 ^ 2 * m2 ^ 2 +
    360 * m1 ^ 4 * m2 - 120 * m1 ^ 6

noncomputable def jetC2 (f0 f1 f2 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => cumulant2 (normalizedJet f0 f1 u) (normalizedJet f0 f2 u)
noncomputable def jetC3 (f0 f1 f2 f3 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => cumulant3 (normalizedJet f0 f1 u) (normalizedJet f0 f2 u)
    (normalizedJet f0 f3 u)
noncomputable def jetC4 (f0 f1 f2 f3 f4 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => cumulant4 (normalizedJet f0 f1 u) (normalizedJet f0 f2 u)
    (normalizedJet f0 f3 u) (normalizedJet f0 f4 u)
noncomputable def jetC5 (f0 f1 f2 f3 f4 f5 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => cumulant5 (normalizedJet f0 f1 u) (normalizedJet f0 f2 u)
    (normalizedJet f0 f3 u) (normalizedJet f0 f4 u) (normalizedJet f0 f5 u)
noncomputable def jetC6
    (f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => cumulant6 (normalizedJet f0 f1 u) (normalizedJet f0 f2 u)
    (normalizedJet f0 f3 u) (normalizedJet f0 f4 u) (normalizedJet f0 f5 u)
    (normalizedJet f0 f6 u)

/-- The curvature derivative tower reconstructed from the raw kernel jet. -/
noncomputable def jetQ1 (f0 f1 f2 f3 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => -jetC3 f0 f1 f2 f3 u
noncomputable def jetQ2 (f0 f1 f2 f3 f4 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => -jetC4 f0 f1 f2 f3 f4 u
noncomputable def jetQ3
    (f0 f1 f2 f3 f4 f5 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => -jetC5 f0 f1 f2 f3 f4 f5 u
noncomputable def jetQ4
    (f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => -jetC6 f0 f1 f2 f3 f4 f5 f6 u

/-- The exact three cleared polynomials used by CERT12. -/
def clearedQ (a0 a1 a2 : ℝ) : ℝ := a1 ^ 2 - a0 * a2

def clearedF2 (a0 a1 a2 a3 a4 : ℝ) : ℝ :=
  -a0 ^ 4 * a2 * a4 + a0 ^ 4 * a3 ^ 2 + a0 ^ 3 * a1 ^ 2 * a4 -
    2 * a0 ^ 3 * a1 * a2 * a3 + 2 * a0 ^ 3 * a2 ^ 3 -
    3 * a0 ^ 2 * a1 ^ 2 * a2 ^ 2 + 3 * a0 * a1 ^ 4 * a2 - a1 ^ 6

def clearedC4 (a0 a1 a2 a3 a4 a5 a6 : ℝ) : ℝ :=
  a0 * a2 * a4 * a6 - a0 * a2 * a5 ^ 2 - a0 * a3 ^ 2 * a6 +
    2 * a0 * a3 * a4 * a5 - a0 * a4 ^ 3 - a1 ^ 2 * a4 * a6 +
    a1 ^ 2 * a5 ^ 2 + 2 * a1 * a2 * a3 * a6 -
    2 * a1 * a2 * a4 * a5 - 2 * a1 * a3 ^ 2 * a5 +
    2 * a1 * a3 * a4 ^ 2 - a2 ^ 3 * a6 + 2 * a2 ^ 2 * a3 * a5 +
    a2 ^ 2 * a4 ^ 2 - 3 * a2 * a3 ^ 2 * a4 + a3 ^ 4

/-- The literal raw derivative Hankel matrix used by CERT12 before expansion. -/
def rawHankel4 (a0 a1 a2 a3 a4 a5 a6 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![a0, a1, a2, a3;
     a1, a2, a3, a4;
     a2, a3, a4, a5;
     a3, a4, a5, a6]

/-- The expanded `clearedC4` interface is exactly the determinant computed by
the certificate, not merely a polynomial with the same intended sign. -/
theorem clearedC4_eq_rawHankel4_det (a0 a1 a2 a3 a4 a5 a6 : ℝ) :
    clearedC4 a0 a1 a2 a3 a4 a5 a6 =
      (rawHankel4 a0 a1 a2 a3 a4 a5 a6).det := by
  unfold clearedC4 rawHankel4
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- The normalized derivative recurrence packages every quotient derivative
needed below in one reusable closed form. -/
theorem normalizedJet_hasDerivAt
    {f0 f1 fj fj1 : ℝ → ℝ}
    (hf0 : ∀ u, HasDerivAt f0 (f1 u) u)
    (hfj : ∀ u, HasDerivAt fj (fj1 u) u)
    (hf0pos : ∀ u, 0 < f0 u) (u : ℝ) :
    HasDerivAt (normalizedJet f0 fj)
      (normalizedJet f0 fj1 u -
        normalizedJet f0 f1 u * normalizedJet f0 fj u) u := by
  have hraw := (hfj u).fun_div (hf0 u) (hf0pos u).ne'
  unfold normalizedJet
  apply hraw.congr_deriv
  field_simp [(hf0pos u).ne']

theorem hasDerivAt_jetC2
    {f0 f1 f2 f3 : ℝ → ℝ}
    (hf0 : ∀ u, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u, HasDerivAt f2 (f3 u) u)
    (hf0pos : ∀ u, 0 < f0 u) (u : ℝ) :
    HasDerivAt (jetC2 f0 f1 f2) (jetC3 f0 f1 f2 f3 u) u := by
  have hm1 := normalizedJet_hasDerivAt hf0 hf1 hf0pos u
  have hm2 := normalizedJet_hasDerivAt hf0 hf2 hf0pos u
  have hraw := hm2.sub (hm1.pow 2)
  apply hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only [jetC2, cumulant2, Pi.sub_apply, Pi.pow_apply]) |>.congr_deriv
  simp only [jetC3, cumulant3]
  ring

theorem hasDerivAt_jetC3
    {f0 f1 f2 f3 f4 : ℝ → ℝ}
    (hf0 : ∀ u, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u, HasDerivAt f2 (f3 u) u)
    (hf3 : ∀ u, HasDerivAt f3 (f4 u) u)
    (hf0pos : ∀ u, 0 < f0 u) (u : ℝ) :
    HasDerivAt (jetC3 f0 f1 f2 f3) (jetC4 f0 f1 f2 f3 f4 u) u := by
  have hm1 := normalizedJet_hasDerivAt hf0 hf1 hf0pos u
  have hm2 := normalizedJet_hasDerivAt hf0 hf2 hf0pos u
  have hm3 := normalizedJet_hasDerivAt hf0 hf3 hf0pos u
  have hraw := (hm3.sub ((hm2.mul hm1).const_mul 3)).add
    ((hm1.pow 3).const_mul 2)
  apply hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only [jetC3, cumulant3, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring) |>.congr_deriv
  simp only [jetC4, cumulant4]
  ring

theorem hasDerivAt_jetC4
    {f0 f1 f2 f3 f4 f5 : ℝ → ℝ}
    (hf0 : ∀ u, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u, HasDerivAt f2 (f3 u) u)
    (hf3 : ∀ u, HasDerivAt f3 (f4 u) u)
    (hf4 : ∀ u, HasDerivAt f4 (f5 u) u)
    (hf0pos : ∀ u, 0 < f0 u) (u : ℝ) :
    HasDerivAt (jetC4 f0 f1 f2 f3 f4) (jetC5 f0 f1 f2 f3 f4 f5 u) u := by
  have hm1 := normalizedJet_hasDerivAt hf0 hf1 hf0pos u
  have hm2 := normalizedJet_hasDerivAt hf0 hf2 hf0pos u
  have hm3 := normalizedJet_hasDerivAt hf0 hf3 hf0pos u
  have hm4 := normalizedJet_hasDerivAt hf0 hf4 hf0pos u
  have hraw := (((hm4.sub ((hm3.mul hm1).const_mul 4)).sub
    ((hm2.pow 2).const_mul 3)).add ((hm2.mul (hm1.pow 2)).const_mul 12)).sub
    ((hm1.pow 4).const_mul 6)
  apply hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only [jetC4, cumulant4, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring) |>.congr_deriv
  simp only [jetC5, cumulant5, Pi.pow_apply]
  ring

theorem hasDerivAt_jetC5
    {f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ}
    (hf0 : ∀ u, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u, HasDerivAt f2 (f3 u) u)
    (hf3 : ∀ u, HasDerivAt f3 (f4 u) u)
    (hf4 : ∀ u, HasDerivAt f4 (f5 u) u)
    (hf5 : ∀ u, HasDerivAt f5 (f6 u) u)
    (hf0pos : ∀ u, 0 < f0 u) (u : ℝ) :
    HasDerivAt (jetC5 f0 f1 f2 f3 f4 f5)
      (jetC6 f0 f1 f2 f3 f4 f5 f6 u) u := by
  have hm1 := normalizedJet_hasDerivAt hf0 hf1 hf0pos u
  have hm2 := normalizedJet_hasDerivAt hf0 hf2 hf0pos u
  have hm3 := normalizedJet_hasDerivAt hf0 hf3 hf0pos u
  have hm4 := normalizedJet_hasDerivAt hf0 hf4 hf0pos u
  have hm5 := normalizedJet_hasDerivAt hf0 hf5 hf0pos u
  have hraw :=
    (((((hm5.sub ((hm1.mul hm4).const_mul 5)).sub
      ((hm2.mul hm3).const_mul 10)).add
      (((hm1.pow 2).mul hm3).const_mul 20)).add
      ((hm1.mul (hm2.pow 2)).const_mul 30)).sub
      (((hm1.pow 3).mul hm2).const_mul 60)).add ((hm1.pow 5).const_mul 24)
  apply hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => by
    simp only [jetC5, cumulant5, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]
    ring) |>.congr_deriv
  simp only [jetC6, cumulant6, Pi.pow_apply]
  ring

/-- The maintained curvature is exactly the negative second logarithmic
cumulant of the raw kernel jet. -/
theorem kernelCurvature_eq_neg_jetC2
    {f0 f1 f2 : ℝ → ℝ} (hf0pos : ∀ u, 0 < f0 u) :
    kernelCurvature f0 f1 f2 = fun u => -jetC2 f0 f1 f2 u := by
  funext u
  unfold kernelCurvature jetC2 cumulant2 normalizedJet
  field_simp [(hf0pos u).ne']
  ring

/-- One ordinary raw derivative tower produces exactly the maintained
curvature derivative tower. -/
theorem curvatureDerivativeTower_of_rawJet
    {f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ}
    (hf0 : ∀ u, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u, HasDerivAt f2 (f3 u) u)
    (hf3 : ∀ u, HasDerivAt f3 (f4 u) u)
    (hf4 : ∀ u, HasDerivAt f4 (f5 u) u)
    (hf5 : ∀ u, HasDerivAt f5 (f6 u) u)
    (hf0pos : ∀ u, 0 < f0 u) :
    (∀ u, HasDerivAt (kernelCurvature f0 f1 f2)
      (jetQ1 f0 f1 f2 f3 u) u) ∧
    (∀ u, HasDerivAt (jetQ1 f0 f1 f2 f3)
      (jetQ2 f0 f1 f2 f3 f4 u) u) ∧
    (∀ u, HasDerivAt (jetQ2 f0 f1 f2 f3 f4)
      (jetQ3 f0 f1 f2 f3 f4 f5 u) u) ∧
    (∀ u, HasDerivAt (jetQ3 f0 f1 f2 f3 f4 f5)
      (jetQ4 f0 f1 f2 f3 f4 f5 f6 u) u) := by
  have hcurv := kernelCurvature_eq_neg_jetC2 (f1 := f1) (f2 := f2) hf0pos
  constructor
  · intro u
    rw [hcurv]
    exact (hasDerivAt_jetC2 hf0 hf1 hf2 hf0pos u).neg
  constructor
  · intro u
    exact (hasDerivAt_jetC3 hf0 hf1 hf2 hf3 hf0pos u).neg
  constructor
  · intro u
    exact (hasDerivAt_jetC4 hf0 hf1 hf2 hf3 hf4 hf0pos u).neg
  · intro u
    exact (hasDerivAt_jetC5 hf0 hf1 hf2 hf3 hf4 hf5 hf0pos u).neg

/-- Continuity of the sixth raw jet gives continuity of the top curvature
derivative reconstructed from it. -/
theorem continuous_jetQ4_of_rawJet
    {f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ}
    (hf0 : ∀ u, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u, HasDerivAt f2 (f3 u) u)
    (hf3 : ∀ u, HasDerivAt f3 (f4 u) u)
    (hf4 : ∀ u, HasDerivAt f4 (f5 u) u)
    (hf5 : ∀ u, HasDerivAt f5 (f6 u) u)
    (hf6cont : Continuous f6) (hf0pos : ∀ u, 0 < f0 u) :
    Continuous (jetQ4 f0 f1 f2 f3 f4 f5 f6) := by
  have hc0 : Continuous f0 := continuous_iff_continuousAt.mpr fun u =>
    (hf0 u).continuousAt
  have hc1 : Continuous f1 := continuous_iff_continuousAt.mpr fun u =>
    (hf1 u).continuousAt
  have hc2 : Continuous f2 := continuous_iff_continuousAt.mpr fun u =>
    (hf2 u).continuousAt
  have hc3 : Continuous f3 := continuous_iff_continuousAt.mpr fun u =>
    (hf3 u).continuousAt
  have hc4 : Continuous f4 := continuous_iff_continuousAt.mpr fun u =>
    (hf4 u).continuousAt
  have hc5 : Continuous f5 := continuous_iff_continuousAt.mpr fun u =>
    (hf5 u).continuousAt
  have hm1 : Continuous (normalizedJet f0 f1) := by
    unfold normalizedJet
    exact hc1.div hc0 (fun u => (hf0pos u).ne')
  have hm2 : Continuous (normalizedJet f0 f2) := by
    unfold normalizedJet
    exact hc2.div hc0 (fun u => (hf0pos u).ne')
  have hm3 : Continuous (normalizedJet f0 f3) := by
    unfold normalizedJet
    exact hc3.div hc0 (fun u => (hf0pos u).ne')
  have hm4 : Continuous (normalizedJet f0 f4) := by
    unfold normalizedJet
    exact hc4.div hc0 (fun u => (hf0pos u).ne')
  have hm5 : Continuous (normalizedJet f0 f5) := by
    unfold normalizedJet
    exact hc5.div hc0 (fun u => (hf0pos u).ne')
  have hm6 : Continuous (normalizedJet f0 f6) := by
    unfold normalizedJet
    exact hf6cont.div hc0 (fun u => (hf0pos u).ne')
  unfold jetQ4 jetC6 cumulant6
  fun_prop

/-- Cleared curvature numerator identity used by the certificate. -/
theorem clearedQ_identity (a0 a1 a2 : ℝ) (ha0 : a0 ≠ 0) :
    clearedQ a0 a1 a2 = a0 ^ 2 *
      (-cumulant2 (a1 / a0) (a2 / a0)) := by
  unfold clearedQ cumulant2
  field_simp [ha0]
  ring

/-- Cleared `F2` identity used by the certificate. -/
theorem clearedF2_identity (a0 a1 a2 a3 a4 : ℝ) (ha0 : a0 ≠ 0) :
    clearedF2 a0 a1 a2 a3 a4 = a0 ^ 6 *
      ((-cumulant2 (a1 / a0) (a2 / a0)) ^ 3 -
        ((-cumulant2 (a1 / a0) (a2 / a0)) *
          (-cumulant4 (a1 / a0) (a2 / a0) (a3 / a0) (a4 / a0)) -
        (-cumulant3 (a1 / a0) (a2 / a0) (a3 / a0)) ^ 2)) := by
  unfold clearedF2 cumulant2 cumulant3 cumulant4
  field_simp [ha0]
  ring

/-- Cleared raw Hankel identity used by the certificate. -/
theorem clearedC4_identity (a0 a1 a2 a3 a4 a5 a6 : ℝ) (ha0 : a0 ≠ 0) :
    clearedC4 a0 a1 a2 a3 a4 a5 a6 = a0 ^ 4 *
      determinantC4
        (cumulant2 (a1 / a0) (a2 / a0))
        (cumulant3 (a1 / a0) (a2 / a0) (a3 / a0))
        (cumulant4 (a1 / a0) (a2 / a0) (a3 / a0) (a4 / a0))
        (cumulant5 (a1 / a0) (a2 / a0) (a3 / a0) (a4 / a0) (a5 / a0))
        (cumulant6 (a1 / a0) (a2 / a0) (a3 / a0) (a4 / a0) (a5 / a0)
          (a6 / a0)) := by
  rw [determinantC4_eq_cumulantC4Polynomial]
  unfold clearedC4 cumulant2 cumulant3 cumulant4 cumulant5 cumulant6
    cumulantC4Polynomial
  field_simp [ha0]
  ring

/-- Strict signs of the three cleared certificate polynomials transfer to the
literal maintained curvature objects.  No downstream sign is a premise. -/
theorem kernelSigns_of_clearedSigns
    {f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ}
    (hf0pos : ∀ u, 0 < f0 u)
    (hQclear : ∀ u, 0 < clearedQ (f0 u) (f1 u) (f2 u))
    (hF2clear : ∀ u, 0 < clearedF2
      (f0 u) (f1 u) (f2 u) (f3 u) (f4 u))
    (hC4clear : ∀ u, 0 < clearedC4
      (f0 u) (f1 u) (f2 u) (f3 u) (f4 u) (f5 u) (f6 u)) :
    (∀ u, 0 < kernelCurvature f0 f1 f2 u) ∧
    (∀ u, 0 < kernelF2 (kernelCurvature f0 f1 f2)
      (jetQ1 f0 f1 f2 f3) (jetQ2 f0 f1 f2 f3 f4) u) ∧
    (∀ u, 0 < kernelDeterminantC4 (kernelCurvature f0 f1 f2)
      (jetQ1 f0 f1 f2 f3) (jetQ2 f0 f1 f2 f3 f4)
      (jetQ3 f0 f1 f2 f3 f4 f5) (jetQ4 f0 f1 f2 f3 f4 f5 f6) u) := by
  have hcurv := kernelCurvature_eq_neg_jetC2 (f1 := f1) (f2 := f2) hf0pos
  constructor
  · intro u
    have hid := clearedQ_identity (f0 u) (f1 u) (f2 u) (hf0pos u).ne'
    have hden : 0 < f0 u ^ 2 := sq_pos_of_pos (hf0pos u)
    rw [hcurv]
    have hprod' : 0 < f0 u ^ 2 *
        (-cumulant2 (f1 u / f0 u) (f2 u / f0 u)) := by
      rw [← hid]
      exact hQclear u
    have hprod : 0 < f0 u ^ 2 * (-jetC2 f0 f1 f2 u) := by
      simpa only [jetC2, normalizedJet] using hprod'
    nlinarith
  constructor
  · intro u
    have hid := clearedF2_identity (f0 u) (f1 u) (f2 u) (f3 u) (f4 u)
      (hf0pos u).ne'
    have hden : 0 < f0 u ^ 6 := pow_pos (hf0pos u) 6
    unfold kernelF2
    rw [congrFun hcurv u]
    unfold jetQ1 jetQ2 jetC2 jetC3 jetC4 normalizedJet
    nlinarith [hF2clear u, hid]
  · intro u
    have hid := clearedC4_identity (f0 u) (f1 u) (f2 u) (f3 u) (f4 u)
      (f5 u) (f6 u) (hf0pos u).ne'
    have hden : 0 < f0 u ^ 4 := pow_pos (hf0pos u) 4
    unfold kernelDeterminantC4
    rw [congrFun hcurv u]
    unfold jetQ1 jetQ2 jetQ3 jetQ4 jetC2 jetC3 jetC4
      jetC5 jetC6 normalizedJet
    simp only [neg_neg]
    nlinarith [hC4clear u, hid]

/-- Direct CERT12-shaped entry to the maintained actual-coordinate theorem.
The premises mention only a positive raw kernel, its ordinary derivative jet,
continuity of the top raw jet, and the three cleared strict inequalities. -/
theorem actualCoordinatePartialXiPsi_neg_of_clearedJetSigns
    {f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ}
    (hf0 : ∀ u, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u, HasDerivAt f2 (f3 u) u)
    (hf3 : ∀ u, HasDerivAt f3 (f4 u) u)
    (hf4 : ∀ u, HasDerivAt f4 (f5 u) u)
    (hf5 : ∀ u, HasDerivAt f5 (f6 u) u)
    (hf6cont : Continuous f6)
    (hf0pos : ∀ u, 0 < f0 u)
    (hQclear : ∀ u, 0 < clearedQ (f0 u) (f1 u) (f2 u))
    (hF2clear : ∀ u, 0 < clearedF2
      (f0 u) (f1 u) (f2 u) (f3 u) (f4 u))
    (hC4clear : ∀ u, 0 < clearedC4
      (f0 u) (f1 u) (f2 u) (f3 u) (f4 u) (f5 u) (f6 u))
    {x m r : ℝ} (hxm : x < m) (hmr : m < r) :
    coordinateQ (logSlope f0 f1) (kernelCurvature f0 f1 f2)
        (kernelCoordinate (logSlope f0 f1) x) *
      deriv (fun y => coordinatePsi
        (coordinateQ (logSlope f0 f1) (kernelCurvature f0 f1 f2))
        (coordinateQ1 (logSlope f0 f1) (kernelCurvature f0 f1 f2)
          (jetQ1 f0 f1 f2 f3)) y
        (kernelCoordinate (logSlope f0 f1) m)
        (kernelCoordinate (logSlope f0 f1) r))
        (kernelCoordinate (logSlope f0 f1) x) < 0 := by
  have htower := curvatureDerivativeTower_of_rawJet
    hf0 hf1 hf2 hf3 hf4 hf5 hf0pos
  have hsigns := kernelSigns_of_clearedSigns hf0pos hQclear hF2clear hC4clear
  exact PF4.LocalFinalAssembly.actualCoordinatePartialXiPsi_neg
    (fun u => hasDerivAt_logSlope hf0 hf1 hf0pos u)
    htower.1 htower.2.1 htower.2.2.1 htower.2.2.2
    (continuous_jetQ4_of_rawJet hf0 hf1 hf2 hf3 hf4 hf5 hf6cont hf0pos)
    hsigns.1 hsigns.2.1 hsigns.2.2 hxm hmr

/-- Generic actual-coordinate decrease in the original variable.  This is the
range-safe monotonicity form consumed by the terminal quotient. -/
theorem actualCoordinatePsi_strictAntiOn_Iio
    {S q q1 q2 q3 q4 : ℝ → ℝ} {m r : ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hq3 : ∀ u, HasDerivAt q3 (q4 u) u)
    (hq4cont : Continuous q4)
    (hqpos : ∀ u, 0 < q u)
    (hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u)
    (hC4pos : ∀ u, 0 < kernelDeterminantC4 q q1 q2 q3 q4 u)
    (hmr : m < r) :
    StrictAntiOn
      (fun x => coordinatePsi (coordinateQ S q) (coordinateQ1 S q q1)
        (kernelCoordinate S x) (kernelCoordinate S m) (kernelCoordinate S r))
      (Iio m) := by
  let psi := fun y => coordinatePsi (coordinateQ S q) (coordinateQ1 S q q1)
    y (kernelCoordinate S m) (kernelCoordinate S r)
  let g := fun x => psi (kernelCoordinate S x)
  have hderiv : ∀ x ∈ Iio m, deriv g x < 0 := by
    intro x hx
    have hmul := PF4.LocalFinalAssembly.actualCoordinatePartialXiPsi_neg
      hS hq hq1 hq2 hq3 hq4cont hqpos hF2pos hC4pos hx hmr
    have hpsineg : deriv psi (kernelCoordinate S x) < 0 := by
      dsimp [psi] at hmul ⊢
      rw [coordinateQ_apply_kernelCoordinate hS hqpos] at hmul
      nlinarith [hqpos x]
    have hpsideriv : HasDerivAt psi (deriv psi (kernelCoordinate S x))
        (kernelCoordinate S x) :=
      (differentiableAt_of_deriv_ne_zero hpsineg.ne).hasDerivAt
    have hgderiv : HasDerivAt g
        (deriv psi (kernelCoordinate S x) * q x) x := by
      dsimp [g]
      exact hpsideriv.comp x (hasDerivAt_kernelCoordinate hS x)
    rw [hgderiv.deriv]
    nlinarith [hpsineg, hqpos x]
  have hcont : ContinuousOn g (Iio m) := by
    intro x hx
    exact (differentiableAt_of_deriv_ne_zero (hderiv x hx).ne).continuousAt
      |>.continuousWithinAt
  change StrictAntiOn g (Iio m)
  apply strictAntiOn_of_deriv_neg (convex_Iio m) hcont
  intro x hx
  have hx' : x ∈ Iio m := by simpa only [interior_Iio] using hx
  exact hderiv x hx'

theorem actualCoordinatePsi_decreases_on_ordered_points
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
    {x1 x2 m r : ℝ} (hx12 : x1 < x2) (hx2m : x2 < m) (hmr : m < r) :
    coordinatePsi (coordinateQ S q) (coordinateQ1 S q q1)
        (kernelCoordinate S x2) (kernelCoordinate S m) (kernelCoordinate S r) <
      coordinatePsi (coordinateQ S q) (coordinateQ1 S q q1)
        (kernelCoordinate S x1) (kernelCoordinate S m) (kernelCoordinate S r) := by
  have hanti := actualCoordinatePsi_strictAntiOn_Iio hS hq hq1 hq2 hq3
    hq4cont hqpos hF2pos hC4pos hmr
  exact hanti (hx12.trans hx2m) hx2m hx12

/-- The lower three-point factor is also a consequence of the same raw
curvature package: its coordinate form is a sum of two positive triangular
curvature integrals. -/
theorem lowerLambda_pos_of_actualCoordinate
    {S q q1 q2 q3 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hqpos : ∀ u, 0 < q u)
    (hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u)
    {x m r : ℝ} (hxm : x < m) (hmr : m < r) :
    0 < lowerLambda S q x m r := by
  let Q := coordinateQ S q
  let Q1 := coordinateQ1 S q q1
  let Q2 := coordinateQ2 S q q1 q2
  let p := kernelCoordinate S x
  let z := kernelCoordinate S m
  let w := kernelCoordinate S r
  have hmono := kernelCoordinate_strictMono hS hqpos
  have hpz : p < z := hmono hxm
  have hzw : z < w := hmono hmr
  have hrange : Icc p w ⊆ Set.range (kernelCoordinate S) := by
    dsimp [p, w]
    exact PF4.RangeLocalFinalAssembly.kernelCoordinate_Icc_subset_range hS hqpos
  have hQ : ∀ y ∈ Icc p w, HasDerivAt Q (Q1 y) y := by
    intro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q, Q1]
    rw [coordinateQ1_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ hS hq hqpos u
  have hQ1 : ∀ y ∈ Icc p w, HasDerivAt Q1 (Q2 y) y := by
    intro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q1, Q2]
    rw [coordinateQ2_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ1 hS hq hq1 hqpos u
  have hQ2cont : ContinuousOn Q2 (Icc p w) := by
    intro y hy
    rcases hrange hy with ⟨u, rfl⟩
    exact (hasDerivAt_coordinateQ2 hS hq hq1 hq2 hqpos u).continuousAt
      |>.continuousWithinAt
  have hkcont : ContinuousOn (curvature Q2) (Icc p w) := by
    unfold curvature
    exact continuousOn_const.sub hQ2cont
  have hkpos : ∀ y ∈ Icc p w, 0 < curvature Q2 y := by
    intro y hy
    rcases hrange hy with ⟨u, rfl⟩
    dsimp [Q2]
    exact curvature_coordinateQ2_pos_on_range hS hqpos hF2pos u
  have hcoord : 0 < coordinateLambda Q p z w :=
    coordinateLambda_pos hpz hzw hQ hQ1 hkcont hkpos
  have hQreal : ∀ u, Q (kernelCoordinate S u) = q u := by
    intro u
    exact coordinateQ_apply_kernelCoordinate hS hqpos u
  rw [lowerLambda_eq_coordinateLambda hQreal]
  exact hcoord

/-- End-to-end cleared-certificate interface for the terminal cascade.  The
three strict sign premises are precisely the raw polynomial statements checked
by CERT12, not reformulations of the terminal conclusion. -/
theorem terminalQuotD_pos_of_clearedJetSigns
    {f0 f1 f2 f3 f4 f5 f6 : ℝ → ℝ}
    (hf0 : ∀ u, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u, HasDerivAt f2 (f3 u) u)
    (hf3 : ∀ u, HasDerivAt f3 (f4 u) u)
    (hf4 : ∀ u, HasDerivAt f4 (f5 u) u)
    (hf5 : ∀ u, HasDerivAt f5 (f6 u) u)
    (hf6cont : Continuous f6)
    (hf0pos : ∀ u, 0 < f0 u)
    (hQclear : ∀ u, 0 < clearedQ (f0 u) (f1 u) (f2 u))
    (hF2clear : ∀ u, 0 < clearedF2
      (f0 u) (f1 u) (f2 u) (f3 u) (f4 u))
    (hC4clear : ∀ u, 0 < clearedC4
      (f0 u) (f1 u) (f2 u) (f3 u) (f4 u) (f5 u) (f6 u))
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    ∀ t, 0 < terminalQuotD f0 f1 f2 f3 a c b d t := by
  let S := logSlope f0 f1
  let q := kernelCurvature f0 f1 f2
  let q1 := jetQ1 f0 f1 f2 f3
  let q2 := jetQ2 f0 f1 f2 f3 f4
  let q3 := jetQ3 f0 f1 f2 f3 f4 f5
  let q4 := jetQ4 f0 f1 f2 f3 f4 f5 f6
  let Q := coordinateQ S q
  let Q1 := coordinateQ1 S q q1
  have hS : ∀ u, HasDerivAt S (-q u) u := by
    intro u
    exact hasDerivAt_logSlope hf0 hf1 hf0pos u
  have htower := curvatureDerivativeTower_of_rawJet
    hf0 hf1 hf2 hf3 hf4 hf5 hf0pos
  have hsigns := kernelSigns_of_clearedSigns hf0pos hQclear hF2clear hC4clear
  have hq : ∀ u, HasDerivAt q (q1 u) u := htower.1
  have hq1 : ∀ u, HasDerivAt q1 (q2 u) u := htower.2.1
  have hq2 : ∀ u, HasDerivAt q2 (q3 u) u := htower.2.2.1
  have hq3 : ∀ u, HasDerivAt q3 (q4 u) u := htower.2.2.2
  have hq4cont : Continuous q4 :=
    continuous_jetQ4_of_rawJet hf0 hf1 hf2 hf3 hf4 hf5 hf6cont hf0pos
  have hqpos : ∀ u, 0 < q u := hsigns.1
  have hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u := hsigns.2.1
  have hC4pos : ∀ u, 0 < kernelDeterminantC4 q q1 q2 q3 q4 u :=
    hsigns.2.2
  have hLambda : ∀ x m r, x < m → m < r →
      0 < lowerLambda S q x m r := by
    intro x m r hxm hmr
    exact lowerLambda_pos_of_actualCoordinate hS hq hq1 hq2 hqpos hF2pos
      hxm hmr
  have hfirst := firstQuotD_pos_of_kernelCurvature_pos
    hf0 hf1 hf0pos hqpos hac
  have hsecondB := secondQuotD_pos_of_lowerLambda_pos
    hf0 hf1 hf0pos hqpos hLambda hac hcb
  have hsecondD := secondQuotD_pos_of_lowerLambda_pos
    hf0 hf1 hf0pos hqpos hLambda hac (hcb.trans hbd)
  have hSanti := logSlope_strictAnti_of_kernelCurvature_pos
    hf0 hf1 hf0pos hqpos
  have hchord : ∀ {u v : ℝ}, u < v → slopeChord S u v ≠ 0 := by
    intro u v huv
    exact (slopeChord_pos_of_lt hSanti huv).ne'
  have hQreal : ∀ u, Q (kernelCoordinate S u) = q u := by
    intro u
    exact coordinateQ_apply_kernelCoordinate hS hqpos u
  have hQ1real : ∀ u, Q1 (kernelCoordinate S u) = q1 u / q u := by
    intro u
    exact coordinateQ1_apply_kernelCoordinate hS hqpos u
  intro t
  have hAb : ∀ s, slopeChord S (s - b) (s - a) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAd : ∀ s, slopeChord S (s - d) (s - a) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAc : ∀ s, slopeChord S (s - c) (s - a) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAbc : ∀ s, slopeChord S (s - b) (s - c) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAdc : ∀ s, slopeChord S (s - d) (s - c) ≠ 0 :=
    fun s => hchord (by linarith)
  have hLambdaB : ∀ s, lowerLambda S q (s - b) (s - c) (s - a) ≠ 0 :=
    fun s => (hLambda _ _ _ (by linarith) (by linarith)).ne'
  have hLambdaD : ∀ s, lowerLambda S q (s - d) (s - c) (s - a) ≠ 0 :=
    fun s => (hLambda _ _ _ (by linarith) (by linarith)).ne'
  rw [terminalQuotD_eq_terminalQuot_mul_coordinatePsi_sub hf0 hf1 hf2
    hf0pos hqpos hq hQreal hQ1real a c b d hfirst hAb hAd hAc hAbc hAdc
    hLambdaB hLambdaD hsecondB]
  have hPsi : coordinatePsi Q Q1
        (kernelCoordinate S (t - b)) (kernelCoordinate S (t - c))
        (kernelCoordinate S (t - a)) <
      coordinatePsi Q Q1
        (kernelCoordinate S (t - d)) (kernelCoordinate S (t - c))
        (kernelCoordinate S (t - a)) := by
    exact actualCoordinatePsi_decreases_on_ordered_points
      hS hq hq1 hq2 hq3 hq4cont hqpos hF2pos hC4pos
      (by linarith) (by linarith) (by linarith)
  exact mul_pos (div_pos (hsecondD t) (hsecondB t)) (sub_pos.mpr hPsi)

end PF4.ClearedJetCertificateBridge

