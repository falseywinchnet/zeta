import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option linter.style.header false

/-!
# The theta modular identity and the global even `H` continuation

This file fixes the paper's real theta normalization against mathlib's
Poisson-summation-backed Jacobi theta development.  It does not define the
global Riemann kernel by composing the positive-side kernel with `abs`.
-/

namespace PF4.Advancement.ThetaModularContinuation

open Real

/-- The paper's real theta function, using mathlib's zero-characteristic
Hurwitz kernel.  On the positive axis this is the sum over all integers. -/
noncomputable def riemannTheta (x : ℝ) : ℝ :=
  HurwitzZeta.evenKernel 0 x

/-- Exact identification with the paper's integer Gaussian series. -/
theorem hasSum_int_riemannTheta {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℤ ↦ Real.exp (-Real.pi * (n : ℝ) ^ 2 * x))
      (riemannTheta x) := by
  simpa [riemannTheta] using HurwitzZeta.hasSum_int_evenKernel (0 : ℝ) hx

/-- The exact theta transformation in the normalization used by the paper. -/
theorem riemannTheta_modular (x : ℝ) :
    riemannTheta x = 1 / x ^ (1 / 2 : ℝ) * riemannTheta (1 / x) := by
  simpa [riemannTheta, HurwitzZeta.evenKernel_eq_cosKernel_of_zero] using
    HurwitzZeta.evenKernel_functional_equation (0 : AddCircle 1) x

/-- The paper's globally defined theta normalization before applying the
second-order differential operator that produces the Riemann kernel. -/
noncomputable def riemannH (t : ℝ) : ℝ :=
  Real.exp (t / 2) * riemannTheta (Real.exp (2 * t))

theorem exp_neg_two_mul_rpow_half (t : ℝ) :
    Real.exp (-2 * t) ^ (1 / 2 : ℝ) = Real.exp (-t) := by
  rw [← Real.exp_mul]
  congr 1
  ring

/-- The modular identity constructs the required global even continuation. -/
theorem riemannH_neg (t : ℝ) : riemannH (-t) = riemannH t := by
  rw [riemannH, riemannH]
  have hmod := riemannTheta_modular (Real.exp (-2 * t))
  rw [show 2 * -t = -2 * t by ring, hmod, exp_neg_two_mul_rpow_half]
  rw [show 1 / Real.exp (-2 * t) = Real.exp (2 * t) by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring]
  rw [show 1 / Real.exp (-t) = Real.exp t by
    rw [one_div, ← Real.exp_neg]
    ring]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Public evenness form, avoiding a bespoke continuation predicate. -/
theorem riemannH_even : Function.Even riemannH := riemannH_neg

/-! The same object also has a local holomorphic realization near every real
point.  This supplies smoothness independently of the evenness equation. -/

theorem riemannTheta_eq_re_jacobiTheta (x : ℝ) :
    riemannTheta x = (jacobiTheta (Complex.I * x)).re := by
  have h := congrArg Complex.re (HurwitzZeta.cosKernel_def (0 : ℝ) x)
  simpa [riemannTheta, HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
    jacobiTheta_eq_jacobiTheta₂] using h

/-- A holomorphic expression whose real restriction is `riemannH`. -/
noncomputable def riemannHComplex (z : ℂ) : ℂ :=
  Complex.exp (z / 2) * jacobiTheta (Complex.I * Complex.exp (2 * z))

theorem riemannH_eq_re_riemannHComplex (t : ℝ) :
    riemannH t = (riemannHComplex t).re := by
  rw [riemannH, riemannTheta_eq_re_jacobiTheta]
  simp [riemannHComplex, Complex.exp_ofReal_re]

theorem analyticAt_riemannHComplex_at_real (t : ℝ) :
    AnalyticAt ℂ riemannHComplex t := by
  let tau : ℂ := Complex.I * Complex.exp (2 * (t : ℂ))
  have htau : 0 < tau.im := by
    simp [tau, Complex.exp_ofReal_re]
  have hthetaDiff : DifferentiableOn ℂ jacobiTheta Complex.upperHalfPlaneSet :=
    fun z hz ↦ differentiableAt_jacobiTheta hz
  have htheta : AnalyticAt ℂ jacobiTheta tau :=
    hthetaDiff.analyticAt (Complex.isOpen_upperHalfPlaneSet.mem_nhds htau)
  have hinner : AnalyticAt ℂ
      (fun z : ℂ ↦ Complex.I * Complex.exp (2 * z)) t := by
    fun_prop
  have hpref : AnalyticAt ℂ (fun z : ℂ ↦ Complex.exp (z / 2)) t := by
    fun_prop
  unfold riemannHComplex
  exact hpref.mul (htheta.comp hinner)

theorem analyticAt_riemannH (t : ℝ) : AnalyticAt ℝ riemannH t := by
  have h := (analyticAt_riemannHComplex_at_real t).re_ofReal
  simpa only [← riemannH_eq_re_riemannHComplex] using h

/-- The legal global form is smooth to every finite order before any
positive-side series representation is invoked. -/
theorem contDiff_riemannH : ContDiff ℝ ∞ riemannH := by
  exact contDiff_iff_contDiffAt.mpr fun t ↦ (analyticAt_riemannH t).contDiffAt

/-!
## A legal global kernel form

The second-order operator is applied to the globally defined `riemannH`
directly.  No absolute value or piecewise reflection occurs in the definition.
The positive-side theta-series representation will be attached later by a
termwise-differentiation identity.
-/

/-- The global Riemann-kernel candidate in the paper's primary `H` form. -/
noncomputable def globalRiemannKernel (t : ℝ) : ℝ :=
  (iteratedDeriv 2 riemannH t - (1 / 4 : ℝ) * riemannH t) / 2

/-- The iterated-derivative definition is exactly the paper's displayed
ordinary second-derivative formula. -/
theorem globalRiemannKernel_eq_paper_form (t : ℝ) :
    globalRiemannKernel t =
      (deriv (deriv riemannH) t - (1 / 4 : ℝ) * riemannH t) / 2 := by
  simp [globalRiemannKernel, show (2 : ℕ) = 1 + 1 by omega,
    iteratedDeriv_succ, iteratedDeriv_one]

theorem continuous_globalRiemannKernel : Continuous globalRiemannKernel := by
  unfold globalRiemannKernel
  exact (contDiff_riemannH.continuous_iteratedDeriv 2 (by simp)).sub
    (continuous_const.mul contDiff_riemannH.continuous) |>.div_const 2

theorem iteratedDeriv_two_riemannH_neg (t : ℝ) :
    iteratedDeriv 2 riemannH (-t) = iteratedDeriv 2 riemannH t := by
  have hfun : (fun x : ℝ ↦ riemannH (-x)) = riemannH := by
    funext x
    exact riemannH_neg x
  have h := iteratedDeriv_comp_neg 2 riemannH t
  rw [hfun] at h
  simpa using h.symm

/-- Evenness is inherited by the exact second-order kernel operator. -/
theorem globalRiemannKernel_even : Function.Even globalRiemannKernel := by
  intro t
  rw [globalRiemannKernel, globalRiemannKernel,
    iteratedDeriv_two_riemannH_neg, riemannH_neg]

end PF4.Advancement.ThetaModularContinuation
