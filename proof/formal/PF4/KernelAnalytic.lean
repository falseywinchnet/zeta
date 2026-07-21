import PF4.Kernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

set_option linter.style.header false

/-!
# Real Poisson parity bridge

This module specializes mathlib's real Gaussian
Poisson-summation theorem to the maintained literal theta sum.  It changes no
definition and keeps the imported analytic theorem visible.
-/

namespace PF4

open Real

/-- The exact theta transformation in the paper's normalization. -/
theorem riemannTheta_modular {x : ℝ} (hx : 0 < x) :
    PF4.riemannTheta x =
      1 / x ^ (1 / 2 : ℝ) * PF4.riemannTheta (1 / x) := by
  simpa [PF4.riemannTheta, div_eq_mul_inv, mul_assoc] using
    Real.tsum_exp_neg_mul_int_sq hx

theorem exp_neg_two_mul_rpow_half (t : ℝ) :
    Real.exp (-2 * t) ^ (1 / 2 : ℝ) = Real.exp (-t) := by
  rw [← Real.exp_mul]
  congr 1
  ring

/-- Poisson summation gives evenness of the already-global real `H`. -/
theorem riemannH_neg (t : ℝ) : PF4.riemannH (-t) = PF4.riemannH t := by
  rw [PF4.riemannH, PF4.riemannH]
  have hmod := riemannTheta_modular (Real.exp_pos (-2 * t))
  rw [show 2 * -t = -2 * t by ring, hmod, exp_neg_two_mul_rpow_half]
  rw [show 1 / Real.exp (-2 * t) = Real.exp (2 * t) by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring]
  rw [show 1 / Real.exp (-t) = Real.exp t by
    rw [one_div, ← Real.exp_neg]
    ring_nf]
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  ring_nf

theorem riemannH_even : Function.Even PF4.riemannH := riemannH_neg

/-! ## Independent analytic regularity

The definitions stay real.  A complex Jacobi-theta realization is used only
as a library-backed proof that the real `H` is analytic, hence smooth to every
finite order.
-/

theorem riemannTheta_eq_evenKernel {x : ℝ} (hx : 0 < x) :
    PF4.riemannTheta x = HurwitzZeta.evenKernel 0 x := by
  simpa [PF4.riemannTheta, mul_comm, mul_left_comm, mul_assoc] using
    (HurwitzZeta.hasSum_int_evenKernel (0 : ℝ) hx).tsum_eq

theorem riemannTheta_eq_re_jacobiTheta {x : ℝ} (hx : 0 < x) :
    PF4.riemannTheta x = (jacobiTheta (Complex.I * x)).re := by
  rw [riemannTheta_eq_evenKernel hx]
  have h := congrArg Complex.re (HurwitzZeta.cosKernel_def (0 : ℝ) x)
  simpa [HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
    jacobiTheta_eq_jacobiTheta₂] using h

/-- A holomorphic expression whose real restriction is the maintained `H`. -/
noncomputable def riemannHComplex (z : ℂ) : ℂ :=
  Complex.exp (z / 2) * jacobiTheta (Complex.I * Complex.exp (2 * z))

theorem riemannH_eq_re_riemannHComplex (t : ℝ) :
    PF4.riemannH t = (riemannHComplex t).re := by
  rw [PF4.riemannH,
    riemannTheta_eq_re_jacobiTheta (Real.exp_pos (2 * t))]
  have hdiv : (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hpref_re : (Complex.exp ((t : ℂ) / 2)).re = Real.exp (t / 2) := by
    rw [hdiv, Complex.exp_ofReal_re]
  have hpref_im : (Complex.exp ((t : ℂ) / 2)).im = 0 := by
    rw [hdiv, Complex.exp_ofReal_im]
  have hexp : Complex.exp (2 * (t : ℂ)) = (Real.exp (2 * t) : ℂ) := by
    calc
      Complex.exp (2 * (t : ℂ)) = Complex.exp ((2 * t : ℝ) : ℂ) := by
        congr 1
        norm_num
      _ = (Real.exp (2 * t) : ℂ) := (Complex.ofReal_exp (2 * t)).symm
  rw [riemannHComplex, Complex.mul_re, hpref_re, hpref_im]
  rw [hexp]
  simp only [zero_mul, sub_zero]

theorem analyticAt_riemannHComplex_at_real (t : ℝ) :
    AnalyticAt ℂ riemannHComplex t := by
  have hexp : Complex.exp (2 * (t : ℂ)) = (Real.exp (2 * t) : ℂ) := by
    calc
      Complex.exp (2 * (t : ℂ)) = Complex.exp ((2 * t : ℝ) : ℂ) := by
        congr 1
        norm_num
      _ = (Real.exp (2 * t) : ℂ) := (Complex.ofReal_exp (2 * t)).symm
  have htau : 0 < (Complex.I * Complex.exp (2 * (t : ℂ))).im := by
    rw [hexp, Complex.I_mul_im, Complex.ofReal_re]
    exact Real.exp_pos _
  have hthetaDiff : DifferentiableOn ℂ jacobiTheta
      UpperHalfPlane.upperHalfPlaneSet :=
    fun z hz ↦ (differentiableAt_jacobiTheta hz).differentiableWithinAt
  have htheta :
      AnalyticAt ℂ jacobiTheta (Complex.I * Complex.exp (2 * (t : ℂ))) :=
    hthetaDiff.analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds htau)
  have hinner : AnalyticAt ℂ
      (fun z : ℂ ↦ Complex.I * Complex.exp (2 * z)) t := by
    fun_prop
  have hpref : AnalyticAt ℂ (fun z : ℂ ↦ Complex.exp (z / 2)) t := by
    fun_prop
  unfold riemannHComplex
  have hcomp := AnalyticAt.comp
    (g := jacobiTheta)
    (f := fun z : ℂ ↦ Complex.I * Complex.exp (2 * z)) htheta hinner
  exact hpref.mul (by simpa [Function.comp_def] using hcomp)

theorem analyticAt_riemannH (t : ℝ) : AnalyticAt ℝ PF4.riemannH t := by
  have h := (analyticAt_riemannHComplex_at_real t).re_ofReal
  simpa only [← riemannH_eq_re_riemannHComplex] using h

/-- The maintained real `H` is smooth to every finite order. -/
theorem contDiff_riemannH : ContDiff ℝ ⊤ PF4.riemannH := by
  exact contDiff_iff_contDiffAt.mpr fun t ↦ (analyticAt_riemannH t).contDiffAt

theorem continuous_globalRiemannKernel :
    Continuous PF4.globalRiemannKernel := by
  unfold PF4.globalRiemannKernel
  exact (contDiff_riemannH.continuous_iteratedDeriv 2 (by simp)).sub
    (continuous_const.mul contDiff_riemannH.continuous) |>.div_const 2

theorem analyticAt_globalRiemannKernel (t : ℝ) :
    AnalyticAt ℝ PF4.globalRiemannKernel t := by
  have htwo : AnalyticAt ℝ (iteratedDeriv 2 PF4.riemannH) t := by
    simpa [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ] using
      (analyticAt_riemannH t).deriv.deriv
  unfold PF4.globalRiemannKernel
  exact (htwo.sub (analyticAt_const.mul (analyticAt_riemannH t))).div_const

/-- The maintained differential-operator kernel is globally smooth. -/
theorem contDiff_globalRiemannKernel :
    ContDiff ℝ ⊤ PF4.globalRiemannKernel := by
  exact contDiff_iff_contDiffAt.mpr fun t ↦
    (analyticAt_globalRiemannKernel t).contDiffAt

theorem iteratedDeriv_two_riemannH_neg (t : ℝ) :
    iteratedDeriv 2 PF4.riemannH (-t) =
      iteratedDeriv 2 PF4.riemannH t := by
  have hfun : (fun x : ℝ ↦ PF4.riemannH (-x)) = PF4.riemannH := by
    funext x
    exact riemannH_neg x
  have h := iteratedDeriv_comp_neg 2 PF4.riemannH t
  rw [hfun] at h
  simpa using h.symm

/-- The maintained differential-operator kernel inherits evenness. -/
theorem globalRiemannKernel_even : Function.Even PF4.globalRiemannKernel := by
  intro t
  rw [PF4.globalRiemannKernel, PF4.globalRiemannKernel,
    iteratedDeriv_two_riemannH_neg, riemannH_neg]

/-- On the negative half-line, the global kernel is represented by the
already-checked positive-mode series at the reflected point. -/
theorem globalRiemannKernel_eq_thetaSeries_neg {t : ℝ} (ht : t ≤ 0) :
    PF4.globalRiemannKernel t = PF4.thetaSeries (-t) := by
  rw [← globalRiemannKernel_even t]
  exact PF4.globalRiemannKernel_eq_thetaSeries_of_nonneg (neg_nonneg.mpr ht)

/-- Exact global reflected-series representation.  The absolute value appears
only in the theorem statement, never in the definition of the kernel. -/
theorem globalRiemannKernel_eq_thetaSeries_abs (t : ℝ) :
    PF4.globalRiemannKernel t = PF4.thetaSeries |t| := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    exact PF4.globalRiemannKernel_eq_thetaSeries_of_nonneg ht
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht']
    exact globalRiemannKernel_eq_thetaSeries_neg ht'

end PF4
