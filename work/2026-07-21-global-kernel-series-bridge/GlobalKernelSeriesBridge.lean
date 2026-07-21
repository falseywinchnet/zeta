import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Ring

set_option linter.style.header false
set_option maxHeartbeats 800000

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
    HurwitzZeta.evenKernel_functional_equation (0 : UnitAddCircle) x

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
  calc
    Real.exp (-t / 2) * (Real.exp t * riemannTheta (Real.exp (2 * t))) =
        (Real.exp (-t / 2) * Real.exp t) * riemannTheta (Real.exp (2 * t)) := by ring
    _ = Real.exp (t / 2) * riemannTheta (Real.exp (2 * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Public evenness form, avoiding a bespoke continuation predicate. -/
theorem riemannH_even : Function.Even riemannH := riemannH_neg

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
    iteratedDeriv_succ]

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

/-!
## Positive-mode representation

The index `k : ℕ` denotes the positive integer `n = k + 1`.
-/

/-- The positive integer represented by a zero-based natural index. -/
def modeN (k : ℕ) : ℝ := (k + 1 : ℕ)

/-- One positive Gaussian mode of `H`, including the factor from the pair
`n` and `-n`. -/
noncomputable def hMode (k : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp (t / 2) *
    Real.exp (-Real.pi * modeN k ^ 2 * Real.exp (2 * t))

noncomputable def hSeries (t : ℝ) : ℝ := ∑' k : ℕ, hMode k t

theorem riemannTheta_eq_re_jacobiTheta (x : ℝ) :
    riemannTheta x = (jacobiTheta (Complex.I * x)).re := by
  have h := congrArg Complex.re (HurwitzZeta.cosKernel_def (0 : ℝ) x)
  simpa [riemannTheta, HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
    jacobiTheta_eq_jacobiTheta₂] using h

theorem complex_gaussian_term_eq (k : ℕ) (t : ℝ) :
    Complex.exp
        (Real.pi * Complex.I * ((k : ℂ) + 1) ^ 2 *
          (Complex.I * Real.exp (2 * t))) =
      (Real.exp (-Real.pi * modeN k ^ 2 * Real.exp (2 * t)) : ℂ) := by
  rw [Complex.ofReal_exp
    (-Real.pi * modeN k ^ 2 * Real.exp (2 * t))]
  apply congrArg Complex.exp
  unfold modeN
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The positive Gaussian series is exactly the nonconstant half of the
integer theta series. -/
theorem hasSum_nat_gaussian (t : ℝ) :
    HasSum
      (fun k : ℕ ↦ Real.exp (-Real.pi * modeN k ^ 2 * Real.exp (2 * t)))
      ((riemannTheta (Real.exp (2 * t)) - 1) / 2) := by
  have hcomplex := hasSum_nat_jacobiTheta
    (show 0 < (Complex.I * (Real.exp (2 * t) : ℂ)).im by
      rw [Complex.mul_im]
      simpa only [Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, one_mul, zero_add] using Real.exp_pos (2 * t))
  have hre := Complex.reCLM.hasSum hcomplex
  have htheta := riemannTheta_eq_re_jacobiTheta (Real.exp (2 * t))
  have hreal :
      (((jacobiTheta (Complex.I * (Real.exp (2 * t) : ℂ)) - 1) / 2 : ℂ).re) =
        ((jacobiTheta (Complex.I * (Real.exp (2 * t) : ℂ))).re - 1) / 2 := by
    norm_num [Complex.div_re]
  simp only [Complex.reCLM_apply] at hre
  rw [hreal, ← htheta] at hre
  simpa only [complex_gaussian_term_eq, Complex.ofReal_re] using hre

/-- Value-level decomposition of the global analytic `H` into its constant
mode and the literal positive Gaussian series. -/
theorem riemannH_eq_base_add_hSeries (t : ℝ) :
    riemannH t = Real.exp (t / 2) + hSeries t := by
  have hsum := (hasSum_nat_gaussian t).tsum_eq
  unfold riemannH hSeries hMode
  rw [tsum_mul_left]
  rw [hsum]
  ring

/-!
## Two differentiated positive modes
-/

/-- Polynomial recurrence for derivatives of a paired positive `H` mode. -/
noncomputable def hCertPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | j + 1 => (Polynomial.C (1 / 2) - Polynomial.C 2 * Polynomial.X) * hCertPoly j +
      Polynomial.C 2 * Polynomial.X * (hCertPoly j).derivative

noncomputable def modeX (k : ℕ) (t : ℝ) : ℝ :=
  Real.pi * modeN k ^ 2 * Real.exp (2 * t)

noncomputable def hModeJet (j k : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp (t / 2) * (hCertPoly j).eval (modeX k t) *
    Real.exp (-(modeX k t))

theorem modeN_pos (k : ℕ) : 0 < modeN k := by
  unfold modeN
  exact_mod_cast Nat.succ_pos k

theorem modeX_pos (k : ℕ) (t : ℝ) : 0 < modeX k t := by
  unfold modeX
  exact mul_pos (mul_pos Real.pi_pos (sq_pos_of_pos (modeN_pos k))) (Real.exp_pos _)

theorem hasDerivAt_modeX (k : ℕ) (t : ℝ) :
    HasDerivAt (modeX k) (2 * modeX k t) t := by
  change HasDerivAt
    (fun s : ℝ ↦ Real.pi * modeN k ^ 2 * Real.exp (2 * s))
    (2 * (Real.pi * modeN k ^ 2 * Real.exp (2 * t))) t
  have hinner : HasDerivAt (fun s : ℝ ↦ 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have h := ((Real.hasDerivAt_exp (2 * t)).comp t hinner).const_mul
    (Real.pi * modeN k ^ 2)
  simpa only [Function.comp_def, mul_assoc, mul_comm, mul_left_comm] using! h

theorem hModeJet_zero_eq_hMode (k : ℕ) (t : ℝ) :
    hModeJet 0 k t = hMode k t := by
  simp [hModeJet, hMode, hCertPoly, modeX]

theorem hasDerivAt_hModeJet (j k : ℕ) (t : ℝ) :
    HasDerivAt (hModeJet j k) (hModeJet (j + 1) k t) t := by
  let x : ℝ := modeX k t
  let p : Polynomial ℝ := hCertPoly j
  have hx : HasDerivAt (modeX k) (2 * x) t := by
    simpa [x] using hasDerivAt_modeX k t
  have he : HasDerivAt (fun s : ℝ ↦ Real.exp (s / 2))
      ((1 / 2) * Real.exp (t / 2)) t := by
    have hinner : HasDerivAt (fun s : ℝ ↦ s / 2) (1 / 2) t :=
      (hasDerivAt_id t).div_const 2
    simpa only [Function.comp_def, mul_comm] using!
      (Real.hasDerivAt_exp (t / 2)).comp t hinner
  have hp : HasDerivAt (fun s : ℝ ↦ p.eval (modeX k s))
      (p.derivative.eval x * (2 * x)) t := by
    simpa only [Function.comp_apply] using! (p.hasDerivAt x).comp t hx
  have hdecay : HasDerivAt (fun s : ℝ ↦ Real.exp (-(modeX k s)))
      (-(2 * x) * Real.exp (-x)) t := by
    simpa only [Function.comp_def, mul_comm] using!
      (Real.hasDerivAt_exp (-x)).comp t hx.neg
  have hraw := (((he.const_mul (2 : ℝ)).mul hp).mul hdecay)
  apply hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp [hModeJet, p]) |>.congr_deriv
  simp only [hModeJet, hCertPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  dsimp [x, p]
  ring

noncomputable def hSeriesJet (j : ℕ) (t : ℝ) : ℝ :=
  ∑' k : ℕ, hModeJet j k t

theorem hSeriesJet_zero_eq_hSeries (t : ℝ) : hSeriesJet 0 t = hSeries t := by
  apply tsum_congr
  intro k
  exact hModeJet_zero_eq_hMode k t

theorem summable_hModeJet_zero_at_zero :
    Summable fun k : ℕ ↦ hModeJet 0 k 0 := by
  have h := (hasSum_nat_gaussian 0).summable.mul_left (2 : ℝ)
  simpa [hModeJet_zero_eq_hMode, hMode] using h

namespace HIntervalControl

open Polynomial Set

noncomputable def coeffL1 (p : ℝ[X]) : ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|

theorem coeffL1_nonneg (p : ℝ[X]) : 0 ≤ coeffL1 p := by
  unfold coeffL1
  positivity

theorem abs_eval_le_coeffL1_mul_max (p : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    |p.eval x| ≤ coeffL1 p * max 1 x ^ p.natDegree := by
  rw [p.eval_eq_sum_range]
  calc
    |∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i| ≤
        ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i * x ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
        |p.coeff i| * max 1 x ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_pow, abs_of_nonneg hx]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ hx (le_max_right 1 x) i).trans
        (pow_le_pow_right₀ (le_max_left 1 x)
          (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = coeffL1 p * max 1 x ^ p.natDegree := by
      simp only [coeffL1, Finset.sum_mul]

noncomputable def intervalC (B : ℝ) : ℝ :=
  max 1 (Real.pi * Real.exp (2 * B))

noncomputable def intervalR : ℝ := Real.pi * Real.exp (-2)

noncomputable def intervalK (B : ℝ) (j : ℕ) : ℝ :=
  2 * Real.exp (B / 2) * coeffL1 (hCertPoly (j + 1)) *
    intervalC B ^ (hCertPoly (j + 1)).natDegree

noncomputable def intervalMajorant (B : ℝ) (j k : ℕ) : ℝ :=
  intervalK B j * modeN k ^ (2 * (hCertPoly (j + 1)).natDegree) *
    Real.exp (-intervalR * modeN k)

theorem intervalR_pos : 0 < intervalR := by unfold intervalR; positivity

theorem intervalC_one_le (B : ℝ) : 1 ≤ intervalC B := le_max_left _ _

theorem intervalC_pos (B : ℝ) : 0 < intervalC B :=
  zero_lt_one.trans_le (intervalC_one_le B)

theorem intervalK_nonneg (B : ℝ) (j : ℕ) : 0 ≤ intervalK B j := by
  unfold intervalK
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · exact coeffL1_nonneg _
  · exact pow_nonneg (intervalC_pos B).le _

theorem summable_modeN_pow_mul_exp_neg (d : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable fun k : ℕ ↦ modeN k ^ d * Real.exp (-r * modeN k) := by
  have h := Real.summable_pow_mul_exp_neg_nat_mul d hr
  have hs := h.comp_injective Nat.succ_injective
  simpa [Function.comp_def, modeN, Nat.cast_succ] using hs

theorem summable_intervalMajorant (B : ℝ) (j : ℕ) :
    Summable (intervalMajorant B j) := by
  unfold intervalMajorant
  simpa only [mul_assoc] using
    (summable_modeN_pow_mul_exp_neg
      (2 * (hCertPoly (j + 1)).natDegree) intervalR_pos).mul_left (intervalK B j)

theorem modeN_one_le (k : ℕ) : 1 ≤ modeN k := by
  unfold modeN
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)

theorem modeN_le_sq (k : ℕ) : modeN k ≤ modeN k ^ 2 := by
  have hn := modeN_one_le k
  nlinarith [sq_nonneg (modeN k - 1)]

theorem modeX_le_interval (B : ℝ) (k : ℕ) {t : ℝ} (ht : t < B) :
    modeX k t ≤ intervalC B * modeN k ^ 2 := by
  have hexp : Real.exp (2 * t) ≤ Real.exp (2 * B) :=
    Real.exp_monotone (by linarith)
  unfold modeX
  calc
    Real.pi * modeN k ^ 2 * Real.exp (2 * t) =
        (Real.pi * Real.exp (2 * t)) * modeN k ^ 2 := by ring
    _ ≤ intervalC B * modeN k ^ 2 := by
      gcongr
      exact (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le).trans (le_max_right _ _)

theorem max_modeX_le_interval (B : ℝ) (k : ℕ) {t : ℝ} (ht : t < B) :
    max 1 (modeX k t) ≤ intervalC B * modeN k ^ 2 := by
  apply max_le
  · have hC := intervalC_one_le B
    have hn := modeN_one_le k
    nlinarith [sq_nonneg (modeN k - 1)]
  · exact modeX_le_interval B k ht

theorem exp_prefactor_le (B : ℝ) {t : ℝ} (ht : t < B) :
    Real.exp (t / 2) ≤ Real.exp (B / 2) := by
  exact Real.exp_monotone (by linarith)

theorem exp_decay_le (k : ℕ) {t : ℝ} (ht : -1 < t) :
    Real.exp (-(modeX k t)) ≤ Real.exp (-intervalR * modeN k) := by
  apply Real.exp_monotone
  have hexp : Real.exp (-2) ≤ Real.exp (2 * t) :=
    Real.exp_monotone (by linarith)
  have hbase : intervalR * modeN k ^ 2 ≤ modeX k t := by
    unfold intervalR modeX
    calc
      Real.pi * Real.exp (-2) * modeN k ^ 2 =
          Real.pi * modeN k ^ 2 * Real.exp (-2) := by ring
      _ ≤ Real.pi * modeN k ^ 2 * Real.exp (2 * t) := by
        exact mul_le_mul_of_nonneg_left hexp
          (mul_nonneg Real.pi_pos.le (sq_nonneg _))
  have hlin : intervalR * modeN k ≤ intervalR * modeN k ^ 2 :=
    mul_le_mul_of_nonneg_left (modeN_le_sq k) intervalR_pos.le
  linarith

theorem norm_hModeJet_le_intervalMajorant (B : ℝ) (j k : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioo (-1 : ℝ) B) :
    ‖hModeJet (j + 1) k t‖ ≤ intervalMajorant B j k := by
  let p := hCertPoly (j + 1)
  let d := p.natDegree
  have hp := abs_eval_le_coeffL1_mul_max p (modeX_pos k t).le
  have hmax := max_modeX_le_interval B k ht.2
  have heval : |p.eval (modeX k t)| ≤
      coeffL1 p * intervalC B ^ d * modeN k ^ (2 * d) := by
    calc
      |p.eval (modeX k t)| ≤ coeffL1 p * max 1 (modeX k t) ^ d := hp
      _ ≤ coeffL1 p * (intervalC B * modeN k ^ 2) ^ d := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hmax d) (coeffL1_nonneg p)
      _ = coeffL1 p * intervalC B ^ d * modeN k ^ (2 * d) := by
        rw [mul_pow, ← pow_mul]
        ring
  have hpref := exp_prefactor_le B ht.2
  have hdecay := exp_decay_le k ht.1
  have hcoeff : 0 ≤ coeffL1 (hCertPoly (j + 1)) := coeffL1_nonneg _
  unfold hModeJet intervalMajorant intervalK
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
    abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg (Real.exp_nonneg _)]
  dsimp [p, d] at heval ⊢
  calc
    2 * Real.exp (t / 2) * |(hCertPoly (j + 1)).eval (modeX k t)| *
          Real.exp (-(modeX k t)) ≤
        2 * Real.exp (B / 2) *
          (coeffL1 (hCertPoly (j + 1)) *
            intervalC B ^ (hCertPoly (j + 1)).natDegree *
            modeN k ^ (2 * (hCertPoly (j + 1)).natDegree)) *
          Real.exp (-intervalR * modeN k) := by
      gcongr
      exact mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg hcoeff (pow_nonneg (intervalC_pos B).le _))
          (pow_nonneg (modeN_pos k).le _))
    _ = (2 * Real.exp (B / 2) * coeffL1 (hCertPoly (j + 1)) *
          intervalC B ^ (hCertPoly (j + 1)).natDegree) *
        modeN k ^ (2 * (hCertPoly (j + 1)).natDegree) *
          Real.exp (-intervalR * modeN k) := by ring

theorem summable_hModeJet_at_zero {j : ℕ} (hj : j ≤ 2) :
    Summable fun k : ℕ ↦ hModeJet j k 0 := by
  cases j with
  | zero => exact summable_hModeJet_zero_at_zero
  | succ j =>
      have hjlt : j < 2 := Nat.lt_of_succ_le hj
      exact (summable_intervalMajorant 1 j).of_norm_bounded fun k ↦
        norm_hModeJet_le_intervalMajorant 1 j k (by constructor <;> norm_num)

theorem hasDerivAt_hSeriesJet_on_Ioo (B : ℝ) (hB : 0 < B)
    {j : ℕ} (hj : j < 2) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) B) :
    HasDerivAt (hSeriesJet j) (hSeriesJet (j + 1) t) t := by
  have hsum := hasDerivAt_tsum_of_isPreconnected
    (summable_intervalMajorant B j) isOpen_Ioo ordConnected_Ioo.isPreconnected
    (fun k y _ ↦ hasDerivAt_hModeJet j k y)
    (fun k y hy ↦ norm_hModeJet_le_intervalMajorant B j k hy)
    (show (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) B by exact ⟨by norm_num, hB⟩)
    (summable_hModeJet_at_zero hj.le) ht
  simpa only [hSeriesJet] using! hsum

theorem derivativeTowerThroughTwo_at_nonneg {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (hSeriesJet 0) (hSeriesJet 1 t) t ∧
    HasDerivAt (hSeriesJet 1) (hSeriesJet 2 t) t := by
  let B := t + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) B := by
    dsimp [B]
    constructor <;> linarith
  exact ⟨hasDerivAt_hSeriesJet_on_Ioo B hB (by omega) htIoo,
    hasDerivAt_hSeriesJet_on_Ioo B hB (by omega) htIoo⟩

end HIntervalControl

/-!
## Application of the second-order operator
-/

noncomputable def thetaMode (k : ℕ) (t : ℝ) : ℝ :=
  (4 * Real.pi ^ 2 * modeN k ^ 4 * Real.exp ((9 / 2) * t) -
      6 * Real.pi * modeN k ^ 2 * Real.exp ((5 / 2) * t)) *
    Real.exp (-Real.pi * modeN k ^ 2 * Real.exp (2 * t))

noncomputable def thetaSeries (t : ℝ) : ℝ := ∑' k : ℕ, thetaMode k t

theorem secondOrder_hMode_eq_thetaMode (k : ℕ) (t : ℝ) :
    (hModeJet 2 k t - (1 / 4 : ℝ) * hModeJet 0 k t) / 2 = thetaMode k t := by
  unfold hModeJet thetaMode modeX
  simp [hCertPoly]
  rw [show Real.exp ((9 / 2) * t) =
      Real.exp (t / 2) * Real.exp (2 * t) ^ 2 by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring]
  rw [show Real.exp ((5 / 2) * t) = Real.exp (t / 2) * Real.exp (2 * t) by
    rw [← Real.exp_add]
    congr 1
    ring]
  ring

theorem secondOrder_hSeries_eq_thetaSeries {t : ℝ} (ht : 0 ≤ t) :
    (hSeriesJet 2 t - (1 / 4 : ℝ) * hSeriesJet 0 t) / 2 = thetaSeries t := by
  let B := t + 1
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) B := by
    dsimp [B]
    constructor <;> linarith
  have hzero : Summable fun k : ℕ ↦ hModeJet 0 k t := by
    rw [funext fun k ↦ hModeJet_zero_eq_hMode k t]
    exact (hasSum_nat_gaussian t).summable.mul_left (2 * Real.exp (t / 2))
      |>.congr (fun k ↦ by simp [hMode])
  have htwo : Summable fun k : ℕ ↦ hModeJet 2 k t :=
    (HIntervalControl.summable_intervalMajorant B 1).of_norm_bounded fun k ↦
      HIntervalControl.norm_hModeJet_le_intervalMajorant B 1 k htIoo
  unfold hSeriesJet thetaSeries
  rw [← tsum_mul_left, ← htwo.tsum_sub (hzero.mul_left (1 / 4 : ℝ)),
    ← tsum_div_const]
  apply tsum_congr
  intro k
  rw [← secondOrder_hMode_eq_thetaMode]

noncomputable def hBase (t : ℝ) : ℝ := Real.exp (t / 2)
noncomputable def hBaseJetOne (t : ℝ) : ℝ := (1 / 2) * Real.exp (t / 2)
noncomputable def hBaseJetTwo (t : ℝ) : ℝ := (1 / 4) * Real.exp (t / 2)

theorem hasDerivAt_hBase (t : ℝ) : HasDerivAt hBase (hBaseJetOne t) t := by
  change HasDerivAt (fun s : ℝ ↦ Real.exp (s / 2))
    ((1 / 2) * Real.exp (t / 2)) t
  have hinner : HasDerivAt (fun s : ℝ ↦ s / 2) (1 / 2) t :=
    (hasDerivAt_id t).div_const 2
  simpa only [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_exp (t / 2)).comp t hinner

theorem hasDerivAt_hBaseJetOne (t : ℝ) :
    HasDerivAt hBaseJetOne (hBaseJetTwo t) t := by
  change HasDerivAt (fun s : ℝ ↦ (1 / 2) * Real.exp (s / 2))
    ((1 / 4) * Real.exp (t / 2)) t
  have hinner : HasDerivAt (fun s : ℝ ↦ s / 2) (1 / 2) t :=
    (hasDerivAt_id t).div_const 2
  have h := ((Real.hasDerivAt_exp (t / 2)).comp t hinner).const_mul (1 / 2 : ℝ)
  have hcoeff : (1 / 2 : ℝ) * (Real.exp (t / 2) * (1 / 2)) =
      (1 / 4) * Real.exp (t / 2) := by ring
  rw [hcoeff] at h
  simpa only [Function.comp_def] using h

theorem riemannH_eq_hBase_add_hSeriesJet_zero :
    riemannH = fun t ↦ hBase t + hSeriesJet 0 t := by
  funext t
  rw [hBase, hSeriesJet_zero_eq_hSeries]
  exact riemannH_eq_base_add_hSeries t

/-- The globally defined second-order kernel equals the literal positive-side
theta-series kernel at every nonnegative point. Smoothness at zero comes from
the global holomorphic definition, not from this representation theorem. -/
theorem globalRiemannKernel_eq_thetaSeries_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    globalRiemannKernel t = thetaSeries t := by
  let B := t + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) B := by
    dsimp [B]
    constructor <;> linarith
  have hfirst (s : ℝ) (hs : s ∈ Set.Ioo (-1 : ℝ) B) :
      HasDerivAt riemannH (hBaseJetOne s + hSeriesJet 1 s) s := by
    have hraw := (hasDerivAt_hBase s).add
      (HIntervalControl.hasDerivAt_hSeriesJet_on_Ioo B hB (j := 0) (by omega) hs)
    apply hraw.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun u =>
      congrFun riemannH_eq_hBase_add_hSeriesJet_zero u
  have hevent : deriv riemannH =ᶠ[nhds t]
      (fun s ↦ hBaseJetOne s + hSeriesJet 1 s) := by
    filter_upwards [isOpen_Ioo.mem_nhds htIoo] with s hs
    exact (hfirst s hs).deriv
  have hsecondRaw := (hasDerivAt_hBaseJetOne t).add
    (HIntervalControl.hasDerivAt_hSeriesJet_on_Ioo B hB (j := 1) (by omega) htIoo)
  have hsecond : HasDerivAt (deriv riemannH)
      (hBaseJetTwo t + hSeriesJet 2 t) t :=
    hsecondRaw.congr_of_eventuallyEq hevent
  rw [globalRiemannKernel_eq_paper_form, hsecond.deriv,
    riemannH_eq_hBase_add_hSeriesJet_zero]
  change ((1 / 4 : ℝ) * Real.exp (t / 2) + hSeriesJet 2 t -
      (1 / 4 : ℝ) * (Real.exp (t / 2) + hSeriesJet 0 t)) / 2 = thetaSeries t
  rw [← secondOrder_hSeries_eq_thetaSeries ht]
  ring

end PF4.Advancement.ThetaModularContinuation
