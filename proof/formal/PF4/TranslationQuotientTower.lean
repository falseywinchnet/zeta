import PF4.Definitions
import PF4.QuotientIntegral
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Translation quotient tower: object layer

The translate quotient tower `A,B,C = u₂/u₁,u₃/u₁,u₄/u₁`,
`V,W = v₃/v₂,v₄/v₂`, `q = w₄/w₃` for `uⱼ = Φ(·-yⱼ)`, with every level's
derivative an explicit quotient-rule formula and every division carrying a
proved nonzero denominator. The three strict level signs (`v₂>0`, `w₃>0`,
`q'>0`) are named premises here, never conclusions in disguise: they are the
next conversion boundary from the maintained kernel structure and the
maintained conditional `∂ξΨ<0` assembly. The final theorem identifies the original
`PF4.translationMinor` with the engine's factored determinant and concludes
strict order-four minor positivity from the maintained continuous quotient
engine.
-/

namespace PF4.TranslationQuotientTower

open PF4.ContinuousQuotientBox

/-! ## Level zero: translates -/

theorem hasDerivAt_translate {Φ Φ1 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t) (c t : ℝ) :
    HasDerivAt (fun s => Φ (s - c)) (Φ1 (t - c)) t := by
  have h := (hΦ (t - c)).comp t ((hasDerivAt_id t).sub_const c)
  simpa [Function.comp_def] using h

theorem continuous_translate {Φ : ℝ → ℝ} (hΦc : Continuous Φ) (c : ℝ) :
    Continuous fun s : ℝ => Φ (s - c) :=
  hΦc.comp (continuous_id.sub continuous_const)

/-! ## Level one: the translate quotients `A,B,C` and their jets -/

/-- The first-level translate quotient `Φ(·-b)/Φ(·-a)`. -/
noncomputable def firstQuot (Φ : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun t => Φ (t - b) / Φ (t - a)

/-- Exact quotient-rule derivative of `firstQuot`. -/
noncomputable def firstQuotD (Φ Φ1 : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun t => (Φ1 (t - b) * Φ (t - a) - Φ (t - b) * Φ1 (t - a)) / Φ (t - a) ^ 2

/-- Exact second derivative of `firstQuot`. -/
noncomputable def firstQuotD2 (Φ Φ1 Φ2 : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun t =>
    ((Φ2 (t - b) * Φ (t - a) - Φ (t - b) * Φ2 (t - a)) * Φ (t - a) ^ 2 -
      (Φ1 (t - b) * Φ (t - a) - Φ (t - b) * Φ1 (t - a)) *
        (2 * Φ (t - a) * Φ1 (t - a))) / Φ (t - a) ^ 4

/-- Exact third derivative of `firstQuot`. -/
noncomputable def firstQuotD3 (Φ Φ1 Φ2 Φ3 : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun t =>
    (((Φ3 (t - b) * Φ (t - a) + Φ2 (t - b) * Φ1 (t - a) -
          Φ1 (t - b) * Φ2 (t - a) - Φ (t - b) * Φ3 (t - a)) * Φ (t - a) ^ 2 -
        (Φ1 (t - b) * Φ (t - a) - Φ (t - b) * Φ1 (t - a)) *
          (2 * Φ1 (t - a) ^ 2 + 2 * Φ (t - a) * Φ2 (t - a))) *
        Φ (t - a) ^ 4 -
      ((Φ2 (t - b) * Φ (t - a) - Φ (t - b) * Φ2 (t - a)) * Φ (t - a) ^ 2 -
        (Φ1 (t - b) * Φ (t - a) - Φ (t - b) * Φ1 (t - a)) *
          (2 * Φ (t - a) * Φ1 (t - a))) *
        (4 * Φ (t - a) ^ 3 * Φ1 (t - a))) / Φ (t - a) ^ 8

theorem hasDerivAt_firstQuot {Φ Φ1 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t) (hΦpos : ∀ t, 0 < Φ t) (a b t : ℝ) :
    HasDerivAt (firstQuot Φ a b) (firstQuotD Φ Φ1 a b t) t :=
  (hasDerivAt_translate hΦ b t).fun_div (hasDerivAt_translate hΦ a t)
    (hΦpos (t - a)).ne'

theorem hasDerivAt_firstQuotD {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t) (a b t : ℝ) :
    HasDerivAt (firstQuotD Φ Φ1 a b) (firstQuotD2 Φ Φ1 Φ2 a b t) t := by
  have hN : HasDerivAt
      (fun s => Φ1 (s - b) * Φ (s - a) - Φ (s - b) * Φ1 (s - a))
      (Φ2 (t - b) * Φ (t - a) - Φ (t - b) * Φ2 (t - a)) t := by
    have h := ((hasDerivAt_translate hΦ1 b t).mul
        (hasDerivAt_translate hΦ a t)).sub
      ((hasDerivAt_translate hΦ b t).mul (hasDerivAt_translate hΦ1 a t))
    exact h.congr_deriv (by ring)
  have hD : HasDerivAt (fun s => Φ (s - a) ^ 2)
      (2 * Φ (t - a) * Φ1 (t - a)) t := by
    have h := (hasDerivAt_translate hΦ a t).fun_pow 2
    exact h.congr_deriv (by push_cast; ring)
  have h := hN.fun_div hD (pow_ne_zero 2 (hΦpos (t - a)).ne')
  exact h.congr_deriv (by unfold firstQuotD2; ring)

theorem hasDerivAt_firstQuotD2 {Φ Φ1 Φ2 Φ3 : ℝ → ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦ2 : ∀ t, HasDerivAt Φ2 (Φ3 t) t)
    (hΦpos : ∀ t, 0 < Φ t) (a b t : ℝ) :
    HasDerivAt (firstQuotD2 Φ Φ1 Φ2 a b) (firstQuotD3 Φ Φ1 Φ2 Φ3 a b t) t := by
  have hN1 : HasDerivAt
      (fun s => Φ2 (s - b) * Φ (s - a) - Φ (s - b) * Φ2 (s - a))
      (Φ3 (t - b) * Φ (t - a) + Φ2 (t - b) * Φ1 (t - a) -
        Φ1 (t - b) * Φ2 (t - a) - Φ (t - b) * Φ3 (t - a)) t := by
    have h := ((hasDerivAt_translate hΦ2 b t).mul
        (hasDerivAt_translate hΦ a t)).sub
      ((hasDerivAt_translate hΦ b t).mul (hasDerivAt_translate hΦ2 a t))
    exact h.congr_deriv (by ring)
  have hN : HasDerivAt
      (fun s => Φ1 (s - b) * Φ (s - a) - Φ (s - b) * Φ1 (s - a))
      (Φ2 (t - b) * Φ (t - a) - Φ (t - b) * Φ2 (t - a)) t := by
    have h := ((hasDerivAt_translate hΦ1 b t).mul
        (hasDerivAt_translate hΦ a t)).sub
      ((hasDerivAt_translate hΦ b t).mul (hasDerivAt_translate hΦ1 a t))
    exact h.congr_deriv (by ring)
  have hg2 : HasDerivAt (fun s => Φ (s - a) ^ 2)
      (2 * Φ (t - a) * Φ1 (t - a)) t := by
    have h := (hasDerivAt_translate hΦ a t).fun_pow 2
    exact h.congr_deriv (by push_cast; ring)
  have h2gg1 : HasDerivAt (fun s => 2 * Φ (s - a) * Φ1 (s - a))
      (2 * Φ1 (t - a) ^ 2 + 2 * Φ (t - a) * Φ2 (t - a)) t := by
    have h := (((hasDerivAt_translate hΦ a t).const_mul 2).mul
      (hasDerivAt_translate hΦ1 a t))
    exact h.congr_deriv (by ring)
  have hM : HasDerivAt
      (fun s => (Φ2 (s - b) * Φ (s - a) - Φ (s - b) * Φ2 (s - a)) *
          Φ (s - a) ^ 2 -
        (Φ1 (s - b) * Φ (s - a) - Φ (s - b) * Φ1 (s - a)) *
          (2 * Φ (s - a) * Φ1 (s - a)))
      ((Φ3 (t - b) * Φ (t - a) + Φ2 (t - b) * Φ1 (t - a) -
          Φ1 (t - b) * Φ2 (t - a) - Φ (t - b) * Φ3 (t - a)) * Φ (t - a) ^ 2 -
        (Φ1 (t - b) * Φ (t - a) - Φ (t - b) * Φ1 (t - a)) *
          (2 * Φ1 (t - a) ^ 2 + 2 * Φ (t - a) * Φ2 (t - a))) t := by
    have h := (hN1.mul hg2).sub (hN.mul h2gg1)
    exact h.congr_deriv (by ring)
  have hg4 : HasDerivAt (fun s => Φ (s - a) ^ 4)
      (4 * Φ (t - a) ^ 3 * Φ1 (t - a)) t := by
    have h := (hasDerivAt_translate hΦ a t).fun_pow 4
    exact h.congr_deriv (by push_cast; ring)
  have h := hM.fun_div hg4 (pow_ne_zero 4 (hΦpos (t - a)).ne')
  exact h.congr_deriv (by unfold firstQuotD3; ring)

theorem continuous_firstQuotD {Φ Φ1 : ℝ → ℝ}
    (hΦc : Continuous Φ) (hΦ1c : Continuous Φ1)
    (hΦpos : ∀ t, 0 < Φ t) (a b : ℝ) :
    Continuous (firstQuotD Φ Φ1 a b) := by
  unfold firstQuotD
  refine Continuous.div (by fun_prop) ((continuous_translate hΦc a).pow 2)
    fun t => pow_ne_zero 2 (hΦpos (t - a)).ne'

theorem continuous_firstQuotD2 {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦc : Continuous Φ) (hΦ1c : Continuous Φ1) (hΦ2c : Continuous Φ2)
    (hΦpos : ∀ t, 0 < Φ t) (a b : ℝ) :
    Continuous (firstQuotD2 Φ Φ1 Φ2 a b) := by
  unfold firstQuotD2
  refine Continuous.div (by fun_prop) ((continuous_translate hΦc a).pow 4)
    fun t => pow_ne_zero 4 (hΦpos (t - a)).ne'

theorem continuous_firstQuotD3 {Φ Φ1 Φ2 Φ3 : ℝ → ℝ}
    (hΦc : Continuous Φ) (hΦ1c : Continuous Φ1) (hΦ2c : Continuous Φ2)
    (hΦ3c : Continuous Φ3)
    (hΦpos : ∀ t, 0 < Φ t) (a b : ℝ) :
    Continuous (firstQuotD3 Φ Φ1 Φ2 Φ3 a b) := by
  unfold firstQuotD3
  refine Continuous.div (by fun_prop) ((continuous_translate hΦc a).pow 8)
    fun t => pow_ne_zero 8 (hΦpos (t - a)).ne'

/-! ## Level two: the quotient-derivative quotients `V,W` and their jets -/

/-- The second-level quotient `v_b/v_c` of first-level derivatives with
pivot column `c`. -/
noncomputable def secondQuot (Φ Φ1 : ℝ → ℝ) (a c b : ℝ) : ℝ → ℝ :=
  fun t => firstQuotD Φ Φ1 a b t / firstQuotD Φ Φ1 a c t

/-- Exact quotient-rule derivative of `secondQuot`. -/
noncomputable def secondQuotD (Φ Φ1 Φ2 : ℝ → ℝ) (a c b : ℝ) : ℝ → ℝ :=
  fun t => (firstQuotD2 Φ Φ1 Φ2 a b t * firstQuotD Φ Φ1 a c t -
      firstQuotD Φ Φ1 a b t * firstQuotD2 Φ Φ1 Φ2 a c t) /
    firstQuotD Φ Φ1 a c t ^ 2

/-- Exact second derivative of `secondQuot`. -/
noncomputable def secondQuotD2 (Φ Φ1 Φ2 Φ3 : ℝ → ℝ) (a c b : ℝ) : ℝ → ℝ :=
  fun t =>
    ((firstQuotD3 Φ Φ1 Φ2 Φ3 a b t * firstQuotD Φ Φ1 a c t -
        firstQuotD Φ Φ1 a b t * firstQuotD3 Φ Φ1 Φ2 Φ3 a c t) *
        firstQuotD Φ Φ1 a c t ^ 2 -
      (firstQuotD2 Φ Φ1 Φ2 a b t * firstQuotD Φ Φ1 a c t -
        firstQuotD Φ Φ1 a b t * firstQuotD2 Φ Φ1 Φ2 a c t) *
        (2 * firstQuotD Φ Φ1 a c t * firstQuotD2 Φ Φ1 Φ2 a c t)) /
      firstQuotD Φ Φ1 a c t ^ 4

theorem hasDerivAt_secondQuot {Φ Φ1 Φ2 : ℝ → ℝ} {a c : ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦpos : ∀ t, 0 < Φ t)
    (hpivot : ∀ t, 0 < firstQuotD Φ Φ1 a c t) (b t : ℝ) :
    HasDerivAt (secondQuot Φ Φ1 a c b) (secondQuotD Φ Φ1 Φ2 a c b t) t :=
  (hasDerivAt_firstQuotD hΦ hΦ1 hΦpos a b t).fun_div
    (hasDerivAt_firstQuotD hΦ hΦ1 hΦpos a c t) (hpivot t).ne'

theorem hasDerivAt_secondQuotD {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {a c : ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦ2 : ∀ t, HasDerivAt Φ2 (Φ3 t) t)
    (hΦpos : ∀ t, 0 < Φ t)
    (hpivot : ∀ t, 0 < firstQuotD Φ Φ1 a c t) (b t : ℝ) :
    HasDerivAt (secondQuotD Φ Φ1 Φ2 a c b)
      (secondQuotD2 Φ Φ1 Φ2 Φ3 a c b t) t := by
  have hK : HasDerivAt
      (fun s => firstQuotD2 Φ Φ1 Φ2 a b s * firstQuotD Φ Φ1 a c s -
        firstQuotD Φ Φ1 a b s * firstQuotD2 Φ Φ1 Φ2 a c s)
      (firstQuotD3 Φ Φ1 Φ2 Φ3 a b t * firstQuotD Φ Φ1 a c t -
        firstQuotD Φ Φ1 a b t * firstQuotD3 Φ Φ1 Φ2 Φ3 a c t) t := by
    have h := ((hasDerivAt_firstQuotD2 hΦ hΦ1 hΦ2 hΦpos a b t).mul
        (hasDerivAt_firstQuotD hΦ hΦ1 hΦpos a c t)).sub
      ((hasDerivAt_firstQuotD hΦ hΦ1 hΦpos a b t).mul
        (hasDerivAt_firstQuotD2 hΦ hΦ1 hΦ2 hΦpos a c t))
    exact h.congr_deriv (by ring)
  have hP : HasDerivAt (fun s => firstQuotD Φ Φ1 a c s ^ 2)
      (2 * firstQuotD Φ Φ1 a c t * firstQuotD2 Φ Φ1 Φ2 a c t) t := by
    have h := (hasDerivAt_firstQuotD hΦ hΦ1 hΦpos a c t).fun_pow 2
    exact h.congr_deriv (by push_cast; ring)
  have h := hK.fun_div hP (pow_ne_zero 2 (hpivot t).ne')
  exact h.congr_deriv (by unfold secondQuotD2; ring)

theorem continuous_secondQuotD {Φ Φ1 Φ2 : ℝ → ℝ} {a c : ℝ}
    (hΦc : Continuous Φ) (hΦ1c : Continuous Φ1) (hΦ2c : Continuous Φ2)
    (hΦpos : ∀ t, 0 < Φ t)
    (hpivot : ∀ t, 0 < firstQuotD Φ Φ1 a c t) (b : ℝ) :
    Continuous (secondQuotD Φ Φ1 Φ2 a c b) := by
  have h1 := continuous_firstQuotD hΦc hΦ1c hΦpos a b
  have h2 := continuous_firstQuotD hΦc hΦ1c hΦpos a c
  have h3 := continuous_firstQuotD2 hΦc hΦ1c hΦ2c hΦpos a b
  have h4 := continuous_firstQuotD2 hΦc hΦ1c hΦ2c hΦpos a c
  unfold secondQuotD
  refine Continuous.div (by fun_prop) (h2.pow 2)
    fun t => pow_ne_zero 2 (hpivot t).ne'

theorem continuous_secondQuotD2 {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {a c : ℝ}
    (hΦc : Continuous Φ) (hΦ1c : Continuous Φ1) (hΦ2c : Continuous Φ2)
    (hΦ3c : Continuous Φ3)
    (hΦpos : ∀ t, 0 < Φ t)
    (hpivot : ∀ t, 0 < firstQuotD Φ Φ1 a c t) (b : ℝ) :
    Continuous (secondQuotD2 Φ Φ1 Φ2 Φ3 a c b) := by
  have h1 := continuous_firstQuotD hΦc hΦ1c hΦpos a b
  have h2 := continuous_firstQuotD hΦc hΦ1c hΦpos a c
  have h3 := continuous_firstQuotD2 hΦc hΦ1c hΦ2c hΦpos a b
  have h4 := continuous_firstQuotD2 hΦc hΦ1c hΦ2c hΦpos a c
  have h5 := continuous_firstQuotD3 hΦc hΦ1c hΦ2c hΦ3c hΦpos a b
  have h6 := continuous_firstQuotD3 hΦc hΦ1c hΦ2c hΦ3c hΦpos a c
  unfold secondQuotD2
  refine Continuous.div (by fun_prop) (h2.pow 4)
    fun t => pow_ne_zero 4 (hpivot t).ne'

/-! ## Level three: the terminal quotient `q` and its jet -/

/-- The terminal quotient `w_e/w_d` of second-level derivatives with second
pivot column `d`. -/
noncomputable def terminalQuot (Φ Φ1 Φ2 : ℝ → ℝ) (a c d e : ℝ) : ℝ → ℝ :=
  fun t => secondQuotD Φ Φ1 Φ2 a c e t / secondQuotD Φ Φ1 Φ2 a c d t

/-- Exact quotient-rule derivative of `terminalQuot`. -/
noncomputable def terminalQuotD (Φ Φ1 Φ2 Φ3 : ℝ → ℝ) (a c d e : ℝ) : ℝ → ℝ :=
  fun t => (secondQuotD2 Φ Φ1 Φ2 Φ3 a c e t * secondQuotD Φ Φ1 Φ2 a c d t -
      secondQuotD Φ Φ1 Φ2 a c e t * secondQuotD2 Φ Φ1 Φ2 Φ3 a c d t) /
    secondQuotD Φ Φ1 Φ2 a c d t ^ 2

theorem hasDerivAt_terminalQuot {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {a c d : ℝ}
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦ2 : ∀ t, HasDerivAt Φ2 (Φ3 t) t)
    (hΦpos : ∀ t, 0 < Φ t)
    (hpivot : ∀ t, 0 < firstQuotD Φ Φ1 a c t)
    (hsecond : ∀ t, 0 < secondQuotD Φ Φ1 Φ2 a c d t) (e t : ℝ) :
    HasDerivAt (terminalQuot Φ Φ1 Φ2 a c d e)
      (terminalQuotD Φ Φ1 Φ2 Φ3 a c d e t) t :=
  (hasDerivAt_secondQuotD hΦ hΦ1 hΦ2 hΦpos hpivot e t).fun_div
    (hasDerivAt_secondQuotD hΦ hΦ1 hΦ2 hΦpos hpivot d t) (hsecond t).ne'

theorem continuous_terminalQuotD {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {a c d : ℝ}
    (hΦc : Continuous Φ) (hΦ1c : Continuous Φ1) (hΦ2c : Continuous Φ2)
    (hΦ3c : Continuous Φ3)
    (hΦpos : ∀ t, 0 < Φ t)
    (hpivot : ∀ t, 0 < firstQuotD Φ Φ1 a c t)
    (hsecond : ∀ t, 0 < secondQuotD Φ Φ1 Φ2 a c d t) (e : ℝ) :
    Continuous (terminalQuotD Φ Φ1 Φ2 Φ3 a c d e) := by
  have h1 := continuous_secondQuotD hΦc hΦ1c hΦ2c hΦpos hpivot d
  have h2 := continuous_secondQuotD hΦc hΦ1c hΦ2c hΦpos hpivot e
  have h3 := continuous_secondQuotD2 hΦc hΦ1c hΦ2c hΦ3c hΦpos hpivot d
  have h4 := continuous_secondQuotD2 hΦc hΦ1c hΦ2c hΦ3c hΦpos hpivot e
  unfold terminalQuotD
  refine Continuous.div (by fun_prop) (h1.pow 2)
    fun t => pow_ne_zero 2 (hsecond t).ne'

/-! ## Exact factor identities -/

theorem firstQuotD_factor {Φ Φ1 : ℝ → ℝ} {a c : ℝ}
    (hpivot : ∀ t, 0 < firstQuotD Φ Φ1 a c t) (b t : ℝ) :
    firstQuotD Φ Φ1 a b t =
      firstQuotD Φ Φ1 a c t * secondQuot Φ Φ1 a c b t := by
  unfold secondQuot
  field_simp [(hpivot t).ne']

theorem secondQuotD_factor {Φ Φ1 Φ2 : ℝ → ℝ} {a c d : ℝ}
    (hsecond : ∀ t, 0 < secondQuotD Φ Φ1 Φ2 a c d t) (e t : ℝ) :
    secondQuotD Φ Φ1 Φ2 a c e t =
      secondQuotD Φ Φ1 Φ2 a c d t * terminalQuot Φ Φ1 Φ2 a c d e t := by
  unfold terminalQuot
  field_simp [(hsecond t).ne']

/-! ## Object identity with the original translation minor -/

theorem translate_mul_firstQuot {Φ : ℝ → ℝ} (hΦpos : ∀ t, 0 < Φ t)
    (a b r : ℝ) :
    Φ (r - a) * firstQuot Φ a b r = Φ (r - b) := by
  unfold firstQuot
  field_simp [(hΦpos (r - a)).ne']

theorem translationMinor_eq_rawFactoredDet4 {Φ : ℝ → ℝ}
    (hΦpos : ∀ t, 0 < Φ t) (t₁ t₂ t₃ t₄ y₁ y₂ y₃ y₄ : ℝ) :
    PF4.translationMinor Φ ![t₁, t₂, t₃, t₄] ![y₁, y₂, y₃, y₄] =
      rawFactoredDet4
        (Φ (t₁ - y₁)) (Φ (t₂ - y₁)) (Φ (t₃ - y₁)) (Φ (t₄ - y₁))
        (firstQuot Φ y₁ y₂ t₁) (firstQuot Φ y₁ y₃ t₁) (firstQuot Φ y₁ y₄ t₁)
        (firstQuot Φ y₁ y₂ t₂) (firstQuot Φ y₁ y₃ t₂) (firstQuot Φ y₁ y₄ t₂)
        (firstQuot Φ y₁ y₂ t₃) (firstQuot Φ y₁ y₃ t₃) (firstQuot Φ y₁ y₄ t₃)
        (firstQuot Φ y₁ y₂ t₄) (firstQuot Φ y₁ y₃ t₄)
        (firstQuot Φ y₁ y₄ t₄) := by
  unfold PF4.translationMinor PF4.translationMatrix rawFactoredDet4
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translate_mul_firstQuot hΦpos]

/-! ## Strict order-four minor positivity from the tower signs -/

/-- Conditional instantiation boundary: for the actual translate quotient
tower, strict positivity of the three quotient levels (`v₂ = A' > 0`,
`w₃ = V' > 0`, `q' > 0`) forces strict positivity of the original order-four
translation minor at strictly increasing rows. The three level signs are the
named upstream conversion boundary; no minor, Wronskian, finite difference,
integral, or terminal quotient-derivative sign is assumed elsewhere. -/
theorem translationMinor_pos_of_quotient_tower_signs
    {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {t₁ t₂ t₃ t₄ y₁ y₂ y₃ y₄ : ℝ}
    (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃) (ht₃₄ : t₃ < t₄)
    (hΦ : ∀ t, HasDerivAt Φ (Φ1 t) t)
    (hΦ1 : ∀ t, HasDerivAt Φ1 (Φ2 t) t)
    (hΦ2 : ∀ t, HasDerivAt Φ2 (Φ3 t) t)
    (hΦ3c : Continuous Φ3)
    (hΦpos : ∀ t, 0 < Φ t)
    (hfirst : ∀ t, 0 < firstQuotD Φ Φ1 y₁ y₂ t)
    (hsecond : ∀ t, 0 < secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t)
    (hterminal : ∀ t, 0 < terminalQuotD Φ Φ1 Φ2 Φ3 y₁ y₂ y₃ y₄ t) :
    0 < PF4.translationMinor Φ ![t₁, t₂, t₃, t₄] ![y₁, y₂, y₃, y₄] := by
  have hΦc : Continuous Φ :=
    continuous_iff_continuousAt.mpr fun t => (hΦ t).continuousAt
  have hΦ1c : Continuous Φ1 :=
    continuous_iff_continuousAt.mpr fun t => (hΦ1 t).continuousAt
  have hΦ2c : Continuous Φ2 :=
    continuous_iff_continuousAt.mpr fun t => (hΦ2 t).continuousAt
  rw [translationMinor_eq_rawFactoredDet4 hΦpos t₁ t₂ t₃ t₄ y₁ y₂ y₃ y₄]
  exact rawFactoredDet4_pos_of_full_quotient_chain ht₁₂ ht₂₃ ht₃₄
    (hΦpos (t₁ - y₁)) (hΦpos (t₂ - y₁)) (hΦpos (t₃ - y₁)) (hΦpos (t₄ - y₁))
    (fun t => hasDerivAt_firstQuot hΦ hΦpos y₁ y₂ t)
    (fun t => hasDerivAt_firstQuot hΦ hΦpos y₁ y₃ t)
    (fun t => hasDerivAt_firstQuot hΦ hΦpos y₁ y₄ t)
    (fun t => hasDerivAt_secondQuot hΦ hΦ1 hΦpos hfirst y₃ t)
    (fun t => hasDerivAt_secondQuot hΦ hΦ1 hΦpos hfirst y₄ t)
    (fun t => hasDerivAt_terminalQuot hΦ hΦ1 hΦ2 hΦpos hfirst hsecond y₄ t)
    (continuous_firstQuotD hΦc hΦ1c hΦpos y₁ y₂)
    (continuous_firstQuotD hΦc hΦ1c hΦpos y₁ y₃)
    (continuous_firstQuotD hΦc hΦ1c hΦpos y₁ y₄)
    (continuous_secondQuotD hΦc hΦ1c hΦ2c hΦpos hfirst y₃)
    (continuous_secondQuotD hΦc hΦ1c hΦ2c hΦpos hfirst y₄)
    (continuous_terminalQuotD hΦc hΦ1c hΦ2c hΦ3c hΦpos hfirst hsecond y₄)
    (fun t => firstQuotD_factor hfirst y₃ t)
    (fun t => firstQuotD_factor hfirst y₄ t)
    (fun t => secondQuotD_factor hsecond y₄ t)
    hfirst hsecond hterminal

end PF4.TranslationQuotientTower


