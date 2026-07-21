import PF4.KernelAnalytic
import PF4.ClearedJetCertificateBridge
import Mathlib.Analysis.Calculus.TangentCone.Real

set_option linter.style.header false

/-!
# Global kernel jet identification candidate

The origin is handled by uniqueness of the derivative within `Set.Ici 0`.
Both functions already possess ordinary two-sided derivatives there, and their
values agree on the whole right half-line.
-/

namespace PF4.GlobalKernelJetIdentification

open Set

/-- Two ordinary derivatives agree when the underlying functions agree on the
right half-line containing the base point. This includes its endpoint. -/
theorem derivative_eq_of_eqOn_Ici
    {f g : ℝ → ℝ} {f' g' t : ℝ} (ht : 0 ≤ t)
    (hfg : Set.EqOn f g (Set.Ici 0))
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    f' = g' := by
  have hf' : HasDerivWithinAt g f' (Set.Ici 0) t :=
    hf.hasDerivWithinAt.congr_of_mem
      (fun u hu => (hfg hu).symm) ht
  exact (uniqueDiffOn_Ici 0 t ht).eq_deriv g hf' hg.hasDerivWithinAt

/-- The maintained explicit series jets form the required ordinary derivative
tower at every nonnegative input. -/
theorem hasDerivAt_thetaSeriesJet_of_lt_six
    {j : ℕ} (hj : j < 6) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (thetaSeriesJet j) (thetaSeriesJet (j + 1) t) t := by
  rcases IntervalControl.derivativeTowerThroughSix_at_nonneg ht with
    ⟨h0, h1, h2, h3, h4, h5⟩
  interval_cases j <;> assumption

/-- Every maintained positive-series jet through order six is the corresponding
ordinary iterated derivative of the independently defined global kernel. -/
theorem iteratedDeriv_globalRiemannKernel_eq_thetaSeriesJet
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDeriv j globalRiemannKernel t = thetaSeriesJet j t := by
  induction j with
  | zero =>
      simpa [thetaSeriesJet_zero_eq] using
        globalRiemannKernel_eq_thetaSeries_of_nonneg ht
  | succ j ih =>
      have hjlt : j < 6 := Nat.lt_of_succ_le hj
      have hglobal : HasDerivAt (iteratedDeriv j globalRiemannKernel)
          (iteratedDeriv (j + 1) globalRiemannKernel t) t := by
        simpa only [iteratedDeriv_succ] using
          (contDiff_globalRiemannKernel.differentiable_iteratedDeriv j (by simp)) t
            |>.hasDerivAt
      have hseries := hasDerivAt_thetaSeriesJet_of_lt_six hjlt ht
      apply derivative_eq_of_eqOn_Ici ht _ hglobal hseries
      intro u hu
      exact ih (Nat.le_of_succ_le hj) hu

/-! ## Global parity transport -/

/-- Every global kernel derivative has the parity forced by the even kernel. -/
theorem iteratedDeriv_globalRiemannKernel_neg (j : ℕ) (t : ℝ) :
    iteratedDeriv j globalRiemannKernel (-t) =
      (-1 : ℝ) ^ j * iteratedDeriv j globalRiemannKernel t := by
  have hfun : (fun x : ℝ => globalRiemannKernel (-x)) =
      globalRiemannKernel := by
    funext x
    exact globalRiemannKernel_even x
  have h := iteratedDeriv_comp_neg j globalRiemannKernel (-t)
  rw [hfun] at h
  simpa only [neg_neg, smul_eq_mul] using h

/-- Global reflected formula for every kernel jet through order six. -/
theorem iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
    {j : ℕ} (hj : j ≤ 6) (t : ℝ) :
    iteratedDeriv j globalRiemannKernel t =
      (if 0 ≤ t then 1 else (-1 : ℝ) ^ j) * thetaSeriesJet j |t| := by
  by_cases ht : 0 ≤ t
  · rw [if_pos ht, one_mul, abs_of_nonneg ht]
    exact iteratedDeriv_globalRiemannKernel_eq_thetaSeriesJet hj ht
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [if_neg ht, abs_of_nonpos ht']
    rw [← iteratedDeriv_globalRiemannKernel_neg j (-t)]
    exact iteratedDeriv_globalRiemannKernel_eq_thetaSeriesJet hj
      (neg_nonneg.mpr ht')

open PF4.ClearedJetCertificateBridge

/-- The cleared curvature polynomial is invariant under the alternating parity
substitution on a six-jet. -/
theorem clearedQ_alternating_parity (a0 a1 a2 : ℝ) :
    clearedQ a0 (-a1) a2 = clearedQ a0 a1 a2 := by
  unfold clearedQ
  ring

/-- The cleared `F₂` polynomial is invariant under alternating jet parity. -/
theorem clearedF2_alternating_parity (a0 a1 a2 a3 a4 : ℝ) :
    clearedF2 a0 (-a1) a2 (-a3) a4 = clearedF2 a0 a1 a2 a3 a4 := by
  unfold clearedF2
  ring

/-- The cleared raw Hankel determinant is invariant under alternating jet
parity. -/
theorem clearedC4_alternating_parity (a0 a1 a2 a3 a4 a5 a6 : ℝ) :
    clearedC4 a0 (-a1) a2 (-a3) a4 (-a5) a6 =
      clearedC4 a0 a1 a2 a3 a4 a5 a6 := by
  unfold clearedC4
  ring

/-- Common scaling law for the cleared curvature polynomial. -/
theorem clearedQ_common_scale (c a0 a1 a2 : ℝ) :
    clearedQ (c * a0) (c * a1) (c * a2) =
      c ^ 2 * clearedQ a0 a1 a2 := by
  unfold clearedQ
  ring

/-- Common scaling law for the cleared `F₂` polynomial. -/
theorem clearedF2_common_scale (c a0 a1 a2 a3 a4 : ℝ) :
    clearedF2 (c * a0) (c * a1) (c * a2) (c * a3) (c * a4) =
      c ^ 6 * clearedF2 a0 a1 a2 a3 a4 := by
  unfold clearedF2
  ring

/-- Common scaling law for the four-by-four cleared determinant. -/
theorem clearedC4_common_scale (c a0 a1 a2 a3 a4 a5 a6 : ℝ) :
    clearedC4 (c * a0) (c * a1) (c * a2) (c * a3) (c * a4)
        (c * a5) (c * a6) =
      c ^ 4 * clearedC4 a0 a1 a2 a3 a4 a5 a6 := by
  unfold clearedC4
  ring

/-! ## Half-line certificate transport -/

/-- The actual global kernel jet as a function, kept independent of the series
representation. -/
noncomputable def kernelJet (j : ℕ) : ℝ → ℝ :=
  iteratedDeriv j globalRiemannKernel

theorem hasDerivAt_kernelJet (j : ℕ) (t : ℝ) :
    HasDerivAt (kernelJet j) (kernelJet (j + 1) t) t := by
  unfold kernelJet
  simpa only [iteratedDeriv_succ] using
    (contDiff_globalRiemannKernel.differentiable_iteratedDeriv j (by simp)) t
      |>.hasDerivAt

theorem continuous_kernelJet (j : ℕ) : Continuous (kernelJet j) := by
  unfold kernelJet
  exact contDiff_globalRiemannKernel.continuous_iteratedDeriv j (by simp)

/-- Every positive-mode kernel summand is strictly positive on the
nonnegative half-line. -/
theorem thetaMode_pos_of_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 < thetaMode k t := by
  have hn : 1 ≤ modeN k := modeN_one_le k
  have hn2 : 1 ≤ modeN k ^ 2 := by nlinarith [sq_nonneg (modeN k - 1)]
  have he : 1 ≤ Real.exp (2 * t) := (Real.one_le_exp_iff).2 (by linarith)
  have hprod : 3 < Real.pi * modeN k ^ 2 * Real.exp (2 * t) := by
    calc
      3 < Real.pi := Real.pi_gt_three
      _ ≤ Real.pi * modeN k ^ 2 := by
        nlinarith [Real.pi_pos, hn2]
      _ ≤ Real.pi * modeN k ^ 2 * Real.exp (2 * t) := by
        exact le_mul_of_one_le_right
          (mul_nonneg Real.pi_pos.le (sq_nonneg _)) he
  rw [thetaMode]
  rw [show Real.exp ((9 / 2) * t) =
      Real.exp ((5 / 2) * t) * Real.exp (2 * t) by
    rw [← Real.exp_add]
    congr 1
    ring]
  have hfactor :
      4 * Real.pi ^ 2 * modeN k ^ 4 *
          (Real.exp ((5 / 2) * t) * Real.exp (2 * t)) -
          6 * Real.pi * modeN k ^ 2 * Real.exp ((5 / 2) * t) =
        2 * Real.pi * modeN k ^ 2 * Real.exp ((5 / 2) * t) *
          (2 * (Real.pi * modeN k ^ 2 * Real.exp (2 * t)) - 3) := by
    ring
  rw [hfactor]
  positivity

/-- The positive first theta mode used as the exact normalization in CERT12. -/
noncomputable def firstModeScale (t : ℝ) : ℝ := thetaModeJet 0 0 t

theorem firstModeScale_pos {t : ℝ} (ht : 0 ≤ t) : 0 < firstModeScale t := by
  rw [firstModeScale, thetaModeJet_zero_eq_thetaMode]
  exact thetaMode_pos_of_nonneg 0 ht

/-- The series jet in the first-mode normalization used by the exact sign
certificate. -/
noncomputable def normalizedThetaSeriesJet (j : ℕ) (t : ℝ) : ℝ :=
  thetaSeriesJet j t / firstModeScale t

theorem thetaSeriesJet_eq_firstModeScale_mul_normalized
    (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    thetaSeriesJet j t = firstModeScale t * normalizedThetaSeriesJet j t := by
  unfold normalizedThetaSeriesJet
  field_simp [(firstModeScale_pos ht).ne']

/-- Exact reduction of the absolute `clearedQ` sign to CERT12's first-mode
normalized raw jet. -/
theorem clearedQ_thetaSeriesJet_pos_iff_normalized {t : ℝ} (ht : 0 ≤ t) :
    0 < clearedQ (thetaSeriesJet 0 t) (thetaSeriesJet 1 t)
        (thetaSeriesJet 2 t) ↔
      0 < clearedQ (normalizedThetaSeriesJet 0 t)
        (normalizedThetaSeriesJet 1 t) (normalizedThetaSeriesJet 2 t) := by
  rw [thetaSeriesJet_eq_firstModeScale_mul_normalized 0 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 1 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 2 ht,
    clearedQ_common_scale,
    mul_pos_iff_of_pos_left (pow_pos (firstModeScale_pos ht) 2)]

/-- Exact reduction of the absolute `clearedF2` sign to the normalized jet. -/
theorem clearedF2_thetaSeriesJet_pos_iff_normalized {t : ℝ} (ht : 0 ≤ t) :
    0 < clearedF2 (thetaSeriesJet 0 t) (thetaSeriesJet 1 t)
        (thetaSeriesJet 2 t) (thetaSeriesJet 3 t) (thetaSeriesJet 4 t) ↔
      0 < clearedF2 (normalizedThetaSeriesJet 0 t)
        (normalizedThetaSeriesJet 1 t) (normalizedThetaSeriesJet 2 t)
        (normalizedThetaSeriesJet 3 t) (normalizedThetaSeriesJet 4 t) := by
  rw [thetaSeriesJet_eq_firstModeScale_mul_normalized 0 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 1 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 2 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 3 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 4 ht,
    clearedF2_common_scale,
    mul_pos_iff_of_pos_left (pow_pos (firstModeScale_pos ht) 6)]

/-- Exact reduction of the absolute `clearedC4` sign to the normalized jet. -/
theorem clearedC4_thetaSeriesJet_pos_iff_normalized {t : ℝ} (ht : 0 ≤ t) :
    0 < clearedC4 (thetaSeriesJet 0 t) (thetaSeriesJet 1 t)
        (thetaSeriesJet 2 t) (thetaSeriesJet 3 t) (thetaSeriesJet 4 t)
        (thetaSeriesJet 5 t) (thetaSeriesJet 6 t) ↔
      0 < clearedC4 (normalizedThetaSeriesJet 0 t)
        (normalizedThetaSeriesJet 1 t) (normalizedThetaSeriesJet 2 t)
        (normalizedThetaSeriesJet 3 t) (normalizedThetaSeriesJet 4 t)
        (normalizedThetaSeriesJet 5 t) (normalizedThetaSeriesJet 6 t) := by
  rw [thetaSeriesJet_eq_firstModeScale_mul_normalized 0 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 1 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 2 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 3 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 4 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 5 ht,
    thetaSeriesJet_eq_firstModeScale_mul_normalized 6 ht,
    clearedC4_common_scale,
    mul_pos_iff_of_pos_left (pow_pos (firstModeScale_pos ht) 4)]

/-- The positive-mode kernel series is genuinely summable at every
nonnegative input. -/
theorem summable_thetaMode_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k : ℕ => thetaMode k t := by
  let B := t + 1
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) B := by
    dsimp [B]
    constructor <;> linarith
  have hzero : Summable fun k : ℕ => hModeJet 0 k t := by
    rw [funext fun k => hModeJet_zero_eq_hMode k t]
    exact (hasSum_nat_thetaTerms t).summable.mul_left (2 * Real.exp (t / 2))
      |>.congr (fun k => by simp [hMode])
  have htwo : Summable fun k : ℕ => hModeJet 2 k t :=
    (HIntervalControl.summable_intervalMajorant B 1).of_norm_bounded fun k =>
      HIntervalControl.norm_hModeJet_le_intervalMajorant B 1 k htIoo
  exact (htwo.sub (hzero.mul_left (1 / 4 : ℝ))).div_const 2 |>.congr
    (fun k => secondOrder_hMode_eq_thetaMode k t)

/-- Strict positivity of the literal positive-side series. -/
theorem thetaSeries_pos_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 < thetaSeries t := by
  unfold thetaSeries
  exact (summable_thetaMode_of_nonneg ht).tsum_pos
    (fun k => (thetaMode_pos_of_nonneg k ht).le) 0
    (thetaMode_pos_of_nonneg 0 ht)

/-- The independently defined global Riemann kernel is strictly positive. -/
theorem globalRiemannKernel_pos (t : ℝ) : 0 < globalRiemannKernel t := by
  rw [globalRiemannKernel_eq_thetaSeries_abs]
  exact thetaSeries_pos_of_nonneg (abs_nonneg t)

/-- Positivity of the zeroth positive-side series jet transports to the actual
global kernel. -/
theorem kernelJet_zero_pos_of_thetaSeriesJet_zero_pos
    (h0 : ∀ t, 0 ≤ t → 0 < thetaSeriesJet 0 t) :
    ∀ t, 0 < kernelJet 0 t := by
  intro t
  rw [kernelJet,
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 0) (by omega)]
  simpa using h0 |t| (abs_nonneg t)

/-- A nonnegative-axis `clearedQ` certificate transports globally. -/
theorem clearedQ_kernelJet_pos_of_nonneg
    (hQ : ∀ t, 0 ≤ t →
      0 < clearedQ (thetaSeriesJet 0 t) (thetaSeriesJet 1 t)
        (thetaSeriesJet 2 t)) :
    ∀ t, 0 < clearedQ (kernelJet 0 t) (kernelJet 1 t) (kernelJet 2 t) := by
  intro t
  have hs := hQ |t| (abs_nonneg t)
  unfold kernelJet
  rw [iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 0) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 1) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 2) (by omega)]
  by_cases ht : 0 ≤ t
  · simpa [ht] using hs
  · simpa [ht, clearedQ_alternating_parity] using hs

/-- A nonnegative-axis `clearedF2` certificate transports globally. -/
theorem clearedF2_kernelJet_pos_of_nonneg
    (hF2 : ∀ t, 0 ≤ t →
      0 < clearedF2 (thetaSeriesJet 0 t) (thetaSeriesJet 1 t)
        (thetaSeriesJet 2 t) (thetaSeriesJet 3 t) (thetaSeriesJet 4 t)) :
    ∀ t, 0 < clearedF2 (kernelJet 0 t) (kernelJet 1 t) (kernelJet 2 t)
      (kernelJet 3 t) (kernelJet 4 t) := by
  intro t
  have hs := hF2 |t| (abs_nonneg t)
  unfold kernelJet
  rw [iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 0) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 1) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 2) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 3) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 4) (by omega)]
  by_cases ht : 0 ≤ t
  · simpa [ht] using hs
  · simpa [ht, clearedF2_alternating_parity] using hs

/-- A nonnegative-axis `clearedC4` certificate transports globally. -/
theorem clearedC4_kernelJet_pos_of_nonneg
    (hC4 : ∀ t, 0 ≤ t →
      0 < clearedC4 (thetaSeriesJet 0 t) (thetaSeriesJet 1 t)
        (thetaSeriesJet 2 t) (thetaSeriesJet 3 t) (thetaSeriesJet 4 t)
        (thetaSeriesJet 5 t) (thetaSeriesJet 6 t)) :
    ∀ t, 0 < clearedC4 (kernelJet 0 t) (kernelJet 1 t) (kernelJet 2 t)
      (kernelJet 3 t) (kernelJet 4 t) (kernelJet 5 t) (kernelJet 6 t) := by
  intro t
  have hs := hC4 |t| (abs_nonneg t)
  unfold kernelJet
  rw [iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 0) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 1) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 2) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 3) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 4) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 5) (by omega),
    iteratedDeriv_globalRiemannKernel_eq_sign_mul_thetaSeriesJet_abs
      (j := 6) (by omega)]
  by_cases ht : 0 ≤ t
  · simpa [ht] using hs
  · simpa [ht, clearedC4_alternating_parity] using hs

/-- The actual global kernel closes the terminal PF4 quotient cascade from
only the three canonical nonnegative-axis certificate propositions. -/
theorem terminalQuotD_kernelJet_pos_of_nonneg_clearedSigns
    (hQ : ∀ t, 0 ≤ t →
      0 < clearedQ (thetaSeriesJet 0 t) (thetaSeriesJet 1 t)
        (thetaSeriesJet 2 t))
    (hF2 : ∀ t, 0 ≤ t →
      0 < clearedF2 (thetaSeriesJet 0 t) (thetaSeriesJet 1 t)
        (thetaSeriesJet 2 t) (thetaSeriesJet 3 t) (thetaSeriesJet 4 t))
    (hC4 : ∀ t, 0 ≤ t →
      0 < clearedC4 (thetaSeriesJet 0 t) (thetaSeriesJet 1 t)
        (thetaSeriesJet 2 t) (thetaSeriesJet 3 t) (thetaSeriesJet 4 t)
        (thetaSeriesJet 5 t) (thetaSeriesJet 6 t))
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    ∀ t, 0 < PF4.TranslationQuotientTower.terminalQuotD
      (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
      a c b d t := by
  apply terminalQuotD_pos_of_clearedJetSigns
    (hf0 := hasDerivAt_kernelJet 0)
    (hf1 := hasDerivAt_kernelJet 1)
    (hf2 := hasDerivAt_kernelJet 2)
    (hf3 := hasDerivAt_kernelJet 3)
    (hf4 := hasDerivAt_kernelJet 4)
    (hf5 := hasDerivAt_kernelJet 5)
    (hf6cont := continuous_kernelJet 6)
    (hf0pos := fun t => by simpa [kernelJet] using globalRiemannKernel_pos t)
    (hQclear := clearedQ_kernelJet_pos_of_nonneg hQ)
    (hF2clear := clearedF2_kernelJet_pos_of_nonneg hF2)
    (hC4clear := clearedC4_kernelJet_pos_of_nonneg hC4)
    hac hcb hbd

/-- Final handoff in the exact first-mode normalization used internally by
CERT12. No absolute jet sign or global parity premise remains. -/
theorem terminalQuotD_kernelJet_pos_of_nonneg_normalizedClearedSigns
    (hQ : ∀ t, 0 ≤ t →
      0 < clearedQ (normalizedThetaSeriesJet 0 t)
        (normalizedThetaSeriesJet 1 t) (normalizedThetaSeriesJet 2 t))
    (hF2 : ∀ t, 0 ≤ t →
      0 < clearedF2 (normalizedThetaSeriesJet 0 t)
        (normalizedThetaSeriesJet 1 t) (normalizedThetaSeriesJet 2 t)
        (normalizedThetaSeriesJet 3 t) (normalizedThetaSeriesJet 4 t))
    (hC4 : ∀ t, 0 ≤ t →
      0 < clearedC4 (normalizedThetaSeriesJet 0 t)
        (normalizedThetaSeriesJet 1 t) (normalizedThetaSeriesJet 2 t)
        (normalizedThetaSeriesJet 3 t) (normalizedThetaSeriesJet 4 t)
        (normalizedThetaSeriesJet 5 t) (normalizedThetaSeriesJet 6 t))
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    ∀ t, 0 < PF4.TranslationQuotientTower.terminalQuotD
      (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
      a c b d t := by
  apply terminalQuotD_kernelJet_pos_of_nonneg_clearedSigns
    (hQ := fun t ht =>
      (clearedQ_thetaSeriesJet_pos_iff_normalized ht).2 (hQ t ht))
    (hF2 := fun t ht =>
      (clearedF2_thetaSeriesJet_pos_iff_normalized ht).2 (hF2 t ht))
    (hC4 := fun t ht =>
      (clearedC4_thetaSeriesJet_pos_iff_normalized ht).2 (hC4 t ht))
    hac hcb hbd

end PF4.GlobalKernelJetIdentification

#print axioms PF4.GlobalKernelJetIdentification.iteratedDeriv_globalRiemannKernel_eq_thetaSeriesJet
#print axioms PF4.GlobalKernelJetIdentification.globalRiemannKernel_pos
#print axioms PF4.GlobalKernelJetIdentification.terminalQuotD_kernelJet_pos_of_nonneg_normalizedClearedSigns
