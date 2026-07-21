set_option linter.style.header false

namespace PF4.UnscaledOuterClosure

open Set Polynomial
namespace R := PF4.InfiniteTailRefactor
namespace F := PF4.CERT12Inequalities.Generated
namespace P := PF4.CERT12Inequalities.Perturbation.Generated
namespace C := PF4.RobustThreeModeClosure
namespace OP := PF4.CERT12Inequalities.Perturbation
namespace D := PF4.UnscaledOuterClosure.C4Data
namespace K := PF4.GlobalKernelJetIdentification

/-! The elementary absolute envelope is valid already from `s=5`. -/

theorem certPoly_abs_le_outerEnvelope
    {j : ℕ} (hj : j ≤ 6) {s : ℝ} (hs : 5 ≤ s) :
    |(PF4.certPoly j).eval s| ≤ 2 ^ (j + 1) * s ^ (j + 1) := by
  let z := s - 5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hs_eq : s = z + 5 := by dsimp [z]; ring
  rw [hs_eq]
  rw [abs_le]
  interval_cases j <;>
    norm_num [PF4.certPoly, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] <;>
    constructor <;> positivity

theorem abs_twoModeNormalizedJet_le_outer
    {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 5 ≤ x) :
    |F.twoModeNormalizedJet j x (Real.exp (-3 * x))| ≤
      2 ^ (j + 2) * x ^ j := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hden : 0 < 2 * x - 3 := by linarith
  have hypos : 0 < Real.exp (-3 * x) := Real.exp_pos _
  have hy := PF4.CERT12Inequalities.exp_neg_three_mul_lt_inv_3000000 hx
  have hp := certPoly_abs_le_outerEnvelope hj hx
  have hp4 := certPoly_abs_le_outerEnvelope hj
    (show 5 ≤ 4 * x by nlinarith)
  have hfactor : 4 ^ (j + 2) * Real.exp (-3 * x) ≤ (1 : ℝ) := by
    interval_cases j <;> norm_num at hy ⊢ <;> nlinarith
  rw [F.twoModeNormalizedJet, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |(PF4.certPoly j).eval x +
        4 * Real.exp (-3 * x) * (PF4.certPoly j).eval (4 * x)| ≤
        |(PF4.certPoly j).eval x| +
          |4 * Real.exp (-3 * x) * (PF4.certPoly j).eval (4 * x)| :=
      abs_add _ _
    _ = |(PF4.certPoly j).eval x| +
        4 * Real.exp (-3 * x) * |(PF4.certPoly j).eval (4 * x)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_pos hypos]
    _ ≤ 2 ^ (j + 1) * x ^ (j + 1) +
        4 * Real.exp (-3 * x) *
          (2 ^ (j + 1) * (4 * x) ^ (j + 1)) := by gcongr
    _ = (2 ^ (j + 1) * x ^ (j + 1)) *
        (1 + 4 ^ (j + 2) * Real.exp (-3 * x)) := by ring
    _ ≤ (2 ^ (j + 1) * x ^ (j + 1)) * 2 := by
      gcongr
      · positivity
      · linarith
    _ ≤ (2 ^ (j + 2) * x ^ j) * (2 * x - 3) := by
      have hxpow : 0 ≤ x ^ j := pow_nonneg hxpos.le _
      rw [show (2 : ℝ) ^ (j + 1) * x ^ (j + 1) * 2 =
          2 ^ (j + 2) * x ^ j * x by ring]
      gcongr
      · positivity
      · linarith

theorem thirdProfile_le_outerHalf
    {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 5 ≤ x) :
    C.thirdProfile j x ≤
      2 ^ (j + 1) * 3 ^ (2 * j + 4) * x ^ j * Real.exp (-8 * x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hden : 0 < 2 * x - 3 := by linarith
  have hp := certPoly_abs_le_outerEnvelope hj
    (show 5 ≤ 9 * x by nlinarith)
  rw [C.thirdProfile]
  apply (div_le_iff₀ hden).2
  calc
    9 * Real.exp (-8 * x) *
        ((-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x)) ≤
      9 * Real.exp (-8 * x) * |(PF4.certPoly j).eval (9 * x)| := by
        gcongr
        · positivity
        · exact le_abs_self _
    _ ≤ 9 * Real.exp (-8 * x) *
        (2 ^ (j + 1) * (9 * x) ^ (j + 1)) := by gcongr
    _ = (2 ^ (j + 1) * 3 ^ (2 * j + 4) * x ^ j *
        Real.exp (-8 * x)) * x := by ring
    _ ≤ (2 ^ (j + 1) * 3 ^ (2 * j + 4) * x ^ j *
        Real.exp (-8 * x)) * (2 * x - 3) := by
      gcongr
      · positivity
      · linarith

theorem norm_fullModeTail_lt_outer
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t)
    (hx : 5 ≤ R.certX t) :
    ‖R.fullModeTail j t‖ <
      2 ^ (j + 2) * 3 ^ (2 * j + 4) * R.certX t ^ j *
        Real.exp (-8 * R.certX t) := by
  have htail := C.norm_fullModeTail_lt_profile hj ht
  have hprofile := thirdProfile_le_outerHalf hj hx
  let A := 2 ^ (j + 1) * 3 ^ (2 * j + 4) * R.certX t ^ j *
    Real.exp (-8 * R.certX t)
  have hA : 0 < A := by dsimp [A]; positivity
  have hscale : (1001 / 1000 : ℝ) * A < 2 * A := by nlinarith
  calc
    ‖R.fullModeTail j t‖ <
        (1001 / 1000 : ℝ) * C.thirdProfile j (R.certX t) := htail
    _ ≤ (1001 / 1000 : ℝ) * A := by
      dsimp [A]
      gcongr
    _ < 2 * A := hscale
    _ = 2 ^ (j + 2) * 3 ^ (2 * j + 4) * R.certX t ^ j *
        Real.exp (-8 * R.certX t) := by dsimp [A]; ring

theorem strictAntiOn_pow_mul_exp_outer
    {w k : ℕ} (hw : w ≤ 12) (hk : 1 ≤ k) :
    StrictAntiOn
      (fun x : ℝ => x ^ w * Real.exp (-8 * k * x)) (Set.Ici 5) := by
  apply strictAntiOn_of_deriv_neg convex_Ici
  · fun_prop
  · intro x hx
    have hxpos : 0 < x := by linarith
    have hcoef : (w : ℝ) - 8 * k * x < 0 := by
      norm_num at hx ⊢
      have hw' : (w : ℝ) ≤ 12 := by exact_mod_cast hw
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have hd : HasDerivAt
        (fun x : ℝ => x ^ w * Real.exp (-8 * k * x))
        (x ^ (w - 1) * Real.exp (-8 * k * x) *
          ((w : ℝ) - 8 * k * x)) x := by
      convert (hasDerivAt_pow w x).mul
        (Real.hasDerivAt_exp (-8 * k * x) |>.comp x (by fun_prop)) using 1 <;>
        ring
    rw [hd.deriv]
    exact mul_neg_of_pos_of_neg (mul_pos (pow_pos hxpos _) (Real.exp_pos _)) hcoef

theorem pow_mul_exp_outer_le_endpoint
    {w k : ℕ} (hw : w ≤ 12) (hk : 1 ≤ k) {x : ℝ} (hx : 5 ≤ x) :
    x ^ w * Real.exp (-8 * k * x) ≤
      5 ^ w * Real.exp (-8 * k * 5) := by
  by_cases h : x = 5
  · simp [h]
  · exact ((strictAntiOn_pow_mul_exp_outer hw hk)
      (by norm_num) hx (lt_of_le_of_ne hx (Ne.symm h))).le

noncomputable def outerBaseAt (x : ℝ) (j : Fin 7) : ℝ :=
  2 ^ ((j : ℕ) + 2) * x ^ (j : ℕ)

noncomputable def outerErrorAt (x : ℝ) (j : Fin 7) : ℝ :=
  2 ^ ((j : ℕ) + 2) * 3 ^ (2 * (j : ℕ) + 4) * x ^ (j : ℕ) *
    Real.exp (-8 * x)

noncomputable def qOuterBudget (r : ℝ) : ℝ :=
  518400 * r + 68024448 * r ^ 2

noncomputable def f2OuterBudget (r : ℝ) : ℝ :=
  377534545920 * r + 2499346004705280 * r ^ 2 +
  1178221437272457216 * r ^ 3 + 210167384418845982720 * r ^ 4 +
  17166267142238282711040 * r ^ 5 +
  550849713054151526055936 * r ^ 6

noncomputable def c4OuterBudget (r : ℝ) : ℝ :=
  342660376166400 * r + 124115336951985340416 * r ^ 2 +
  1194782854457795700326400 * r ^ 3 +
  305957669193505876186497024 * r ^ 4

theorem q_polynomialErrorBudget_outerAt (x : ℝ) :
    OP.polynomialErrorBudget P.qTerms (outerBaseAt x) (outerErrorAt x) =
      x ^ 2 * qOuterBudget (Real.exp (-8 * x)) := by
  norm_num [OP.polynomialErrorBudget, OP.monomialErrorBudget, P.qTerms,
    outerBaseAt, outerErrorAt, qOuterBudget, Fin.sum_univ_succ,
    Fin.prod_univ_succ]
  ring

theorem f2_polynomialErrorBudget_outerAt (x : ℝ) :
    OP.polynomialErrorBudget P.f2Terms (outerBaseAt x) (outerErrorAt x) =
      x ^ 6 * f2OuterBudget (Real.exp (-8 * x)) := by
  norm_num [OP.polynomialErrorBudget, OP.monomialErrorBudget, P.f2Terms,
    outerBaseAt, outerErrorAt, f2OuterBudget, Fin.sum_univ_succ,
    Fin.prod_univ_succ]
  ring

theorem c4_polynomialErrorBudget_outerAt (x : ℝ) :
    OP.polynomialErrorBudget P.c4Terms (outerBaseAt x) (outerErrorAt x) =
      x ^ 12 * c4OuterBudget (Real.exp (-8 * x)) := by
  norm_num [OP.polynomialErrorBudget, OP.monomialErrorBudget, P.c4Terms,
    outerBaseAt, outerErrorAt, c4OuterBudget, Fin.sum_univ_succ,
    Fin.prod_univ_succ]
  ring

theorem outer_term_le_rational_endpoint
    {w k : ℕ} (hw : w ≤ 12) (hk : 1 ≤ k) {x : ℝ} (hx : 5 ≤ x) :
    x ^ w * Real.exp (-8 * x) ^ k ≤
      5 ^ w * (1 / 200000000000000000 : ℝ) ^ k := by
  have hmono := pow_mul_exp_outer_le_endpoint hw hk hx
  have hexp := C.exp_neg_40_lt_inv_two_e17
  rw [← Real.exp_nat_mul] at ⊢
  rw [show (k : ℝ) * (-8 * x) = -8 * k * x by ring]
  calc
    x ^ w * Real.exp (-8 * k * x) ≤
        5 ^ w * Real.exp (-8 * k * 5) := hmono
    _ = 5 ^ w * Real.exp (-40) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ 5 ^ w * (1 / 200000000000000000 : ℝ) ^ k := by
      gcongr
      · positivity
      · exact hexp.le

theorem q_polynomialErrorBudget_outer_lt {x : ℝ} (hx : 5 ≤ x) :
    OP.polynomialErrorBudget P.qTerms (outerBaseAt x) (outerErrorAt x) < 10 := by
  rw [q_polynomialErrorBudget_outerAt]
  have h1 := outer_term_le_rational_endpoint (w := 2) (k := 1)
    (by norm_num) (by norm_num) hx
  have h2 := outer_term_le_rational_endpoint (w := 2) (k := 2)
    (by norm_num) (by norm_num) hx
  dsimp [qOuterBudget]
  ring_nf at ⊢
  nlinarith

theorem f2_polynomialErrorBudget_outer_lt {x : ℝ} (hx : 5 ≤ x) :
    OP.polynomialErrorBudget P.f2Terms (outerBaseAt x) (outerErrorAt x) < 1000 := by
  rw [f2_polynomialErrorBudget_outerAt]
  have h1 := outer_term_le_rational_endpoint (w := 6) (k := 1)
    (by norm_num) (by norm_num) hx
  have h2 := outer_term_le_rational_endpoint (w := 6) (k := 2)
    (by norm_num) (by norm_num) hx
  have h3 := outer_term_le_rational_endpoint (w := 6) (k := 3)
    (by norm_num) (by norm_num) hx
  have h4 := outer_term_le_rational_endpoint (w := 6) (k := 4)
    (by norm_num) (by norm_num) hx
  have h5 := outer_term_le_rational_endpoint (w := 6) (k := 5)
    (by norm_num) (by norm_num) hx
  have h6 := outer_term_le_rational_endpoint (w := 6) (k := 6)
    (by norm_num) (by norm_num) hx
  dsimp [f2OuterBudget]
  ring_nf at ⊢
  nlinarith

theorem c4_polynomialErrorBudget_outer_lt {x : ℝ} (hx : 5 ≤ x) :
    OP.polynomialErrorBudget P.c4Terms (outerBaseAt x) (outerErrorAt x) < 50000000 := by
  rw [c4_polynomialErrorBudget_outerAt]
  have h1 := outer_term_le_rational_endpoint (w := 12) (k := 1)
    (by norm_num) (by norm_num) hx
  have h2 := outer_term_le_rational_endpoint (w := 12) (k := 2)
    (by norm_num) (by norm_num) hx
  have h3 := outer_term_le_rational_endpoint (w := 12) (k := 3)
    (by norm_num) (by norm_num) hx
  have h4 := outer_term_le_rational_endpoint (w := 12) (k := 4)
    (by norm_num) (by norm_num) hx
  dsimp [c4OuterBudget]
  ring_nf at ⊢
  nlinarith

private noncomputable def baseJet (t : ℝ) (j : Fin 7) : ℝ :=
  F.twoModeNormalizedJet j (R.certX t) (Real.exp (-3 * R.certX t))

private noncomputable def tailJet (t : ℝ) (j : Fin 7) : ℝ :=
  R.fullModeTail j t

theorem abs_baseJet_le_outerBaseAt {t : ℝ} (hx : 5 ≤ R.certX t)
    (j : Fin 7) : |baseJet t j| ≤ outerBaseAt (R.certX t) j := by
  exact abs_twoModeNormalizedJet_le_outer (by omega) hx

theorem abs_tailJet_le_outerErrorAt {t : ℝ} (ht : 0 ≤ t)
    (hx : 5 ≤ R.certX t) (j : Fin 7) :
    |tailJet t j| ≤ outerErrorAt (R.certX t) j := by
  rw [← Real.norm_eq_abs]
  exact (norm_fullModeTail_lt_outer (by omega) ht hx).le

theorem abs_q_literal_perturbation_lt_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ R.certX t) :
    |PF4.ClearedJetCertificateBridge.clearedQ
        (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
        (baseJet t 2 + tailJet t 2) -
      PF4.ClearedJetCertificateBridge.clearedQ
        (baseJet t 0) (baseJet t 1) (baseJet t 2)| < 10 := by
  have h := OP.abs_polynomialValue_add_sub_le P.qTerms (baseJet t) (tailJet t)
    (outerBaseAt (R.certX t)) (outerErrorAt (R.certX t))
    (by intro i; unfold outerBaseAt; positivity)
    (by intro i; unfold outerErrorAt; positivity)
    (abs_baseJet_le_outerBaseAt hx) (abs_tailJet_le_outerErrorAt ht hx)
  rw [P.qTerms_value, P.qTerms_value] at h
  exact h.trans_lt (q_polynomialErrorBudget_outer_lt hx)

theorem abs_f2_literal_perturbation_lt_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ R.certX t) :
    |PF4.ClearedJetCertificateBridge.clearedF2
        (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
        (baseJet t 2 + tailJet t 2) (baseJet t 3 + tailJet t 3)
        (baseJet t 4 + tailJet t 4) -
      PF4.ClearedJetCertificateBridge.clearedF2
        (baseJet t 0) (baseJet t 1) (baseJet t 2)
        (baseJet t 3) (baseJet t 4)| < 1000 := by
  have h := OP.abs_polynomialValue_add_sub_le P.f2Terms (baseJet t) (tailJet t)
    (outerBaseAt (R.certX t)) (outerErrorAt (R.certX t))
    (by intro i; unfold outerBaseAt; positivity)
    (by intro i; unfold outerErrorAt; positivity)
    (abs_baseJet_le_outerBaseAt hx) (abs_tailJet_le_outerErrorAt ht hx)
  rw [P.f2Terms_value, P.f2Terms_value] at h
  exact h.trans_lt (f2_polynomialErrorBudget_outer_lt hx)

theorem abs_c4_literal_perturbation_lt_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ R.certX t) :
    |PF4.ClearedJetCertificateBridge.clearedC4
        (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
        (baseJet t 2 + tailJet t 2) (baseJet t 3 + tailJet t 3)
        (baseJet t 4 + tailJet t 4) (baseJet t 5 + tailJet t 5)
        (baseJet t 6 + tailJet t 6) -
      PF4.ClearedJetCertificateBridge.clearedC4
        (baseJet t 0) (baseJet t 1) (baseJet t 2) (baseJet t 3)
        (baseJet t 4) (baseJet t 5) (baseJet t 6)| < 50000000 := by
  have h := OP.abs_polynomialValue_add_sub_le P.c4Terms (baseJet t) (tailJet t)
    (outerBaseAt (R.certX t)) (outerErrorAt (R.certX t))
    (by intro i; unfold outerBaseAt; positivity)
    (by intro i; unfold outerErrorAt; positivity)
    (abs_baseJet_le_outerBaseAt hx) (abs_tailJet_le_outerErrorAt ht hx)
  rw [P.c4Terms_value, P.c4Terms_value] at h
  exact h.trans_lt (c4_polynomialErrorBudget_outer_lt hx)

/-! Direct decreasing-correction certificate for the cleared q margin. -/

noncomputable def qMarginBase (x : ℝ) : ℝ :=
  16*x^3 - 88*x^2 + 180*x - 90

noncomputable def qMarginNeg (x : ℝ) : ℝ :=
  2304*x^4 - 5600*x^3 + 5424*x^2 - 1200*x

noncomputable def qMarginPos (x : ℝ) : ℝ :=
  16384*x^3 - 12288*x^2 + 3840*x

noncomputable def qMarginDecay (x : ℝ) : ℝ :=
  3*qMarginNeg x*qMarginBase x -
    (9216*x^3 - 16800*x^2 + 10848*x - 1200)*qMarginBase x +
    qMarginNeg x*(48*x^2 - 176*x + 180)

noncomputable def qMarginRatio (x : ℝ) : ℝ :=
  qMarginNeg x * Real.exp (-3*x) / qMarginBase x

theorem qMarginCorePolynomial_decomposition (x y : ℝ) :
    F.qMarginCorePolynomial x y =
      qMarginBase x - qMarginNeg x*y + qMarginPos x*y^2 := by
  simp [F.qMarginCorePolynomial, qMarginBase, qMarginNeg, qMarginPos]
  ring

theorem qMarginBase_pos {x : ℝ} (hx : 5 ≤ x) : 0 < qMarginBase x := by
  let z := x-5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [qMarginBase]
  positivity

theorem qMarginNeg_pos {x : ℝ} (hx : 5 ≤ x) : 0 < qMarginNeg x := by
  let z := x-5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [qMarginNeg]
  positivity

theorem qMarginPos_nonneg {x : ℝ} (hx : 5 ≤ x) : 0 ≤ qMarginPos x := by
  let z := x-5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [qMarginPos]
  positivity

theorem qMarginDecay_pos {x : ℝ} (hx : 5 ≤ x) : 0 < qMarginDecay x := by
  let z := x-5
  have hz : 0 ≤ z := by dsimp [z]; linarith
  rw [show x=z+5 by dsimp [z]; ring]
  norm_num [qMarginDecay, qMarginBase, qMarginNeg]
  positivity

theorem hasDerivAt_qMarginRatio {x : ℝ} (hx : 5 ≤ x) :
    HasDerivAt qMarginRatio
      (-Real.exp (-3*x)*qMarginDecay x/(qMarginBase x)^2) x := by
  have hb := (qMarginBase_pos hx).ne'
  unfold qMarginRatio qMarginDecay qMarginBase qMarginNeg
  fun_prop (disch := aesop)
  field_simp [hb]
  ring

theorem strictAntiOn_qMarginRatio :
    StrictAntiOn qMarginRatio (Set.Ici 5) := by
  apply strictAntiOn_of_deriv_neg convex_Ici
  · fun_prop (disch := aesop)
  · intro x hx
    have hd := hasDerivAt_qMarginRatio hx.le
    rw [hd.deriv]
    have hdecay := qMarginDecay_pos hx.le
    have hb := qMarginBase_pos hx.le
    have hsq : 0 < qMarginBase x ^ 2 := sq_pos_of_pos hb
    positivity

theorem qMarginRatio_lt_one {x : ℝ} (hx : 5 ≤ x) :
    qMarginRatio x < 1 := by
  have hend : qMarginRatio 5 < 1 := by
    have he := PF4.CERT12Inequalities.exp_neg_three_mul_lt_inv_3000000
      (show (5 : ℝ) ≤ 5 by norm_num)
    norm_num [qMarginRatio, qMarginNeg, qMarginBase] at he ⊢
    nlinarith
  by_cases h : x=5
  · simpa [h] using hend
  · exact ((strictAntiOn_qMarginRatio (by norm_num) hx
      (lt_of_le_of_ne hx (Ne.symm h))).trans hend.le)

theorem qTwoModeMarginNumerator_pos_outer {x : ℝ} (hx : 5 ≤ x) :
    0 < F.qMarginCorePolynomial x (Real.exp (-3*x)) := by
  rw [qMarginCorePolynomial_decomposition]
  have hb := qMarginBase_pos hx
  have hm := qMarginNeg_pos hx
  have hp := qMarginPos_nonneg hx
  have he := Real.exp_pos (-3*x)
  have hr := qMarginRatio_lt_one hx
  have hmb : qMarginNeg x * Real.exp (-3*x) < qMarginBase x := by
    rw [qMarginRatio, div_lt_one hb] at hr
    exact hr
  nlinarith [mul_nonneg hp (sq_nonneg (Real.exp (-3*x)))]

theorem clearedQ_twoMode_gt_ten_outer {x : ℝ} (hx : 5 ≤ x) :
    10 < PF4.ClearedJetCertificateBridge.clearedQ
      (F.twoModeNormalizedJet 0 x (Real.exp (-3*x)))
      (F.twoModeNormalizedJet 1 x (Real.exp (-3*x)))
      (F.twoModeNormalizedJet 2 x (Real.exp (-3*x))) := by
  have hx0 : (157/50 : ℝ) ≤ x := by linarith
  rw [← sub_pos, F.clearedQ_twoMode_sub_ten _ _
    (F.two_mul_sub_three_pos hx0).ne']
  exact div_pos (qTwoModeMarginNumerator_pos_outer hx)
    (pow_pos (F.two_mul_sub_three_pos hx0) 2)

/-! Direct decreasing-correction certificate for the cleared C4 margin. -/

noncomputable def c4MarginRatio1 (x : ℝ) : ℝ :=
  D.c4MarginNeg1 x * Real.exp (-3*x) / D.c4MarginBase x

noncomputable def c4MarginRatio3 (x : ℝ) : ℝ :=
  D.c4MarginNeg3 x * Real.exp (-9*x) / D.c4MarginBase x

theorem hasDerivAt_c4MarginRatio1 {x : ℝ} (hx : 5 ≤ x) :
    HasDerivAt c4MarginRatio1
      (-Real.exp (-3*x)*D.c4MarginDecay1 x/(D.c4MarginBase x)^2) x := by
  have hb := (D.c4MarginBase_pos hx).ne'
  unfold c4MarginRatio1 D.c4MarginDecay1 D.c4MarginBase D.c4MarginNeg1
  fun_prop (disch := aesop)
  field_simp [hb]
  ring

theorem hasDerivAt_c4MarginRatio3 {x : ℝ} (hx : 5 ≤ x) :
    HasDerivAt c4MarginRatio3
      (-Real.exp (-9*x)*D.c4MarginDecay3 x/(D.c4MarginBase x)^2) x := by
  have hb := (D.c4MarginBase_pos hx).ne'
  unfold c4MarginRatio3 D.c4MarginDecay3 D.c4MarginBase D.c4MarginNeg3
  fun_prop (disch := aesop)
  field_simp [hb]
  ring

theorem strictAntiOn_c4MarginRatio1 :
    StrictAntiOn c4MarginRatio1 (Set.Ici 5) := by
  apply strictAntiOn_of_deriv_neg convex_Ici
  · fun_prop (disch := aesop)
  · intro x hx
    have hd := hasDerivAt_c4MarginRatio1 hx.le
    rw [hd.deriv]
    have hdecay := D.c4MarginDecay1_pos hx.le
    have hb := D.c4MarginBase_pos hx.le
    have hsq : 0 < D.c4MarginBase x ^ 2 := sq_pos_of_pos hb
    positivity

theorem strictAntiOn_c4MarginRatio3 :
    StrictAntiOn c4MarginRatio3 (Set.Ici 5) := by
  apply strictAntiOn_of_deriv_neg convex_Ici
  · fun_prop (disch := aesop)
  · intro x hx
    have hd := hasDerivAt_c4MarginRatio3 hx.le
    rw [hd.deriv]
    have hdecay := D.c4MarginDecay3_pos hx.le
    have hb := D.c4MarginBase_pos hx.le
    have hsq : 0 < D.c4MarginBase x ^ 2 := sq_pos_of_pos hb
    positivity

theorem c4MarginRatio_sum_lt_one {x : ℝ} (hx : 5 ≤ x) :
    c4MarginRatio1 x + c4MarginRatio3 x < 1 := by
  have he15 := PF4.CERT12Inequalities.exp_neg_three_mul_lt_inv_3000000
    (show (5 : ℝ) ≤ 5 by norm_num)
  have he45 : Real.exp (-45) < (1/3000000 : ℝ)^3 := by
    rw [show (-45 : ℝ)=3*(-15) by ring, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ (Real.exp_pos _).le he15 (by omega)
  have h1end : c4MarginRatio1 5 <
      D.c4MarginNeg1 5*(1/3000000 : ℝ)/D.c4MarginBase 5 := by
    norm_num [c4MarginRatio1, D.c4MarginNeg1, D.c4MarginBase] at he15 ⊢
    nlinarith
  have h3end : c4MarginRatio3 5 <
      D.c4MarginNeg3 5*(1/3000000 : ℝ)^3/D.c4MarginBase 5 := by
    norm_num [c4MarginRatio3, D.c4MarginNeg3, D.c4MarginBase] at he45 ⊢
    nlinarith
  have hend : c4MarginRatio1 5 + c4MarginRatio3 5 < 1 := by
    have hexact : D.c4MarginNeg1 5*(1/3000000 : ℝ)/D.c4MarginBase 5 +
        D.c4MarginNeg3 5*(1/3000000 : ℝ)^3/D.c4MarginBase 5 < 1 := by
      norm_num [D.c4MarginNeg1, D.c4MarginNeg3, D.c4MarginBase]
    linarith
  have h1 : c4MarginRatio1 x ≤ c4MarginRatio1 5 := by
    by_cases h : x=5
    · simp [h]
    · exact (strictAntiOn_c4MarginRatio1 (by norm_num) hx
        (lt_of_le_of_ne hx (Ne.symm h))).le
  have h3 : c4MarginRatio3 x ≤ c4MarginRatio3 5 := by
    by_cases h : x=5
    · simp [h]
    · exact (strictAntiOn_c4MarginRatio3 (by norm_num) hx
        (lt_of_le_of_ne hx (Ne.symm h))).le
  linarith

theorem c4TwoModeMarginNumerator_pos_outer {x : ℝ} (hx : 5 ≤ x) :
    0 < F.c4MarginCorePolynomial x (Real.exp (-3*x)) := by
  rw [D.decomposition]
  have hb := D.c4MarginBase_pos hx
  have hp2 := D.c4MarginPos2_pos hx
  have hp4 := D.c4MarginPos4_pos hx
  have he := Real.exp_pos (-3*x)
  have hr := c4MarginRatio_sum_lt_one hx
  have hexp3 : Real.exp (-3*x)^3 = Real.exp (-9*x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hneg : D.c4MarginNeg1 x*Real.exp (-3*x) +
      D.c4MarginNeg3 x*Real.exp (-3*x)^3 < D.c4MarginBase x := by
    rw [hexp3]
    rw [c4MarginRatio1, c4MarginRatio3, ← add_div, div_lt_one hb] at hr
    exact hr
  nlinarith [mul_nonneg hp2 (sq_nonneg (Real.exp (-3*x))),
    mul_nonneg hp4 (pow_nonneg he.le 4)]

theorem clearedC4_twoMode_gt_margin_outer {x : ℝ} (hx : 5 ≤ x) :
    50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (F.twoModeNormalizedJet 0 x (Real.exp (-3*x)))
      (F.twoModeNormalizedJet 1 x (Real.exp (-3*x)))
      (F.twoModeNormalizedJet 2 x (Real.exp (-3*x)))
      (F.twoModeNormalizedJet 3 x (Real.exp (-3*x)))
      (F.twoModeNormalizedJet 4 x (Real.exp (-3*x)))
      (F.twoModeNormalizedJet 5 x (Real.exp (-3*x)))
      (F.twoModeNormalizedJet 6 x (Real.exp (-3*x))) := by
  have hx0 : (157/50 : ℝ) ≤ x := by linarith
  rw [← sub_pos, F.clearedC4_twoMode_sub_margin _ _
    (F.two_mul_sub_three_pos hx0).ne']
  exact div_pos (c4TwoModeMarginNumerator_pos_outer hx)
    (pow_pos (F.two_mul_sub_three_pos hx0) 4)

/-! ## Literal outer and universal half-line closure -/

theorem normalizedSeriesJet_eq_base_add_tail
    (j : Fin 7) {t : ℝ} (ht : 0 ≤ t) :
    R.normalizedSeriesJet j t = baseJet t j + tailJet t j := by
  exact C.normalizedSeriesJet_eq_twoMode_add_fullTail (by omega) ht

theorem normalized_clearedQ_pos_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ R.certX t) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) := by
  have hbase := clearedQ_twoMode_gt_ten_outer hx
  have hpert := abs_q_literal_perturbation_lt_outer ht hx
  rw [abs_lt] at hpert
  have hpos : 0 < PF4.ClearedJetCertificateBridge.clearedQ
      (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
      (baseJet t 2 + tailJet t 2) := by linarith
  simpa only [← normalizedSeriesJet_eq_base_add_tail (t:=t) ht] using hpos

theorem normalized_clearedF2_pos_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ R.certX t) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) (R.normalizedSeriesJet 3 t)
      (R.normalizedSeriesJet 4 t) := by
  have hx0 : (157/50 : ℝ) ≤ R.certX t := by linarith
  have hbase := F.clearedF2_twoMode_gt_thousand hx0
  have hpert := abs_f2_literal_perturbation_lt_outer ht hx
  rw [abs_lt] at hpert
  have hpos : 0 < PF4.ClearedJetCertificateBridge.clearedF2
      (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
      (baseJet t 2 + tailJet t 2) (baseJet t 3 + tailJet t 3)
      (baseJet t 4 + tailJet t 4) := by linarith
  simpa only [← normalizedSeriesJet_eq_base_add_tail (t:=t) ht] using hpos

theorem normalized_clearedC4_pos_outer
    {t : ℝ} (ht : 0 ≤ t) (hx : 5 ≤ R.certX t) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) (R.normalizedSeriesJet 3 t)
      (R.normalizedSeriesJet 4 t) (R.normalizedSeriesJet 5 t)
      (R.normalizedSeriesJet 6 t) := by
  have hbase := clearedC4_twoMode_gt_margin_outer hx
  have hpert := abs_c4_literal_perturbation_lt_outer ht hx
  rw [abs_lt] at hpert
  have hpos : 0 < PF4.ClearedJetCertificateBridge.clearedC4
      (baseJet t 0 + tailJet t 0) (baseJet t 1 + tailJet t 1)
      (baseJet t 2 + tailJet t 2) (baseJet t 3 + tailJet t 3)
      (baseJet t 4 + tailJet t 4) (baseJet t 5 + tailJet t 5)
      (baseJet t 6 + tailJet t 6) := by linarith
  simpa only [← normalizedSeriesJet_eq_base_add_tail (t:=t) ht] using hpos

theorem normalized_clearedQ_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) := by
  by_cases hx : R.certX t ≤ 5
  · exact C.normalized_clearedQ_pos_of_certX_le_five ht hx
  · exact normalized_clearedQ_pos_outer ht (le_of_not_ge hx)

theorem normalized_clearedF2_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) (R.normalizedSeriesJet 3 t)
      (R.normalizedSeriesJet 4 t) := by
  by_cases hx : R.certX t ≤ 5
  · exact C.normalized_clearedF2_pos_of_certX_le_five ht hx
  · exact normalized_clearedF2_pos_outer ht (le_of_not_ge hx)

theorem normalized_clearedC4_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) (R.normalizedSeriesJet 3 t)
      (R.normalizedSeriesJet 4 t) (R.normalizedSeriesJet 5 t)
      (R.normalizedSeriesJet 6 t) := by
  by_cases hx : R.certX t ≤ 5
  · exact C.normalized_clearedC4_pos_of_certX_le_five ht hx
  · exact normalized_clearedC4_pos_outer ht (le_of_not_ge hx)

theorem normalized_cleared_signs_pos {t : ℝ} (ht : 0 ≤ t) :
    (0 < PF4.ClearedJetCertificateBridge.clearedQ
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t)) ∧
    (0 < PF4.ClearedJetCertificateBridge.clearedF2
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) (R.normalizedSeriesJet 3 t)
      (R.normalizedSeriesJet 4 t)) ∧
    (0 < PF4.ClearedJetCertificateBridge.clearedC4
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) (R.normalizedSeriesJet 3 t)
      (R.normalizedSeriesJet 4 t) (R.normalizedSeriesJet 5 t)
      (R.normalizedSeriesJet 6 t)) :=
  ⟨normalized_clearedQ_pos ht, normalized_clearedF2_pos ht,
    normalized_clearedC4_pos ht⟩

theorem normalizedSeriesJet_eq_globalNormalized (j : ℕ) (t : ℝ) :
    R.normalizedSeriesJet j t = K.normalizedThetaSeriesJet j t := by
  rfl

theorem terminalQuotD_global_kernel_pos
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    ∀ t, 0 < PF4.TranslationQuotientTower.terminalQuotD
      (K.kernelJet 0) (K.kernelJet 1) (K.kernelJet 2) (K.kernelJet 3)
      a c b d t := by
  apply K.terminalQuotD_kernelJet_pos_of_nonneg_normalizedClearedSigns
    (hQ := fun t ht => by
      simpa only [← normalizedSeriesJet_eq_globalNormalized] using
        normalized_clearedQ_pos ht)
    (hF2 := fun t ht => by
      simpa only [← normalizedSeriesJet_eq_globalNormalized] using
        normalized_clearedF2_pos ht)
    (hC4 := fun t ht => by
      simpa only [← normalizedSeriesJet_eq_globalNormalized] using
        normalized_clearedC4_pos ht)
    hac hcb hbd

end PF4.UnscaledOuterClosure

#print axioms PF4.UnscaledOuterClosure.normalized_cleared_signs_pos
#print axioms PF4.UnscaledOuterClosure.terminalQuotD_global_kernel_pos
