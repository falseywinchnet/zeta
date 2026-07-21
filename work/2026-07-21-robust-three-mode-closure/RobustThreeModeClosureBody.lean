set_option linter.style.header false

namespace PF4.RobustThreeModeClosure

open Set Polynomial

namespace R := PF4.InfiniteTailRefactor
namespace F := PF4.CERT12Inequalities.Generated
namespace P := PF4.CERT12Inequalities.Perturbation.Generated
namespace G := PF4.RobustThreeModeClosure.Generated

/-! Exact exponential bounds used by the continuum C4 bands. -/

theorem exp_21_div_2_gt_36000 : (36000 : ℝ) < Real.exp (21 / 2) := by
  have hsum : (36000 : ℝ) <
      ∑ i ∈ Finset.range 32, (21 / 2 : ℝ) ^ i / i ! := by
    norm_num [Finset.sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 32)

theorem exp_12_gt_160000 : (160000 : ℝ) < Real.exp 12 := by
  have hsum : (160000 : ℝ) <
      ∑ i ∈ Finset.range 35, (12 : ℝ) ^ i / i ! := by
    norm_num [Finset.sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 35)

theorem exp_27_div_2_gt_700000 : (700000 : ℝ) < Real.exp (27 / 2) := by
  have hsum : (700000 : ℝ) <
      ∑ i ∈ Finset.range 38, (27 / 2 : ℝ) ^ i / i ! := by
    norm_num [Finset.sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 38)

theorem exp_neg_three_mul_lt_inv_of_exp_bound
    {x a N : ℝ} (hax : a ≤ 3 * x) (hN : N < Real.exp a) (hN0 : 0 < N) :
    Real.exp (-3 * x) < 1 / N := by
  have h := hN.trans_le (Real.exp_monotone hax)
  have hi := one_div_lt_one_div_of_lt hN0 h
  simpa [one_div, ← Real.exp_neg] using hi

theorem c4TwoModeMarginNumerator_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < F.c4MarginCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hA : x ≤ 10 / 3
  · exact F.c4MarginCore_box_pos hx0 hA (Real.exp_pos _).le
      (PF4.CERT12Inequalities.exp_neg_three_mul_lt_inv_12000 hx0).le
  have h10 : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hA).le
  by_cases hB : x ≤ 7 / 2
  · exact G.c4BandA_box_pos h10 hB (Real.exp_pos _).le
      (PF4.CERT12Inequalities.exp_neg_three_mul_lt_inv_22000 h10).le
  have h7 : (7 / 2 : ℝ) ≤ x := (lt_of_not_ge hB).le
  by_cases hC : x ≤ 4
  · exact G.c4BandB_box_pos h7 hC (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_of_exp_bound (by linarith)
        exp_21_div_2_gt_36000 (by norm_num)).le
  have h4 : (4 : ℝ) ≤ x := (lt_of_not_ge hC).le
  by_cases hD : x ≤ 9 / 2
  · exact G.c4BandC_box_pos h4 hD (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_of_exp_bound (by linarith)
        exp_12_gt_160000 (by norm_num)).le
  have h9 : (9 / 2 : ℝ) ≤ x := (lt_of_not_ge hD).le
  exact G.c4BandD_box_pos h9 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_of_exp_bound (by linarith)
      exp_27_div_2_gt_700000 (by norm_num)).le

theorem clearedC4_twoMode_gt_margin_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (F.twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (F.twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (F.twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (F.twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (F.twoModeNormalizedJet 4 x (Real.exp (-3 * x)))
      (F.twoModeNormalizedJet 5 x (Real.exp (-3 * x)))
      (F.twoModeNormalizedJet 6 x (Real.exp (-3 * x))) := by
  rw [← sub_pos, F.clearedC4_twoMode_sub_margin _ _
    (F.two_mul_sub_three_pos hx0).ne']
  exact div_pos (c4TwoModeMarginNumerator_pos_to_five hx0 hx5)
    (pow_pos (F.two_mul_sub_three_pos hx0) 4)

/-- Absolute value of the exact normalized `n=3` coordinate, written as a
positive signed polynomial on `x>=3`. -/
noncomputable def thirdProfile (j : ℕ) (x : ℝ) : ℝ :=
  9 * Real.exp (-8 * x) *
      ((-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x)) /
    (2 * x - 3)

/-- Positive numerator of `-thirdProfile'`. -/
noncomputable def thirdDecay (j : ℕ) (x : ℝ) : ℝ :=
  (8 * (2 * x - 3) + 2) *
      ((-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x)) -
    9 * (2 * x - 3) *
      ((-1 : ℝ) ^ j * (PF4.certPoly j).derivative.eval (9 * x))

theorem thirdDecay_pos {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 3 ≤ x) :
    0 < thirdDecay j x := by
  let z := x - 3
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hx_eq : x = z + 3 := by dsimp [z]; ring
  rw [hx_eq]
  interval_cases j <;>
    norm_num [thirdDecay, PF4.certPoly, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul] <;>
    positivity

theorem hasDerivAt_thirdProfile (j : ℕ) {x : ℝ} (hx : 3 < x) :
    HasDerivAt (thirdProfile j)
      (-9 * Real.exp (-8 * x) * thirdDecay j x / (2 * x - 3) ^ 2) x := by
  have hden : 2 * x - 3 ≠ 0 := by linarith
  unfold thirdProfile thirdDecay
  fun_prop (disch := aesop)
  field_simp [hden]
  ring

theorem strictAntiOn_thirdProfile (j : ℕ) (hj : j ≤ 6) :
    StrictAntiOn (thirdProfile j) (Set.Ici 3) := by
  apply strictAntiOn_of_deriv_neg convex_Ici
  · fun_prop
  · intro x hx
    have hx3 : 3 < x := hx
    have hd := hasDerivAt_thirdProfile j hx3
    rw [hd.deriv]
    have hdecay := thirdDecay_pos hj hx.le
    have hden : 0 < (2 * x - 3) ^ 2 := sq_pos_of_pos (by linarith)
    positivity

theorem norm_thirdModeJet_eq_signed
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ‖R.thirdModeJet j t‖ = (-1 : ℝ) ^ j * R.thirdModeJet j t := by
  have hp := R.normalizedModeJet_alternating_pos hj (k := 2) (by omega) ht
  rw [Real.norm_eq_abs]
  interval_cases j <;> norm_num at hp ⊢
  · rw [abs_of_pos hp]
  · rw [abs_of_neg (by linarith)]
  · rw [abs_of_pos hp]
  · rw [abs_of_neg (by linarith)]
  · rw [abs_of_pos hp]
  · rw [abs_of_neg (by linarith)]
  · rw [abs_of_pos hp]

theorem norm_thirdModeJet_eq_profile
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ‖R.thirdModeJet j t‖ = thirdProfile j (R.certX t) := by
  rw [norm_thirdModeJet_eq_signed hj ht]
  unfold R.thirdModeJet
  rw [R.normalizedModeJet_eq j 2 ht]
  simp only [PF4.modeN, Nat.cast_ofNat, reducePow, Nat.cast_one]
  unfold thirdProfile
  rw [show -(9 - 1) * R.certX t = -8 * R.certX t by ring]
  ring

theorem thirdProfile_le_at_three
    {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 3 ≤ x) :
    thirdProfile j x ≤ thirdProfile j 3 := by
  by_cases h : x = 3
  · simp [h]
  · exact (strictAntiOn_thirdProfile j hj).le_iff_le.mp
      (by simpa only using lt_of_le_of_ne hx (Ne.symm h))

theorem exp_neg_24_lt_inv_25000000000 :
    Real.exp (-24) < (1 / 25000000000 : ℝ) := by
  have hsum : (25000000000 : ℝ) <
      ∑ i ∈ Finset.range 60, (24 : ℝ) ^ i / i ! := by
    norm_num [Finset.sum_range_succ]
  have he : (25000000000 : ℝ) < Real.exp 24 :=
    hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 60)
  have hinv := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 25000000000) he
  simpa [one_div, ← Real.exp_neg] using hinv

theorem thirdProfile_core_bound (j : Fin 7) :
    (1001 / 1000 : ℝ) * thirdProfile j 3 < P.coreE j := by
  have he := exp_neg_24_lt_inv_25000000000
  fin_cases j <;>
    norm_num [thirdProfile, PF4.certPoly, P.coreE,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul] at he ⊢ <;>
    nlinarith

theorem norm_fullModeTail_lt_coreE
    (j : Fin 7) {t : ℝ} (ht : 0 ≤ t) :
    ‖R.fullModeTail j t‖ < P.coreE j := by
  have hj : (j : ℕ) ≤ 6 := by omega
  have hsplit := R.fullModeTail_eq_third_add_later
    (R.summable_fullModeTail_of_nonneg hj ht)
  have hrelative := R.laterModeTail_lt_one_thousandth_closed hj ht
  have hx := R.certX_ge_three ht
  have hthird := norm_thirdModeJet_eq_profile hj ht
  have hmono := thirdProfile_le_at_three hj hx
  calc
    ‖R.fullModeTail j t‖ =
        ‖R.thirdModeJet j t + R.laterModeTail j t‖ := by rw [hsplit]
    _ ≤ ‖R.thirdModeJet j t‖ + ‖R.laterModeTail j t‖ := norm_add_le _ _
    _ < ‖R.thirdModeJet j t‖ +
        (1 / 1000 : ℝ) * ‖R.thirdModeJet j t‖ := by gcongr
    _ = (1001 / 1000 : ℝ) * thirdProfile j (R.certX t) := by
      rw [hthird]
      ring
    _ ≤ (1001 / 1000 : ℝ) * thirdProfile j 3 := by gcongr
    _ < P.coreE j := thirdProfile_core_bound j

theorem norm_fullModeTail_lt_profile
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ‖R.fullModeTail j t‖ <
      (1001 / 1000 : ℝ) * thirdProfile j (R.certX t) := by
  have hsplit := R.fullModeTail_eq_third_add_later
    (R.summable_fullModeTail_of_nonneg hj ht)
  have hrelative := R.laterModeTail_lt_one_thousandth_closed hj ht
  have hthird := norm_thirdModeJet_eq_profile hj ht
  calc
    ‖R.fullModeTail j t‖ =
        ‖R.thirdModeJet j t + R.laterModeTail j t‖ := by rw [hsplit]
    _ ≤ ‖R.thirdModeJet j t‖ + ‖R.laterModeTail j t‖ := norm_add_le _ _
    _ < ‖R.thirdModeJet j t‖ +
        (1 / 1000 : ℝ) * ‖R.thirdModeJet j t‖ := by gcongr
    _ = (1001 / 1000 : ℝ) * thirdProfile j (R.certX t) := by
      rw [hthird]
      ring

/-! ## Literal series decomposition -/

theorem firstTwoModeJets_eq_twoModeNormalizedJet
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    R.normalizedModeJet j 0 t + R.normalizedModeJet j 1 t =
      F.twoModeNormalizedJet j (R.certX t) (Real.exp (-3 * R.certX t)) := by
  rw [R.normalizedModeJet_eq j 0 ht, R.normalizedModeJet_eq j 1 ht]
  simp only [PF4.modeN, Nat.cast_one, Nat.cast_ofNat, one_pow, reducePow,
    one_mul, sub_self, neg_zero, Real.exp_zero]
  unfold F.twoModeNormalizedJet
  ring

theorem normalizedSeriesJet_eq_twoMode_add_fullTail
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    R.normalizedSeriesJet j t =
      F.twoModeNormalizedJet j (R.certX t) (Real.exp (-3 * R.certX t)) +
        R.fullModeTail j t := by
  rw [R.normalizedSeriesJet_eq_tsum_normalizedModeJet]
  have hs := R.summable_normalizedModeJet_of_nonneg hj ht
  rw [← hs.sum_add_tsum_nat_add 2]
  rw [show ∑ x ∈ Finset.range 2, R.normalizedModeJet j x t =
      R.normalizedModeJet j 0 t + R.normalizedModeJet j 1 t by
    simp [Finset.sum_range_succ]]
  rw [firstTwoModeJets_eq_twoModeNormalizedJet hj ht]
  rfl

private noncomputable def baseJet (t : ℝ) (j : Fin 7) : ℝ :=
  F.twoModeNormalizedJet j (R.certX t) (Real.exp (-3 * R.certX t))

private noncomputable def tailJet (t : ℝ) (j : Fin 7) : ℝ :=
  R.fullModeTail j t

theorem normalizedSeriesJet_eq_baseJet_add_tailJet
    (j : Fin 7) {t : ℝ} (ht : 0 ≤ t) :
    R.normalizedSeriesJet j t = baseJet t j + tailJet t j := by
  exact normalizedSeriesJet_eq_twoMode_add_fullTail (by omega) ht

theorem abs_baseJet_le_coreB {t : ℝ} (ht : 0 ≤ t)
    (hx5 : R.certX t ≤ 5) (j : Fin 7) :
    |baseJet t j| ≤ P.coreB j := by
  have hx0 : (157 / 50 : ℝ) ≤ R.certX t := by
    have := R.certX_ge_three ht
    linarith
  fin_cases j
  · simpa [baseJet, P.coreB] using F.abs_twoModeNormalizedJet_0_le_coreBase hx0 hx5
  · simpa [baseJet, P.coreB] using F.abs_twoModeNormalizedJet_1_le_coreBase hx0 hx5
  · simpa [baseJet, P.coreB] using F.abs_twoModeNormalizedJet_2_le_coreBase hx0 hx5
  · simpa [baseJet, P.coreB] using F.abs_twoModeNormalizedJet_3_le_coreBase hx0 hx5
  · simpa [baseJet, P.coreB] using F.abs_twoModeNormalizedJet_4_le_coreBase hx0 hx5
  · simpa [baseJet, P.coreB] using F.abs_twoModeNormalizedJet_5_le_coreBase hx0 hx5
  · simpa [baseJet, P.coreB] using F.abs_twoModeNormalizedJet_6_le_coreBase hx0 hx5

theorem abs_tailJet_le_coreE {t : ℝ} (ht : 0 ≤ t) (j : Fin 7) :
    |tailJet t j| ≤ P.coreE j := by
  rw [← Real.norm_eq_abs]
  exact (norm_fullModeTail_lt_coreE j ht).le

/-! ## Fully connected compact closure -/

theorem normalized_clearedQ_pos_of_certX_le_five
    {t : ℝ} (ht : 0 ≤ t) (hx5 : R.certX t ≤ 5) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) := by
  have hx0 : (157 / 50 : ℝ) ≤ R.certX t := by
    have := R.certX_ge_three ht
    linarith
  have h := P.clearedQ_pos_of_base_margin_and_core_error
    (baseJet t) (tailJet t) (abs_baseJet_le_coreB ht hx5)
    (abs_tailJet_le_coreE ht)
    (F.clearedQ_twoMode_gt_ten_to_five hx0 hx5)
  simpa only [← normalizedSeriesJet_eq_baseJet_add_tailJet (t := t) ht] using h

theorem normalized_clearedF2_pos_of_certX_le_five
    {t : ℝ} (ht : 0 ≤ t) (hx5 : R.certX t ≤ 5) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) (R.normalizedSeriesJet 3 t)
      (R.normalizedSeriesJet 4 t) := by
  have hx0 : (157 / 50 : ℝ) ≤ R.certX t := by
    have := R.certX_ge_three ht
    linarith
  have h := P.clearedF2_pos_of_base_margin_and_core_error
    (baseJet t) (tailJet t) (abs_baseJet_le_coreB ht hx5)
    (abs_tailJet_le_coreE ht)
    (F.clearedF2_twoMode_gt_thousand hx0)
  simpa only [← normalizedSeriesJet_eq_baseJet_add_tailJet (t := t) ht] using h

theorem normalized_clearedC4_pos_of_certX_le_five
    {t : ℝ} (ht : 0 ≤ t) (hx5 : R.certX t ≤ 5) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (R.normalizedSeriesJet 0 t) (R.normalizedSeriesJet 1 t)
      (R.normalizedSeriesJet 2 t) (R.normalizedSeriesJet 3 t)
      (R.normalizedSeriesJet 4 t) (R.normalizedSeriesJet 5 t)
      (R.normalizedSeriesJet 6 t) := by
  have hx0 : (157 / 50 : ℝ) ≤ R.certX t := by
    have := R.certX_ge_three ht
    linarith
  have h := P.clearedC4_pos_of_base_margin_and_core_error
    (baseJet t) (tailJet t) (abs_baseJet_le_coreB ht hx5)
    (abs_tailJet_le_coreE ht)
    (clearedC4_twoMode_gt_margin_to_five hx0 hx5)
  simpa only [← normalizedSeriesJet_eq_baseJet_add_tailJet (t := t) ht] using h

/-! ## Outer weighted normalization -/

private noncomputable def scaledBaseJet (t : ℝ) (j : Fin 7) : ℝ :=
  baseJet t j / R.certX t ^ (j : ℕ)

private noncomputable def scaledTailJet (t : ℝ) (j : Fin 7) : ℝ :=
  tailJet t j / R.certX t ^ (j : ℕ)

private theorem abs_div_div_le_of_polynomial_bounds
    {raw den scale B : ℝ} (hden : 0 < den) (hscale : 0 < scale)
    (hlower : 0 < B * scale * den + raw)
    (hupper : 0 < B * scale * den - raw) :
    |raw / den / scale| ≤ B := by
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hscale, le_div_iff₀ hden]
    nlinarith
  · rw [div_le_iff₀ hscale, div_le_iff₀ hden]
    nlinarith

theorem abs_scaledBaseJet_le_outerB {t : ℝ} (ht : 0 ≤ t)
    (hx5 : 5 ≤ R.certX t) (j : Fin 7) :
    |scaledBaseJet t j| ≤ P.outerB j := by
  let x := R.certX t
  let y := Real.exp (-3 * x)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx5
  have hden : 0 < 2 * x - 3 := by linarith
  have hy0 : 0 ≤ y := (Real.exp_pos _).le
  have hy1 : y ≤ (1 / 3000000 : ℝ) := by
    exact (PF4.CERT12Inequalities.exp_neg_three_mul_lt_inv_3000000 hx5).le
  unfold scaledBaseJet baseJet F.twoModeNormalizedJet
  dsimp [x, y] at hxpos hden hy0 hy1 hx5 ⊢
  fin_cases j <;>
    apply abs_div_div_le_of_polynomial_bounds hden (pow_pos hxpos _) <;>
    first
    | simpa [G.baseOuter0LowerPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter0Lower_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter0UpperPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter0Upper_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter1LowerPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter1Lower_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter1UpperPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter1Upper_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter2LowerPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter2Lower_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter2UpperPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter2Upper_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter3LowerPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter3Lower_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter3UpperPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter3Upper_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter4LowerPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter4Lower_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter4UpperPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter4Upper_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter5LowerPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter5Lower_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter5UpperPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter5Upper_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter6LowerPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter6Lower_region_pos hx5 hy0 hy1
    | simpa [G.baseOuter6UpperPolynomial, PF4.certPoly, P.outerB] using
        G.baseOuter6Upper_region_pos hx5 hy0 hy1

theorem exp_40_gt_two_e17 :
    (200000000000000000 : ℝ) < Real.exp 40 := by
  have hsum : (200000000000000000 : ℝ) <
      ∑ i ∈ Finset.range 100, (40 : ℝ) ^ i / i ! := by
    norm_num [Finset.sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 100)

theorem exp_neg_40_lt_inv_two_e17 :
    Real.exp (-40) < (1 / 200000000000000000 : ℝ) := by
  have hi := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 200000000000000000) exp_40_gt_two_e17
  simpa [one_div, ← Real.exp_neg] using hi

theorem thirdProfile_outer_bound (j : Fin 7) :
    (1001 / 1000 : ℝ) * thirdProfile j 5 < P.outerE j * 5 ^ (j : ℕ) := by
  have he := exp_neg_40_lt_inv_two_e17
  fin_cases j <;>
    norm_num [thirdProfile, PF4.certPoly, P.outerE,
      Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.derivative_add,
      Polynomial.derivative_sub, Polynomial.derivative_mul] at he ⊢ <;>
    nlinarith

theorem abs_scaledTailJet_lt_outerE {t : ℝ} (ht : 0 ≤ t)
    (hx5 : 5 ≤ R.certX t) (j : Fin 7) :
    |scaledTailJet t j| < P.outerE j := by
  have hxpos : 0 < R.certX t := lt_of_lt_of_le (by norm_num) hx5
  have hp : 0 < R.certX t ^ (j : ℕ) := pow_pos hxpos _
  rw [scaledTailJet, abs_div, abs_of_pos hp, ← Real.norm_eq_abs,
    div_lt_iff₀ hp]
  have hj : (j : ℕ) ≤ 6 := by omega
  have hmono := thirdProfile_le_at_three hj
    (show 3 ≤ R.certX t from le_trans (by norm_num) hx5)
  have hprofile5 : thirdProfile j (R.certX t) ≤ thirdProfile j 5 := by
    exact (strictAntiOn_thirdProfile j hj).antitoneOn
      (by norm_num) hx5
  calc
    ‖tailJet t j‖ <
        (1001 / 1000 : ℝ) * thirdProfile j (R.certX t) :=
      norm_fullModeTail_lt_profile hj ht
    _ ≤ (1001 / 1000 : ℝ) * thirdProfile j 5 := by gcongr
    _ < P.outerE j * 5 ^ (j : ℕ) := thirdProfile_outer_bound j
    _ ≤ P.outerE j * R.certX t ^ (j : ℕ) := by
      gcongr
      · fin_cases j <;> norm_num [P.outerE]
      · exact pow_le_pow_left₀ (by norm_num) hx5 _

end PF4.RobustThreeModeClosure
