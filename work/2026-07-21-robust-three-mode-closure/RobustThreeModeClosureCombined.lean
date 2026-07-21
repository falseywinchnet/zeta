import PF4.ClearedJetCertificateBridge
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Tactic

set_option linter.style.header false

/-! Generated all-in-one replay for the robust three-mode closure round. -/



set_option linter.style.header false

/-!
# Relative infinite-tail interface

The infinite theta tail should not enter the final sign theorem as seven
unrelated decimal bounds.  This file isolates its first term (the original
theta mode `n = 3`) and gives a reusable theorem turning a geometric
majorant for all later modes into one relative bound.
-/

namespace PF4.InfiniteTailRefactor

open Finset Set

noncomputable def firstModeScale (t : ℝ) : ℝ := PF4.thetaModeJet 0 0 t

noncomputable def normalizedModeJet (j k : ℕ) (t : ℝ) : ℝ :=
  PF4.thetaModeJet j k t / firstModeScale t

noncomputable def certX (t : ℝ) : ℝ := PF4.modeX 0 t

noncomputable def normalizedSeriesJet (j : ℕ) (t : ℝ) : ℝ :=
  PF4.thetaSeriesJet j t / firstModeScale t

/-- The exact first term of the old tail: index `k=2`, hence theta mode
`n=k+1=3`. -/
noncomputable def thirdModeJet (j : ℕ) (t : ℝ) : ℝ :=
  normalizedModeJet j 2 t

/-- The genuinely infinite remainder after peeling off `n=3`; its first
term is `k=3`, hence `n=4`. -/
noncomputable def laterModeTail (j : ℕ) (t : ℝ) : ℝ :=
  ∑' r : ℕ, normalizedModeJet j (r + 3) t

/-- The tail used by the previous two-mode decomposition. -/
noncomputable def fullModeTail (j : ℕ) (t : ℝ) : ℝ :=
  ∑' r : ℕ, normalizedModeJet j (r + 2) t

/-- Every polynomial occurring in a tail mode has the expected alternating
strict sign.  The proof is finite only in derivative order (`j<=6`); its
variable `s` ranges over the complete half-line `s>=27`. -/
theorem certPoly_alternating_pos
    {j : ℕ} (hj : j ≤ 6) {s : ℝ} (hs : 27 ≤ s) :
    0 < (-1 : ℝ) ^ j * (PF4.certPoly j).eval s := by
  let z := s - 27
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hs_eq : s = z + 27 := by dsimp [z]; ring
  rw [hs_eq]
  interval_cases j <;>
    norm_num [PF4.certPoly, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_mul] <;>
    positivity

/-- Uniform polynomial envelope on the complete tail half-line. -/
theorem certPoly_alternating_le_envelope
    {j : ℕ} (hj : j ≤ 6) {s : ℝ} (hs : 27 ≤ s) :
    (-1 : ℝ) ^ j * (PF4.certPoly j).eval s ≤
      2 ^ (j + 1) * s ^ (j + 1) := by
  let z := s - 27
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hs_eq : s = z + 27 := by dsimp [z]; ring
  rw [hs_eq]
  interval_cases j <;>
    norm_num [PF4.certPoly, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_mul] <;>
    positivity

theorem abs_certPoly_le_envelope
    {j : ℕ} (hj : j ≤ 6) {s : ℝ} (hs : 27 ≤ s) :
    |(PF4.certPoly j).eval s| ≤ 2 ^ (j + 1) * s ^ (j + 1) := by
  have hp := certPoly_alternating_pos hj hs
  have hu := certPoly_alternating_le_envelope hj hs
  interval_cases j <;> norm_num at hp hu ⊢
  · rw [abs_of_pos hp]
    exact hu
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos hp]
    exact hu
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos hp]
    exact hu
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos hp]
    exact hu

/-- The signed `n=3` polynomial is bounded below by its endpoint value for
every `x>=3`. -/
theorem thirdMode_certPoly_endpoint_le
    {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 3 ≤ x) :
    (-1 : ℝ) ^ j * (PF4.certPoly j).eval 27 ≤
      (-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x) := by
  let z := x - 3
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hx_eq : x = z + 3 := by dsimp [z]; ring
  rw [hx_eq]
  interval_cases j <;>
    norm_num [PF4.certPoly, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_mul] <;>
    positivity

theorem thirdMode_abs_certPoly_endpoint_le
    {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 3 ≤ x) :
    (-1 : ℝ) ^ j * (PF4.certPoly j).eval 27 ≤
      |(PF4.certPoly j).eval (9 * x)| := by
  have hp := certPoly_alternating_pos hj
    (s := 9 * x) (by nlinarith)
  have hl := thirdMode_certPoly_endpoint_le hj hx
  interval_cases j <;> norm_num at hp hl ⊢
  · rw [abs_of_pos hp]
    exact hl
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos hp]
    exact hl
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos hp]
    exact hl
  · rw [abs_of_neg (by linarith)]
    linarith
  · rw [abs_of_pos hp]
    exact hl

/-- The worst rational coefficient in the later-tail/third-mode comparison
is below `1000`; combined with `exp 21 > 10^6` this leaves the desired
`10⁻³` relative margin. -/
theorem relative_tail_coefficient_lt_1000
    {j : ℕ} (hj : j ≤ 6) :
    (2 : ℝ) * 2 ^ (j + 1) * 4 ^ (2 * j + 4) * 3 ^ (j + 1) <
      1000 * 9 *
        ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) := by
  interval_cases j <;>
    norm_num [PF4.certPoly, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.derivative_add, Polynomial.derivative_sub,
      Polynomial.derivative_mul]

/-- Exact endpoint inequality after the exponential decay `exp(-21)` is
included. -/
theorem relative_tail_endpoint_constant
    {j : ℕ} (hj : j ≤ 6) :
    (2 : ℝ) * 2 ^ (j + 1) * 4 ^ (2 * j + 4) * 3 ^ (j + 1) *
        Real.exp (-21) <
      (1 / 1000 : ℝ) * 9 *
        ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) := by
  have hc := relative_tail_coefficient_lt_1000 hj
  have hp := certPoly_alternating_pos hj (s := 27) (by norm_num)
  have he : (1000000 : ℝ) < Real.exp 21 := by
    have hsum : (1000000 : ℝ) <
        ∑ i ∈ range 50, (21 : ℝ) ^ i / i ! := by
      norm_num [sum_range_succ]
    exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 50)
  have he0 := Real.exp_pos 21
  rw [show Real.exp (-21) = (Real.exp 21)⁻¹ by
    rw [← Real.exp_neg]
    norm_num]
  rw [inv_eq_one_div]
  rw [div_lt_iff₀ he0]
  nlinarith

/-- Polynomial growth cannot reverse the seven-unit exponential decay on
`x>=3`.  This supplies the continuous half-line step in the relative-tail
comparison. -/
theorem pow_mul_exp_neg_seven_le_endpoint
    {m : ℕ} (hm : m ≤ 7) {x : ℝ} (hx : 3 ≤ x) :
    x ^ m * Real.exp (-7 * x) ≤
      3 ^ m * Real.exp (-21) := by
  have hx0 : 0 ≤ x := by linarith
  have hratio0 : 0 ≤ x / 3 := by positivity
  have hratio : x / 3 ≤ Real.exp (x - 3) := by
    calc
      x / 3 ≤ (x - 3) + 1 := by linarith
      _ ≤ Real.exp (x - 3) := Real.add_one_le_exp (x - 3)
  have hpow : (x / 3) ^ m ≤ Real.exp (7 * (x - 3)) := by
    calc
      (x / 3) ^ m ≤ Real.exp (x - 3) ^ m := by gcongr
      _ = Real.exp (m * (x - 3)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      _ ≤ Real.exp (7 * (x - 3)) := by
        apply Real.exp_monotone
        have hxm : 0 ≤ x - 3 := by linarith
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hxm
  calc
    x ^ m * Real.exp (-7 * x) =
        3 ^ m * ((x / 3) ^ m * Real.exp (-7 * x)) := by
      field_simp
    _ ≤ 3 ^ m *
        (Real.exp (7 * (x - 3)) * Real.exp (-7 * x)) := by
      gcongr
    _ = 3 ^ m * Real.exp (-21) := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Consecutive polynomial-exponential majorants from mode `n=4` onward
contract by less than `10⁻⁹`, uniformly in `x>=3` and `j<=6`. -/
theorem successive_tail_majorant_ratio_lt
    {j n : ℕ} (hj : j ≤ 6) (hn : 4 ≤ n) {x : ℝ} (hx : 3 ≤ x) :
    (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (2 * j + 4) *
        Real.exp (-((2 * n + 1 : ℕ) : ℝ) * x) <
      (1 / 1000000000 : ℝ) := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hfrac0 : 0 ≤ (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by positivity
  have hfrac : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 5 / 4 := by
    rw [div_le_iff₀ hn0]
    push_cast
    nlinarith
  have hpow :
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (2 * j + 4) ≤
        ((5 : ℝ) / 4) ^ 16 := by
    calc
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ (2 * j + 4) ≤
          ((5 : ℝ) / 4) ^ (2 * j + 4) := by gcongr
      _ ≤ ((5 : ℝ) / 4) ^ 16 := by
        apply pow_le_pow_right'
        · norm_num
        · omega
  have harg :
      -(((2 * n + 1 : ℕ) : ℝ) * x) ≤ (-27 : ℝ) := by
    have hcount : (9 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 9 ≤ 2 * n + 1 by omega)
    nlinarith
  have hexp :
      Real.exp (-(((2 * n + 1 : ℕ) : ℝ) * x)) ≤ Real.exp (-27) :=
    Real.exp_monotone harg
  have he27 : (500000000000 : ℝ) < Real.exp 27 := by
    have hsum : (500000000000 : ℝ) <
        ∑ i ∈ range 60, (27 : ℝ) ^ i / i ! := by
      norm_num [sum_range_succ]
    exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 60)
  have he0 := Real.exp_pos 27
  have hconstant :
      ((5 : ℝ) / 4) ^ 16 * Real.exp (-27) <
        (1 / 1000000000 : ℝ) := by
    rw [show Real.exp (-27) = (Real.exp 27)⁻¹ by
      rw [← Real.exp_neg]
      norm_num]
    rw [inv_eq_one_div, div_lt_iff₀ he0]
    have hp : ((5 : ℝ) / 4) ^ 16 < 36 := by norm_num
    nlinarith
  exact (mul_le_mul hpow hexp (Real.exp_nonneg _) (pow_nonneg hfrac0 _)).trans_lt
    hconstant

theorem modeX_ge_27 {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    27 ≤ PF4.modeX k t := by
  have hn : (3 : ℝ) ≤ PF4.modeN k := by
    exact_mod_cast Nat.succ_le_succ hk
  have hn2 : (9 : ℝ) ≤ PF4.modeN k ^ 2 := by nlinarith
  have he : (1 : ℝ) ≤ Real.exp (2 * t) :=
    (Real.one_le_exp_iff).2 (by linarith)
  unfold PF4.modeX
  calc
    (27 : ℝ) = 3 * 9 * 1 := by norm_num
    _ ≤ Real.pi * PF4.modeN k ^ 2 * Real.exp (2 * t) := by
      gcongr
      exact Real.pi_gt_three.le

theorem certX_ge_three {t : ℝ} (ht : 0 ≤ t) : 3 ≤ certX t := by
  have he : (1 : ℝ) ≤ Real.exp (2 * t) :=
    (Real.one_le_exp_iff).2 (by linarith)
  unfold certX PF4.modeX PF4.modeN
  simp only [Nat.cast_one, one_pow, mul_one]
  calc
    (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    _ ≤ Real.pi * Real.exp (2 * t) :=
      le_mul_of_one_le_right Real.pi_pos.le he

theorem modeX_eq_modeN_sq_mul_certX (k : ℕ) (t : ℝ) :
    PF4.modeX k t = PF4.modeN k ^ 2 * certX t := by
  unfold PF4.modeX certX
  simp only [PF4.modeN, Nat.cast_one, one_pow, mul_one]
  ring

theorem firstModeScale_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < firstModeScale t := by
  have he : (1 : ℝ) ≤ Real.exp (2 * t) :=
    (Real.one_le_exp_iff).2 (by linarith)
  have hx : 3 < PF4.modeX 0 t := by
    unfold PF4.modeX PF4.modeN
    simp only [Nat.cast_one, one_pow, mul_one]
    calc
      (3 : ℝ) < Real.pi := Real.pi_gt_three
      _ ≤ Real.pi * Real.exp (2 * t) := by
        exact le_mul_of_one_le_right Real.pi_pos.le he
  unfold firstModeScale PF4.thetaModeJet PF4.certPoly
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, PF4.modeN, Nat.cast_one, one_pow, mul_one]
  positivity

theorem normalizedModeJet_eq
    (j k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    normalizedModeJet j k t =
      PF4.modeN k ^ 2 *
        Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
        (PF4.certPoly j).eval (PF4.modeN k ^ 2 * certX t) /
        (2 * certX t - 3) := by
  have hs := (firstModeScale_pos ht).ne'
  unfold normalizedModeJet firstModeScale PF4.thetaModeJet
  rw [modeX_eq_modeN_sq_mul_certX]
  rw [show PF4.modeX 0 t = certX t by rfl]
  unfold PF4.certPoly
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, PF4.modeN, Nat.cast_one, one_pow, mul_one]
  field_simp
  rw [← Real.exp_add]
  congr 1
  ring

theorem thirdMode_norm_lower
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    9 * Real.exp (-8 * certX t) *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) /
        (2 * certX t - 3) ≤
      ‖thirdModeJet j t‖ := by
  have hx := certX_ge_three ht
  have hden : 0 < 2 * certX t - 3 := by linarith
  have hp := thirdMode_abs_certPoly_endpoint_le hj hx
  unfold thirdModeJet
  rw [normalizedModeJet_eq j 2 ht, Real.norm_eq_abs]
  simp only [PF4.modeN, Nat.cast_ofNat, reducePow, Nat.cast_one]
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
    abs_of_pos (Real.exp_pos _), abs_of_pos hden]
  norm_num
  rw [show -(9 - 1) * certX t = -8 * certX t by ring]
  gcongr

noncomputable def normalizedModeMajorant
    (j k : ℕ) (t : ℝ) : ℝ :=
  2 ^ (j + 1) * PF4.modeN k ^ (2 * j + 4) * certX t ^ (j + 1) *
    Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) /
    (2 * certX t - 3)

theorem norm_normalizedModeJet_le_majorant
    {j k : ℕ} (hj : j ≤ 6) (hk : 2 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    ‖normalizedModeJet j k t‖ ≤ normalizedModeMajorant j k t := by
  have hx := certX_ge_three ht
  have hden : 0 < 2 * certX t - 3 := by linarith
  have hs : 27 ≤ PF4.modeN k ^ 2 * certX t := by
    rw [← modeX_eq_modeN_sq_mul_certX]
    exact modeX_ge_27 hk ht
  have hp := abs_certPoly_le_envelope hj hs
  rw [normalizedModeJet_eq j k ht, Real.norm_eq_abs]
  unfold normalizedModeMajorant
  rw [abs_div, abs_mul, abs_mul,
    abs_of_nonneg (sq_nonneg (PF4.modeN k)),
    abs_of_pos (Real.exp_pos _), abs_of_pos hden]
  calc
    PF4.modeN k ^ 2 * Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
          |(PF4.certPoly j).eval (PF4.modeN k ^ 2 * certX t)| /
        (2 * certX t - 3) ≤
      PF4.modeN k ^ 2 * Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) *
          (2 ^ (j + 1) *
            (PF4.modeN k ^ 2 * certX t) ^ (j + 1)) /
        (2 * certX t - 3) := by gcongr
    _ = 2 ^ (j + 1) * PF4.modeN k ^ (2 * j + 4) *
          certX t ^ (j + 1) *
          Real.exp (-(PF4.modeN k ^ 2 - 1) * certX t) /
        (2 * certX t - 3) := by
      rw [mul_pow]
      ring

theorem normalizedModeMajorant_succ_eq
    (j k : ℕ) (t : ℝ) :
    normalizedModeMajorant j (k + 1) t =
      normalizedModeMajorant j k t *
        (((PF4.modeN (k + 1)) / PF4.modeN k) ^ (2 * j + 4) *
          Real.exp (-(2 * PF4.modeN k + 1) * certX t)) := by
  have hn0 : PF4.modeN k ≠ 0 := (PF4.modeN_pos k).ne'
  unfold normalizedModeMajorant PF4.modeN
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← Real.exp_add]
  field_simp
  congr 1
  · ring
  · ring

theorem normalizedModeMajorant_succ_lt
    {j k : ℕ} (hj : j ≤ 6) (hk : 3 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    normalizedModeMajorant j (k + 1) t <
      normalizedModeMajorant j k t * (1 / 1000000000 : ℝ) := by
  have hx := certX_ge_three ht
  have hratio := successive_tail_majorant_ratio_lt
    hj (n := k + 1) (by omega) hx
  simp only [PF4.modeN, Nat.cast_add, Nat.cast_one] at hratio
  have hden : 0 < 2 * certX t - 3 := by linarith
  have hmajor : 0 < normalizedModeMajorant j k t := by
    unfold normalizedModeMajorant
    positivity
  rw [normalizedModeMajorant_succ_eq]
  simp only [PF4.modeN, Nat.cast_add, Nat.cast_one]
  exact mul_lt_mul_of_pos_left hratio hmajor

theorem normalizedModeMajorant_geometric
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) (r : ℕ) :
    normalizedModeMajorant j (r + 3) t ≤
      normalizedModeMajorant j 3 t * (1 / 1000000000 : ℝ) ^ r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      have hstep := normalizedModeMajorant_succ_lt
        hj (k := r + 3) (by omega) ht
      calc
        normalizedModeMajorant j (r + 1 + 3) t =
            normalizedModeMajorant j ((r + 3) + 1) t := by congr 2 <;> omega
        _ < normalizedModeMajorant j (r + 3) t *
            (1 / 1000000000 : ℝ) := hstep
        _ ≤ (normalizedModeMajorant j 3 t *
              (1 / 1000000000 : ℝ) ^ r) *
            (1 / 1000000000 : ℝ) := by gcongr
        _ = normalizedModeMajorant j 3 t *
            (1 / 1000000000 : ℝ) ^ (r + 1) := by rw [pow_succ]; ring

theorem norm_later_mode_term_geometric
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) (r : ℕ) :
    ‖normalizedModeJet j (r + 3) t‖ ≤
      normalizedModeMajorant j 3 t * (1 / 1000000000 : ℝ) ^ r :=
  (norm_normalizedModeJet_le_majorant hj (by omega) ht).trans
    (normalizedModeMajorant_geometric hj ht r)

theorem two_later_majorant_lt_third_lower
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    2 * normalizedModeMajorant j 3 t <
      (1 / 1000 : ℝ) *
        (9 * Real.exp (-8 * certX t) *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) /
          (2 * certX t - 3)) := by
  have hx := certX_ge_three ht
  have hden : 0 < 2 * certX t - 3 := by linarith
  have hdecay := pow_mul_exp_neg_seven_le_endpoint
    (m := j + 1) (by omega) hx
  have hendpoint := relative_tail_endpoint_constant hj
  have hcore :
      2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4) *
          certX t ^ (j + 1) * Real.exp (-7 * certX t) <
        (1 / 1000 : ℝ) * 9 *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) := by
    calc
      2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4) *
          certX t ^ (j + 1) * Real.exp (-7 * certX t) =
        (2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4)) *
          (certX t ^ (j + 1) * Real.exp (-7 * certX t)) := by ring
      _ ≤ (2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4)) *
          (3 ^ (j + 1) * Real.exp (-21)) := by gcongr
      _ < (1 / 1000 : ℝ) * 9 *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) := by
        simpa only [mul_assoc] using hendpoint
  unfold normalizedModeMajorant
  simp only [PF4.modeN, Nat.cast_ofNat, reducePow]
  rw [show Real.exp (-(16 - 1) * certX t) =
      Real.exp (-7 * certX t) * Real.exp (-8 * certX t) by
    rw [← Real.exp_add]
    congr 1
    ring]
  calc
    2 *
        (2 ^ (j + 1) * 4 ^ (2 * j + 4) * certX t ^ (j + 1) *
          (Real.exp (-7 * certX t) * Real.exp (-8 * certX t)) /
          (2 * certX t - 3)) =
      (2 * 2 ^ (j + 1) * 4 ^ (2 * j + 4) *
          certX t ^ (j + 1) * Real.exp (-7 * certX t)) *
        (Real.exp (-8 * certX t) / (2 * certX t - 3)) := by ring
    _ < ((1 / 1000 : ℝ) * 9 *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27)) *
        (Real.exp (-8 * certX t) / (2 * certX t - 3)) := by
      gcongr
    _ = (1 / 1000 : ℝ) *
        (9 * Real.exp (-8 * certX t) *
          ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) /
          (2 * certX t - 3)) := by ring

/-- Every individual normalized mode `n>=3` has the same alternating strict
sign through derivative order six. -/
theorem normalizedModeJet_alternating_pos
    {j k : ℕ} (hj : j ≤ 6) (hk : 2 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    0 < (-1 : ℝ) ^ j * normalizedModeJet j k t := by
  have hp := certPoly_alternating_pos hj (modeX_ge_27 hk ht)
  have hs := firstModeScale_pos ht
  unfold normalizedModeJet PF4.thetaModeJet
  rw [show (-1 : ℝ) ^ j *
      ((2 * Real.pi * PF4.modeN k ^ 2 * Real.exp ((5 / 2) * t) *
          (PF4.certPoly j).eval (PF4.modeX k t) *
          Real.exp (-PF4.modeX k t)) / firstModeScale t) =
      (2 * Real.pi * PF4.modeN k ^ 2 * Real.exp ((5 / 2) * t)) *
        ((-1 : ℝ) ^ j * (PF4.certPoly j).eval (PF4.modeX k t)) *
        Real.exp (-PF4.modeX k t) / firstModeScale t by ring]
  positivity

theorem summable_thetaMode_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k : ℕ => PF4.thetaMode k t := by
  let B := t + 1
  have htIoo : t ∈ Set.Ioo (-1 : ℝ) B := by
    dsimp [B]
    constructor <;> linarith
  have hzero : Summable fun k : ℕ => PF4.hModeJet 0 k t := by
    rw [funext fun k => PF4.hModeJet_zero_eq_hMode k t]
    exact (PF4.hasSum_nat_thetaTerms t).summable.mul_left
      (2 * Real.exp (t / 2)) |>.congr (fun k => by simp [PF4.hMode])
  have htwo : Summable fun k : ℕ => PF4.hModeJet 2 k t :=
    (PF4.HIntervalControl.summable_intervalMajorant B 1).of_norm_bounded fun k =>
      PF4.HIntervalControl.norm_hModeJet_le_intervalMajorant B 1 k htIoo
  exact (htwo.sub (hzero.mul_left (1 / 4 : ℝ))).div_const 2 |>.congr
    (fun k => PF4.secondOrder_hMode_eq_thetaMode k t)

theorem summable_thetaModeJet_of_nonneg
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k : ℕ => PF4.thetaModeJet j k t := by
  cases j with
  | zero =>
      simpa only [PF4.thetaModeJet_zero_eq_thetaMode] using
        summable_thetaMode_of_nonneg ht
  | succ j =>
      let B := t + 1
      have htIoo : t ∈ Set.Ioo (-1 : ℝ) B := by
        dsimp [B]
        constructor <;> linarith
      exact (PF4.IntervalControl.summable_intervalMajorant B j).of_norm_bounded
        fun k => PF4.IntervalControl.norm_thetaModeJet_le_intervalMajorant
          B j k htIoo

theorem summable_normalizedModeJet_of_nonneg
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k : ℕ => normalizedModeJet j k t := by
  simpa only [normalizedModeJet] using
    (summable_thetaModeJet_of_nonneg hj ht).div_const (firstModeScale t)

theorem normalizedSeriesJet_eq_tsum_normalizedModeJet
    (j : ℕ) (t : ℝ) :
    normalizedSeriesJet j t = ∑' k : ℕ, normalizedModeJet j k t := by
  unfold normalizedSeriesJet normalizedModeJet PF4.thetaSeriesJet
  rw [tsum_div_const]

theorem summable_fullModeTail_of_nonneg
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun r : ℕ => normalizedModeJet j (r + 2) t := by
  apply (summable_normalizedModeJet_of_nonneg hj ht).comp_injective
  intro a b hab
  omega

/-- The genuinely infinite `n>=4` remainder has the exact alternating weak
sign; this already uses every summand, not a truncation. -/
theorem laterModeTail_alternating_nonneg
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (-1 : ℝ) ^ j * laterModeTail j t := by
  unfold laterModeTail
  rw [← tsum_mul_left]
  exact tsum_nonneg fun r =>
    (normalizedModeJet_alternating_pos hj (by omega) ht).le

theorem fullModeTail_eq_third_add_later
    {j : ℕ} {t : ℝ}
    (hs : Summable fun r : ℕ => normalizedModeJet j (r + 2) t) :
    fullModeTail j t = thirdModeJet j t + laterModeTail j t := by
  have hsplit := hs.sum_add_tsum_nat_add 1
  rw [← hsplit]
  simp [fullModeTail, thirdModeJet, laterModeTail]

/-- The complete old tail, including every mode `n>=3`, has a strict
alternating sign through jet order six. -/
theorem fullModeTail_alternating_pos
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    0 < (-1 : ℝ) ^ j * fullModeTail j t := by
  rw [fullModeTail_eq_third_add_later
    (summable_fullModeTail_of_nonneg hj ht)]
  have hthird := normalizedModeJet_alternating_pos hj (by omega) ht
  have hlater := laterModeTail_alternating_nonneg hj ht
  rw [show (-1 : ℝ) ^ j *
      (thirdModeJet j t + laterModeTail j t) =
      (-1 : ℝ) ^ j * thirdModeJet j t +
        (-1 : ℝ) ^ j * laterModeTail j t by ring]
  exact add_pos_of_pos_of_nonneg hthird hlater

/-- A pointwise geometric majorant bounds the norm of the entire `tsum`.
This theorem quantifies over every natural index; it is not a finite-tail
check. -/
theorem norm_tsum_le_of_geometric_bound
    (f : ℕ → ℝ) (A q : ℝ)
    (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ r, ‖f r‖ ≤ A * q ^ r) :
    ‖∑' r, f r‖ ≤ A * (1 - q)⁻¹ := by
  have hgeom : HasSum (fun r : ℕ => A * q ^ r) (A * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).const_mul A
  exact tsum_of_norm_bounded hgeom hbound

/-- One exact inequality on the geometric envelope yields a relative bound
for the genuinely infinite remainder. -/
theorem norm_tsum_lt_relative_of_geometric_bound
    (f : ℕ → ℝ) (A q reference ε : ℝ)
    (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ r, ‖f r‖ ≤ A * q ^ r)
    (henvelope : A * (1 - q)⁻¹ < ε * ‖reference‖) :
    ‖∑' r, f r‖ < ε * ‖reference‖ :=
  (norm_tsum_le_of_geometric_bound f A q hA hq0 hq1 hbound).trans_lt
    henvelope

/-- The intended concrete interface: the complete `n>=4` remainder is less
than one thousandth of the exact `n=3` term. -/
theorem laterModeTail_lt_one_thousandth
    {j : ℕ} {t A q : ℝ}
    (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ r,
      ‖normalizedModeJet j (r + 3) t‖ ≤ A * q ^ r)
    (henvelope : A * (1 - q)⁻¹ < (1 / 1000 : ℝ) * ‖thirdModeJet j t‖) :
    ‖laterModeTail j t‖ <
      (1 / 1000 : ℝ) * ‖thirdModeJet j t‖ := by
  exact norm_tsum_lt_relative_of_geometric_bound
    (fun r => normalizedModeJet j (r + 3) t)
    A q (thirdModeJet j t) (1 / 1000)
    hA hq0 hq1 hbound henvelope

/-- Closed, universal relative estimate for the literal infinite theta tail.
There is no remaining geometric-majorant premise and no finite truncation. -/
theorem laterModeTail_lt_one_thousandth_closed
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ‖laterModeTail j t‖ <
      (1 / 1000 : ℝ) * ‖thirdModeJet j t‖ := by
  let A := normalizedModeMajorant j 3 t
  let q : ℝ := 1 / 1000000000
  have hA : 0 < A := by
    dsimp [A, normalizedModeMajorant]
    have hx := certX_ge_three ht
    have hden : 0 < 2 * certX t - 3 := by linarith
    positivity
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have hbound : ∀ r,
      ‖normalizedModeJet j (r + 3) t‖ ≤ A * q ^ r := by
    intro r
    exact norm_later_mode_term_geometric hj ht r
  have hinv : (1 - q)⁻¹ < (2 : ℝ) := by
    norm_num [q]
  have hlower := thirdMode_norm_lower hj ht
  have htwo := two_later_majorant_lt_third_lower hj ht
  have henvelope : A * (1 - q)⁻¹ <
      (1 / 1000 : ℝ) * ‖thirdModeJet j t‖ := by
    calc
      A * (1 - q)⁻¹ < A * 2 := by gcongr
      _ = 2 * normalizedModeMajorant j 3 t := by dsimp [A]; ring
      _ < (1 / 1000 : ℝ) *
          (9 * Real.exp (-8 * certX t) *
            ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) /
            (2 * certX t - 3)) := htwo
      _ ≤ (1 / 1000 : ℝ) * ‖thirdModeJet j t‖ := by gcongr
  exact laterModeTail_lt_one_thousandth
    hA.le hq0 hq1 hbound henvelope

/-- The theorem-facing refactor: once the relative geometric estimate is
discharged, the old seven-coordinate tail is not an arbitrary error vector.
Each coordinate is its exact `n=3` value times `1+δ`, with one dimensionless
parameter in `[0,10⁻³)`. -/
theorem fullModeTail_eq_third_mul_one_add_relative
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t)
    (hrelative : ‖laterModeTail j t‖ <
      (1 / 1000 : ℝ) * ‖thirdModeJet j t‖) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 / 1000 ∧
      fullModeTail j t = thirdModeJet j t * (1 + δ) := by
  let σ : ℝ := (-1 : ℝ) ^ j
  let third := thirdModeJet j t
  let later := laterModeTail j t
  have hthird : 0 < σ * third := by
    exact normalizedModeJet_alternating_pos hj (by omega) ht
  have hlater : 0 ≤ σ * later := by
    exact laterModeTail_alternating_nonneg hj ht
  have hσ : σ ≠ 0 := by simp [σ]
  have hthird0 : third ≠ 0 := by
    intro h
    rw [h] at hthird
    simp at hthird
  let δ := (σ * later) / (σ * third)
  have hδ0 : 0 ≤ δ := by
    dsimp [δ]
    exact div_nonneg hlater hthird.le
  have hδeq : δ = later / third := by
    dsimp [δ]
    field_simp
  have habsthird : 0 < ‖third‖ := norm_pos_iff.mpr hthird0
  have hδabs : ‖δ‖ = ‖later‖ / ‖third‖ := by
    rw [hδeq, norm_div]
  have hδlt : δ < 1 / 1000 := by
    apply lt_of_le_of_lt (le_norm δ)
    rw [hδabs]
    exact (div_lt_iff₀ habsthird).2 hrelative
  refine ⟨δ, hδ0, hδlt, ?_⟩
  rw [fullModeTail_eq_third_add_later
    (summable_fullModeTail_of_nonneg hj ht)]
  dsimp [third, later] at hδeq ⊢
  rw [hδeq]
  field_simp
  ring

/-- Final closed theorem-facing form of the infinite tail refactor. -/
theorem fullModeTail_eq_third_mul_one_add_relative_closed
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 / 1000 ∧
      fullModeTail j t = thirdModeJet j t * (1 + δ) := by
  exact fullModeTail_eq_third_mul_one_add_relative hj ht
    (laterModeTail_lt_one_thousandth_closed hj ht)

/-- The literal normalized theta-series jet is exactly two leading modes plus
the exact third mode times a relative factor in `[1,1.001)`.  The infinite
tail no longer appears in the exported theorem statement. -/
theorem normalizedSeriesJet_eq_first_three_relative
    {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : 0 ≤ t) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < 1 / 1000 ∧
      normalizedSeriesJet j t =
        normalizedModeJet j 0 t + normalizedModeJet j 1 t +
          thirdModeJet j t * (1 + δ) := by
  obtain ⟨δ, hδ0, hδ1, htail⟩ :=
    fullModeTail_eq_third_mul_one_add_relative_closed hj ht
  refine ⟨δ, hδ0, hδ1, ?_⟩
  rw [normalizedSeriesJet_eq_tsum_normalizedModeJet]
  have hsplit :=
    (summable_normalizedModeJet_of_nonneg hj ht).sum_add_tsum_nat_add 2
  rw [← hsplit]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd]
  rw [show (∑' x : ℕ, normalizedModeJet j (2 + x) t) =
      fullModeTail j t by
    unfold fullModeTail
    congr 1
    funext x
    congr 2
    omega]
  rw [htail]
  ring

/-- Same-sign summands give the tail its exact alternating sign. -/
theorem signed_tsum_nonneg
    (f : ℕ → ℝ) (sign : ℝ)
    (hterm : ∀ r, 0 ≤ sign * f r) :
    0 ≤ sign * ∑' r, f r := by
  rw [← tsum_mul_left]
  exact tsum_nonneg hterm

end PF4.InfiniteTailRefactor

#print axioms PF4.InfiniteTailRefactor.fullModeTail_eq_third_add_later
#print axioms PF4.InfiniteTailRefactor.fullModeTail_alternating_pos
#print axioms PF4.InfiniteTailRefactor.laterModeTail_lt_one_thousandth
#print axioms PF4.InfiniteTailRefactor.laterModeTail_lt_one_thousandth_closed
#print axioms PF4.InfiniteTailRefactor.fullModeTail_eq_third_mul_one_add_relative
#print axioms PF4.InfiniteTailRefactor.fullModeTail_eq_third_mul_one_add_relative_closed
#print axioms PF4.InfiniteTailRefactor.normalizedSeriesJet_eq_first_three_relative
#print axioms PF4.InfiniteTailRefactor.signed_tsum_nonneg


set_option linter.style.header false

/-!
# Executable Bernstein-box certificate semantics

The external certificate converts exact rational polynomials to tensor-product
Bernstein form.  This file gives that data a small mathematical meaning in
Lean: a checked coefficient floor implies a pointwise lower bound on the unit
square.  No numerical approximation or process result enters the theorem.
-/

namespace PF4.CERT12Inequalities

open Finset Polynomial

/-- Evaluation of the ordinary Bernstein basis polynomial. -/
noncomputable def bernsteinBasis (n i : ℕ) (x : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ n i).eval x

theorem bernsteinBasis_eq (n i : ℕ) (x : ℝ) :
    bernsteinBasis n i x =
      (n.choose i : ℝ) * x ^ i * (1 - x) ^ (n - i) := by
  simp [bernsteinBasis, bernsteinPolynomial]

theorem bernsteinBasis_nonneg {n i : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bernsteinBasis n i x := by
  rw [bernsteinBasis_eq]
  have hsub : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  positivity

theorem sum_bernsteinBasis (n : ℕ) (x : ℝ) :
    ∑ i ∈ range (n + 1), bernsteinBasis n i x = 1 := by
  rw [← Polynomial.eval_finset_sum]
  simp only [bernsteinBasis]
  rw [bernsteinPolynomial.sum]
  simp

/-- Tensor-product Bernstein evaluation for a rational coefficient table. -/
noncomputable def bernsteinBoxEval
    (nx ny : ℕ) (c : ℕ → ℕ → ℚ) (x y : ℝ) : ℝ :=
  ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
    (c i j : ℝ) * bernsteinBasis nx i x * bernsteinBasis ny j y

/-- A rational coefficient floor is a complete positivity certificate for the
corresponding Bernstein form on the closed unit square. -/
theorem bernsteinBoxEval_lower_bound
    {nx ny : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc : ∀ i ∈ range (nx + 1), ∀ j ∈ range (ny + 1), ε ≤ c i j) :
    (ε : ℝ) ≤ bernsteinBoxEval nx ny c x y := by
  have hxsum := sum_bernsteinBasis nx x
  have hysum := sum_bernsteinBasis ny y
  rw [bernsteinBoxEval]
  calc
    (ε : ℝ) = (ε : ℝ) *
        (∑ i ∈ range (nx + 1), bernsteinBasis nx i x) *
        (∑ j ∈ range (ny + 1), bernsteinBasis ny j y) := by
      rw [hxsum, hysum]
      ring
    _ = ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
          (ε : ℝ) * bernsteinBasis nx i x * bernsteinBasis ny j y := by
      rw [mul_sum, mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [sum_mul]
    _ ≤ ∑ i ∈ range (nx + 1), ∑ j ∈ range (ny + 1),
          (c i j : ℝ) * bernsteinBasis nx i x * bernsteinBasis ny j y := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      gcongr
      · exact_mod_cast hc i hi j hj
      · exact bernsteinBasis_nonneg hx0 hx1
      · exact bernsteinBasis_nonneg hy0 hy1

theorem bernsteinBoxEval_pos
    {nx ny : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {x y : ℝ}
    (hε : 0 < ε)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hc : ∀ i ∈ range (nx + 1), ∀ j ∈ range (ny + 1), ε ≤ c i j) :
    0 < bernsteinBoxEval nx ny c x y := by
  exact_mod_cast hε.trans_le
    (bernsteinBoxEval_lower_bound hx0 hx1 hy0 hy1 hc)

/-- Bernstein in the bounded coordinate and the ordinary nonnegative power
basis in an unbounded coordinate. -/
noncomputable def bernsteinHalfstripEval
    (nv nz : ℕ) (c : ℕ → ℕ → ℚ) (v z : ℝ) : ℝ :=
  ∑ j ∈ range (nv + 1), ∑ k ∈ range (nz + 1),
    (c j k : ℝ) * bernsteinBasis nv j v * z ^ k

theorem bernsteinHalfstripEval_lower_bound
    {nv nz : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {v z : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hz : 0 ≤ z)
    (hc0 : ∀ j ∈ range (nv + 1), ε ≤ c j 0)
    (hc : ∀ j ∈ range (nv + 1), ∀ k ∈ range (nz + 1), 0 ≤ c j k) :
    (ε : ℝ) ≤ bernsteinHalfstripEval nv nz c v z := by
  have hvsum := sum_bernsteinBasis nv v
  rw [bernsteinHalfstripEval]
  calc
    (ε : ℝ) = ∑ j ∈ range (nv + 1),
        (ε : ℝ) * bernsteinBasis nv j v := by
      rw [← mul_sum, hvsum, mul_one]
    _ ≤ ∑ j ∈ range (nv + 1), ∑ k ∈ range (nz + 1),
          (c j k : ℝ) * bernsteinBasis nv j v * z ^ k := by
      apply sum_le_sum
      intro j hj
      calc
        (ε : ℝ) * bernsteinBasis nv j v ≤
            (c j 0 : ℝ) * bernsteinBasis nv j v := by
          gcongr
          exact_mod_cast hc0 j hj
        _ = (c j 0 : ℝ) * bernsteinBasis nv j v * z ^ 0 := by simp
        _ ≤ ∑ k ∈ range (nz + 1),
            (c j k : ℝ) * bernsteinBasis nv j v * z ^ k := by
          apply single_le_sum
          · intro k hk
            exact mul_nonneg
              (mul_nonneg (by exact_mod_cast hc j hj k hk)
                (bernsteinBasis_nonneg hv0 hv1))
              (pow_nonneg hz k)
          · simp

theorem bernsteinHalfstripEval_pos
    {nv nz : ℕ} {c : ℕ → ℕ → ℚ} {ε : ℚ} {v z : ℝ}
    (hε : 0 < ε) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hz : 0 ≤ z)
    (hc0 : ∀ j ∈ range (nv + 1), ε ≤ c j 0)
    (hc : ∀ j ∈ range (nv + 1), ∀ k ∈ range (nz + 1), 0 ≤ c j k) :
    0 < bernsteinHalfstripEval nv nz c v z := by
  exact_mod_cast hε.trans_le
    (bernsteinHalfstripEval_lower_bound hv0 hv1 hz hc0 hc)

end PF4.CERT12Inequalities


set_option linter.style.header false

namespace PF4.CERT12Inequalities

open Finset

theorem exp_471_div_50_gt_12000 :
    (12000 : ℝ) < Real.exp (471 / 50) := by
  have hsum : (12000 : ℝ) <
      ∑ i ∈ range 30, (471 / 50 : ℝ) ^ i / i ! := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 30)

theorem exp_10_gt_22000 : (22000 : ℝ) < Real.exp 10 := by
  have hsum : (22000 : ℝ) <
      ∑ i ∈ range 30, (10 : ℝ) ^ i / i ! := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 30)

theorem exp_10_lt_23000 : Real.exp 10 < (23000 : ℝ) := by
  calc
    Real.exp 10 = Real.exp 1 ^ 10 := by
      convert Real.exp_nat_mul (1 : ℝ) 10 using 1 <;> norm_num
    _ < (2.7182818286 : ℝ) ^ 10 := by
      exact pow_lt_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9 (by omega)
    _ < 23000 := by norm_num

theorem exp_15_gt_3000000 : (3000000 : ℝ) < Real.exp 15 := by
  have hsum : (3000000 : ℝ) <
      ∑ i ∈ range 40, (15 : ℝ) ^ i / i ! := by
    norm_num [sum_range_succ]
  exact hsum.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 40)

theorem exp_neg_three_mul_lt_inv_12000 {x : ℝ}
    (hx : (157 / 50 : ℝ) ≤ x) :
    Real.exp (-3 * x) < 1 / 12000 := by
  have harg : (471 / 50 : ℝ) ≤ 3 * x := by linarith
  have hexp : (12000 : ℝ) < Real.exp (3 * x) :=
    exp_471_div_50_gt_12000.trans_le (Real.exp_monotone harg)
  have hinv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 12000) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

theorem exp_neg_three_mul_lt_inv_22000 {x : ℝ}
    (hx : (10 / 3 : ℝ) ≤ x) :
    Real.exp (-3 * x) < 1 / 22000 := by
  have harg : (10 : ℝ) ≤ 3 * x := by linarith
  have hexp : (22000 : ℝ) < Real.exp (3 * x) :=
    exp_10_gt_22000.trans_le (Real.exp_monotone harg)
  have hinv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 22000) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

theorem inv_23000_lt_exp_neg_three_mul {x : ℝ}
    (hx : x ≤ (10 / 3 : ℝ)) :
    1 / 23000 < Real.exp (-3 * x) := by
  have harg : 3 * x ≤ (10 : ℝ) := by linarith
  have hexp : Real.exp (3 * x) < (23000 : ℝ) :=
    (Real.exp_monotone harg).trans_lt exp_10_lt_23000
  have hinv := one_div_lt_one_div_of_lt (Real.exp_pos (3 * x)) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

theorem exp_neg_three_mul_lt_inv_3000000 {x : ℝ}
    (hx : (5 : ℝ) ≤ x) :
    Real.exp (-3 * x) < 1 / 3000000 := by
  have harg : (15 : ℝ) ≤ 3 * x := by linarith
  have hexp : (3000000 : ℝ) < Real.exp (3 * x) :=
    exp_15_gt_3000000.trans_le (Real.exp_monotone harg)
  have hinv := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3000000) hexp
  simpa [one_div, ← Real.exp_neg] using hinv

end PF4.CERT12Inequalities

namespace PF4.CERT12Inequalities.Generated

noncomputable def qCorePolynomial (x y : ℝ) : ℝ :=
  (((-48 : ℝ) * (x ^ 2)) + ((16 : ℝ) * (x ^ 3)) + ((60 : ℝ) * x) + ((-12288 : ℝ) * (x ^ 2) * (y ^ 2)) + ((-5424 : ℝ) * y * (x ^ 2)) + ((-2304 : ℝ) * y * (x ^ 4)) + ((1200 : ℝ) * x * y) + ((3840 : ℝ) * x * (y ^ 2)) + ((5600 : ℝ) * y * (x ^ 3)) + ((16384 : ℝ) * (x ^ 3) * (y ^ 2)))

def qCoreCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (3288836 / 15625 : ℚ)
  | 0, 1 => (241764504257 / 1171875000 : ℚ)
  | 0, 2 => (3553043228473 / 17578125000 : ℚ)
  | 1, 0 => (3463909 / 15625 : ℚ)
  | 1, 1 => (16290238639 / 75000000 : ℚ)
  | 1, 2 => (7478405528869 / 35156250000 : ℚ)
  | 2, 0 => (1313633 / 5625 : ℚ)
  | 2, 1 => (15438429017 / 67500000 : ℚ)
  | 2, 2 => (1416887598031 / 6328125000 : ℚ)
  | 3, 0 => (66433 / 270 : ℚ)
  | 3, 1 => (390218657 / 1620000 : ℚ)
  | 3, 2 => (143191685311 / 607500000 : ℚ)
  | 4, 0 => (7000 / 27 : ℚ)
  | 4, 1 => (205501 / 810 : ℚ)
  | 4, 2 => (75376769 / 303750 : ℚ)
  | _, _ => 0

theorem qCoreCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (2 + 1), (3553043228473 / 17578125000 : ℚ) ≤ qCoreCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [qCoreCoeff]

theorem qCore_representation (u v : ℝ) :
    qCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 4 2 qCoreCoeff u v := by
  norm_num [qCorePolynomial, bernsteinBoxEval, qCoreCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem qCore_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < qCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [qCore_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (3553043228473 / 17578125000 : ℚ)) hu0 hu1 hv0 hv1 qCoreCoeff_floor

theorem qCore_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ ((10 : ℝ) / 3))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < qCorePolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((29 : ℝ) / 150)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((29 : ℝ) / 150))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := qCore_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def qMidPolynomial (x y : ℝ) : ℝ :=
  (((-48 : ℝ) * (x ^ 2)) + ((16 : ℝ) * (x ^ 3)) + ((60 : ℝ) * x) + ((-12288 : ℝ) * (x ^ 2) * (y ^ 2)) + ((-5424 : ℝ) * y * (x ^ 2)) + ((-2304 : ℝ) * y * (x ^ 4)) + ((1200 : ℝ) * x * y) + ((3840 : ℝ) * x * (y ^ 2)) + ((5600 : ℝ) * y * (x ^ 3)) + ((16384 : ℝ) * (x ^ 3) * (y ^ 2)))

def qMidCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (7000 / 27 : ℚ)
  | 0, 1 => (34591 / 135 : ℚ)
  | 0, 2 => (517004788 / 2041875 : ℚ)
  | 1, 0 => (10075 / 27 : ℚ)
  | 1, 1 => (875135 / 2376 : ℚ)
  | 1, 2 => (742219267 / 2041875 : ℚ)
  | 2, 0 => (4850 / 9 : ℚ)
  | 2, 1 => (262936 / 495 : ℚ)
  | 2, 2 => (712588153 / 1361250 : ℚ)
  | 3, 0 => 775
  | 3, 1 => (67115 / 88 : ℚ)
  | 3, 2 => (56744734 / 75625 : ℚ)
  | 4, 0 => 1100
  | 4, 1 => (59413 / 55 : ℚ)
  | 4, 2 => (291631 / 275 : ℚ)
  | _, _ => 0

theorem qMidCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (2 + 1), (517004788 / 2041875 : ℚ) ≤ qMidCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [qMidCoeff]

theorem qMid_representation (u v : ℝ) :
    qMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) =
      bernsteinBoxEval 4 2 qMidCoeff u v := by
  norm_num [qMidPolynomial, bernsteinBoxEval, qMidCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem qMid_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < qMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) := by
  rw [qMid_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (517004788 / 2041875 : ℚ)) hu0 hu1 hv0 hv1 qMidCoeff_floor

theorem qMid_box_pos {x y : ℝ}
    (hx0 : ((10 : ℝ) / 3) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 22000)) :
    0 < qMidPolynomial x y := by
  let u := (x - ((10 : ℝ) / 3)) / ((5 : ℝ) / 3)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 22000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((5 : ℝ) / 3))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 22000))]
    linarith
  have h := qMid_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def f2CorePolynomial (x y : ℝ) : ℝ :=
  (((-518400 : ℝ) * (x ^ 4)) + ((-411648 : ℝ) * (x ^ 6)) + ((-36864 : ℝ) * (x ^ 8)) + ((4096 : ℝ) * (x ^ 9)) + ((146880 : ℝ) * (x ^ 3)) + ((156672 : ℝ) * (x ^ 7)) + ((642816 : ℝ) * (x ^ 5)) + ((-13056834797568 : ℝ) * (x ^ 8) * (y ^ 5)) + ((-9895604649984 : ℝ) * (x ^ 8) * (y ^ 6)) + ((-6906307411968 : ℝ) * (x ^ 6) * (y ^ 6)) + ((-6509019267072 : ℝ) * (x ^ 6) * (y ^ 5)) + ((-4696546738176 : ℝ) * (x ^ 10) * (y ^ 5)) + ((-2116175265792 : ℝ) * (x ^ 8) * (y ^ 4)) + ((-2062440529920 : ℝ) * (x ^ 6) * (y ^ 4)) + ((-543581798400 : ℝ) * (x ^ 4) * (y ^ 6)) + ((-526170193920 : ℝ) * (x ^ 4) * (y ^ 5)) + ((-331681935360 : ℝ) * (x ^ 6) * (y ^ 3)) + ((-217021317120 : ℝ) * (x ^ 4) * (y ^ 4)) + ((-199313326080 : ℝ) * (x ^ 10) * (y ^ 4)) + ((-168488304640 : ℝ) * (x ^ 9) * (y ^ 3)) + ((-68797071360 : ℝ) * (x ^ 11) * (y ^ 3)) + ((-47060766720 : ℝ) * (x ^ 4) * (y ^ 3)) + ((-35351101440 : ℝ) * (x ^ 6) * (y ^ 2)) + ((-31525650432 : ℝ) * (x ^ 8) * (y ^ 3)) + ((-26499612672 : ℝ) * (x ^ 8) * (y ^ 2)) + ((-5115985920 : ℝ) * (x ^ 4) * (y ^ 2)) + ((-2972712960 : ℝ) * (x ^ 10) * (y ^ 2)) + ((-1023662592 : ℝ) * y * (x ^ 6)) + ((-579391488 : ℝ) * y * (x ^ 8)) + ((-206219520 : ℝ) * y * (x ^ 4)) + ((-50651136 : ℝ) * y * (x ^ 10)) + ((5308416 : ℝ) * y * (x ^ 11)) + ((21876480 : ℝ) * y * (x ^ 3)) + ((222130176 : ℝ) * y * (x ^ 9)) + ((339738624 : ℝ) * (x ^ 11) * (y ^ 2)) + ((570240000 : ℝ) * (x ^ 3) * (y ^ 2)) + ((646154496 : ℝ) * y * (x ^ 5)) + ((966131712 : ℝ) * y * (x ^ 7)) + ((5438361600 : ℝ) * (x ^ 3) * (y ^ 3)) + ((11514347520 : ℝ) * (x ^ 9) * (y ^ 2)) + ((12230590464 : ℝ) * (x ^ 12) * (y ^ 3)) + ((18707189760 : ℝ) * (x ^ 5) * (y ^ 2)) + ((21743271936 : ℝ) * (x ^ 11) * (y ^ 4)) + ((23954227200 : ℝ) * (x ^ 3) * (y ^ 4)) + ((38503710720 : ℝ) * (x ^ 3) * (y ^ 6)) + ((38740377600 : ℝ) * (x ^ 7) * (y ^ 2)) + ((49474437120 : ℝ) * (x ^ 3) * (y ^ 5)) + ((162203959296 : ℝ) * (x ^ 10) * (y ^ 3)) + ((175433195520 : ℝ) * (x ^ 5) * (y ^ 3)) + ((293549137920 : ℝ) * (x ^ 7) * (y ^ 3)) + ((843180933120 : ℝ) * (x ^ 9) * (y ^ 4)) + ((878934343680 : ℝ) * (x ^ 5) * (y ^ 4)) + ((1391569403904 : ℝ) * (x ^ 11) * (y ^ 5)) + ((2415350513664 : ℝ) * (x ^ 5) * (y ^ 5)) + ((2696165720064 : ℝ) * (x ^ 5) * (y ^ 6)) + ((2816353566720 : ℝ) * (x ^ 7) * (y ^ 4)) + ((4398046511104 : ℝ) * (x ^ 9) * (y ^ 6)) + ((9428526956544 : ℝ) * (x ^ 9) * (y ^ 5)) + ((10514079940608 : ℝ) * (x ^ 7) * (y ^ 6)) + ((11508192903168 : ℝ) * (x ^ 7) * (y ^ 5)))

def f2CoreCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (1941588054452421056 / 3814697265625 : ℚ)
  | 0, 1 => (1126780771869943026888868 / 894069671630859375 : ℚ)
  | 0, 2 => (3373433671542590711394749272 / 1676380634307861328125 : ℚ)
  | 0, 3 => (5562564880011204974839504184588641 / 2011656761169433593750000000 : ℚ)
  | 0, 4 => (849441564399520238640551453943124963 / 241398811340332031250000000000 : ℚ)
  | 0, 5 => (309475959023082580335995916607038376057 / 72419643402099609375000000000000 : ℚ)
  | 0, 6 => (546279042295007792787012362713444563203 / 108629465103149414062500000000000 : ℚ)
  | 1, 0 => (2595161773001868464 / 3814697265625 : ℚ)
  | 1, 1 => (886620667743921946748551 / 596046447753906250 : ℚ)
  | 1, 2 => (15392680015174680353646416299 / 6705522537231445312500 : ℚ)
  | 1, 3 => (15987241274330888750407000211191 / 5149841308593750000000000 : ℚ)
  | 1, 4 => (1259852341476948695189276946587968087 / 321865081787109375000000000000 : ℚ)
  | 1, 5 => (2737463921884226065708174376700661803863 / 579357147216796875000000000000000 : ℚ)
  | 1, 6 => (4811672128520643579009101243468132335147 / 869035720825195312500000000000000 : ℚ)
  | 2, 0 => (36406708313435559728 / 41961669921875 : ℚ)
  | 2, 1 => (8189786757576522623250329 / 4720687866210937500 : ℚ)
  | 2, 2 => (2304024609502924803061595047 / 885128974914550781250 : ℚ)
  | 2, 3 => (655641193036574703681946500089573 / 188827514648437500000000000 : ℚ)
  | 2, 4 => (1106931103433011916010116754864613093 / 254917144775390625000000000000 : ℚ)
  | 2, 5 => (249190990317745228595764417888280763113 / 47796964645385742187500000000000 : ℚ)
  | 2, 6 => (2908858488859178698122154830464555956243 / 477969646453857421875000000000000 : ℚ)
  | 3, 0 => (2024336411753834951576 / 1888275146484375 : ℚ)
  | 3, 1 => (2063894837375853750510083 / 1029968261718750000 : ℚ)
  | 3, 2 => (6238336766889367044024007351 / 2124309539794921875000 : ℚ)
  | 3, 3 => (3157307934279510312807972559220927 / 815734863281250000000000000 : ℚ)
  | 3, 4 => (1470003502465838445325233148539494581 / 305900573730468750000000000000 : ℚ)
  | 3, 5 => (2634564552510932042827062739739652742631 / 458850860595703125000000000000000 : ℚ)
  | 3, 6 => (574629149579372884274829727423257511623509 / 86034536361694335937500000000000000 : ℚ)
  | 4, 0 => (880200942123708316624 / 679779052734375 : ℚ)
  | 4, 1 => (2341123485959976862421081 / 1019668579101562500 : ℚ)
  | 4, 2 => (6305786675665673813541630719 / 1911878585815429687500 : ℚ)
  | 4, 3 => (1579049880491614772125660105867193 / 367080688476562500000000000 : ℚ)
  | 4, 4 => (182610242069472149487321131313616573 / 34413814544677734375000000000 : ℚ)
  | 4, 5 => (130337480070051768087819178973849568239 / 20648288726806640625000000000000 : ℚ)
  | 4, 6 => (28338145465766025040177319641468376164883 / 3871554136276245117187500000000000 : ℚ)
  | 5, 0 => (25079637901534985698 / 16314697265625 : ℚ)
  | 5, 1 => (1023082005897115535497591 / 391552734375000000 : ℚ)
  | 5, 2 => (90296025415047554542701233 / 24472045898437500000 : ℚ)
  | 5, 3 => (1221970407364687383975060117293 / 256289062500000000000000 : ℚ)
  | 5, 4 => (1545476764991450650850779737161377 / 264298095703125000000000000 : ℚ)
  | 5, 5 => (18311731079730313925444965051798145227 / 2642980957031250000000000000000 : ℚ)
  | 5, 6 => (1082691152132655830177493401050236438799 / 135152435302734375000000000000000 : ℚ)
  | 6, 0 => (8225572314024156218 / 4568115234375 : ℚ)
  | 6, 1 => (81029770215436405328551 / 27408691406250000 : ℚ)
  | 6, 2 => (84557587898142362565391733 / 20556518554687500000 : ℚ)
  | 6, 3 => (10403735809130489451292612692737 / 1973425781250000000000000 : ℚ)
  | 6, 4 => (4759837194927468691258746903526081 / 740034667968750000000000000 : ℚ)
  | 6, 5 => (2107287026110050296539800226530991027 / 277513000488281250000000000000 : ℚ)
  | 6, 6 => (911283139316162062233012302104803298459 / 104067375183105468750000000000000 : ℚ)
  | 7, 0 => (490186558997010001 / 234931640625 : ℚ)
  | 7, 1 => (18765787372220752044017 / 5638359375000000 : ℚ)
  | 7, 2 => (9665835065657473856264359 / 2114384765625000000 : ℚ)
  | 7, 3 => (295147847292409033404880138217 / 50745234375000000000000 : ℚ)
  | 7, 4 => (537598782436030310681927059833403 / 76117851562500000000000000 : ℚ)
  | 7, 5 => (948909935899184488171210456246861907 / 114176777343750000000000000000 : ℚ)
  | 7, 6 => (204679918802354157173146400579590133813 / 21408145751953125000000000000000 : ℚ)
  | 8, 0 => (1228320011040632 / 512578125 : ℚ)
  | 8, 1 => (52584939187738695391 / 14095898437500 : ℚ)
  | 8, 2 => (803411544056512915730281 / 158578857421875000 : ℚ)
  | 8, 3 => (24372402898961700905634458569 / 3805892578125000000000 : ℚ)
  | 8, 4 => (68217146959167862355952088073 / 8809936523437500000000 : ℚ)
  | 8, 5 => (3889618559427609138812108590987531 / 428162915039062500000000000 : ℚ)
  | 8, 6 => (6697086479175524582075088507063301 / 642244372558593750000000000 : ℚ)
  | 9, 0 => (9241825133443442 / 3383015625 : ℚ)
  | 9, 1 => (3843070220248249153 / 922640625000 : ℚ)
  | 9, 2 => (85260744038701466639827 / 15223570312500000 : ℚ)
  | 9, 3 => (257135377825230131673833699 / 36536568750000000000 : ℚ)
  | 9, 4 => (580720140994503249394415036489 / 68506066406250000000000 : ℚ)
  | 9, 5 => (1019179488282283460431232577718609 / 102759099609375000000000000 : ℚ)
  | 9, 6 => (27363273335639070716202484369148237 / 2408416397094726562500000000 : ℚ)
  | 10, 0 => (16750849564016 / 5412825 : ℚ)
  | 10, 1 => (1045311145167617 / 225534375 : ℚ)
  | 10, 2 => (18807118845480979181 / 3044714062500 : ℚ)
  | 10, 3 => (282106569031658321869973 / 36536568750000000 : ℚ)
  | 10, 4 => (3847808030724755247574987 / 415188281250000000 : ℚ)
  | 10, 5 => (222294550296494595240079662239 / 20551819921875000000000 : ℚ)
  | 10, 6 => (2978565751746865144784106579611 / 240841639709472656250000 : ℚ)
  | 11, 0 => (68628268960 / 19683 : ℚ)
  | 11, 1 => (7589964328606 / 1476225 : ℚ)
  | 11, 2 => (2509009494070033 / 369056250 : ℚ)
  | 11, 3 => (112369346310045972919 / 13286025000000 : ℚ)
  | 11, 4 => (2016689531715979105559 / 199290375000000 : ℚ)
  | 11, 5 => (29354153518771834227406093 / 2491129687500000000 : ℚ)
  | 11, 6 => (9423589173989714869311676553 / 700630224609375000000 : ℚ)
  | 12, 0 => (76957120000 / 19683 : ℚ)
  | 12, 1 => (335857178080 / 59049 : ℚ)
  | 12, 2 => (33073845593224 / 4428675 : ℚ)
  | 12, 3 => (61454219956360487 / 6643012500 : ℚ)
  | 12, 4 => (27493114354315453927 / 2491129687500 : ℚ)
  | 12, 5 => (47921460594578593168229 / 3736694531250000 : ℚ)
  | 12, 6 => (5120039143822332646062433 / 350315112304687500 : ℚ)
  | _, _ => 0

theorem f2CoreCoeff_floor : ∀ i ∈ Finset.range (12 + 1), ∀ j ∈ Finset.range (6 + 1), (1941588054452421056 / 3814697265625 : ℚ) ≤ f2CoreCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [f2CoreCoeff]

theorem f2Core_representation (u v : ℝ) :
    f2CorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 12 6 f2CoreCoeff u v := by
  norm_num [f2CorePolynomial, bernsteinBoxEval, f2CoreCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem f2Core_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < f2CorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [f2Core_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (1941588054452421056 / 3814697265625 : ℚ)) hu0 hu1 hv0 hv1 f2CoreCoeff_floor

theorem f2Core_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ ((10 : ℝ) / 3))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < f2CorePolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((29 : ℝ) / 150)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((29 : ℝ) / 150))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := f2Core_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def f2MidPolynomial (x y : ℝ) : ℝ :=
  (((-518400 : ℝ) * (x ^ 4)) + ((-411648 : ℝ) * (x ^ 6)) + ((-36864 : ℝ) * (x ^ 8)) + ((4096 : ℝ) * (x ^ 9)) + ((146880 : ℝ) * (x ^ 3)) + ((156672 : ℝ) * (x ^ 7)) + ((642816 : ℝ) * (x ^ 5)) + ((-13056834797568 : ℝ) * (x ^ 8) * (y ^ 5)) + ((-9895604649984 : ℝ) * (x ^ 8) * (y ^ 6)) + ((-6906307411968 : ℝ) * (x ^ 6) * (y ^ 6)) + ((-6509019267072 : ℝ) * (x ^ 6) * (y ^ 5)) + ((-4696546738176 : ℝ) * (x ^ 10) * (y ^ 5)) + ((-2116175265792 : ℝ) * (x ^ 8) * (y ^ 4)) + ((-2062440529920 : ℝ) * (x ^ 6) * (y ^ 4)) + ((-543581798400 : ℝ) * (x ^ 4) * (y ^ 6)) + ((-526170193920 : ℝ) * (x ^ 4) * (y ^ 5)) + ((-331681935360 : ℝ) * (x ^ 6) * (y ^ 3)) + ((-217021317120 : ℝ) * (x ^ 4) * (y ^ 4)) + ((-199313326080 : ℝ) * (x ^ 10) * (y ^ 4)) + ((-168488304640 : ℝ) * (x ^ 9) * (y ^ 3)) + ((-68797071360 : ℝ) * (x ^ 11) * (y ^ 3)) + ((-47060766720 : ℝ) * (x ^ 4) * (y ^ 3)) + ((-35351101440 : ℝ) * (x ^ 6) * (y ^ 2)) + ((-31525650432 : ℝ) * (x ^ 8) * (y ^ 3)) + ((-26499612672 : ℝ) * (x ^ 8) * (y ^ 2)) + ((-5115985920 : ℝ) * (x ^ 4) * (y ^ 2)) + ((-2972712960 : ℝ) * (x ^ 10) * (y ^ 2)) + ((-1023662592 : ℝ) * y * (x ^ 6)) + ((-579391488 : ℝ) * y * (x ^ 8)) + ((-206219520 : ℝ) * y * (x ^ 4)) + ((-50651136 : ℝ) * y * (x ^ 10)) + ((5308416 : ℝ) * y * (x ^ 11)) + ((21876480 : ℝ) * y * (x ^ 3)) + ((222130176 : ℝ) * y * (x ^ 9)) + ((339738624 : ℝ) * (x ^ 11) * (y ^ 2)) + ((570240000 : ℝ) * (x ^ 3) * (y ^ 2)) + ((646154496 : ℝ) * y * (x ^ 5)) + ((966131712 : ℝ) * y * (x ^ 7)) + ((5438361600 : ℝ) * (x ^ 3) * (y ^ 3)) + ((11514347520 : ℝ) * (x ^ 9) * (y ^ 2)) + ((12230590464 : ℝ) * (x ^ 12) * (y ^ 3)) + ((18707189760 : ℝ) * (x ^ 5) * (y ^ 2)) + ((21743271936 : ℝ) * (x ^ 11) * (y ^ 4)) + ((23954227200 : ℝ) * (x ^ 3) * (y ^ 4)) + ((38503710720 : ℝ) * (x ^ 3) * (y ^ 6)) + ((38740377600 : ℝ) * (x ^ 7) * (y ^ 2)) + ((49474437120 : ℝ) * (x ^ 3) * (y ^ 5)) + ((162203959296 : ℝ) * (x ^ 10) * (y ^ 3)) + ((175433195520 : ℝ) * (x ^ 5) * (y ^ 3)) + ((293549137920 : ℝ) * (x ^ 7) * (y ^ 3)) + ((843180933120 : ℝ) * (x ^ 9) * (y ^ 4)) + ((878934343680 : ℝ) * (x ^ 5) * (y ^ 4)) + ((1391569403904 : ℝ) * (x ^ 11) * (y ^ 5)) + ((2415350513664 : ℝ) * (x ^ 5) * (y ^ 5)) + ((2696165720064 : ℝ) * (x ^ 5) * (y ^ 6)) + ((2816353566720 : ℝ) * (x ^ 7) * (y ^ 4)) + ((4398046511104 : ℝ) * (x ^ 9) * (y ^ 6)) + ((9428526956544 : ℝ) * (x ^ 9) * (y ^ 5)) + ((10514079940608 : ℝ) * (x ^ 7) * (y ^ 6)) + ((11508192903168 : ℝ) * (x ^ 7) * (y ^ 5)))

def f2MidCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (76957120000 / 19683 : ℚ)
  | 0, 1 => (96045450560 / 19683 : ℚ)
  | 0, 2 => (348322171412896 / 59541075 : ℚ)
  | 0, 3 => (558456709086900974 / 81868978125 : ℚ)
  | 0, 4 => (877293429198039250708 / 112569844921875 : ℚ)
  | 0, 5 => (1356842918716854165111458 / 154783536767578125 : ℚ)
  | 0, 6 => (188441020513574170619059448 / 19347942095947265625 : ℚ)
  | 1, 0 => (148757560000 / 19683 : ℚ)
  | 1, 1 => (1971684999880 / 216513 : ℚ)
  | 1, 2 => (211503255486524 / 19847025 : ℚ)
  | 1, 3 => (799570605798414097 / 65495182500 : ℚ)
  | 1, 4 => (3098101990175654374391 / 225139689843750 : ℚ)
  | 1, 5 => (1053549477960125145589009 / 68792683007812500 : ℚ)
  | 1, 6 => (3590452164295224623621229364 / 212827363055419921875 : ℚ)
  | 2, 0 => (2927058440000 / 216513 : ℚ)
  | 2, 1 => (38088419972920 / 2381643 : ℚ)
  | 2, 2 => (12095696487107692 / 654951825 : ℚ)
  | 2, 3 => (75451872077015792767 / 3602235037500 : ℚ)
  | 2, 4 => (5274094392108935418937 / 225139689843750 : ℚ)
  | 2, 5 => (176447108326911783402719009 / 6810475617773437500 : ℚ)
  | 2, 6 => (66470504299938713561723997086 / 2341100993609619140625 : ℚ)
  | 3, 0 => (453468562000 / 19683 : ℚ)
  | 3, 1 => (64273483061186 / 2381643 : ℚ)
  | 3, 2 => (101318311106542837 / 3274759125 : ℚ)
  | 3, 3 => (502800605283142764817 / 14408940150000 : ℚ)
  | 3, 4 => (1924503752833406601544229 / 49530731765625000 : ℚ)
  | 3, 5 => (5832262579759990037151037139 / 136209512355468750000 : ℚ)
  | 3, 6 => (547651996888383349569714472879 / 11705504968048095703125 : ℚ)
  | 4, 0 => (2739655736000 / 72171 : ℚ)
  | 4, 1 => (35137471690048 / 793881 : ℚ)
  | 4, 2 => (18399174536556908 / 363862125 : ℚ)
  | 4, 3 => (85370873122057818191 / 1500931265625 : ℚ)
  | 4, 4 => (260850629820079329334999 / 4127560980468750 : ℚ)
  | 4, 5 => (43840844624644948752347161 / 630599594238281250 : ℚ)
  | 4, 6 => (591941854266285325486607250359 / 7803669978698730468750 : ℚ)
  | 5, 0 => (1467308560000 / 24057 : ℚ)
  | 5, 1 => (18798318948055 / 264627 : ℚ)
  | 5, 2 => (5901219485344486 / 72772425 : ℚ)
  | 5, 3 => (145940648003778861713 / 1600993350000 : ℚ)
  | 5, 4 => (445696773019794945786029 / 4402731712500000 : ℚ)
  | 5, 5 => (1347787330929805333816898711 / 12107512209375000000 : ℚ)
  | 5, 6 => (31582928848724559552039413689 / 260122332623291015625 : ℚ)
  | 6, 0 => (1797662600000 / 18711 : ℚ)
  | 6, 1 => (3295324498550 / 29403 : ℚ)
  | 6, 2 => (5447060687504 / 42525 : ℚ)
  | 6, 3 => (16315117235994131693 / 113201550000 : ℚ)
  | 6, 4 => (274248832138327615622489 / 1712173443750000 : ℚ)
  | 6, 5 => (33193836001263817584007321 / 188339078812500000 : ℚ)
  | 6, 6 => (62259517552069065139871109569 / 323707791708984375000 : ℚ)
  | 7, 0 => (397977310000 / 2673 : ℚ)
  | 7, 1 => (155341733785 / 891 : ℚ)
  | 7, 2 => (1615798103581859 / 8085825 : ℚ)
  | 7, 3 => (20043103791346334257 / 88944075000 : ℚ)
  | 7, 4 => (8182166534405818804303 / 32612827500000 : ℚ)
  | 7, 5 => (371916244851137113231051891 / 1345279134375000000 : ℚ)
  | 7, 6 => (17460700985908222642087317353 / 57804962805175781250 : ℚ)
  | 8, 0 => (202748144000 / 891 : ℚ)
  | 8, 1 => (2626727260712 / 9801 : ℚ)
  | 8, 2 => (4157551430376664 / 13476375 : ℚ)
  | 8, 3 => (5174376818987970787 / 14824012500 : ℚ)
  | 8, 4 => (3610090948148042438159 / 9265007812500 : ℚ)
  | 8, 5 => (120595831000025900298385369 / 280266486328125000 : ℚ)
  | 8, 6 => (374999961491250170659703291 / 796211608886718750 : ℚ)
  | 9, 0 => (34013464000 / 99 : ℚ)
  | 9, 1 => (444051556702 / 1089 : ℚ)
  | 9, 2 => (706799331389936 / 1497375 : ℚ)
  | 9, 3 => (8834545873864023707 / 16471125000 : ℚ)
  | 9, 4 => (27212781011118493554293 / 45295593750000 : ℚ)
  | 9, 5 => (82868683666133348553105791 / 124562882812500000 : ℚ)
  | 9, 6 => (3906374625591655572589860533 / 5352311370849609375 : ℚ)
  | 10, 0 => (5644120000 / 11 : ℚ)
  | 10, 1 => (223164059780 / 363 : ℚ)
  | 10, 2 => (6502890722252 / 9075 : ℚ)
  | 10, 3 => (59917439401392561 / 73205000 : ℚ)
  | 10, 4 => (1389861748111145152759 / 1509853125000 : ℚ)
  | 10, 5 => (4246315235398222809481319 / 4152096093750000 : ℚ)
  | 10, 6 => (535222810975743105751248437 / 475761010742187500 : ℚ)
  | 11, 0 => 758630000
  | 11, 1 => (10112925340 / 11 : ℚ)
  | 11, 2 => (3267834259189 / 3025 : ℚ)
  | 11, 3 => (82614467712821791 / 66550000 : ℚ)
  | 11, 4 => (128355858630704972137 / 91506250000 : ℚ)
  | 11, 5 => (35783780895961347315929 / 22876562500000 : ℚ)
  | 11, 6 => (18661996449837821651721947 / 10812750244140625 : ℚ)
  | 12, 0 => 1111160000
  | 12, 1 => (15011142680 / 11 : ℚ)
  | 12, 2 => (4895796771332 / 3025 : ℚ)
  | 12, 3 => (6230916132859733 / 3327500 : ℚ)
  | 12, 4 => (48657837137022733097 / 22876562500 : ℚ)
  | 12, 5 => (149834917674622963693007 / 62910546875000 : ℚ)
  | 12, 6 => (28510816985877191462340629 / 10812750244140625 : ℚ)
  | _, _ => 0

theorem f2MidCoeff_floor : ∀ i ∈ Finset.range (12 + 1), ∀ j ∈ Finset.range (6 + 1), (76957120000 / 19683 : ℚ) ≤ f2MidCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [f2MidCoeff]

theorem f2Mid_representation (u v : ℝ) :
    f2MidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) =
      bernsteinBoxEval 12 6 f2MidCoeff u v := by
  norm_num [f2MidPolynomial, bernsteinBoxEval, f2MidCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem f2Mid_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < f2MidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) := by
  rw [f2Mid_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (76957120000 / 19683 : ℚ)) hu0 hu1 hv0 hv1 f2MidCoeff_floor

theorem f2Mid_box_pos {x y : ℝ}
    (hx0 : ((10 : ℝ) / 3) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 22000)) :
    0 < f2MidPolynomial x y := by
  let u := (x - ((10 : ℝ) / 3)) / ((5 : ℝ) / 3)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 22000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((5 : ℝ) / 3))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 22000))]
    linarith
  have h := f2Mid_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def c4CorePolynomial (x y : ℝ) : ℝ :=
  (((-41287680 : ℝ) * (x ^ 7)) + ((-4718592 : ℝ) * (x ^ 9)) + ((786432 : ℝ) * (x ^ 10)) + ((17694720 : ℝ) * (x ^ 8)) + ((46448640 : ℝ) * (x ^ 6)) + ((-522657825030144 : ℝ) * (x ^ 9) * (y ^ 3)) + ((-319756557090816 : ℝ) * (x ^ 11) * (y ^ 3)) + ((-316659348799488 : ℝ) * (x ^ 9) * (y ^ 4)) + ((-173173081374720 : ℝ) * (x ^ 7) * (y ^ 4)) + ((-103223163617280 : ℝ) * (x ^ 7) * (y ^ 3)) + ((-58482889850880 : ℝ) * (x ^ 9) * (y ^ 2)) + ((-35786792632320 : ℝ) * (x ^ 11) * (y ^ 2)) + ((-25048249270272 : ℝ) * (x ^ 13) * (y ^ 3)) + ((-9225319219200 : ℝ) * (x ^ 7) * (y ^ 2)) + ((-3608024186880 : ℝ) * (x ^ 13) * (y ^ 2)) + ((-308900560896 : ℝ) * y * (x ^ 9)) + ((-141059358720 : ℝ) * y * (x ^ 7)) + ((-61970448384 : ℝ) * y * (x ^ 11)) + ((-1528823808 : ℝ) * y * (x ^ 13)) + ((14077919232 : ℝ) * y * (x ^ 12)) + ((15792537600 : ℝ) * y * (x ^ 6)) + ((173237403648 : ℝ) * y * (x ^ 10)) + ((312563957760 : ℝ) * y * (x ^ 8)) + ((440301256704 : ℝ) * (x ^ 14) * (y ^ 2)) + ((1061258526720 : ℝ) * (x ^ 6) * (y ^ 2)) + ((14404832722944 : ℝ) * (x ^ 12) * (y ^ 2)) + ((16171558502400 : ℝ) * (x ^ 6) * (y ^ 3)) + ((33577217556480 : ℝ) * (x ^ 8) * (y ^ 2)) + ((48704929136640 : ℝ) * (x ^ 6) * (y ^ 4)) + ((57854526750720 : ℝ) * (x ^ 10) * (y ^ 2)) + ((124197569298432 : ℝ) * (x ^ 12) * (y ^ 3)) + ((211106232532992 : ℝ) * (x ^ 10) * (y ^ 4)) + ((296868139499520 : ℝ) * (x ^ 8) * (y ^ 4)) + ((305687754178560 : ℝ) * (x ^ 8) * (y ^ 3)) + ((519124442677248 : ℝ) * (x ^ 10) * (y ^ 3)))

def c4CoreCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (1977585360731187970962432 / 95367431640625 : ℚ)
  | 0, 1 => (3520225571147026183528193984198 / 186264514923095703125 : ℚ)
  | 0, 2 => (121512603425674826339300756103273643 / 6984919309616088867187500 : ℚ)
  | 0, 3 => (1700080268730820931958958890605570507 / 104773789644241333007812500 : ℚ)
  | 0, 4 => (2418081297841039307251450158709747237 / 157160684466361999511718750 : ℚ)
  | 1, 0 => (14452733462175892461758464 / 667572021484375 : ℚ)
  | 1, 1 => (153627961773149965558435794363319 / 7823109626770019531250 : ℚ)
  | 1, 2 => (21104697257175292336199167488779249 / 1173466444015502929687500 : ℚ)
  | 1, 3 => (18359784423970155063481780649772985579 / 1100124791264533996582031250 : ℚ)
  | 1, 4 => (51970722009573835554538266734304508573 / 3300374373793601989746093750 : ℚ)
  | 2, 0 => (196171338538271858522043392 / 8678436279296875 : ℚ)
  | 2, 1 => (41499813829837257151322697856729 / 2034008502960205078125 : ℚ)
  | 2, 2 => (113417667458500157141615839593853573 / 6102025508880615234375000 : ℚ)
  | 2, 3 => (39251784383739259309866264145382760233 / 2288259565830230712890625000 : ℚ)
  | 2, 4 => (7894646754652040368061635335529598509 / 490341335535049438476562500 : ℚ)
  | 3, 0 => (204834023813212868788063232 / 8678436279296875 : ℚ)
  | 3, 1 => (13795803923161860851434805184749 / 650882720947265625000 : ℚ)
  | 3, 2 => (1874732788375220937280793342935003 / 97632408142089843750000 : ℚ)
  | 3, 3 => (3225362495796130544246152429872470593 / 183060765266418457031250000 : ℚ)
  | 3, 4 => (3225287105307732269553625290355254043 / 196136534214019775390625000 : ℚ)
  | 4, 0 => (7058391619160753319125693696 / 286388397216796875 : ℚ)
  | 4, 1 => (181879203100643528645243808361 / 8261203765869140625 : ℚ)
  | 4, 2 => (1277769781931821181530214608504589 / 64437389373779296875000 : ℚ)
  | 4, 3 => (2184900740931411353727253749485236901 / 120820105075836181640625000 : ℚ)
  | 4, 4 => (380037641598202271516662937842962404579 / 22653769701719284057617187500 : ℚ)
  | 5, 0 => (884501821205498271724612096 / 34366607666015625 : ℚ)
  | 5, 1 => (1178701129876255545974095204739 / 51549911499023437500 : ℚ)
  | 5, 2 => (19784878732916097330343396795202 / 966560840606689453125 : ℚ)
  | 5, 3 => (67223331985492081063709888162855077 / 3624603152275085449218750 : ℚ)
  | 5, 4 => (11616740724010681206578968969259777119 / 679613091051578521728515625 : ℚ)
  | 6, 0 => (199519382616423994315412992 / 7423187255859375 : ℚ)
  | 6, 1 => (66095228892541100662714121417 / 2783695220947265625 : ℚ)
  | 6, 2 => (22047321891677800142664592605664 / 1043885707855224609375 : ℚ)
  | 6, 3 => (7439512000647050918385218234844884 / 391457140445709228515625 : ℚ)
  | 6, 4 => (2553228887510216253536212164908224876 / 146796427667140960693359375 : ℚ)
  | 7, 0 => (3572075620189116732002944 / 127254638671875 : ℚ)
  | 7, 1 => (2352818189204756976633717139 / 95440979003906250 : ℚ)
  | 7, 2 => (77958804277601990687272581146 / 3579036712646484375 : ℚ)
  | 7, 3 => (130567614076011295328106349705802 / 6710693836212158203125 : ℚ)
  | 7, 4 => (44472320319309855145588922865725206 / 2516510188579559326171875 : ℚ)
  | 8, 0 => (94963550181826969794304 / 3239208984375 : ℚ)
  | 8, 1 => (68387943151987563157898072 / 2672347412109375 : ℚ)
  | 8, 2 => (112505627571924930000103750088 / 5010651397705078125 : ℚ)
  | 8, 3 => (7478414567803711487253207349112 / 375798854827880859375 : ℚ)
  | 8, 4 => (12632041099768174607148395378810384 / 704622852802276611328125 : ℚ)
  | 9, 0 => (78554407937925485464576 / 2565453515625 : ℚ)
  | 9, 1 => (464596688931755541625472 / 17491728515625 : ℚ)
  | 9, 2 => (8345634134225916395124664672 / 360766900634765625 : ℚ)
  | 9, 3 => (550141673712515264517862071712 / 27057517547607421875 : ℚ)
  | 9, 4 => (131576745682606304431625692527808 / 7247549343109130859375 : ℚ)
  | 10, 0 => (393837081775552294912 / 12314176875 : ℚ)
  | 10, 1 => (2314158440504449483136 / 83960296875 : ℚ)
  | 10, 2 => (41248716742053623834214784 / 1731681123046875 : ℚ)
  | 10, 3 => (2695006227600524256084290176 / 129876084228515625 : ℚ)
  | 10, 4 => (638359119225861425823324134656 / 34788236846923828125 : ℚ)
  | 11, 0 => (23013921711767552 / 688905 : ℚ)
  | 11, 1 => (295501470230911744 / 10333575 : ℚ)
  | 11, 2 => (30871629027550298757632 / 1259404453125 : ℚ)
  | 11, 3 => (1997900490144553205566976 / 94455333984375 : ℚ)
  | 11, 4 => (3277907015517413710387122176 / 177103751220703125 : ℚ)
  | 12, 0 => (20834207211520000 / 597051 : ℚ)
  | 12, 1 => (265650638322464768 / 8955765 : ℚ)
  | 12, 2 => (28221773331958921216 / 1119470625 : ℚ)
  | 12, 3 => (27118096247927753013248 / 1259404453125 : ℚ)
  | 12, 4 => (676636861311815713755136 / 36328974609375 : ℚ)
  | 13, 0 => (5022295162880000 / 137781 : ℚ)
  | 13, 1 => (12715162188185600 / 413343 : ℚ)
  | 13, 2 => (803208797641711616 / 31000725 : ℚ)
  | 13, 3 => (50892716076669231104 / 2325054375 : ℚ)
  | 13, 4 => (81500299211330014527488 / 4359476953125 : ℚ)
  | 14, 0 => (749486080000000 / 19683 : ℚ)
  | 14, 1 => (1883326566400000 / 59049 : ℚ)
  | 14, 2 => (4713722334576640 / 177147 : ℚ)
  | 14, 3 => (59034299015856128 / 2657205 : ℚ)
  | 14, 4 => (93225656456539602944 / 4982259375 : ℚ)
  | _, _ => 0

theorem c4CoreCoeff_floor : ∀ i ∈ Finset.range (14 + 1), ∀ j ∈ Finset.range (4 + 1), (2418081297841039307251450158709747237 / 157160684466361999511718750 : ℚ) ≤ c4CoreCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4CoreCoeff]

theorem c4Core_representation (u v : ℝ) :
    c4CorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 14 4 c4CoreCoeff u v := by
  norm_num [c4CorePolynomial, bernsteinBoxEval, c4CoreCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4Core_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < c4CorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [c4Core_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (2418081297841039307251450158709747237 / 157160684466361999511718750 : ℚ)) hu0 hu1 hv0 hv1 c4CoreCoeff_floor

theorem c4Core_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ ((10 : ℝ) / 3))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < c4CorePolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((29 : ℝ) / 150)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((29 : ℝ) / 150))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := c4Core_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def qMarginCorePolynomial (x y : ℝ) : ℝ :=
  ((-90 : ℝ) + ((-88 : ℝ) * (x ^ 2)) + ((16 : ℝ) * (x ^ 3)) + ((180 : ℝ) * x) + ((-12288 : ℝ) * (x ^ 2) * (y ^ 2)) + ((-5424 : ℝ) * y * (x ^ 2)) + ((-2304 : ℝ) * y * (x ^ 4)) + ((1200 : ℝ) * x * y) + ((3840 : ℝ) * x * (y ^ 2)) + ((5600 : ℝ) * y * (x ^ 3)) + ((16384 : ℝ) * (x ^ 3) * (y ^ 2)))

def qMarginCoreCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (1607836 / 15625 : ℚ)
  | 0, 1 => (115689504257 / 1171875000 : ℚ)
  | 0, 2 => (1661918228473 / 17578125000 : ℚ)
  | 1, 0 => (5051477 / 46875 : ℚ)
  | 1, 1 => (2581946213 / 25000000 : ℚ)
  | 1, 2 => (3473218028869 / 35156250000 : ℚ)
  | 2, 0 => (1907194 / 16875 : ℚ)
  | 2, 1 => (811512113 / 7500000 : ℚ)
  | 2, 2 => (654248223031 / 6328125000 : ℚ)
  | 3, 0 => (32047 / 270 : ℚ)
  | 3, 1 => (183902657 / 1620000 : ℚ)
  | 3, 2 => (65823185311 / 607500000 : ℚ)
  | 4, 0 => (3370 / 27 : ℚ)
  | 4, 1 => (96601 / 810 : ℚ)
  | 4, 2 => (34539269 / 303750 : ℚ)
  | _, _ => 0

theorem qMarginCoreCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (2 + 1), (1661918228473 / 17578125000 : ℚ) ≤ qMarginCoreCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [qMarginCoreCoeff]

theorem qMarginCore_representation (u v : ℝ) :
    qMarginCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 4 2 qMarginCoreCoeff u v := by
  norm_num [qMarginCorePolynomial, bernsteinBoxEval, qMarginCoreCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem qMarginCore_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < qMarginCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [qMarginCore_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (1661918228473 / 17578125000 : ℚ)) hu0 hu1 hv0 hv1 qMarginCoreCoeff_floor

theorem qMarginCore_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ ((10 : ℝ) / 3))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < qMarginCorePolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((29 : ℝ) / 150)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((29 : ℝ) / 150))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := qMarginCore_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def qMarginMidPolynomial (x y : ℝ) : ℝ :=
  ((-90 : ℝ) + ((-88 : ℝ) * (x ^ 2)) + ((16 : ℝ) * (x ^ 3)) + ((180 : ℝ) * x) + ((-12288 : ℝ) * (x ^ 2) * (y ^ 2)) + ((-5424 : ℝ) * y * (x ^ 2)) + ((-2304 : ℝ) * y * (x ^ 4)) + ((1200 : ℝ) * x * y) + ((3840 : ℝ) * x * (y ^ 2)) + ((5600 : ℝ) * y * (x ^ 3)) + ((16384 : ℝ) * (x ^ 3) * (y ^ 2)))

def qMarginMidCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (3370 / 27 : ℚ)
  | 0, 1 => (16441 / 135 : ℚ)
  | 0, 2 => (242486038 / 2041875 : ℚ)
  | 1, 0 => (4795 / 27 : ℚ)
  | 1, 1 => (410495 / 2376 : ℚ)
  | 1, 2 => (342919267 / 2041875 : ℚ)
  | 2, 0 => (7120 / 27 : ℚ)
  | 2, 1 => (380158 / 1485 : ℚ)
  | 2, 2 => (1013976959 / 4083750 : ℚ)
  | 3, 0 => (1205 / 3 : ℚ)
  | 3, 1 => (102785 / 264 : ℚ)
  | 3, 2 => (85534202 / 226875 : ℚ)
  | 4, 0 => 610
  | 4, 1 => (32463 / 55 : ℚ)
  | 4, 2 => (156881 / 275 : ℚ)
  | _, _ => 0

theorem qMarginMidCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (2 + 1), (242486038 / 2041875 : ℚ) ≤ qMarginMidCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [qMarginMidCoeff]

theorem qMarginMid_representation (u v : ℝ) :
    qMarginMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) =
      bernsteinBoxEval 4 2 qMarginMidCoeff u v := by
  norm_num [qMarginMidPolynomial, bernsteinBoxEval, qMarginMidCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem qMarginMid_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < qMarginMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) := by
  rw [qMarginMid_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (242486038 / 2041875 : ℚ)) hu0 hu1 hv0 hv1 qMarginMidCoeff_floor

theorem qMarginMid_box_pos {x y : ℝ}
    (hx0 : ((10 : ℝ) / 3) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 22000)) :
    0 < qMarginMidPolynomial x y := by
  let u := (x - ((10 : ℝ) / 3)) / ((5 : ℝ) / 3)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 22000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((5 : ℝ) / 3))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 22000))]
    linarith
  have h := qMarginMid_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def f2MarginCorePolynomial (x y : ℝ) : ℝ :=
  ((-729000 : ℝ) + ((-4860000 : ℝ) * (x ^ 2)) + ((-2678400 : ℝ) * (x ^ 4)) + ((-475648 : ℝ) * (x ^ 6)) + ((-36864 : ℝ) * (x ^ 8)) + ((4096 : ℝ) * (x ^ 9)) + ((156672 : ℝ) * (x ^ 7)) + ((1218816 : ℝ) * (x ^ 5)) + ((2916000 : ℝ) * x) + ((4466880 : ℝ) * (x ^ 3)) + ((-13056834797568 : ℝ) * (x ^ 8) * (y ^ 5)) + ((-9895604649984 : ℝ) * (x ^ 8) * (y ^ 6)) + ((-6906307411968 : ℝ) * (x ^ 6) * (y ^ 6)) + ((-6509019267072 : ℝ) * (x ^ 6) * (y ^ 5)) + ((-4696546738176 : ℝ) * (x ^ 10) * (y ^ 5)) + ((-2116175265792 : ℝ) * (x ^ 8) * (y ^ 4)) + ((-2062440529920 : ℝ) * (x ^ 6) * (y ^ 4)) + ((-543581798400 : ℝ) * (x ^ 4) * (y ^ 6)) + ((-526170193920 : ℝ) * (x ^ 4) * (y ^ 5)) + ((-331681935360 : ℝ) * (x ^ 6) * (y ^ 3)) + ((-217021317120 : ℝ) * (x ^ 4) * (y ^ 4)) + ((-199313326080 : ℝ) * (x ^ 10) * (y ^ 4)) + ((-168488304640 : ℝ) * (x ^ 9) * (y ^ 3)) + ((-68797071360 : ℝ) * (x ^ 11) * (y ^ 3)) + ((-47060766720 : ℝ) * (x ^ 4) * (y ^ 3)) + ((-35351101440 : ℝ) * (x ^ 6) * (y ^ 2)) + ((-31525650432 : ℝ) * (x ^ 8) * (y ^ 3)) + ((-26499612672 : ℝ) * (x ^ 8) * (y ^ 2)) + ((-5115985920 : ℝ) * (x ^ 4) * (y ^ 2)) + ((-2972712960 : ℝ) * (x ^ 10) * (y ^ 2)) + ((-1023662592 : ℝ) * y * (x ^ 6)) + ((-579391488 : ℝ) * y * (x ^ 8)) + ((-206219520 : ℝ) * y * (x ^ 4)) + ((-50651136 : ℝ) * y * (x ^ 10)) + ((5308416 : ℝ) * y * (x ^ 11)) + ((21876480 : ℝ) * y * (x ^ 3)) + ((222130176 : ℝ) * y * (x ^ 9)) + ((339738624 : ℝ) * (x ^ 11) * (y ^ 2)) + ((570240000 : ℝ) * (x ^ 3) * (y ^ 2)) + ((646154496 : ℝ) * y * (x ^ 5)) + ((966131712 : ℝ) * y * (x ^ 7)) + ((5438361600 : ℝ) * (x ^ 3) * (y ^ 3)) + ((11514347520 : ℝ) * (x ^ 9) * (y ^ 2)) + ((12230590464 : ℝ) * (x ^ 12) * (y ^ 3)) + ((18707189760 : ℝ) * (x ^ 5) * (y ^ 2)) + ((21743271936 : ℝ) * (x ^ 11) * (y ^ 4)) + ((23954227200 : ℝ) * (x ^ 3) * (y ^ 4)) + ((38503710720 : ℝ) * (x ^ 3) * (y ^ 6)) + ((38740377600 : ℝ) * (x ^ 7) * (y ^ 2)) + ((49474437120 : ℝ) * (x ^ 3) * (y ^ 5)) + ((162203959296 : ℝ) * (x ^ 10) * (y ^ 3)) + ((175433195520 : ℝ) * (x ^ 5) * (y ^ 3)) + ((293549137920 : ℝ) * (x ^ 7) * (y ^ 3)) + ((843180933120 : ℝ) * (x ^ 9) * (y ^ 4)) + ((878934343680 : ℝ) * (x ^ 5) * (y ^ 4)) + ((1391569403904 : ℝ) * (x ^ 11) * (y ^ 5)) + ((2415350513664 : ℝ) * (x ^ 5) * (y ^ 5)) + ((2696165720064 : ℝ) * (x ^ 5) * (y ^ 6)) + ((2816353566720 : ℝ) * (x ^ 7) * (y ^ 4)) + ((4398046511104 : ℝ) * (x ^ 9) * (y ^ 6)) + ((9428526956544 : ℝ) * (x ^ 9) * (y ^ 5)) + ((10514079940608 : ℝ) * (x ^ 7) * (y ^ 6)) + ((11508192903168 : ℝ) * (x ^ 7) * (y ^ 5)))

def f2MarginCoreCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (69746122380813197534077945501604540376511 / 43084114149678498506546020507812500 : ℚ)
  | 0, 1 => (14829476328507565205382543463269591749003 / 7492889417335391044616699218750000 : ℚ)
  | 0, 2 => (1524401910059620564026524794080902461199 / 651555601507425308227539062500000 : ℚ)
  | 0, 3 => (15299231615182585544316957047866252081 / 5665700882673263549804687500000 : ℚ)
  | 0, 4 => (3257642635672031933441892405080117930651 / 1064166426658630371093750000000000 : ℚ)
  | 0, 5 => (1900126467669526700330684661461659547417 / 555217266082763671875000000000000 : ℚ)
  | 0, 6 => (411012401994656230287012362713444563203 / 108629465103149414062500000000000 : ℚ)
  | 1, 0 => (489109711744070216406187750797463533160163 / 258504684898070991039276123046875000 : ℚ)
  | 1, 1 => (409869412381786684191931732071828204746641 / 179829346016049385070800781250000000 : ℚ)
  | 1, 2 => (5212245283953894316494520157523112882301 / 1954666804522275924682617187500000 : ℚ)
  | 1, 3 => (9966989208685267757878648216429160130137 / 3263443708419799804687500000000000 : ℚ)
  | 1, 4 => (21976666100898734051959505703932809786303 / 6384998559951782226562500000000000 : ℚ)
  | 1, 5 => (17011582275921013868287576030484112841223 / 4441738128662109375000000000000000 : ℚ)
  | 1, 6 => (3665754736707909204009101243468132335147 / 869035720825195312500000000000000 : ℚ)
  | 2, 0 => (324971361871503221292831716436997541823949 / 148359210463240742683410644531250000 : ℚ)
  | 2, 1 => (1546743122209606449354439646705372591876389 / 593436841852962970733642578125000000 : ℚ)
  | 2, 2 => (77988665124661536430724626988525488553837 / 25801601819694042205810546875000000 : ℚ)
  | 2, 3 => (123455715546365857159101914948992202636197 / 35897880792617797851562500000000000 : ℚ)
  | 2, 4 => (36108063233765922801447355465624680288581 / 9364664554595947265625000000000000 : ℚ)
  | 2, 5 => (23485674452495107613062471966642777708673 / 5496650934219360351562500000000000 : ℚ)
  | 2, 6 => (2241642754238661119997154830464555956243 / 477969646453857421875000000000000 : ℚ)
  | 3, 0 => (128771414187419981892132823043122626328915733 / 51183927609818056225776672363281250000 : ℚ)
  | 3, 1 => (105495058638244480843392159315680459211918019 / 35606210511177778244018554687500000000 : ℚ)
  | 3, 2 => (10558189150605679719413750504349538577022649 / 3096192218363285064697265625000000000 : ℚ)
  | 3, 3 => (15706367867511238842043079516998899066833 / 4071593284606933593750000000000000 : ℚ)
  | 3, 4 => (403177855491924752992262195375095817682461 / 93646645545959472656250000000000000 : ℚ)
  | 3, 5 => (2090199414789452065195283028842694204701899 / 439732074737548828125000000000000000 : ℚ)
  | 3, 6 => (447522983581384290524829727423257511623509 / 86034536361694335937500000000000000 : ℚ)
  | 4, 0 => (26445306411164839743473381913201125498010509 / 9213106969767250120639801025390625000 : ℚ)
  | 4, 1 => (10737434539100041584573053768632674143583131 / 3204558946006000041961669921875000000 : ℚ)
  | 4, 2 => (1067601013899403410083883629874067530763001 / 278657299652695655822753906250000000 : ℚ)
  | 4, 3 => (835890779437486328358062453820924679104043 / 193848556280136108398437500000000000 : ℚ)
  | 4, 4 => (15149350084704830877751000829604329314099 / 3160574287176132202148437500000000 : ℚ)
  | 4, 5 => (104374986314537916014577476073596721882563 / 19787943363189697265625000000000000 : ℚ)
  | 4, 6 => (22286347212798483731583569641468376164883 / 3871554136276245117187500000000000 : ℚ)
  | 5, 0 => (5760085458735328940177437674673953643182061 / 1768916538195312023162841796875000000 : ℚ)
  | 5, 1 => (2321027643604367425858004310957922329232999 / 615275317633152008056640625000000000 : ℚ)
  | 5, 2 => (229455626154065435486652553788180860145979 / 53502201533317565917968750000000000 : ℚ)
  | 5, 3 => (178852077526924322318735501173484195794097 / 37218922805786132812500000000000000 : ℚ)
  | 5, 4 => (38757717886167350177352789963528345424927 / 7281963157653808593750000000000000 : ℚ)
  | 5, 5 => (133121945663030512113704900131088155675687 / 22795710754394531250000000000000000 : ℚ)
  | 5, 6 => (9451509210728948096014927411552600826789 / 1486676788330078125000000000000000 : ℚ)
  | 6, 0 => (1365479422876078908060737193010861755076673 / 371472473021015524864196777343750000 : ℚ)
  | 6, 1 => (156170621658537412409192068491800335705027 / 36916519057989120483398437500000000 : ℚ)
  | 6, 2 => (107528596601116263524634700714660267572469 / 22470924643993377685546875000000000 : ℚ)
  | 6, 3 => (83481537749217138706231997327927960393417 / 15631947578430175781250000000000000 : ℚ)
  | 6, 4 => (36065027726467754489725505189996750962969 / 6116849052429199218750000000000000 : ℚ)
  | 6, 5 => (5147687828627558198541462019899325855961 / 797849876403808593750000000000000 : ℚ)
  | 6, 6 => (729331262419847817693949802104803298459 / 104067375183105468750000000000000 : ℚ)
  | 7, 0 => (35081110452694760351532675372604096568879 / 8490799383337497711181640625000000 : ℚ)
  | 7, 1 => (6980912077835821616957830865557334727043 / 1476660762319564819335937500000000 : ℚ)
  | 7, 2 => (683593009904085855375345429815850362653 / 128405283679962158203125000000000 : ℚ)
  | 7, 3 => (793251904001027956051001689689757562431 / 133988122100830078125000000000000 : ℚ)
  | 7, 4 => (455604592757403070736627034090346540181 / 69906846313476562500000000000000 : ℚ)
  | 7, 5 => (86498559314054558979003169702820599727 / 12157712402343750000000000000000 : ℚ)
  | 7, 6 => (165110609402305972204396400579590133813 / 21408145751953125000000000000000 : ℚ)
  | 8, 0 => (392818239659164494298959243661736693 / 84907993833374977111816406250 : ℚ)
  | 8, 1 => (155540689246806389673227974129594289 / 29533215246391296386718750000 : ℚ)
  | 8, 2 => (15170539340360407532021770580388761 / 2568105673599243164062500000 : ℚ)
  | 8, 3 => (35096115952243679693611531165514737 / 5359524884033203125000000000 : ℚ)
  | 8, 4 => (753931784211882127353480098991143 / 104860269470214843750000000 : ℚ)
  | 8, 5 => (77125769804492405496033902557369249 / 9847747045898437500000000000 : ℚ)
  | 8, 6 => (5442517380309296863325088507063301 / 642244372558593750000000000 : ℚ)
  | 9, 0 => (365313654044965333967597711297145071 / 70756661527812480926513671875 : ℚ)
  | 9, 1 => (575986454455694398399124641526995231 / 98444050821304321289062500000 : ℚ)
  | 9, 2 => (167936149837715207787023208964770553 / 25681056735992431640625000000 : ℚ)
  | 9, 3 => (1162185728708840628319736196361475011 / 160785746520996093750000000000 : ℚ)
  | 9, 4 => (1494416248110541139928054838904559181 / 188748485046386718750000000000 : ℚ)
  | 9, 5 => (847627092247368907143301264662858181 / 98477470458984375000000000000 : ℚ)
  | 9, 6 => (22392566706886894934952484369148237 / 2408416397094726562500000000 : ℚ)
  | 10, 0 => (650330398514318904984887339123108 / 113210658444499969482421875 : ℚ)
  | 10, 1 => (127654959200110257753825984985661 / 19688810164260864257812500 : ℚ)
  | 10, 2 => (333905010538160770641175598748787 / 46225902124786376953125000 : ℚ)
  | 10, 3 => (100207092731422488905509411841503 / 12583232336425781250000000 : ℚ)
  | 10, 4 => (42858724523079989033214908114971 / 4923873522949218750000000 : ℚ)
  | 10, 5 => (186034315437228157016658392589611 / 19695494091796875000000000 : ℚ)
  | 10, 6 => (2453531200512105623299731579611 / 240841639709472656250000 : ℚ)
  | 11, 0 => (524812318254795307570479821996 / 82335024323272705078125 : ℚ)
  | 11, 1 => (153967586521567504919207189873 / 21478701997375488281250 : ℚ)
  | 11, 2 => (401570634812921086887782374991 / 50428256863403320312500 : ℚ)
  | 11, 3 => (921767435885360264131840910339 / 105241579541015625000000 : ℚ)
  | 11, 4 => (393469871605715168633774201473 / 41181487646484375000000 : ℚ)
  | 11, 5 => (222402746819812222847036958473 / 21485993554687500000000 : ℚ)
  | 11, 6 => (7810744720871550806811676553 / 700630224609375000000 : ℚ)
  | 12, 0 => (4647334416091367874304665496 / 658680194586181640625 : ℚ)
  | 12, 1 => (679497813689510855679478624 / 85914807989501953125 : ℚ)
  | 12, 2 => (294602449642553825089663468 / 33618837908935546875 : ℚ)
  | 12, 3 => (168696482233968483559983593 / 17540263256835937500 : ℚ)
  | 12, 4 => (71881911486522830480954351 / 6863581274414062500 : ℚ)
  | 12, 5 => (1502540881694296841892763 / 132629589843750000 : ℚ)
  | 12, 6 => (4268729691600652958562433 / 350315112304687500 : ℚ)
  | _, _ => 0

theorem f2MarginCoreCoeff_floor : ∀ i ∈ Finset.range (12 + 1), ∀ j ∈ Finset.range (6 + 1), (69746122380813197534077945501604540376511 / 43084114149678498506546020507812500 : ℚ) ≤ f2MarginCoreCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [f2MarginCoreCoeff]

theorem f2MarginCore_representation (u v : ℝ) :
    f2MarginCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) (((1 : ℝ) / 23000) + (((11 : ℝ) / 276000)) * v) =
      bernsteinBoxEval 12 6 f2MarginCoreCoeff u v := by
  norm_num [f2MarginCorePolynomial, bernsteinBoxEval, f2MarginCoreCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem f2MarginCore_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < f2MarginCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) (((1 : ℝ) / 23000) + (((11 : ℝ) / 276000)) * v) := by
  rw [f2MarginCore_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (69746122380813197534077945501604540376511 / 43084114149678498506546020507812500 : ℚ)) hu0 hu1 hv0 hv1 f2MarginCoreCoeff_floor

theorem f2MarginCore_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ ((10 : ℝ) / 3))
    (hy0 : ((1 : ℝ) / 23000) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < f2MarginCorePolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((29 : ℝ) / 150)
  let v := (y - ((1 : ℝ) / 23000)) / ((11 : ℝ) / 276000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((29 : ℝ) / 150))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((11 : ℝ) / 276000))]
    linarith
  have h := f2MarginCore_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def f2MarginMidPolynomial (x y : ℝ) : ℝ :=
  ((-729000 : ℝ) + ((-4860000 : ℝ) * (x ^ 2)) + ((-2678400 : ℝ) * (x ^ 4)) + ((-475648 : ℝ) * (x ^ 6)) + ((-36864 : ℝ) * (x ^ 8)) + ((4096 : ℝ) * (x ^ 9)) + ((156672 : ℝ) * (x ^ 7)) + ((1218816 : ℝ) * (x ^ 5)) + ((2916000 : ℝ) * x) + ((4466880 : ℝ) * (x ^ 3)) + ((-13056834797568 : ℝ) * (x ^ 8) * (y ^ 5)) + ((-9895604649984 : ℝ) * (x ^ 8) * (y ^ 6)) + ((-6906307411968 : ℝ) * (x ^ 6) * (y ^ 6)) + ((-6509019267072 : ℝ) * (x ^ 6) * (y ^ 5)) + ((-4696546738176 : ℝ) * (x ^ 10) * (y ^ 5)) + ((-2116175265792 : ℝ) * (x ^ 8) * (y ^ 4)) + ((-2062440529920 : ℝ) * (x ^ 6) * (y ^ 4)) + ((-543581798400 : ℝ) * (x ^ 4) * (y ^ 6)) + ((-526170193920 : ℝ) * (x ^ 4) * (y ^ 5)) + ((-331681935360 : ℝ) * (x ^ 6) * (y ^ 3)) + ((-217021317120 : ℝ) * (x ^ 4) * (y ^ 4)) + ((-199313326080 : ℝ) * (x ^ 10) * (y ^ 4)) + ((-168488304640 : ℝ) * (x ^ 9) * (y ^ 3)) + ((-68797071360 : ℝ) * (x ^ 11) * (y ^ 3)) + ((-47060766720 : ℝ) * (x ^ 4) * (y ^ 3)) + ((-35351101440 : ℝ) * (x ^ 6) * (y ^ 2)) + ((-31525650432 : ℝ) * (x ^ 8) * (y ^ 3)) + ((-26499612672 : ℝ) * (x ^ 8) * (y ^ 2)) + ((-5115985920 : ℝ) * (x ^ 4) * (y ^ 2)) + ((-2972712960 : ℝ) * (x ^ 10) * (y ^ 2)) + ((-1023662592 : ℝ) * y * (x ^ 6)) + ((-579391488 : ℝ) * y * (x ^ 8)) + ((-206219520 : ℝ) * y * (x ^ 4)) + ((-50651136 : ℝ) * y * (x ^ 10)) + ((5308416 : ℝ) * y * (x ^ 11)) + ((21876480 : ℝ) * y * (x ^ 3)) + ((222130176 : ℝ) * y * (x ^ 9)) + ((339738624 : ℝ) * (x ^ 11) * (y ^ 2)) + ((570240000 : ℝ) * (x ^ 3) * (y ^ 2)) + ((646154496 : ℝ) * y * (x ^ 5)) + ((966131712 : ℝ) * y * (x ^ 7)) + ((5438361600 : ℝ) * (x ^ 3) * (y ^ 3)) + ((11514347520 : ℝ) * (x ^ 9) * (y ^ 2)) + ((12230590464 : ℝ) * (x ^ 12) * (y ^ 3)) + ((18707189760 : ℝ) * (x ^ 5) * (y ^ 2)) + ((21743271936 : ℝ) * (x ^ 11) * (y ^ 4)) + ((23954227200 : ℝ) * (x ^ 3) * (y ^ 4)) + ((38503710720 : ℝ) * (x ^ 3) * (y ^ 6)) + ((38740377600 : ℝ) * (x ^ 7) * (y ^ 2)) + ((49474437120 : ℝ) * (x ^ 3) * (y ^ 5)) + ((162203959296 : ℝ) * (x ^ 10) * (y ^ 3)) + ((175433195520 : ℝ) * (x ^ 5) * (y ^ 3)) + ((293549137920 : ℝ) * (x ^ 7) * (y ^ 3)) + ((843180933120 : ℝ) * (x ^ 9) * (y ^ 4)) + ((878934343680 : ℝ) * (x ^ 5) * (y ^ 4)) + ((1391569403904 : ℝ) * (x ^ 11) * (y ^ 5)) + ((2415350513664 : ℝ) * (x ^ 5) * (y ^ 5)) + ((2696165720064 : ℝ) * (x ^ 5) * (y ^ 6)) + ((2816353566720 : ℝ) * (x ^ 7) * (y ^ 4)) + ((4398046511104 : ℝ) * (x ^ 9) * (y ^ 6)) + ((9428526956544 : ℝ) * (x ^ 9) * (y ^ 5)) + ((10514079940608 : ℝ) * (x ^ 7) * (y ^ 6)) + ((11508192903168 : ℝ) * (x ^ 7) * (y ^ 5)))

def f2MarginMidCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (29124973000 / 19683 : ℚ)
  | 0, 1 => (48213303560 / 19683 : ℚ)
  | 0, 2 => (203629926737896 / 59541075 : ℚ)
  | 0, 3 => (359504872658775974 / 81868978125 : ℚ)
  | 0, 4 => (603734654109367375708 / 112569844921875 : ℚ)
  | 0, 5 => (980699602969930336986458 / 154783536767578125 : ℚ)
  | 0, 6 => (141423106045208692103434448 / 19347942095947265625 : ℚ)
  | 1, 0 => (79183528000 / 19683 : ℚ)
  | 1, 1 => (1206370647880 / 216513 : ℚ)
  | 1, 2 => (141349439886524 / 19847025 : ℚ)
  | 1, 3 => (568063014318414097 / 65495182500 : ℚ)
  | 1, 4 => (2302294644463154374391 / 225139689843750 : ℚ)
  | 1, 5 => (810386122325750145589009 / 68792683007812500 : ℚ)
  | 1, 6 => (2838165532801376967371229364 / 212827363055419921875 : ℚ)
  | 2, 0 => (1823756603000 / 216513 : ℚ)
  | 2, 1 => (25952099765920 / 2381643 : ℚ)
  | 2, 2 => (8758208430182692 / 654951825 : ℚ)
  | 2, 3 => (57095687763928292767 / 3602235037500 : ℚ)
  | 2, 4 => (4126832872540966668937 / 225139689843750 : ℚ)
  | 2, 5 => (141742447359980728715219009 / 6810475617773437500 : ℚ)
  | 2, 6 => (54540777092556163512895872086 / 2341100993609619140625 : ℚ)
  | 3, 0 => (310191010000 / 19683 : ℚ)
  | 3, 1 => (46936899269186 / 2381643 : ℚ)
  | 3, 2 => (77480508392542837 / 3274759125 : ℚ)
  | 3, 3 => (397914273341542764817 / 14408940150000 : ℚ)
  | 3, 4 => (1563956986784156601544229 / 49530731765625000 : ℚ)
  | 3, 5 => (4840758973124552537151037139 / 136209512355468750000 : ℚ)
  | 3, 6 => (462444655693150439413464472879 / 11705504968048095703125 : ℚ)
  | 4, 0 => (1996190717000 / 72171 : ℚ)
  | 4, 1 => (26959356481048 / 793881 : ℚ)
  | 4, 2 => (4883623910810636 / 121287375 : ℚ)
  | 4, 3 => (69909124055042193191 / 1500931265625 : ℚ)
  | 4, 4 => (218330819885786360584999 / 4127560980468750 : ℚ)
  | 4, 5 => (112034287654050568913291483 / 1891798782714843750 : ℚ)
  | 4, 6 => (511552838609262681443638500359 / 7803669978698730468750 : ℚ)
  | 5, 0 => (373305824000 / 8019 : ℚ)
  | 5, 1 => (14977016980055 / 264627 : ℚ)
  | 5, 2 => (1616787148048162 / 24257475 : ℚ)
  | 5, 3 => (122821771097378861713 / 1600993350000 : ℚ)
  | 5, 4 => (42457762391910549531781 / 489192412500000 : ℚ)
  | 5, 5 => (1172950824325155333816898711 / 12107512209375000000 : ℚ)
  | 5, 6 => (9275558592380094069429804563 / 86707444207763671875 : ℚ)
  | 6, 0 => (12802800629000 / 168399 : ℚ)
  | 6, 1 => (170467652927650 / 1852389 : ℚ)
  | 6, 2 => (454854938787896 / 4209975 : ℚ)
  | 6, 3 => (126410270359397185237 / 1018813950000 : ℚ)
  | 6, 4 => (2159299494681129790602401 / 15409560993750000 : ℚ)
  | 6, 5 => (264761124609354295756065889 / 1695051709312500000 : ℚ)
  | 6, 6 => (501926690246399603836964986121 / 2913370125380859375000 : ℚ)
  | 7, 0 => (972864874000 / 8019 : ℚ)
  | 7, 1 => (1177008548065 / 8019 : ℚ)
  | 7, 2 => (4178666466345577 / 24257475 : ℚ)
  | 7, 3 => (52773305085639002771 / 266832225000 : ℚ)
  | 7, 4 => (65547891892412369238727 / 293515447500000 : ℚ)
  | 7, 5 => (1004489139441361339693155673 / 4035837403125000000 : ℚ)
  | 7, 6 => (47601417230253769488761952059 / 173414888415527343750 : ℚ)
  | 8, 0 => (507886895000 / 2673 : ℚ)
  | 8, 1 => (6776248875136 / 29403 : ℚ)
  | 8, 2 => (10954746544004992 / 40429125 : ℚ)
  | 8, 3 => (13853431935126412361 / 44472037500 : ℚ)
  | 8, 4 => (9786711268295689814477 / 27795023437500 : ℚ)
  | 8, 5 => (330219755321587466520156107 / 840799458984375000 : ℚ)
  | 8, 6 => (1035318811523494164322859873 / 2388634826660156250 : ℚ)
  | 9, 0 => (86997784000 / 297 : ℚ)
  | 9, 1 => (1166685982106 / 3267 : ℚ)
  | 9, 2 => (1892878548169808 / 4492125 : ℚ)
  | 9, 3 => (24000923715592071121 / 49413375000 : ℚ)
  | 9, 4 => (74755879791855480662879 / 135886781250000 : ℚ)
  | 9, 5 => (229679277084275045659317373 / 373688648437500000 : ℚ)
  | 9, 6 => (10905864060152408124019581599 / 16056934112548828125 : ℚ)
  | 10, 0 => (44095889000 / 99 : ℚ)
  | 10, 1 => (595779078340 / 1089 : ℚ)
  | 10, 2 => (17665844641756 / 27225 : ℚ)
  | 10, 3 => (494660528507533049 / 658845000 : ℚ)
  | 10, 4 => (3862984814861560458277 / 4529559375000 : ℚ)
  | 10, 5 => (11895794525147012178443957 / 12456288281250000 : ℚ)
  | 10, 6 => (4527172080296556115823735933 / 4281849096679687500 : ℚ)
  | 11, 0 => (2006978000 / 3 : ℚ)
  | 11, 1 => (27380744020 / 33 : ℚ)
  | 11, 2 => (8990043977567 / 9075 : ℚ)
  | 11, 3 => (229947309538465373 / 199650000 : ℚ)
  | 11, 4 => (360460447192114916411 / 274518750000 : ℚ)
  | 11, 5 => (101199560512884041947787 / 68629687500000 : ℚ)
  | 11, 6 => (53078311055861121205165841 / 32438250732421875 : ℚ)
  | 12, 0 => 993511000
  | 12, 1 => (13717003680 / 11 : ℚ)
  | 12, 2 => (4539908546332 / 3025 : ℚ)
  | 12, 3 => (5839439085359733 / 3327500 : ℚ)
  | 12, 4 => (45966432435460233097 / 22876562500 : ℚ)
  | 12, 5 => (142433554745326088693007 / 62910546875000 : ℚ)
  | 12, 6 => (27238707732404291071715629 / 10812750244140625 : ℚ)
  | _, _ => 0

theorem f2MarginMidCoeff_floor : ∀ i ∈ Finset.range (12 + 1), ∀ j ∈ Finset.range (6 + 1), (29124973000 / 19683 : ℚ) ≤ f2MarginMidCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [f2MarginMidCoeff]

theorem f2MarginMid_representation (u v : ℝ) :
    f2MarginMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) =
      bernsteinBoxEval 12 6 f2MarginMidCoeff u v := by
  norm_num [f2MarginMidPolynomial, bernsteinBoxEval, f2MarginMidCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem f2MarginMid_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < f2MarginMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) := by
  rw [f2MarginMid_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (29124973000 / 19683 : ℚ)) hu0 hu1 hv0 hv1 f2MarginMidCoeff_floor

theorem f2MarginMid_box_pos {x y : ℝ}
    (hx0 : ((10 : ℝ) / 3) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 22000)) :
    0 < f2MarginMidPolynomial x y := by
  let u := (x - ((10 : ℝ) / 3)) / ((5 : ℝ) / 3)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 22000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((5 : ℝ) / 3))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 22000))]
    linarith
  have h := f2MarginMid_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def c4MarginCorePolynomial (x y : ℝ) : ℝ :=
  ((-4050000000 : ℝ) + ((-10800000000 : ℝ) * (x ^ 2)) + ((-800000000 : ℝ) * (x ^ 4)) + ((-41287680 : ℝ) * (x ^ 7)) + ((-4718592 : ℝ) * (x ^ 9)) + ((786432 : ℝ) * (x ^ 10)) + ((17694720 : ℝ) * (x ^ 8)) + ((46448640 : ℝ) * (x ^ 6)) + ((4800000000 : ℝ) * (x ^ 3)) + ((10800000000 : ℝ) * x) + ((-522657825030144 : ℝ) * (x ^ 9) * (y ^ 3)) + ((-319756557090816 : ℝ) * (x ^ 11) * (y ^ 3)) + ((-316659348799488 : ℝ) * (x ^ 9) * (y ^ 4)) + ((-173173081374720 : ℝ) * (x ^ 7) * (y ^ 4)) + ((-103223163617280 : ℝ) * (x ^ 7) * (y ^ 3)) + ((-58482889850880 : ℝ) * (x ^ 9) * (y ^ 2)) + ((-35786792632320 : ℝ) * (x ^ 11) * (y ^ 2)) + ((-25048249270272 : ℝ) * (x ^ 13) * (y ^ 3)) + ((-9225319219200 : ℝ) * (x ^ 7) * (y ^ 2)) + ((-3608024186880 : ℝ) * (x ^ 13) * (y ^ 2)) + ((-308900560896 : ℝ) * y * (x ^ 9)) + ((-141059358720 : ℝ) * y * (x ^ 7)) + ((-61970448384 : ℝ) * y * (x ^ 11)) + ((-1528823808 : ℝ) * y * (x ^ 13)) + ((14077919232 : ℝ) * y * (x ^ 12)) + ((15792537600 : ℝ) * y * (x ^ 6)) + ((173237403648 : ℝ) * y * (x ^ 10)) + ((312563957760 : ℝ) * y * (x ^ 8)) + ((440301256704 : ℝ) * (x ^ 14) * (y ^ 2)) + ((1061258526720 : ℝ) * (x ^ 6) * (y ^ 2)) + ((14404832722944 : ℝ) * (x ^ 12) * (y ^ 2)) + ((16171558502400 : ℝ) * (x ^ 6) * (y ^ 3)) + ((33577217556480 : ℝ) * (x ^ 8) * (y ^ 2)) + ((48704929136640 : ℝ) * (x ^ 6) * (y ^ 4)) + ((57854526750720 : ℝ) * (x ^ 10) * (y ^ 2)) + ((124197569298432 : ℝ) * (x ^ 12) * (y ^ 3)) + ((211106232532992 : ℝ) * (x ^ 10) * (y ^ 4)) + ((296868139499520 : ℝ) * (x ^ 8) * (y ^ 4)) + ((305687754178560 : ℝ) * (x ^ 8) * (y ^ 3)) + ((519124442677248 : ℝ) * (x ^ 10) * (y ^ 3)))

def c4MarginCoreCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (1425678915418687970962432 / 95367431640625 : ℚ)
  | 0, 1 => (2442283295146049621028193984198 / 186264514923095703125 : ℚ)
  | 0, 2 => (81089768075638205245550756103273643 / 6984919309616088867187500 : ℚ)
  | 0, 3 => (1093737738480271615552708890605570507 / 104773789644241333007812500 : ℚ)
  | 0, 4 => (1508567502465215332642075158709747237 / 157160684466361999511718750 : ℚ)
  | 1, 0 => (4482541740486096769325056 / 286102294921875 : ℚ)
  | 1, 1 => (106829492229692934308435794363319 / 7823109626770019531250 : ℚ)
  | 1, 2 => (14084926825656737648699167488779249 / 1173466444015502929687500 : ℚ)
  | 1, 3 => (11778749644421510043950530649772985579 / 1100124791264533996582031250 : ℚ)
  | 1, 4 => (32227617670927900495944516734304508573 / 3300374373793601989746093750 : ℚ)
  | 2, 0 => (61079400458924546509447168 / 3719329833984375 : ℚ)
  | 2, 1 => (9641651161968050560857565952243 / 678002834320068359375 : ℚ)
  | 2, 2 => (75693086426700840735365839593853573 / 6102025508880615234375000 : ℚ)
  | 2, 3 => (25105066496814515657522514145382760233 / 2288259565830230712890625000 : ℚ)
  | 2, 4 => (34042450452177167097915822348707189563 / 3432389348745346069335937500 : ℚ)
  | 3, 0 => (4033711638440145894777707264 / 234317779541015625 : ℚ)
  | 3, 1 => (86742060195541708600413246662741 / 5857944488525390625000 : ℚ)
  | 3, 2 => (288706893036916219901336925292693 / 22530555725097656250000 : ℚ)
  | 3, 3 => (2055982023517535573543027429872470593 / 183060765266418457031250000 : ℚ)
  | 3, 4 => (13806656195064663606601939532486778301 / 1372955739498138427734375000 : ℚ)
  | 4, 0 => (139549277191644538835143729792 / 7732486724853515625 : ℚ)
  | 4, 1 => (1146265745927947519525944275249 / 74350833892822265625 : ℚ)
  | 4, 2 => (2557626932653068525059393825513767 / 193312168121337890625000 : ℚ)
  | 4, 3 => (154177692524157162946691388831692989 / 13424456119537353515625000 : ℚ)
  | 4, 4 => (230543608808077855165344578467962404579 / 22653769701719284057617187500 : ℚ)
  | 5, 0 => (5852380066688839914271508864 / 309299468994140625 : ℚ)
  | 5, 1 => (225639566140767670208844146747 / 14059066772460937500 : ℚ)
  | 5, 2 => (4398984239971361056729048931734 / 322186946868896484375 : ℚ)
  | 5, 3 => (42518609436734527963123950662855077 / 3624603152275085449218750 : ℚ)
  | 5, 4 => (6984605246118640000219105688009777119 / 679613091051578521728515625 : ℚ)
  | 6, 0 => (21038933872053316152201856 / 1060455322265625 : ℚ)
  | 6, 1 => (46502661825522057693964121417 / 2783695220947265625 : ℚ)
  | 6, 2 => (14700109241545659029383342605664 / 1043885707855224609375 : ℚ)
  | 6, 3 => (669186750978214000129249926406412 / 55922448635101318359375 : ℚ)
  | 6, 4 => (1520027108585383909481036383658224876 / 146796427667140960693359375 : ℚ)
  | 7, 0 => (2647360207393022982002944 / 127254638671875 : ℚ)
  | 7, 1 => (1659281629607686664133717139 / 95440979003906250 : ℚ)
  | 7, 2 => (51951183292711853968522581146 / 3579036712646484375 : ℚ)
  | 7, 3 => (81803324729342288980450099705802 / 6710693836212158203125 : ℚ)
  | 7, 4 => (26185711814308977765217829115725206 / 2516510188579559326171875 : ℚ)
  | 8, 0 => (777331464848159167737344 / 35631298828125 : ℚ)
  | 8, 1 => (4394806737781113696172552 / 242940673828125 : ℚ)
  | 8, 2 => (5763163317591055312507980776 / 385434722900390625 : ℚ)
  | 8, 3 => (4659576734560620666940707349112 / 375798854827880859375 : ℚ)
  | 8, 4 => (95411950161524406741070881542992 / 9150946140289306640625 : ℚ)
  | 9, 0 => (58694602996753985464576 / 2565453515625 : ℚ)
  | 9, 1 => (3621078207661448457880192 / 192409013671875 : ℚ)
  | 9, 2 => (5552849064373674207624664672 / 360766900634765625 : ℚ)
  | 9, 3 => (340682793473597100455362071712 / 27057517547607421875 : ℚ)
  | 9, 4 => (40638601486944044108014795976512 / 3902526569366455078125 : ℚ)
  | 10, 0 => (42210669242142236416 / 1759168125 : ℚ)
  | 10, 1 => (18078563064507196314496 / 923563265625 : ℚ)
  | 10, 2 => (27416504652600346334214784 / 1731681123046875 : ℚ)
  | 10, 3 => (1657590320891528443584290176 / 129876084228515625 : ℚ)
  | 10, 4 => (2523359009501662832325768942592 / 243517657928466796875 : ℚ)
  | 11, 0 => (225380930486130176 / 8955765 : ℚ)
  | 11, 1 => (2734518336499132672 / 134336475 : ℚ)
  | 11, 2 => (20493496747837298757632 / 1259404453125 : ℚ)
  | 11, 3 => (1219540569166078205566976 / 94455333984375 : ℚ)
  | 11, 4 => (259783166240396155055303168 / 25300535888671875 : ℚ)
  | 12, 0 => (15759468169840000 / 597051 : ℚ)
  | 12, 1 => (189529552697264768 / 8955765 : ℚ)
  | 12, 2 => (18706637628808921216 / 1119470625 : ℚ)
  | 12, 3 => (16413568581884003013248 / 1259404453125 : ℚ)
  | 12, 4 => (4782081322287198028816768 / 472276669921875 : ℚ)
  | 13, 0 => (3814596340880000 / 137781 : ℚ)
  | 13, 1 => (1298866531740800 / 59049 : ℚ)
  | 13, 2 => (75925223241673088 / 4428675 : ℚ)
  | 13, 3 => (30512798455419231104 / 2325054375 : ℚ)
  | 13, 4 => (43287953671486264527488 / 4359476953125 : ℚ)
  | 14, 0 => (571597930000000 / 19683 : ℚ)
  | 14, 1 => (1349662116400000 / 59049 : ℚ)
  | 14, 2 => (3112728984576640 / 177147 : ℚ)
  | 14, 3 => (35019398765856128 / 2657205 : ℚ)
  | 14, 4 => (48197718487789602944 / 4982259375 : ℚ)
  | _, _ => 0

theorem c4MarginCoreCoeff_floor : ∀ i ∈ Finset.range (14 + 1), ∀ j ∈ Finset.range (4 + 1), (1508567502465215332642075158709747237 / 157160684466361999511718750 : ℚ) ≤ c4MarginCoreCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4MarginCoreCoeff]

theorem c4MarginCore_representation (u v : ℝ) :
    c4MarginCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 14 4 c4MarginCoreCoeff u v := by
  norm_num [c4MarginCorePolynomial, bernsteinBoxEval, c4MarginCoreCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4MarginCore_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < c4MarginCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [c4MarginCore_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (1508567502465215332642075158709747237 / 157160684466361999511718750 : ℚ)) hu0 hu1 hv0 hv1 c4MarginCoreCoeff_floor

theorem c4MarginCore_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ ((10 : ℝ) / 3))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < c4MarginCorePolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((29 : ℝ) / 150)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((29 : ℝ) / 150))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := c4MarginCore_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base0UpperPolynomial (x y : ℝ) : ℝ :=
  ((-3 : ℝ) + ((2 : ℝ) * x) + ((12 : ℝ) * y) + ((-32 : ℝ) * x * y))

def base0UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (82 / 25 : ℚ)
  | 0, 1 => (245447 / 75000 : ℚ)
  | 1, 0 => 7
  | 1, 1 => (20963 / 3000 : ℚ)
  | _, _ => 0

theorem base0UpperCoeff_floor : ∀ i ∈ Finset.range (1 + 1), ∀ j ∈ Finset.range (1 + 1), (245447 / 75000 : ℚ) ≤ base0UpperCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base0UpperCoeff]

theorem base0Upper_representation (u v : ℝ) :
    base0UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 1 1 base0UpperCoeff u v := by
  norm_num [base0UpperPolynomial, bernsteinBoxEval, base0UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base0Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base0UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base0Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (245447 / 75000 : ℚ)) hu0 hu1 hv0 hv1 base0UpperCoeff_floor

theorem base0Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base0UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base0Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base0LowerPolynomial (x y : ℝ) : ℝ :=
  ((-9 : ℝ) + ((-12 : ℝ) * y) + ((6 : ℝ) * x) + ((32 : ℝ) * x * y))

def base0LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (246 / 25 : ℚ)
  | 0, 1 => (738553 / 75000 : ℚ)
  | 1, 0 => 21
  | 1, 1 => (63037 / 3000 : ℚ)
  | _, _ => 0

theorem base0LowerCoeff_floor : ∀ i ∈ Finset.range (1 + 1), ∀ j ∈ Finset.range (1 + 1), (246 / 25 : ℚ) ≤ base0LowerCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base0LowerCoeff]

theorem base0Lower_representation (u v : ℝ) :
    base0LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 1 1 base0LowerCoeff u v := by
  norm_num [base0LowerPolynomial, bernsteinBoxEval, base0LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base0Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base0LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base0Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (246 / 25 : ℚ)) hu0 hu1 hv0 hv1 base0LowerCoeff_floor

theorem base0Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base0LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base0Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base1UpperPolynomial (x y : ℝ) : ℝ :=
  (((-15 : ℝ) / 2) + ((-5 : ℝ) * x) + ((4 : ℝ) * (x ^ 2)) + ((30 : ℝ) * y) + ((-240 : ℝ) * x * y) + ((256 : ℝ) * y * (x ^ 2)))

def base1UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (10149 / 625 : ℚ)
  | 0, 1 => (61456643 / 3750000 : ℚ)
  | 1, 0 => (699 / 20 : ℚ)
  | 1, 1 => (1056181 / 30000 : ℚ)
  | 2, 0 => (135 / 2 : ℚ)
  | 2, 1 => (81523 / 1200 : ℚ)
  | _, _ => 0

theorem base1UpperCoeff_floor : ∀ i ∈ Finset.range (2 + 1), ∀ j ∈ Finset.range (1 + 1), (10149 / 625 : ℚ) ≤ base1UpperCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base1UpperCoeff]

theorem base1Upper_representation (u v : ℝ) :
    base1UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 2 1 base1UpperCoeff u v := by
  norm_num [base1UpperPolynomial, bernsteinBoxEval, base1UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base1Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base1UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base1Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (10149 / 625 : ℚ)) hu0 hu1 hv0 hv1 base1UpperCoeff_floor

theorem base1Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base1UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base1Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base1LowerPolynomial (x y : ℝ) : ℝ :=
  (((-45 : ℝ) / 2) + ((-30 : ℝ) * y) + ((-4 : ℝ) * (x ^ 2)) + ((25 : ℝ) * x) + ((-256 : ℝ) * y * (x ^ 2)) + ((240 : ℝ) * x * y))

def base1LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (10351 / 625 : ℚ)
  | 0, 1 => (61543357 / 3750000 : ℚ)
  | 1, 0 => (329 / 20 : ℚ)
  | 1, 1 => (485819 / 30000 : ℚ)
  | 2, 0 => (5 / 2 : ℚ)
  | 2, 1 => (2477 / 1200 : ℚ)
  | _, _ => 0

theorem base1LowerCoeff_floor : ∀ i ∈ Finset.range (2 + 1), ∀ j ∈ Finset.range (1 + 1), (2477 / 1200 : ℚ) ≤ base1LowerCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base1LowerCoeff]

theorem base1Lower_representation (u v : ℝ) :
    base1LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 2 1 base1LowerCoeff u v := by
  norm_num [base1LowerPolynomial, bernsteinBoxEval, base1LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base1Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base1LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base1Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (2477 / 1200 : ℚ)) hu0 hu1 hv0 hv1 base1LowerCoeff_floor

theorem base1Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base1LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base1Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base2UpperPolynomial (x y : ℝ) : ℝ :=
  (((-165 : ℝ) / 4) + ((-8 : ℝ) * (x ^ 3)) + ((56 : ℝ) * (x ^ 2)) + ((75 : ℝ) * y) + (((-85 : ℝ) / 2) * x) + ((-2048 : ℝ) * y * (x ^ 3)) + ((-1320 : ℝ) * x * y) + ((3584 : ℝ) * y * (x ^ 2)))

def base2UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (4055139 / 31250 : ℚ)
  | 0, 1 => (23828688367 / 187500000 : ℚ)
  | 1, 0 => (436863 / 2500 : ℚ)
  | 1, 1 => (1275239603 / 7500000 : ℚ)
  | 2, 0 => (987 / 5 : ℚ)
  | 2, 1 => (3782841 / 20000 : ℚ)
  | 3, 0 => (585 / 4 : ℚ)
  | 3, 1 => (63283 / 480 : ℚ)
  | _, _ => 0

theorem base2UpperCoeff_floor : ∀ i ∈ Finset.range (3 + 1), ∀ j ∈ Finset.range (1 + 1), (23828688367 / 187500000 : ℚ) ≤ base2UpperCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base2UpperCoeff]

theorem base2Upper_representation (u v : ℝ) :
    base2UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 3 1 base2UpperCoeff u v := by
  norm_num [base2UpperPolynomial, bernsteinBoxEval, base2UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base2Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base2UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base2Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (23828688367 / 187500000 : ℚ)) hu0 hu1 hv0 hv1 base2UpperCoeff_floor

theorem base2Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base2UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base2Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base2LowerPolynomial (x y : ℝ) : ℝ :=
  (((-315 : ℝ) / 4) + ((-75 : ℝ) * y) + ((-56 : ℝ) * (x ^ 2)) + ((8 : ℝ) * (x ^ 3)) + (((245 : ℝ) / 2) * x) + ((-3584 : ℝ) * y * (x ^ 2)) + ((1320 : ℝ) * x * y) + ((2048 : ℝ) * y * (x ^ 3)))

def base2LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (44861 / 31250 : ℚ)
  | 0, 1 => (771311633 / 187500000 : ℚ)
  | 1, 0 => (15137 / 2500 : ℚ)
  | 1, 1 => (80760397 / 7500000 : ℚ)
  | 2, 0 => 33
  | 2, 1 => (825159 / 20000 : ℚ)
  | 3, 0 => (535 / 4 : ℚ)
  | 3, 1 => (71117 / 480 : ℚ)
  | _, _ => 0

theorem base2LowerCoeff_floor : ∀ i ∈ Finset.range (3 + 1), ∀ j ∈ Finset.range (1 + 1), (44861 / 31250 : ℚ) ≤ base2LowerCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base2LowerCoeff]

theorem base2Lower_representation (u v : ℝ) :
    base2LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 3 1 base2LowerCoeff u v := by
  norm_num [base2LowerPolynomial, bernsteinBoxEval, base2LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base2Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base2LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base2Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (44861 / 31250 : ℚ)) hu0 hu1 hv0 hv1 base2LowerCoeff_floor

theorem base2Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base2LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base2Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base3UpperPolynomial (x y : ℝ) : ℝ :=
  (((-4425 : ℝ) / 8) + ((-180 : ℝ) * (x ^ 3)) + ((16 : ℝ) * (x ^ 4)) + ((529 : ℝ) * (x ^ 2)) + (((-35 : ℝ) / 4) * x) + (((375 : ℝ) / 2) * y) + ((-46080 : ℝ) * y * (x ^ 3)) + ((-6540 : ℝ) * x * y) + ((16384 : ℝ) * y * (x ^ 4)) + ((33856 : ℝ) * y * (x ^ 2)))

def base3UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (965421679 / 1562500 : ℚ)
  | 0, 1 => (6167200272523 / 9375000000 : ℚ)
  | 1, 0 => (60418549 / 100000 : ℚ)
  | 1, 1 => (5084559029 / 7500000 : ℚ)
  | 2, 0 => (4636039 / 10000 : ℚ)
  | 2, 1 => (8977379137 / 15000000 : ℚ)
  | 3, 0 => (7355 / 32 : ℚ)
  | 3, 1 => (7119229 / 15000 : ℚ)
  | 4, 0 => (1025 / 8 : ℚ)
  | 4, 1 => (546511 / 960 : ℚ)
  | _, _ => 0

theorem base3UpperCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (1 + 1), (1025 / 8 : ℚ) ≤ base3UpperCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base3UpperCoeff]

theorem base3Upper_representation (u v : ℝ) :
    base3UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 4 1 base3UpperCoeff u v := by
  norm_num [base3UpperPolynomial, bernsteinBoxEval, base3UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base3Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base3UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base3Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (1025 / 8 : ℚ)) hu0 hu1 hv0 hv1 base3UpperCoeff_floor

theorem base3Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base3UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base3Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base3LowerPolynomial (x y : ℝ) : ℝ :=
  (((-5175 : ℝ) / 8) + ((-529 : ℝ) * (x ^ 2)) + ((-16 : ℝ) * (x ^ 4)) + ((180 : ℝ) * (x ^ 3)) + (((-375 : ℝ) / 2) * y) + (((3235 : ℝ) / 4) * x) + ((-33856 : ℝ) * y * (x ^ 2)) + ((-16384 : ℝ) * y * (x ^ 4)) + ((6540 : ℝ) * x * y) + ((46080 : ℝ) * y * (x ^ 3)))

def base3LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (1084578321 / 1562500 : ℚ)
  | 0, 1 => (6132799727477 / 9375000000 : ℚ)
  | 1, 0 => (107981451 / 100000 : ℚ)
  | 1, 1 => (7545440971 / 7500000 : ℚ)
  | 2, 0 => (15923961 / 10000 : ℚ)
  | 2, 1 => (21862620863 / 15000000 : ℚ)
  | 3, 0 => (70341 / 32 : ℚ)
  | 3, 1 => (29300771 / 15000 : ℚ)
  | 4, 0 => (21375 / 8 : ℚ)
  | 4, 1 => (2141489 / 960 : ℚ)
  | _, _ => 0

theorem base3LowerCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (1 + 1), (6132799727477 / 9375000000 : ℚ) ≤ base3LowerCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base3LowerCoeff]

theorem base3Lower_representation (u v : ℝ) :
    base3LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 4 1 base3LowerCoeff u v := by
  norm_num [base3LowerPolynomial, bernsteinBoxEval, base3LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base3Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base3LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base3Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (6132799727477 / 9375000000 : ℚ)) hu0 hu1 hv0 hv1 base3LowerCoeff_floor

theorem base3Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base3LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base3Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base4UpperPolynomial (x y : ℝ) : ℝ :=
  (((-94125 : ℝ) / 16) + ((-2588 : ℝ) * (x ^ 3)) + ((-32 : ℝ) * (x ^ 5)) + ((528 : ℝ) * (x ^ 4)) + ((4256 : ℝ) * (x ^ 2)) + (((1875 : ℝ) / 4) * y) + (((16535 : ℝ) / 8) * x) + ((-662528 : ℝ) * y * (x ^ 3)) + ((-131072 : ℝ) * y * (x ^ 5)) + ((-30930 : ℝ) * x * y) + ((272384 : ℝ) * y * (x ^ 2)) + ((540672 : ℝ) * y * (x ^ 4)))

def base4UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (313071805519 / 78125000 : ℚ)
  | 0, 1 => (556198996631229 / 156250000000 : ℚ)
  | 1, 0 => (149367555553 / 31250000 : ℚ)
  | 1, 1 => (121166256277781 / 31250000000 : ℚ)
  | 2, 0 => (932687387 / 156250 : ℚ)
  | 2, 1 => (5240154495193 / 1250000000 : ℚ)
  | 3, 0 => (407371903 / 50000 : ℚ)
  | 3, 1 => (235576193181 / 50000000 : ℚ)
  | 4, 0 => (2389513 / 200 : ℚ)
  | 4, 1 => (2160639181 / 400000 : ℚ)
  | 5, 0 => (277625 / 16 : ℚ)
  | 5, 1 => (3220169 / 640 : ℚ)
  | _, _ => 0

theorem base4UpperCoeff_floor : ∀ i ∈ Finset.range (5 + 1), ∀ j ∈ Finset.range (1 + 1), (556198996631229 / 156250000000 : ℚ) ≤ base4UpperCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base4UpperCoeff]

theorem base4Upper_representation (u v : ℝ) :
    base4UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 5 1 base4UpperCoeff u v := by
  norm_num [base4UpperPolynomial, bernsteinBoxEval, base4UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base4Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base4UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base4Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (556198996631229 / 156250000000 : ℚ)) hu0 hu1 hv0 hv1 base4UpperCoeff_floor

theorem base4Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base4UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base4Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base4LowerPolynomial (x y : ℝ) : ℝ :=
  (((-97875 : ℝ) / 16) + ((-4256 : ℝ) * (x ^ 2)) + ((-528 : ℝ) * (x ^ 4)) + ((32 : ℝ) * (x ^ 5)) + ((2588 : ℝ) * (x ^ 3)) + (((-1875 : ℝ) / 4) * y) + (((47465 : ℝ) / 8) * x) + ((-540672 : ℝ) * y * (x ^ 4)) + ((-272384 : ℝ) * y * (x ^ 2)) + ((30930 : ℝ) * x * y) + ((131072 : ℝ) * y * (x ^ 5)) + ((662528 : ℝ) * y * (x ^ 3)))

def base4LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (711928194481 / 78125000 : ℚ)
  | 0, 1 => (1493801003368771 / 156250000000 : ℚ)
  | 1, 0 => (353632444447 / 31250000 : ℚ)
  | 1, 1 => (381833743722219 / 31250000000 : ℚ)
  | 2, 0 => (2047312613 / 156250 : ℚ)
  | 2, 1 => (18599845504807 / 1250000000 : ℚ)
  | 3, 0 => (695028097 / 50000 : ℚ)
  | 3, 1 => (866823806819 / 50000000 : ℚ)
  | 4, 0 => (2615287 / 200 : ℚ)
  | 4, 1 => (7848960819 / 400000 : ℚ)
  | 5, 0 => (170375 / 16 : ℚ)
  | 5, 1 => (14699831 / 640 : ℚ)
  | _, _ => 0

theorem base4LowerCoeff_floor : ∀ i ∈ Finset.range (5 + 1), ∀ j ∈ Finset.range (1 + 1), (711928194481 / 78125000 : ℚ) ≤ base4LowerCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base4LowerCoeff]

theorem base4Lower_representation (u v : ℝ) :
    base4LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 5 1 base4LowerCoeff u v := by
  norm_num [base4LowerPolynomial, bernsteinBoxEval, base4LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base4Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base4LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base4Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (711928194481 / 78125000 : ℚ)) hu0 hu1 hv0 hv1 base4LowerCoeff_floor

theorem base4Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base4LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base4Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base5UpperPolynomial (x y : ℝ) : ℝ :=
  (((-5750625 : ℝ) / 32) + ((-30510 : ℝ) * (x ^ 3)) + ((-1456 : ℝ) * (x ^ 5)) + ((64 : ℝ) * (x ^ 6)) + ((10720 : ℝ) * (x ^ 4)) + (((9375 : ℝ) / 8) * y) + (((126121 : ℝ) / 4) * (x ^ 2)) + (((1777065 : ℝ) / 16) * x) + ((-7810560 : ℝ) * y * (x ^ 3)) + ((-5963776 : ℝ) * y * (x ^ 5)) + ((-142935 : ℝ) * x * y) + ((1048576 : ℝ) * y * (x ^ 6)) + ((2017936 : ℝ) * y * (x ^ 2)) + ((10977280 : ℝ) * y * (x ^ 4)))

def base5UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (759255058262659 / 3906250000 : ℚ)
  | 0, 1 => (4612905402561614003 / 23437500000000 : ℚ)
  | 1, 0 => (149316517017191 / 625000000 : ℚ)
  | 1, 1 => (230207290574921197 / 937500000000 : ℚ)
  | 2, 0 => (3603165506751 / 12500000 : ℚ)
  | 2, 1 => (3801352452260157 / 12500000000 : ℚ)
  | 3, 0 => (342475733413 / 1000000 : ℚ)
  | 3, 1 => (566511307739201 / 1500000000 : ℚ)
  | 4, 0 => (4993828417 / 12500 : ℚ)
  | 4, 1 => (142239066278951 / 300000000 : ℚ)
  | 5, 0 => (145348839 / 320 : ℚ)
  | 5, 1 => (19435899167 / 32000 : ℚ)
  | 6, 0 => (16004225 / 32 : ℚ)
  | 6, 1 => (3098559767 / 3840 : ℚ)
  | _, _ => 0

theorem base5UpperCoeff_floor : ∀ i ∈ Finset.range (6 + 1), ∀ j ∈ Finset.range (1 + 1), (759255058262659 / 3906250000 : ℚ) ≤ base5UpperCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base5UpperCoeff]

theorem base5Upper_representation (u v : ℝ) :
    base5UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 6 1 base5UpperCoeff u v := by
  norm_num [base5UpperPolynomial, bernsteinBoxEval, base5UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base5Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base5UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base5Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (759255058262659 / 3906250000 : ℚ)) hu0 hu1 hv0 hv1 base5UpperCoeff_floor

theorem base5Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base5UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base5Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base5LowerPolynomial (x y : ℝ) : ℝ :=
  (((-5769375 : ℝ) / 32) + ((-10720 : ℝ) * (x ^ 4)) + ((-64 : ℝ) * (x ^ 6)) + ((1456 : ℝ) * (x ^ 5)) + ((30510 : ℝ) * (x ^ 3)) + (((-126121 : ℝ) / 4) * (x ^ 2)) + (((-9375 : ℝ) / 8) * y) + (((2062935 : ℝ) / 16) * x) + ((-10977280 : ℝ) * y * (x ^ 4)) + ((-2017936 : ℝ) * y * (x ^ 2)) + ((-1048576 : ℝ) * y * (x ^ 6)) + ((142935 : ℝ) * x * y) + ((5963776 : ℝ) * y * (x ^ 5)) + ((7810560 : ℝ) * y * (x ^ 3)))

def base5LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (778244941737341 / 3906250000 : ℚ)
  | 0, 1 => (4612094597438385997 / 23437500000000 : ℚ)
  | 1, 0 => (143183482982809 / 625000000 : ℚ)
  | 1, 1 => (208542709425078803 / 937500000000 : ℚ)
  | 2, 0 => (3176834493249 / 12500000 : ℚ)
  | 2, 1 => (2978647547739843 / 12500000000 : ℚ)
  | 3, 0 => (274324266587 / 1000000 : ℚ)
  | 3, 1 => (358688692260799 / 1500000000 : ℚ)
  | 4, 0 => (3646171583 / 12500 : ℚ)
  | 4, 1 => (65120933721049 / 300000000 : ℚ)
  | 5, 0 => (99643161 / 320 : ℚ)
  | 5, 1 => (5063300833 / 32000 : ℚ)
  | 6, 0 => (10875775 / 32 : ℚ)
  | 6, 1 => (127040233 / 3840 : ℚ)
  | _, _ => 0

theorem base5LowerCoeff_floor : ∀ i ∈ Finset.range (6 + 1), ∀ j ∈ Finset.range (1 + 1), (127040233 / 3840 : ℚ) ≤ base5LowerCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base5LowerCoeff]

theorem base5Lower_representation (u v : ℝ) :
    base5LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 6 1 base5LowerCoeff u v := by
  norm_num [base5LowerPolynomial, bernsteinBoxEval, base5LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base5Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base5LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base5Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (127040233 / 3840 : ℚ)) hu0 hu1 hv0 hv1 base5LowerCoeff_floor

theorem base5Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base5LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base5Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base6UpperPolynomial (x y : ℝ) : ℝ :=
  (((-191953125 : ℝ) / 64) + ((-39640 : ℝ) * (x ^ 5)) + ((-128 : ℝ) * (x ^ 7)) + ((3840 : ℝ) * (x ^ 6)) + ((173580 : ℝ) * (x ^ 4)) + (((-644791 : ℝ) / 2) * (x ^ 3)) + (((46875 : ℝ) / 16) * y) + (((445627 : ℝ) / 2) * (x ^ 2)) + (((62694835 : ℝ) / 32) * x) + ((-162365440 : ℝ) * y * (x ^ 5)) + ((-82533248 : ℝ) * y * (x ^ 3)) + ((-8388608 : ℝ) * y * (x ^ 7)) + ((14260064 : ℝ) * y * (x ^ 2)) + ((62914560 : ℝ) * y * (x ^ 6)) + ((177745920 : ℝ) * y * (x ^ 4)) + (((-1305165 : ℝ) / 2) * x * y))

def base6UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (671450032219849099 / 195312500000 : ℚ)
  | 0, 1 => (4063516997096216777407 / 1171875000000000 : ℚ)
  | 1, 0 => (88133202951909553 / 21875000000 : ℚ)
  | 1, 1 => (265890923140351255361 / 65625000000000 : ℚ)
  | 2, 0 => (1009238743628659 / 218750000 : ℚ)
  | 2, 1 => (1722914281303027547 / 375000000000 : ℚ)
  | 3, 0 => (905106931643699 / 175000000 : ℚ)
  | 3, 1 => (2637142194366888349 / 525000000000 : ℚ)
  | 4, 0 => (99355494941099 / 17500000 : ℚ)
  | 4, 1 => (545674256679275597 / 105000000000 : ℚ)
  | 5, 0 => (1708891601393 / 280000 : ℚ)
  | 5, 1 => (4074230191398133 / 840000000 : ℚ)
  | 6, 0 => (225226033 / 35 : ℚ)
  | 6, 1 => (23404793410349 / 6720000 : ℚ)
  | 7, 0 => (427532825 / 64 : ℚ)
  | 7, 1 => (202008359 / 1536 : ℚ)
  | _, _ => 0

theorem base6UpperCoeff_floor : ∀ i ∈ Finset.range (7 + 1), ∀ j ∈ Finset.range (1 + 1), (202008359 / 1536 : ℚ) ≤ base6UpperCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base6UpperCoeff]

theorem base6Upper_representation (u v : ℝ) :
    base6UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 7 1 base6UpperCoeff u v := by
  norm_num [base6UpperPolynomial, bernsteinBoxEval, base6UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base6Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base6UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base6Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (202008359 / 1536 : ℚ)) hu0 hu1 hv0 hv1 base6UpperCoeff_floor

theorem base6Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base6UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base6Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def base6LowerPolynomial (x y : ℝ) : ℝ :=
  (((-192046875 : ℝ) / 64) + ((-173580 : ℝ) * (x ^ 4)) + ((-3840 : ℝ) * (x ^ 6)) + ((128 : ℝ) * (x ^ 7)) + ((39640 : ℝ) * (x ^ 5)) + (((-445627 : ℝ) / 2) * (x ^ 2)) + (((-46875 : ℝ) / 16) * y) + (((644791 : ℝ) / 2) * (x ^ 3)) + (((65305165 : ℝ) / 32) * x) + ((-177745920 : ℝ) * y * (x ^ 4)) + ((-62914560 : ℝ) * y * (x ^ 6)) + ((-14260064 : ℝ) * y * (x ^ 2)) + ((8388608 : ℝ) * y * (x ^ 7)) + ((82533248 : ℝ) * y * (x ^ 3)) + ((162365440 : ℝ) * y * (x ^ 5)) + (((1305165 : ℝ) / 2) * x * y))

def base6LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (609799967780150901 / 195312500000 : ℚ)
  | 0, 1 => (3623983002903783222593 / 1171875000000000 : ℚ)
  | 1, 0 => (78616797048090447 / 21875000000 : ℚ)
  | 1, 1 => (234359076859648744639 / 65625000000000 : ℚ)
  | 2, 0 => (890761256371341 / 218750000 : ℚ)
  | 2, 1 => (10739600030878807171 / 2625000000000 : ℚ)
  | 3, 0 => (800893068356301 / 175000000 : ℚ)
  | 3, 1 => (2480857805633111651 / 525000000000 : ℚ)
  | 4, 0 => (89844505058901 / 17500000 : ℚ)
  | 4, 1 => (589525743320724403 / 105000000000 : ℚ)
  | 5, 0 => (1615908398607 / 280000 : ℚ)
  | 5, 1 => (5900169808601867 / 840000000 : ℚ)
  | 6, 0 => (227573967 / 35 : ℚ)
  | 6, 1 => (9076115227093 / 960000 : ℚ)
  | 7, 0 => (468467175 / 64 : ℚ)
  | 7, 1 => (21301991641 / 1536 : ℚ)
  | _, _ => 0

theorem base6LowerCoeff_floor : ∀ i ∈ Finset.range (7 + 1), ∀ j ∈ Finset.range (1 + 1), (3623983002903783222593 / 1171875000000000 : ℚ) ≤ base6LowerCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [base6LowerCoeff]

theorem base6Lower_representation (u v : ℝ) :
    base6LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 7 1 base6LowerCoeff u v := by
  norm_num [base6LowerPolynomial, bernsteinBoxEval, base6LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem base6Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base6LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base6Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (3623983002903783222593 / 1171875000000000 : ℚ)) hu0 hu1 hv0 hv1 base6LowerCoeff_floor

theorem base6Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base6LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base6Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def f2OuterPolynomial (x y : ℝ) : ℝ :=
  (((-518400 : ℝ) * (x ^ 4)) + ((-411648 : ℝ) * (x ^ 6)) + ((-36864 : ℝ) * (x ^ 8)) + ((4096 : ℝ) * (x ^ 9)) + ((146880 : ℝ) * (x ^ 3)) + ((156672 : ℝ) * (x ^ 7)) + ((642816 : ℝ) * (x ^ 5)) + ((-13056834797568 : ℝ) * (x ^ 8) * (y ^ 5)) + ((-9895604649984 : ℝ) * (x ^ 8) * (y ^ 6)) + ((-6906307411968 : ℝ) * (x ^ 6) * (y ^ 6)) + ((-6509019267072 : ℝ) * (x ^ 6) * (y ^ 5)) + ((-4696546738176 : ℝ) * (x ^ 10) * (y ^ 5)) + ((-2116175265792 : ℝ) * (x ^ 8) * (y ^ 4)) + ((-2062440529920 : ℝ) * (x ^ 6) * (y ^ 4)) + ((-543581798400 : ℝ) * (x ^ 4) * (y ^ 6)) + ((-526170193920 : ℝ) * (x ^ 4) * (y ^ 5)) + ((-331681935360 : ℝ) * (x ^ 6) * (y ^ 3)) + ((-217021317120 : ℝ) * (x ^ 4) * (y ^ 4)) + ((-199313326080 : ℝ) * (x ^ 10) * (y ^ 4)) + ((-168488304640 : ℝ) * (x ^ 9) * (y ^ 3)) + ((-68797071360 : ℝ) * (x ^ 11) * (y ^ 3)) + ((-47060766720 : ℝ) * (x ^ 4) * (y ^ 3)) + ((-35351101440 : ℝ) * (x ^ 6) * (y ^ 2)) + ((-31525650432 : ℝ) * (x ^ 8) * (y ^ 3)) + ((-26499612672 : ℝ) * (x ^ 8) * (y ^ 2)) + ((-5115985920 : ℝ) * (x ^ 4) * (y ^ 2)) + ((-2972712960 : ℝ) * (x ^ 10) * (y ^ 2)) + ((-1023662592 : ℝ) * y * (x ^ 6)) + ((-579391488 : ℝ) * y * (x ^ 8)) + ((-206219520 : ℝ) * y * (x ^ 4)) + ((-50651136 : ℝ) * y * (x ^ 10)) + ((5308416 : ℝ) * y * (x ^ 11)) + ((21876480 : ℝ) * y * (x ^ 3)) + ((222130176 : ℝ) * y * (x ^ 9)) + ((339738624 : ℝ) * (x ^ 11) * (y ^ 2)) + ((570240000 : ℝ) * (x ^ 3) * (y ^ 2)) + ((646154496 : ℝ) * y * (x ^ 5)) + ((966131712 : ℝ) * y * (x ^ 7)) + ((5438361600 : ℝ) * (x ^ 3) * (y ^ 3)) + ((11514347520 : ℝ) * (x ^ 9) * (y ^ 2)) + ((12230590464 : ℝ) * (x ^ 12) * (y ^ 3)) + ((18707189760 : ℝ) * (x ^ 5) * (y ^ 2)) + ((21743271936 : ℝ) * (x ^ 11) * (y ^ 4)) + ((23954227200 : ℝ) * (x ^ 3) * (y ^ 4)) + ((38503710720 : ℝ) * (x ^ 3) * (y ^ 6)) + ((38740377600 : ℝ) * (x ^ 7) * (y ^ 2)) + ((49474437120 : ℝ) * (x ^ 3) * (y ^ 5)) + ((162203959296 : ℝ) * (x ^ 10) * (y ^ 3)) + ((175433195520 : ℝ) * (x ^ 5) * (y ^ 3)) + ((293549137920 : ℝ) * (x ^ 7) * (y ^ 3)) + ((843180933120 : ℝ) * (x ^ 9) * (y ^ 4)) + ((878934343680 : ℝ) * (x ^ 5) * (y ^ 4)) + ((1391569403904 : ℝ) * (x ^ 11) * (y ^ 5)) + ((2415350513664 : ℝ) * (x ^ 5) * (y ^ 5)) + ((2696165720064 : ℝ) * (x ^ 5) * (y ^ 6)) + ((2816353566720 : ℝ) * (x ^ 7) * (y ^ 4)) + ((4398046511104 : ℝ) * (x ^ 9) * (y ^ 6)) + ((9428526956544 : ℝ) * (x ^ 9) * (y ^ 5)) + ((10514079940608 : ℝ) * (x ^ 7) * (y ^ 6)) + ((11508192903168 : ℝ) * (x ^ 7) * (y ^ 5)))

def f2OuterCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => 1111160000
  | 0, 1 => 2538216000
  | 0, 2 => 2542363200
  | 0, 3 => 1473362880
  | 0, 4 => 546624000
  | 0, 5 => 135058176
  | 0, 6 => 22275072
  | 0, 7 => 2368512
  | 0, 8 => 147456
  | 0, 9 => 4096
  | 0, 10 => 0
  | 0, 11 => 0
  | 0, 12 => 0
  | 1, 0 => (83476419134 / 75 : ℚ)
  | 1, 1 => (317889232404 / 125 : ℚ)
  | 1, 2 => (1592648110734 / 625 : ℚ)
  | 1, 3 => (4617483714658 / 3125 : ℚ)
  | 1, 4 => (1714559867988 / 3125 : ℚ)
  | 1, 5 => (2121001469418 / 15625 : ℚ)
  | 1, 6 => (350631027564 / 15625 : ℚ)
  | 1, 7 => (37453140096 / 15625 : ℚ)
  | 1, 8 => (2357750016 / 15625 : ℚ)
  | 1, 9 => (204991264 / 46875 : ℚ)
  | 1, 10 => (209472 / 15625 : ℚ)
  | 1, 11 => (4608 / 15625 : ℚ)
  | 1, 12 => 0
  | 2, 0 => (15677969907074333 / 14062500 : ℚ)
  | 2, 1 => (19906341896725143 / 7812500 : ℚ)
  | 2, 2 => (99769953443806627 / 39062500 : ℚ)
  | 2, 3 => (868257853356228979 / 585937500 : ℚ)
  | 2, 4 => (134446858958960023 / 244140625 : ℚ)
  | 2, 5 => (33308109960167511 / 244140625 : ℚ)
  | 2, 6 => (5518969980299596 / 244140625 : ℚ)
  | 2, 7 => (592160690973932 / 244140625 : ℚ)
  | 2, 8 => (188398477565584 / 1220703125 : ℚ)
  | 2, 9 => (10217936371408 / 2197265625 : ℚ)
  | 2, 10 => (6546028416 / 244140625 : ℚ)
  | 2, 11 => (720003072 / 1220703125 : ℚ)
  | 2, 12 => 0
  | 3, 0 => (9422466875022668964133 / 8437500000000 : ℚ)
  | 3, 1 => (19944607114459550311623 / 7812500000000 : ℚ)
  | 3, 2 => (49999701034501340599867 / 19531250000000 : ℚ)
  | 3, 3 => (2612212599227589407793001 / 1757812500000000 : ℚ)
  | 3, 4 => (809662396906022436818477 / 1464843750000000 : ℚ)
  | 3, 5 => (200853441010218674966023 / 1464843750000000 : ℚ)
  | 3, 6 => (66711966286560420166067 / 2929687500000000 : ℚ)
  | 3, 7 => (3594696785580585483151 / 1464843750000000 : ℚ)
  | 3, 8 => (577793318107479885653 / 3662109375000000 : ℚ)
  | 3, 9 => (16240368922859968349 / 3295898437500000 : ℚ)
  | 3, 10 => (3068464142339517 / 76293945312500 : ℚ)
  | 3, 11 => (3375028804698 / 3814697265625 : ℚ)
  | 3, 12 => (432 / 19073486328125 : ℚ)
  | 4, 0 => (8848267448365384741318325597 / 7910156250000000000 : ℚ)
  | 4, 1 => (11240365881649130577441430751 / 4394531250000000000 : ℚ)
  | 4, 2 => (1409468242453185414560921141 / 549316406250000000 : ℚ)
  | 4, 3 => (122796173764628250452037211783 / 82397460937500000000 : ℚ)
  | 4, 4 => (304741375342135844798951028307 / 549316406250000000000 : ℚ)
  | 4, 5 => (75696836814972863972998648837 / 549316406250000000000 : ℚ)
  | 4, 6 => (1574913216507908641286541229 / 68664550781250000000 : ℚ)
  | 4, 7 => (340915294055699056427108639 / 137329101562500000000 : ℚ)
  | 4, 8 => (2306216079099248216389943 / 14305114746093750000 : ℚ)
  | 4, 9 => (201021578305873517019779 / 38623809814453125000 : ℚ)
  | 4, 10 => (5753395250659783213 / 107288360595703125 : ℚ)
  | 4, 11 => (1054701004404375016 / 894069671630859375 : ℚ)
  | 4, 12 => (1728 / 19073486328125 : ℚ)
  | 5, 0 => (3323614624438954797316856023296757 / 2966308593750000000000000 : ℚ)
  | 5, 1 => (469245435675999448305334649781451 / 183105468750000000000000 : ℚ)
  | 5, 2 => (10595211921599688851002839542181277 / 4119873046875000000000000 : ℚ)
  | 5, 3 => (23089665966759055725181875789786133 / 15449523925781250000000000 : ℚ)
  | 5, 4 => (22939452162440060881910647786778347 / 41198730468750000000000000 : ℚ)
  | 5, 5 => (9509204589897559217801204117690611 / 68664550781250000000000000 : ℚ)
  | 5, 6 => (2379397240457267407516234286715133 / 102996826171875000000000000 : ℚ)
  | 5, 7 => (32327606240630989845140797897231 / 12874603271484375000000000 : ℚ)
  | 5, 8 => (132492794049263421485417041579 / 804662704467773437500000 : ℚ)
  | 5, 9 => (19849352603422504143797082841 / 3620982170104980468750000 : ℚ)
  | 5, 10 => (374571630131482200651317 / 5587935447692871093750 : ℚ)
  | 5, 11 => (12359830181352539812508 / 8381903171539306640625 : ℚ)
  | 5, 12 => (864 / 3814697265625 : ℚ)
  | 6, 0 => (19506615261684607237694595156314660501 / 17380714416503906250000000000 : ℚ)
  | 6, 1 => (459123340886525831608295829410443883 / 178813934326171875000000000 : ℚ)
  | 6, 2 => (165928316352959963906383830322447693201 / 64373016357421875000000000000 : ℚ)
  | 6, 3 => (4341571866681222652842490524444272642353 / 2896785736083984375000000000000 : ℚ)
  | 6, 4 => (107921727883135001410721683009551278107 / 193119049072265625000000000000 : ℚ)
  | 6, 5 => (671927696119650795597514732274667038621 / 4827976226806640625000000000000 : ℚ)
  | 6, 6 => (56166206528122473818345799440540503549 / 2413988113403320312500000000000 : ℚ)
  | 6, 7 => (383137581869323280189765420387098831 / 150874257087707519531250000000 : ℚ)
  | 6, 8 => (3170178713128177370086476550176739 / 18859282135963439941406250000 : ℚ)
  | 6, 9 => (488740807011893206867390067484887 / 84866769611835479736328125000 : ℚ)
  | 6, 10 => (224743954350232212110201 / 2793967723846435546875 : ℚ)
  | 6, 11 => (4943953193818360125016 / 2793967723846435546875 : ℚ)
  | 6, 12 => (1728 / 3814697265625 : ℚ)
  | _, _ => 0

theorem f2OuterCoeff_const_floor : ∀ j ∈ Finset.range (6 + 1), 1111160000 ≤ f2OuterCoeff j 0 := by
  intro j hj
  interval_cases j <;> norm_num [f2OuterCoeff]

theorem f2OuterCoeff_nonneg : ∀ j ∈ Finset.range (6 + 1), ∀ k ∈ Finset.range (12 + 1), 0 ≤ f2OuterCoeff j k := by
  intro j hj k hk
  interval_cases j <;> interval_cases k <;> norm_num [f2OuterCoeff]

theorem f2Outer_representation (v z : ℝ) :
    f2OuterPolynomial (z + 5) (v / 3000000) =
      bernsteinHalfstripEval 6 12 f2OuterCoeff v z := by
  norm_num [f2OuterPolynomial, bernsteinHalfstripEval, f2OuterCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem f2Outer_pos {v z : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hz : 0 ≤ z) :
    0 < f2OuterPolynomial (z + 5) (v / 3000000) := by
  rw [f2Outer_representation]
  exact bernsteinHalfstripEval_pos (by norm_num : (0 : ℚ) < 1111160000) hv0 hv1 hz f2OuterCoeff_const_floor f2OuterCoeff_nonneg

theorem f2Outer_region_pos {x y : ℝ}
    (hx : (5 : ℝ) ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 3000000) :
    0 < f2OuterPolynomial x y := by
  let v := y / (1 / 3000000)
  let z := x - 5
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < 1 / 3000000)]
    exact hy1
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have h := f2Outer_pos hv0 hv1 hz
  dsimp [v, z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def f2MarginOuterPolynomial (x y : ℝ) : ℝ :=
  ((-729000 : ℝ) + ((-4860000 : ℝ) * (x ^ 2)) + ((-2678400 : ℝ) * (x ^ 4)) + ((-475648 : ℝ) * (x ^ 6)) + ((-36864 : ℝ) * (x ^ 8)) + ((4096 : ℝ) * (x ^ 9)) + ((156672 : ℝ) * (x ^ 7)) + ((1218816 : ℝ) * (x ^ 5)) + ((2916000 : ℝ) * x) + ((4466880 : ℝ) * (x ^ 3)) + ((-13056834797568 : ℝ) * (x ^ 8) * (y ^ 5)) + ((-9895604649984 : ℝ) * (x ^ 8) * (y ^ 6)) + ((-6906307411968 : ℝ) * (x ^ 6) * (y ^ 6)) + ((-6509019267072 : ℝ) * (x ^ 6) * (y ^ 5)) + ((-4696546738176 : ℝ) * (x ^ 10) * (y ^ 5)) + ((-2116175265792 : ℝ) * (x ^ 8) * (y ^ 4)) + ((-2062440529920 : ℝ) * (x ^ 6) * (y ^ 4)) + ((-543581798400 : ℝ) * (x ^ 4) * (y ^ 6)) + ((-526170193920 : ℝ) * (x ^ 4) * (y ^ 5)) + ((-331681935360 : ℝ) * (x ^ 6) * (y ^ 3)) + ((-217021317120 : ℝ) * (x ^ 4) * (y ^ 4)) + ((-199313326080 : ℝ) * (x ^ 10) * (y ^ 4)) + ((-168488304640 : ℝ) * (x ^ 9) * (y ^ 3)) + ((-68797071360 : ℝ) * (x ^ 11) * (y ^ 3)) + ((-47060766720 : ℝ) * (x ^ 4) * (y ^ 3)) + ((-35351101440 : ℝ) * (x ^ 6) * (y ^ 2)) + ((-31525650432 : ℝ) * (x ^ 8) * (y ^ 3)) + ((-26499612672 : ℝ) * (x ^ 8) * (y ^ 2)) + ((-5115985920 : ℝ) * (x ^ 4) * (y ^ 2)) + ((-2972712960 : ℝ) * (x ^ 10) * (y ^ 2)) + ((-1023662592 : ℝ) * y * (x ^ 6)) + ((-579391488 : ℝ) * y * (x ^ 8)) + ((-206219520 : ℝ) * y * (x ^ 4)) + ((-50651136 : ℝ) * y * (x ^ 10)) + ((5308416 : ℝ) * y * (x ^ 11)) + ((21876480 : ℝ) * y * (x ^ 3)) + ((222130176 : ℝ) * y * (x ^ 9)) + ((339738624 : ℝ) * (x ^ 11) * (y ^ 2)) + ((570240000 : ℝ) * (x ^ 3) * (y ^ 2)) + ((646154496 : ℝ) * y * (x ^ 5)) + ((966131712 : ℝ) * y * (x ^ 7)) + ((5438361600 : ℝ) * (x ^ 3) * (y ^ 3)) + ((11514347520 : ℝ) * (x ^ 9) * (y ^ 2)) + ((12230590464 : ℝ) * (x ^ 12) * (y ^ 3)) + ((18707189760 : ℝ) * (x ^ 5) * (y ^ 2)) + ((21743271936 : ℝ) * (x ^ 11) * (y ^ 4)) + ((23954227200 : ℝ) * (x ^ 3) * (y ^ 4)) + ((38503710720 : ℝ) * (x ^ 3) * (y ^ 6)) + ((38740377600 : ℝ) * (x ^ 7) * (y ^ 2)) + ((49474437120 : ℝ) * (x ^ 3) * (y ^ 5)) + ((162203959296 : ℝ) * (x ^ 10) * (y ^ 3)) + ((175433195520 : ℝ) * (x ^ 5) * (y ^ 3)) + ((293549137920 : ℝ) * (x ^ 7) * (y ^ 3)) + ((843180933120 : ℝ) * (x ^ 9) * (y ^ 4)) + ((878934343680 : ℝ) * (x ^ 5) * (y ^ 4)) + ((1391569403904 : ℝ) * (x ^ 11) * (y ^ 5)) + ((2415350513664 : ℝ) * (x ^ 5) * (y ^ 5)) + ((2696165720064 : ℝ) * (x ^ 5) * (y ^ 6)) + ((2816353566720 : ℝ) * (x ^ 7) * (y ^ 4)) + ((4398046511104 : ℝ) * (x ^ 9) * (y ^ 6)) + ((9428526956544 : ℝ) * (x ^ 9) * (y ^ 5)) + ((10514079940608 : ℝ) * (x ^ 7) * (y ^ 6)) + ((11508192903168 : ℝ) * (x ^ 7) * (y ^ 5)))

def f2MarginOuterCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => 993511000
  | 0, 1 => 2336532000
  | 0, 2 => 2398303200
  | 0, 3 => 1418482880
  | 0, 4 => 534864000
  | 0, 5 => 133714176
  | 0, 6 => 22211072
  | 0, 7 => 2368512
  | 0, 8 => 147456
  | 0, 9 => 4096
  | 0, 10 => 0
  | 0, 11 => 0
  | 0, 12 => 0
  | 1, 0 => (74652744134 / 75 : ℚ)
  | 1, 1 => (292678732404 / 125 : ℚ)
  | 1, 2 => (1502610610734 / 625 : ℚ)
  | 1, 3 => (4445983714658 / 3125 : ℚ)
  | 1, 4 => (1677809867988 / 3125 : ℚ)
  | 1, 5 => (2100001469418 / 15625 : ℚ)
  | 1, 6 => (349631027564 / 15625 : ℚ)
  | 1, 7 => (37453140096 / 15625 : ℚ)
  | 1, 8 => (2357750016 / 15625 : ℚ)
  | 1, 9 => (204991264 / 46875 : ℚ)
  | 1, 10 => (209472 / 15625 : ℚ)
  | 1, 11 => (4608 / 15625 : ℚ)
  | 1, 12 => 0
  | 2, 0 => (14023530844574333 / 14062500 : ℚ)
  | 2, 1 => (18330685646725143 / 7812500 : ℚ)
  | 2, 2 => (94142609693806627 / 39062500 : ℚ)
  | 2, 3 => (836101603356228979 / 585937500 : ℚ)
  | 2, 4 => (131575765208960023 / 244140625 : ℚ)
  | 2, 5 => (32979984960167511 / 244140625 : ℚ)
  | 2, 6 => (5503344980299596 / 244140625 : ℚ)
  | 2, 7 => (592160690973932 / 244140625 : ℚ)
  | 2, 8 => (188398477565584 / 1220703125 : ℚ)
  | 2, 9 => (10217936371408 / 2197265625 : ℚ)
  | 2, 10 => (6546028416 / 244140625 : ℚ)
  | 2, 11 => (720003072 / 1220703125 : ℚ)
  | 2, 12 => 0
  | 3, 0 => (8429803437522668964133 / 8437500000000 : ℚ)
  | 3, 1 => (18368950864459550311623 / 7812500000000 : ℚ)
  | 3, 2 => (47186029159501340599867 / 19531250000000 : ℚ)
  | 3, 3 => (2515743849227589407793001 / 1757812500000000 : ℚ)
  | 3, 4 => (792435834406022436818477 / 1464843750000000 : ℚ)
  | 3, 5 => (198884691010218674966023 / 1464843750000000 : ℚ)
  | 3, 6 => (66524466286560420166067 / 2929687500000000 : ℚ)
  | 3, 7 => (3594696785580585483151 / 1464843750000000 : ℚ)
  | 3, 8 => (577793318107479885653 / 3662109375000000 : ℚ)
  | 3, 9 => (16240368922859968349 / 3295898437500000 : ℚ)
  | 3, 10 => (3068464142339517 / 76293945312500 : ℚ)
  | 3, 11 => (3375028804698 / 3814697265625 : ℚ)
  | 3, 12 => (432 / 19073486328125 : ℚ)
  | 4, 0 => (7917645475709134741318325597 / 7910156250000000000 : ℚ)
  | 4, 1 => (10354059241024130577441430751 / 4394531250000000000 : ℚ)
  | 4, 2 => (1330333720968810414560921141 / 549316406250000000 : ℚ)
  | 4, 3 => (118274201108378250452037211783 / 82397460937500000000 : ℚ)
  | 4, 4 => (298281414404635844798951028307 / 549316406250000000000 : ℚ)
  | 4, 5 => (74958555564972863972998648837 / 549316406250000000000 : ℚ)
  | 4, 6 => (1570518685257908641286541229 / 68664550781250000000 : ℚ)
  | 4, 7 => (340915294055699056427108639 / 137329101562500000000 : ℚ)
  | 4, 8 => (2306216079099248216389943 / 14305114746093750000 : ℚ)
  | 4, 9 => (201021578305873517019779 / 38623809814453125000 : ℚ)
  | 4, 10 => (5753395250659783213 / 107288360595703125 : ℚ)
  | 4, 11 => (1054701004404375016 / 894069671630859375 : ℚ)
  | 4, 12 => (1728 / 19073486328125 : ℚ)
  | 5, 0 => (2974631384692861047316856023296757 / 2966308593750000000000000 : ℚ)
  | 5, 1 => (432315992316624448305334649781451 / 183105468750000000000000 : ℚ)
  | 5, 2 => (10001703010466876351002839542181277 / 4119873046875000000000000 : ℚ)
  | 5, 3 => (22241796093712180725181875789786133 / 15449523925781250000000000 : ℚ)
  | 5, 4 => (22454955092127560881910647786778347 / 41198730468750000000000000 : ℚ)
  | 5, 5 => (9416919433647559217801204117690611 / 68664550781250000000000000 : ℚ)
  | 5, 6 => (2372805443582267407516234286715133 / 102996826171875000000000000 : ℚ)
  | 5, 7 => (32327606240630989845140797897231 / 12874603271484375000000000 : ℚ)
  | 5, 8 => (132492794049263421485417041579 / 804662704467773437500000 : ℚ)
  | 5, 9 => (19849352603422504143797082841 / 3620982170104980468750000 : ℚ)
  | 5, 10 => (374571630131482200651317 / 5587935447692871093750 : ℚ)
  | 5, 11 => (12359830181352539812508 / 8381903171539306640625 : ℚ)
  | 5, 12 => (864 / 3814697265625 : ℚ)
  | 6, 0 => (17461791591297339171288345156314660501 / 17380714416503906250000000000 : ℚ)
  | 6, 1 => (423059431355886183170795829410443883 / 178813934326171875000000000 : ℚ)
  | 6, 2 => (156654739616509768593883830322447693201 / 64373016357421875000000000000 : ℚ)
  | 6, 3 => (4182596265484933590342490524444272642353 / 2896785736083984375000000000000 : ℚ)
  | 6, 4 => (105650647866045157660721683009551278107 / 193119049072265625000000000000 : ℚ)
  | 6, 5 => (665438896070822670597514732274667038621 / 4827976226806640625000000000000 : ℚ)
  | 6, 6 => (56011711288864661318345799440540503549 / 2413988113403320312500000000000 : ℚ)
  | 6, 7 => (383137581869323280189765420387098831 / 150874257087707519531250000000 : ℚ)
  | 6, 8 => (3170178713128177370086476550176739 / 18859282135963439941406250000 : ℚ)
  | 6, 9 => (488740807011893206867390067484887 / 84866769611835479736328125000 : ℚ)
  | 6, 10 => (224743954350232212110201 / 2793967723846435546875 : ℚ)
  | 6, 11 => (4943953193818360125016 / 2793967723846435546875 : ℚ)
  | 6, 12 => (1728 / 3814697265625 : ℚ)
  | _, _ => 0

theorem f2MarginOuterCoeff_const_floor : ∀ j ∈ Finset.range (6 + 1), 993511000 ≤ f2MarginOuterCoeff j 0 := by
  intro j hj
  interval_cases j <;> norm_num [f2MarginOuterCoeff]

theorem f2MarginOuterCoeff_nonneg : ∀ j ∈ Finset.range (6 + 1), ∀ k ∈ Finset.range (12 + 1), 0 ≤ f2MarginOuterCoeff j k := by
  intro j hj k hk
  interval_cases j <;> interval_cases k <;> norm_num [f2MarginOuterCoeff]

theorem f2MarginOuter_representation (v z : ℝ) :
    f2MarginOuterPolynomial (z + 5) (v / 3000000) =
      bernsteinHalfstripEval 6 12 f2MarginOuterCoeff v z := by
  norm_num [f2MarginOuterPolynomial, bernsteinHalfstripEval, f2MarginOuterCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem f2MarginOuter_pos {v z : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hz : 0 ≤ z) :
    0 < f2MarginOuterPolynomial (z + 5) (v / 3000000) := by
  rw [f2MarginOuter_representation]
  exact bernsteinHalfstripEval_pos (by norm_num : (0 : ℚ) < 993511000) hv0 hv1 hz f2MarginOuterCoeff_const_floor f2MarginOuterCoeff_nonneg

theorem f2MarginOuter_region_pos {x y : ℝ}
    (hx : (5 : ℝ) ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 3000000) :
    0 < f2MarginOuterPolynomial x y := by
  let v := y / (1 / 3000000)
  let z := x - 5
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < 1 / 3000000)]
    exact hy1
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have h := f2MarginOuter_pos hv0 hv1 hz
  dsimp [v, z] at h
  convert h using 1 <;> field_simp <;> ring


/-! ## Natural exponential curve and exact two-mode jet -/

theorem qTwoModeNumerator_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < qCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact qCore_box_pos hx0 hsplit (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    have h := qMid_box_pos hlow hx5 (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_22000 hlow).le
    simpa [qCorePolynomial, qMidPolynomial] using h

theorem f2TwoModeNumerator_pos {x : ℝ} (hx0 : (157 / 50 : ℝ) ≤ x) :
    0 < f2CorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact f2Core_box_pos hx0 hsplit (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    by_cases hfive : x ≤ (5 : ℝ)
    · have h := f2Mid_box_pos hlow hfive (Real.exp_pos _).le
        (exp_neg_three_mul_lt_inv_22000 hlow).le
      simpa [f2CorePolynomial, f2MidPolynomial] using h
    · have h5low : (5 : ℝ) ≤ x := (lt_of_not_ge hfive).le
      have h := f2Outer_region_pos h5low (Real.exp_pos _).le
        (exp_neg_three_mul_lt_inv_3000000 h5low).le
      simpa [f2CorePolynomial, f2OuterPolynomial] using h

theorem c4TwoModeNumerator_pos_core {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx1 : x ≤ 10 / 3) :
    0 < c4CorePolynomial x (Real.exp (-3 * x)) :=
  c4Core_box_pos hx0 hx1 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le

noncomputable def twoModeNormalizedJet (j : ℕ) (x y : ℝ) : ℝ :=
  ((PF4.certPoly j).eval x + 4 * y * (PF4.certPoly j).eval (4 * x)) /
    (2 * x - 3)

theorem clearedQ_twoModeNormalizedJet (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedQ
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) =
      qCorePolynomial x y / (2 * x - 3) ^ 2 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedQ, qCorePolynomial]
  field_simp [hx]
  ring

theorem clearedF2_twoModeNormalizedJet (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedF2
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) (twoModeNormalizedJet 3 x y)
        (twoModeNormalizedJet 4 x y) =
      f2CorePolynomial x y / (2 * x - 3) ^ 6 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedF2, f2CorePolynomial]
  field_simp [hx]
  ring

theorem clearedC4_twoModeNormalizedJet (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedC4
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) (twoModeNormalizedJet 3 x y)
        (twoModeNormalizedJet 4 x y) (twoModeNormalizedJet 5 x y)
        (twoModeNormalizedJet 6 x y) =
      c4CorePolynomial x y / (2 * x - 3) ^ 4 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedC4, c4CorePolynomial]
  field_simp [hx]
  ring

theorem two_mul_sub_three_pos {x : ℝ} (hx : (157 / 50 : ℝ) ≤ x) :
    0 < 2 * x - 3 := by linarith

theorem clearedQ_twoMode_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x))) := by
  rw [clearedQ_twoModeNormalizedJet _ _ (two_mul_sub_three_pos hx0).ne']
  exact div_pos (qTwoModeNumerator_pos_to_five hx0 hx5)
    (pow_pos (two_mul_sub_three_pos hx0) 2)

theorem clearedF2_twoMode_pos {x : ℝ} (hx0 : (157 / 50 : ℝ) ≤ x) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x))) := by
  rw [clearedF2_twoModeNormalizedJet _ _ (two_mul_sub_three_pos hx0).ne']
  exact div_pos (f2TwoModeNumerator_pos hx0)
    (pow_pos (two_mul_sub_three_pos hx0) 6)

theorem clearedC4_twoMode_pos_core {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx1 : x ≤ 10 / 3) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 5 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 6 x (Real.exp (-3 * x))) := by
  rw [clearedC4_twoModeNormalizedJet _ _ (two_mul_sub_three_pos hx0).ne']
  exact div_pos (c4TwoModeNumerator_pos_core hx0 hx1)
    (pow_pos (two_mul_sub_three_pos hx0) 4)

/-! ## Certified quantitative two-mode margins -/

theorem qTwoModeMarginNumerator_pos_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    0 < qMarginCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact qMarginCore_box_pos hx0 hsplit (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    have h := qMarginMid_box_pos hlow hx5 (Real.exp_pos _).le
      (exp_neg_three_mul_lt_inv_22000 hlow).le
    simpa [qMarginCorePolynomial, qMarginMidPolynomial] using h

theorem f2TwoModeMarginNumerator_pos {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) :
    0 < f2MarginCorePolynomial x (Real.exp (-3 * x)) := by
  by_cases hsplit : x ≤ (10 / 3 : ℝ)
  · exact f2MarginCore_box_pos hx0 hsplit
      (inv_23000_lt_exp_neg_three_mul hsplit).le
      (exp_neg_three_mul_lt_inv_12000 hx0).le
  · have hlow : (10 / 3 : ℝ) ≤ x := (lt_of_not_ge hsplit).le
    by_cases hfive : x ≤ (5 : ℝ)
    · have h := f2MarginMid_box_pos hlow hfive (Real.exp_pos _).le
        (exp_neg_three_mul_lt_inv_22000 hlow).le
      simpa [f2MarginCorePolynomial, f2MarginMidPolynomial] using h
    · have h5low : (5 : ℝ) ≤ x := (lt_of_not_ge hfive).le
      have h := f2MarginOuter_region_pos h5low (Real.exp_pos _).le
        (exp_neg_three_mul_lt_inv_3000000 h5low).le
      simpa [f2MarginCorePolynomial, f2MarginOuterPolynomial] using h

theorem c4TwoModeMarginNumerator_pos_core {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx1 : x ≤ 10 / 3) :
    0 < c4MarginCorePolynomial x (Real.exp (-3 * x)) :=
  c4MarginCore_box_pos hx0 hx1 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le

theorem clearedQ_twoMode_sub_ten (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedQ
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) - 10 =
      qMarginCorePolynomial x y / (2 * x - 3) ^ 2 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedQ, qMarginCorePolynomial]
  field_simp [hx]
  ring

theorem clearedF2_twoMode_sub_thousand (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedF2
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) (twoModeNormalizedJet 3 x y)
        (twoModeNormalizedJet 4 x y) - 1000 =
      f2MarginCorePolynomial x y / (2 * x - 3) ^ 6 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedF2, f2MarginCorePolynomial]
  field_simp [hx]
  ring

theorem clearedC4_twoMode_sub_margin (x y : ℝ) (hx : 2 * x - 3 ≠ 0) :
    PF4.ClearedJetCertificateBridge.clearedC4
        (twoModeNormalizedJet 0 x y) (twoModeNormalizedJet 1 x y)
        (twoModeNormalizedJet 2 x y) (twoModeNormalizedJet 3 x y)
        (twoModeNormalizedJet 4 x y) (twoModeNormalizedJet 5 x y)
        (twoModeNormalizedJet 6 x y) - 50000000 =
      c4MarginCorePolynomial x y / (2 * x - 3) ^ 4 := by
  simp [twoModeNormalizedJet, PF4.certPoly,
    PF4.ClearedJetCertificateBridge.clearedC4, c4MarginCorePolynomial]
  field_simp [hx]
  ring

theorem clearedQ_twoMode_gt_ten_to_five {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    10 < PF4.ClearedJetCertificateBridge.clearedQ
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x))) := by
  rw [← sub_pos, clearedQ_twoMode_sub_ten _ _ (two_mul_sub_three_pos hx0).ne']
  exact div_pos (qTwoModeMarginNumerator_pos_to_five hx0 hx5)
    (pow_pos (two_mul_sub_three_pos hx0) 2)

theorem clearedF2_twoMode_gt_thousand {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) :
    1000 < PF4.ClearedJetCertificateBridge.clearedF2
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x))) := by
  rw [← sub_pos, clearedF2_twoMode_sub_thousand _ _
    (two_mul_sub_three_pos hx0).ne']
  exact div_pos (f2TwoModeMarginNumerator_pos hx0)
    (pow_pos (two_mul_sub_three_pos hx0) 6)

theorem clearedC4_twoMode_gt_margin_core {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx1 : x ≤ 10 / 3) :
    50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (twoModeNormalizedJet 0 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 1 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 2 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 3 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 4 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 5 x (Real.exp (-3 * x)))
      (twoModeNormalizedJet 6 x (Real.exp (-3 * x))) := by
  rw [← sub_pos, clearedC4_twoMode_sub_margin _ _
    (two_mul_sub_three_pos hx0).ne']
  exact div_pos (c4TwoModeMarginNumerator_pos_core hx0 hx1)
    (pow_pos (two_mul_sub_three_pos hx0) 4)

theorem abs_twoModeNormalizedJet_0_le_coreBase {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    |twoModeNormalizedJet 0 x (Real.exp (-3 * x))| ≤ 2 := by
  have hupper := base0Upper_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  have hlower := base0Lower_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  rw [abs_le]
  constructor
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [le_div_iff₀ hden]
    simpa [base0LowerPolynomial, PF4.certPoly] using hlower.le
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [div_le_iff₀ hden]
    simpa [base0UpperPolynomial, PF4.certPoly] using hupper.le

theorem abs_twoModeNormalizedJet_1_le_coreBase {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    |twoModeNormalizedJet 1 x (Real.exp (-3 * x))| ≤ 5 := by
  have hupper := base1Upper_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  have hlower := base1Lower_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  rw [abs_le]
  constructor
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [le_div_iff₀ hden]
    simpa [base1LowerPolynomial, PF4.certPoly] using hlower.le
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [div_le_iff₀ hden]
    simpa [base1UpperPolynomial, PF4.certPoly] using hupper.le

theorem abs_twoModeNormalizedJet_2_le_coreBase {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    |twoModeNormalizedJet 2 x (Real.exp (-3 * x))| ≤ 20 := by
  have hupper := base2Upper_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  have hlower := base2Lower_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  rw [abs_le]
  constructor
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [le_div_iff₀ hden]
    simpa [base2LowerPolynomial, PF4.certPoly] using hlower.le
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [div_le_iff₀ hden]
    simpa [base2UpperPolynomial, PF4.certPoly] using hupper.le

theorem abs_twoModeNormalizedJet_3_le_coreBase {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    |twoModeNormalizedJet 3 x (Real.exp (-3 * x))| ≤ 200 := by
  have hupper := base3Upper_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  have hlower := base3Lower_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  rw [abs_le]
  constructor
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [le_div_iff₀ hden]
    simpa [base3LowerPolynomial, PF4.certPoly] using hlower.le
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [div_le_iff₀ hden]
    simpa [base3UpperPolynomial, PF4.certPoly] using hupper.le

theorem abs_twoModeNormalizedJet_4_le_coreBase {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    |twoModeNormalizedJet 4 x (Real.exp (-3 * x))| ≤ 2000 := by
  have hupper := base4Upper_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  have hlower := base4Lower_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  rw [abs_le]
  constructor
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [le_div_iff₀ hden]
    simpa [base4LowerPolynomial, PF4.certPoly] using hlower.le
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [div_le_iff₀ hden]
    simpa [base4UpperPolynomial, PF4.certPoly] using hupper.le

theorem abs_twoModeNormalizedJet_5_le_coreBase {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    |twoModeNormalizedJet 5 x (Real.exp (-3 * x))| ≤ 60000 := by
  have hupper := base5Upper_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  have hlower := base5Lower_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  rw [abs_le]
  constructor
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [le_div_iff₀ hden]
    simpa [base5LowerPolynomial, PF4.certPoly] using hlower.le
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [div_le_iff₀ hden]
    simpa [base5UpperPolynomial, PF4.certPoly] using hupper.le

theorem abs_twoModeNormalizedJet_6_le_coreBase {x : ℝ}
    (hx0 : (157 / 50 : ℝ) ≤ x) (hx5 : x ≤ 5) :
    |twoModeNormalizedJet 6 x (Real.exp (-3 * x))| ≤ 1000000 := by
  have hupper := base6Upper_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  have hlower := base6Lower_box_pos hx0 hx5 (Real.exp_pos _).le
    (exp_neg_three_mul_lt_inv_12000 hx0).le
  rw [abs_le]
  constructor
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [le_div_iff₀ hden]
    simpa [base6LowerPolynomial, PF4.certPoly] using hlower.le
  · rw [twoModeNormalizedJet]
    have hden := two_mul_sub_three_pos hx0
    rw [div_le_iff₀ hden]
    simpa [base6UpperPolynomial, PF4.certPoly] using hupper.le

end PF4.CERT12Inequalities.Generated


set_option linter.style.header false

/-!
# Deterministic polynomial perturbation certificates

This file formalizes the triangle/telescoping calculation used by CERT12.
It turns coordinate bounds for a base jet and an error jet into a rationally
computable error budget for any finite list of monomials.
-/

namespace PF4.CERT12Inequalities.Perturbation

open Finset

theorem abs_prod_sub_prod_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x y M : ι → ℝ)
    (hx : ∀ i ∈ s, |x i| ≤ M i)
    (hy : ∀ i ∈ s, |y i| ≤ M i)
    (hM : ∀ i ∈ s, 0 ≤ M i) :
    |(∏ i ∈ s, x i) - ∏ i ∈ s, y i| ≤
      ∑ i ∈ s, |x i - y i| * ∏ j ∈ s.erase i, M j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hxa := hx a (mem_insert_self a s)
      have hya := hy a (mem_insert_self a s)
      have hMa := hM a (mem_insert_self a s)
      have hxs : ∀ i ∈ s, |x i| ≤ M i :=
        fun i hi => hx i (mem_insert_of_mem hi)
      have hys : ∀ i ∈ s, |y i| ≤ M i :=
        fun i hi => hy i (mem_insert_of_mem hi)
      have hMs : ∀ i ∈ s, 0 ≤ M i :=
        fun i hi => hM i (mem_insert_of_mem hi)
      rw [prod_insert ha, prod_insert ha]
      calc
        |x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i| =
            |(x a - y a) * ∏ i ∈ s, x i +
              y a * ((∏ i ∈ s, x i) - ∏ i ∈ s, y i)| := by
                congr 1
                ring
        _ ≤ |x a - y a| * |∏ i ∈ s, x i| +
              |y a| * |(∏ i ∈ s, x i) - ∏ i ∈ s, y i| := by
                simpa [abs_mul] using abs_add_le
                  ((x a - y a) * ∏ i ∈ s, x i)
                  (y a * ((∏ i ∈ s, x i) - ∏ i ∈ s, y i))
        _ ≤ |x a - y a| * ∏ i ∈ s, M i +
              M a * (∑ i ∈ s,
                |x i - y i| * ∏ j ∈ s.erase i, M j) := by
                gcongr
                · rw [abs_prod]
                  exact prod_le_prod (fun i hi => abs_nonneg _) hxs
                · exact abs_nonneg _
                · exact ih hxs hys hMs
        _ = ∑ i ∈ insert a s,
              |x i - y i| * ∏ j ∈ (insert a s).erase i, M j := by
                rw [sum_insert ha]
                simp only [erase_insert_eq_erase, erase_same, prod_insert]
                rw [erase_eq_of_not_mem ha]
                apply congrArg (fun z => |x a - y a| * ∏ i ∈ s, M i + z)
                rw [mul_sum]
                apply sum_congr rfl
                intro i hi
                have hia : i ≠ a := fun h => ha (h ▸ hi)
                rw [erase_insert hia]
                rw [prod_insert]
                · ring
                · exact not_mem_erase _ _

structure Monomial (n : ℕ) where
  coeff : ℚ
  powers : Fin n → ℕ

noncomputable def monomialValue {n : ℕ} (p : Fin n → ℕ)
    (a : Fin n → ℝ) : ℝ :=
  ∏ i, a i ^ p i

noncomputable def monomialErrorBudget {n : ℕ} (p : Fin n → ℕ)
    (B E : Fin n → ℝ) : ℝ :=
  ∑ i, (E i * p i * (B i + E i) ^ (p i - 1)) *
    ∏ j ∈ Finset.univ.erase i, (B j + E j) ^ p j

theorem abs_pow_add_sub_pow_le
    {a e B E : ℝ} {p : ℕ}
    (hB : 0 ≤ B) (hE : 0 ≤ E) (ha : |a| ≤ B) (he : |e| ≤ E) :
    |(a + e) ^ p - a ^ p| ≤ E * p * (B + E) ^ (p - 1) := by
  have hae : |a + e| ≤ B + E :=
    (abs_add a e).trans (add_le_add ha he)
  have ha' : |a| ≤ B + E := ha.trans (le_add_of_nonneg_right hE)
  calc
    |(a + e) ^ p - a ^ p| ≤
        |a + e - a| * p * max |a + e| |a| ^ (p - 1) :=
      abs_pow_sub_pow_le
    _ ≤ E * p * (B + E) ^ (p - 1) := by
      simp only [add_sub_cancel_left]
      gcongr
      · exact he
      · exact max_le hae ha'

theorem abs_monomialValue_add_sub_le
    {n : ℕ} (p : Fin n → ℕ) (a e B E : Fin n → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hE : ∀ i, 0 ≤ E i)
    (ha : ∀ i, |a i| ≤ B i) (he : ∀ i, |e i| ≤ E i) :
    |monomialValue p (fun i => a i + e i) - monomialValue p a| ≤
      monomialErrorBudget p B E := by
  classical
  unfold monomialValue monomialErrorBudget
  apply (abs_prod_sub_prod_le Finset.univ
    (fun i => (a i + e i) ^ p i)
    (fun i => a i ^ p i)
    (fun i => (B i + E i) ^ p i) ?_ ?_ ?_).trans
  · intro i hi
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add _ _).trans
      (add_le_add (ha i) (he i))) _
  · intro i hi
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((ha i).trans
      (le_add_of_nonneg_right (hE i))) _
  · intro i hi
    positivity
  · apply sum_le_sum
    intro i hi
    gcongr
    exact abs_pow_add_sub_pow_le (hB i) (hE i) (ha i) (he i)

noncomputable def polynomialValue {n m : ℕ} (terms : Fin m → Monomial n)
    (a : Fin n → ℝ) : ℝ :=
  ∑ r, (terms r).coeff * monomialValue (terms r).powers a

noncomputable def polynomialErrorBudget {n m : ℕ}
    (terms : Fin m → Monomial n) (B E : Fin n → ℝ) : ℝ :=
  ∑ r, |((terms r).coeff : ℝ)| *
    monomialErrorBudget (terms r).powers B E

theorem abs_polynomialValue_add_sub_le
    {n m : ℕ} (terms : Fin m → Monomial n) (a e B E : Fin n → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hE : ∀ i, 0 ≤ E i)
    (ha : ∀ i, |a i| ≤ B i) (he : ∀ i, |e i| ≤ E i) :
    |polynomialValue terms (fun i => a i + e i) - polynomialValue terms a| ≤
      polynomialErrorBudget terms B E := by
  unfold polynomialValue polynomialErrorBudget
  rw [← sum_sub_distrib]
  calc
    |∑ r, ((terms r).coeff : ℝ) *
        monomialValue (terms r).powers (fun i => a i + e i) -
        ((terms r).coeff : ℝ) * monomialValue (terms r).powers a| ≤
      ∑ r, |((terms r).coeff : ℝ) *
        monomialValue (terms r).powers (fun i => a i + e i) -
        ((terms r).coeff : ℝ) * monomialValue (terms r).powers a| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, |((terms r).coeff : ℝ)| *
        monomialErrorBudget (terms r).powers B E := by
      apply sum_le_sum
      intro r hr
      rw [← mul_sub, abs_mul]
      gcongr
      exact abs_monomialValue_add_sub_le _ _ _ _ _ hB hE ha he

end PF4.CERT12Inequalities.Perturbation


namespace PF4.CERT12Inequalities.Perturbation.Generated

open PF4.CERT12Inequalities.Perturbation

def coreB : Fin 7 → ℝ := ![2, 5, 20, 200, 2000, 60000, 1000000]
def coreE : Fin 7 → ℝ := ![(7 / 1000000000 : ℝ), (1 / 2500000 : ℝ), (1 / 5000 : ℝ), (7 / 10000 : ℝ), (3 / 100 : ℝ), (11 / 10 : ℝ), 41]
def outerB : Fin 7 → ℝ := ![4, 40, 400, 4000, 40000, 400000, 4000000]
def outerE : Fin 7 → ℝ := ![(81 / 50000000000000000 : ℝ), (729 / 5000000000000000 : ℝ), (6561 / 500000000000000 : ℝ), (59049 / 50000000000000 : ℝ), (531441 / 5000000000000 : ℝ), (4782969 / 500000000000 : ℝ), (43046721 / 50000000000 : ℝ)]
def qTerms : Fin 2 → Monomial 7 :=
  ![{ coeff := -1; powers := ![1, 0, 1, 0, 0, 0, 0] }, { coeff := 1; powers := ![0, 2, 0, 0, 0, 0, 0] }]
theorem qTerms_value (a : Fin 7 → ℝ) :
    polynomialValue qTerms a =
      PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2) := by
  simp [polynomialValue, qTerms, monomialValue, Fin.sum_univ_succ, Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.clearedQ]
  ring

theorem qCoreBudget_lt :
    polynomialErrorBudget qTerms coreB coreE < 10 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, qTerms, coreB, coreE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_q_perturbation_lt_core
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i) :
    |PF4.ClearedJetCertificateBridge.clearedQ (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) - PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2)| < 10 := by
  have h := abs_polynomialValue_add_sub_le qTerms a e coreB coreE
    (by intro i; fin_cases i <;> norm_num [coreB])
    (by intro i; fin_cases i <;> norm_num [coreE]) ha he
  rw [qTerms_value, qTerms_value] at h
  exact h.trans_lt qCoreBudget_lt

theorem qOuterBudget_lt :
    polynomialErrorBudget qTerms outerB outerE < 10 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, qTerms, outerB, outerE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_q_perturbation_lt_outer
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ outerB i) (he : ∀ i, |e i| ≤ outerE i) :
    |PF4.ClearedJetCertificateBridge.clearedQ (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) - PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2)| < 10 := by
  have h := abs_polynomialValue_add_sub_le qTerms a e outerB outerE
    (by intro i; fin_cases i <;> norm_num [outerB])
    (by intro i; fin_cases i <;> norm_num [outerE]) ha he
  rw [qTerms_value, qTerms_value] at h
  exact h.trans_lt qOuterBudget_lt

def f2Terms : Fin 8 → Monomial 7 :=
  ![{ coeff := -1; powers := ![4, 0, 1, 0, 1, 0, 0] }, { coeff := 1; powers := ![4, 0, 0, 2, 0, 0, 0] }, { coeff := 1; powers := ![3, 2, 0, 0, 1, 0, 0] }, { coeff := -2; powers := ![3, 1, 1, 1, 0, 0, 0] }, { coeff := 2; powers := ![3, 0, 3, 0, 0, 0, 0] }, { coeff := -3; powers := ![2, 2, 2, 0, 0, 0, 0] }, { coeff := 3; powers := ![1, 4, 1, 0, 0, 0, 0] }, { coeff := -1; powers := ![0, 6, 0, 0, 0, 0, 0] }]
theorem f2Terms_value (a : Fin 7 → ℝ) :
    polynomialValue f2Terms a =
      PF4.ClearedJetCertificateBridge.clearedF2 (a 0) (a 1) (a 2) (a 3) (a 4) := by
  simp [polynomialValue, f2Terms, monomialValue, Fin.sum_univ_succ, Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.clearedF2]
  ring

theorem f2CoreBudget_lt :
    polynomialErrorBudget f2Terms coreB coreE < 1000 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, f2Terms, coreB, coreE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_f2_perturbation_lt_core
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i) :
    |PF4.ClearedJetCertificateBridge.clearedF2 (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) - PF4.ClearedJetCertificateBridge.clearedF2 (a 0) (a 1) (a 2) (a 3) (a 4)| < 1000 := by
  have h := abs_polynomialValue_add_sub_le f2Terms a e coreB coreE
    (by intro i; fin_cases i <;> norm_num [coreB])
    (by intro i; fin_cases i <;> norm_num [coreE]) ha he
  rw [f2Terms_value, f2Terms_value] at h
  exact h.trans_lt f2CoreBudget_lt

theorem f2OuterBudget_lt :
    polynomialErrorBudget f2Terms outerB outerE < 1000 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, f2Terms, outerB, outerE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_f2_perturbation_lt_outer
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ outerB i) (he : ∀ i, |e i| ≤ outerE i) :
    |PF4.ClearedJetCertificateBridge.clearedF2 (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) - PF4.ClearedJetCertificateBridge.clearedF2 (a 0) (a 1) (a 2) (a 3) (a 4)| < 1000 := by
  have h := abs_polynomialValue_add_sub_le f2Terms a e outerB outerE
    (by intro i; fin_cases i <;> norm_num [outerB])
    (by intro i; fin_cases i <;> norm_num [outerE]) ha he
  rw [f2Terms_value, f2Terms_value] at h
  exact h.trans_lt f2OuterBudget_lt

def c4Terms : Fin 16 → Monomial 7 :=
  ![{ coeff := 1; powers := ![1, 0, 1, 0, 1, 0, 1] }, { coeff := -1; powers := ![1, 0, 1, 0, 0, 2, 0] }, { coeff := -1; powers := ![1, 0, 0, 2, 0, 0, 1] }, { coeff := 2; powers := ![1, 0, 0, 1, 1, 1, 0] }, { coeff := -1; powers := ![1, 0, 0, 0, 3, 0, 0] }, { coeff := -1; powers := ![0, 2, 0, 0, 1, 0, 1] }, { coeff := 1; powers := ![0, 2, 0, 0, 0, 2, 0] }, { coeff := 2; powers := ![0, 1, 1, 1, 0, 0, 1] }, { coeff := -2; powers := ![0, 1, 1, 0, 1, 1, 0] }, { coeff := -2; powers := ![0, 1, 0, 2, 0, 1, 0] }, { coeff := 2; powers := ![0, 1, 0, 1, 2, 0, 0] }, { coeff := -1; powers := ![0, 0, 3, 0, 0, 0, 1] }, { coeff := 2; powers := ![0, 0, 2, 1, 0, 1, 0] }, { coeff := 1; powers := ![0, 0, 2, 0, 2, 0, 0] }, { coeff := -3; powers := ![0, 0, 1, 2, 1, 0, 0] }, { coeff := 1; powers := ![0, 0, 0, 4, 0, 0, 0] }]
theorem c4Terms_value (a : Fin 7 → ℝ) :
    polynomialValue c4Terms a =
      PF4.ClearedJetCertificateBridge.clearedC4 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) := by
  simp [polynomialValue, c4Terms, monomialValue, Fin.sum_univ_succ, Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.clearedC4]
  ring

theorem c4CoreBudget_lt :
    polynomialErrorBudget c4Terms coreB coreE < 50000000 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, c4Terms, coreB, coreE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_c4_perturbation_lt_core
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i) :
    |PF4.ClearedJetCertificateBridge.clearedC4 (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) (a 5 + e 5) (a 6 + e 6) - PF4.ClearedJetCertificateBridge.clearedC4 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)| < 50000000 := by
  have h := abs_polynomialValue_add_sub_le c4Terms a e coreB coreE
    (by intro i; fin_cases i <;> norm_num [coreB])
    (by intro i; fin_cases i <;> norm_num [coreE]) ha he
  rw [c4Terms_value, c4Terms_value] at h
  exact h.trans_lt c4CoreBudget_lt

theorem c4OuterBudget_lt :
    polynomialErrorBudget c4Terms outerB outerE < 50000000 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, c4Terms, outerB, outerE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_c4_perturbation_lt_outer
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ outerB i) (he : ∀ i, |e i| ≤ outerE i) :
    |PF4.ClearedJetCertificateBridge.clearedC4 (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) (a 5 + e 5) (a 6 + e 6) - PF4.ClearedJetCertificateBridge.clearedC4 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)| < 50000000 := by
  have h := abs_polynomialValue_add_sub_le c4Terms a e outerB outerE
    (by intro i; fin_cases i <;> norm_num [outerB])
    (by intro i; fin_cases i <;> norm_num [outerE]) ha he
  rw [c4Terms_value, c4Terms_value] at h
  exact h.trans_lt c4OuterBudget_lt


theorem clearedQ_pos_of_base_margin_and_core_error
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i)
    (hbase : 10 < PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2)) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) := by
  have h := abs_q_perturbation_lt_core a e ha he
  rw [abs_lt] at h
  linarith

theorem clearedF2_pos_of_base_margin_and_core_error
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i)
    (hbase : 1000 < PF4.ClearedJetCertificateBridge.clearedF2
      (a 0) (a 1) (a 2) (a 3) (a 4)) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) := by
  have h := abs_f2_perturbation_lt_core a e ha he
  rw [abs_lt] at h
  linarith

theorem clearedC4_pos_of_base_margin_and_core_error
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i)
    (hbase : 50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3)
      (a 4 + e 4) (a 5 + e 5) (a 6 + e 6) := by
  have h := abs_c4_perturbation_lt_core a e ha he
  rw [abs_lt] at h
  linarith

end PF4.CERT12Inequalities.Perturbation.Generated

set_option linter.style.header false
namespace PF4.RobustThreeModeClosure.Generated
open Finset PF4.CERT12Inequalities

def c4BandACoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (571597930000000 / 19683 : ℚ)
  | 0, 1 => (5557313882800000 / 216513 : ℚ)
  | 0, 2 => (53734106516306560 / 2381643 : ℚ)
  | 0, 3 => (2583469179049841024 / 130990365 : ℚ)
  | 0, 4 => (15443566539252696447104 / 900558759375 : ℚ)
  | 1, 0 => (4162038242000000 / 137781 : ℚ)
  | 1, 1 => (40318510999280000 / 1515591 : ℚ)
  | 1, 2 => (388118290974283904 / 16671501 : ℚ)
  | 1, 3 => (92794586763349250432 / 4584662775 : ℚ)
  | 1, 4 => (550999130074247941109888 / 31519556578125 : ℚ)
  | 2, 0 => (18760844854000000 / 597051 : ℚ)
  | 2, 1 => (181067812040272000 / 6567561 : ℚ)
  | 2, 2 => (4943231599084160 / 205821 : ℚ)
  | 2, 3 => (2062466234139771081344 / 99334360125 : ℚ)
  | 2, 4 => (2432057526338258629873024 / 136584745171875 : ℚ)
  | 3, 0 => (8363834802400000 / 255879 : ℚ)
  | 3, 1 => (562922015985568000 / 19702683 : ℚ)
  | 3, 2 => (26844333619739763968 / 1083647565 : ℚ)
  | 3, 3 => (906344040312806842112 / 42571868625 : ℚ)
  | 3, 4 => (37128668155294127764050176 / 2048771177578125 : ℚ)
  | 4, 0 => (95704503470560000 / 2814669 : ℚ)
  | 4, 1 => (916637365079142400 / 30961359 : ℚ)
  | 4, 2 => (1522528737297195279616 / 59600616075 : ℚ)
  | 4, 3 => (51090395172054959017984 / 2341452774375 : ℚ)
  | 4, 4 => (2076518014718031476442418432 / 112682414766796875 : ℚ)
  | 5, 0 => (232298618698374400 / 6567561 : ℚ)
  | 5, 1 => (2216133205140841984 / 72243171 : ℚ)
  | 5, 2 => (13080870174192137173888 / 496671800625 : ℚ)
  | 5, 3 => (3053014921275936184084096 / 136584745171875 : ℚ)
  | 5, 4 => (17579690852824486127665232896 / 939020123056640625 : ℚ)
  | 6, 0 => (3835708731650560 / 104247 : ℚ)
  | 6, 1 => (1275585580026000944 / 40135095 : ℚ)
  | 6, 2 => (7490552785445814889472 / 275928778125 : ℚ)
  | 6, 3 => (248089767699964876002128 / 10840059140625 : ℚ)
  | 6, 4 => (9911968907586766357530809984 / 521677846142578125 : ℚ)
  | 7, 0 => (3990121499191040 / 104247 : ℚ)
  | 7, 1 => (943909618990834649 / 28667925 : ℚ)
  | 7, 2 => (1102701348741973587562 / 39418396875 : ℚ)
  | 7, 3 => (1269387968867447657978531 / 54200295703125 : ℚ)
  | 7, 4 => (287108469348124416366777476 / 14905081318359375 : ℚ)
  | 8, 0 => (9685081276622720 / 243243 : ℚ)
  | 8, 1 => (2281479178949809922 / 66891825 : ℚ)
  | 8, 2 => (2650720299800298944068 / 91976259375 : ℚ)
  | 8, 3 => (3029272479957142080789734 / 126467356640625 : ℚ)
  | 8, 4 => (308356017168740259235060952 / 15808419580078125 : ℚ)
  | 9, 0 => (3358313094648704 / 81081 : ℚ)
  | 9, 1 => (7877037020341360561 / 222972750 : ℚ)
  | 9, 2 => (910025570857606370437 / 30658753125 : ℚ)
  | 9, 3 => (10320995458628612928898939 / 421557855468750 : ℚ)
  | 9, 4 => (5717497743066805104428079506 / 289821025634765625 : ℚ)
  | 10, 0 => (3493478878652032 / 81081 : ℚ)
  | 10, 1 => (4079027942081374252 / 111486375 : ℚ)
  | 10, 2 => (1874004600516915756343 / 61317506250 : ℚ)
  | 10, 3 => (10542607807672316714241119 / 421557855468750 : ℚ)
  | 10, 4 => (5774778800592589221353299417 / 289821025634765625 : ℚ)
  | 11, 0 => (110122962996224 / 2457 : ℚ)
  | 11, 1 => (39385571310614633 / 1039500 : ℚ)
  | 11, 2 => (116907946482590083081 / 3716212500 : ℚ)
  | 11, 3 => (29646493785898028426459 / 1161316406250 : ℚ)
  | 11, 4 => (352980303505694726385204523 / 17564910644531250 : ℚ)
  | 12, 0 => (12728138023936 / 273 : ℚ)
  | 12, 1 => (14726771771955016 / 375375 : ℚ)
  | 12, 2 => (3037877983114116169 / 93843750 : ℚ)
  | 12, 3 => (36960946323801064891223 / 1419386718750 : ℚ)
  | 12, 4 => (19746655315298524118663881 / 975828369140625 : ℚ)
  | 13, 0 => (1018464428032 / 21 : ℚ)
  | 13, 1 => (1172852312963281 / 28875 : ℚ)
  | 13, 2 => (120192186329956742 / 3609375 : ℚ)
  | 13, 3 => (1448964482790663574741 / 54591796875 : ℚ)
  | 13, 4 => (1526941586557473539035612 / 75063720703125 : ℚ)
  | 14, 0 => 50448102400
  | 14, 1 => (57816325760608 / 1375 : ℚ)
  | 14, 2 => (64741086186884743 / 1890625 : ℚ)
  | 14, 3 => (70270666557816949627 / 2599609375 : ℚ)
  | 14, 4 => (72956550199729163943274 / 3574462890625 : ℚ)
  | _, _ => 0

theorem c4BandACoeff_floor : ∀ i ∈ Finset.range (14+1), ∀ j ∈ Finset.range (4+1), (15443566539252696447104 / 900558759375 : ℚ) ≤ c4BandACoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4BandACoeff]

theorem c4BandA_representation (u v : ℝ) :
    PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial (((10 : ℝ) / 3)+((1 : ℝ) / 6)*u) (((1 : ℝ) / 22000)*v) = bernsteinBoxEval 14 4 c4BandACoeff u v := by
  norm_num [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, bernsteinBoxEval, c4BandACoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4BandA_box_pos {x y : ℝ} (hx0 : ((10 : ℝ) / 3) ≤ x) (hx1 : x ≤ ((7 : ℝ) / 2)) (hy0 : 0 ≤ y) (hy1 : y ≤ ((1 : ℝ) / 22000)) : 0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y := by
  let u := (x-((10 : ℝ) / 3))/((1 : ℝ) / 6)
  let v := y/((1 : ℝ) / 22000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 6))]; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 22000))]; exact hy1
  rw [show x=((10 : ℝ) / 3)+((1 : ℝ) / 6)*u by dsimp [u]; field_simp; ring, show y=((1 : ℝ) / 22000)*v by dsimp [v]; field_simp; ring, c4BandA_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0:ℚ)<(15443566539252696447104 / 900558759375 : ℚ)) hu0 hu1 hv0 hv1 c4BandACoeff_floor

def c4BandBCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => 50448102400
  | 0, 1 => (16993069226768 / 375 : ℚ)
  | 0, 2 => (68181328222649581 / 1687500 : ℚ)
  | 0, 3 => (67801529729964316667 / 1898437500 : ℚ)
  | 0, 4 => (33367070195457063574751 / 1067871093750 : ℚ)
  | 1, 0 => (394082439168 / 7 : ℚ)
  | 1, 1 => (87869660289527 / 1750 : ℚ)
  | 1, 2 => (43690670713202747 / 984375 : ℚ)
  | 1, 3 => (34388404177558940591 / 885937500 : ℚ)
  | 1, 4 => (8348624510834627774623 / 249169921875 : ℚ)
  | 2, 0 => (5716550650880 / 91 : ℚ)
  | 2, 1 => (1897704482441512 / 34125 : ℚ)
  | 2, 2 => (14958206681048310499 / 307125000 : ℚ)
  | 2, 3 => (2909203001480313304033 / 69103125000 : ℚ)
  | 2, 4 => (6957094628612342171021297 / 194352539062500 : ℚ)
  | 3, 0 => (490611627008 / 7 : ℚ)
  | 3, 1 => (16805096305056889 / 273000 : ℚ)
  | 3, 2 => (32788528783032307423 / 614250000 : ℚ)
  | 3, 3 => (2421517109280746383763 / 53156250000 : ℚ)
  | 3, 4 => (2960477319800540357728801 / 77741015625000 : ℚ)
  | 4, 0 => (78261798364800 / 1001 : ℚ)
  | 4, 1 => (8520894482392648 / 125125 : ℚ)
  | 4, 2 => (65795309509747962979 / 1126125000 : ℚ)
  | 4, 3 => (62286188050664138826989 / 1266890625000 : ℚ)
  | 4, 4 => (28728309958402741702307009 / 712625976562500 : ℚ)
  | 5, 0 => (87285288748928 / 1001 : ℚ)
  | 5, 1 => (113042664924995807 / 1501500 : ℚ)
  | 5, 2 => (53931899914367310527 / 844593750 : ℚ)
  | 5, 3 => (25133893743073410859313 / 475083984375 : ℚ)
  | 5, 4 => (22678446639760684105881826 / 534469482421875 : ℚ)
  | 6, 0 => (97327402324608 / 1001 : ℚ)
  | 6, 1 => (6244164388896019 / 75075 : ℚ)
  | 6, 2 => (29423672704612101922 / 422296875 : ℚ)
  | 6, 3 => (26955391922861238902774 / 475083984375 : ℚ)
  | 6, 4 => (2155366069941161599133576 / 48588134765625 : ℚ)
  | 7, 0 => (15499676699904 / 143 : ℚ)
  | 7, 1 => (3282278196371633 / 35750 : ℚ)
  | 7, 2 => (1526081912068914812 / 20109375 : ℚ)
  | 7, 3 => (1371399590100362698576 / 22623046875 : ℚ)
  | 7, 4 => (1170804205284730128721586 / 25450927734375 : ℚ)
  | 8, 0 => (120916983418368 / 1001 : ℚ)
  | 8, 1 => (2923963873098232 / 28875 : ℚ)
  | 8, 2 => (34836651527524805912 / 422296875 : ℚ)
  | 8, 3 => (6127284621012302159576 / 95016796875 : ℚ)
  | 8, 4 => (3606964249033001967095888 / 76352783203125 : ℚ)
  | 9, 0 => (19245424957184 / 143 : ℚ)
  | 9, 1 => (5983694603510336 / 53625 : ℚ)
  | 9, 2 => (37785516031982142016 / 422296875 : ℚ)
  | 9, 3 => (32428482738662610420032 / 475083984375 : ℚ)
  | 9, 4 => (25616769191847809522448256 / 534469482421875 : ℚ)
  | 10, 0 => (150046825830144 / 1001 : ℚ)
  | 10, 1 => (1182296729868544 / 9625 : ℚ)
  | 10, 2 => (13628314491136540928 / 140765625 : ℚ)
  | 10, 3 => (11375756932373938369792 / 158361328125 : ℚ)
  | 10, 4 => (1706384636111825769727744 / 35631298828125 : ℚ)
  | 11, 0 => 166897276160
  | 11, 1 => (4609590519869696 / 34125 : ℚ)
  | 11, 2 => (4010914337261970688 / 38390625 : ℚ)
  | 11, 3 => (3242919810604628433152 / 43189453125 : ℚ)
  | 11, 4 => (2279089564109529468767488 / 48588134765625 : ℚ)
  | 12, 0 => (2414889890432 / 13 : ℚ)
  | 12, 1 => (202532023268992 / 1365 : ℚ)
  | 12, 2 => (4315380233405844608 / 38390625 : ℚ)
  | 12, 3 => (480357709001219784064 / 6169921875 : ℚ)
  | 12, 4 => (434531880825949767196288 / 9717626953125 : ℚ)
  | 13, 0 => (1446767149440 / 7 : ℚ)
  | 13, 1 => (28486755476864 / 175 : ℚ)
  | 13, 2 => (118653391753361792 / 984375 : ℚ)
  | 13, 3 => (88532374257174392704 / 1107421875 : ℚ)
  | 13, 4 => (51082893681460986887552 / 1245849609375 : ℚ)
  | 14, 0 => 229870589824
  | 14, 1 => (66882928487552 / 375 : ℚ)
  | 14, 2 => (54324930330431104 / 421875 : ℚ)
  | 14, 3 => (38497953898498013312 / 474609375 : ℚ)
  | 14, 4 => (755758098378452266624 / 21357421875 : ℚ)
  | _, _ => 0

theorem c4BandBCoeff_floor : ∀ i ∈ Finset.range (14+1), ∀ j ∈ Finset.range (4+1), (33367070195457063574751 / 1067871093750 : ℚ) ≤ c4BandBCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4BandBCoeff]

theorem c4BandB_representation (u v : ℝ) :
    PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial (((7 : ℝ) / 2)+((1 : ℝ) / 2)*u) (((1 : ℝ) / 36000)*v) = bernsteinBoxEval 14 4 c4BandBCoeff u v := by
  norm_num [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, bernsteinBoxEval, c4BandBCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4BandB_box_pos {x y : ℝ} (hx0 : ((7 : ℝ) / 2) ≤ x) (hx1 : x ≤ (4 : ℝ)) (hy0 : 0 ≤ y) (hy1 : y ≤ ((1 : ℝ) / 36000)) : 0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y := by
  let u := (x-((7 : ℝ) / 2))/((1 : ℝ) / 2)
  let v := y/((1 : ℝ) / 36000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 2))]; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 36000))]; exact hy1
  rw [show x=((7 : ℝ) / 2)+((1 : ℝ) / 2)*u by dsimp [u]; field_simp; ring, show y=((1 : ℝ) / 36000)*v by dsimp [v]; field_simp; ring, c4BandB_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0:ℚ)<(33367070195457063574751 / 1067871093750 : ℚ)) hu0 hu1 hv0 hv1 c4BandBCoeff_floor

def c4BandCCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => 229870589824
  | 0, 1 => (136424665128832 / 625 : ℚ)
  | 0, 2 => (80775835213326208 / 390625 : ℚ)
  | 0, 3 => (47702778406241427328 / 244140625 : ℚ)
  | 0, 4 => (1123613034252505850752 / 6103515625 : ℚ)
  | 1, 0 => (1771421108096 / 7 : ℚ)
  | 1, 1 => (1048929474236288 / 4375 : ℚ)
  | 1, 2 => (123901246482792832 / 546875 : ℚ)
  | 1, 3 => (364835754402331336064 / 1708984375 : ℚ)
  | 1, 4 => (214169433176782319748992 / 1068115234375 : ℚ)
  | 2, 0 => (25345232158080 / 91 : ℚ)
  | 2, 1 => (1151729100483456 / 4375 : ℚ)
  | 2, 2 => (8819661416351101824 / 35546875 : ℚ)
  | 2, 3 => (5178792078756519354048 / 22216796875 : ℚ)
  | 2, 4 => (432869155128765172025472 / 1983642578125 : ℚ)
  | 3, 0 => (27887837346816 / 91 : ℚ)
  | 3, 1 => (657356504997888 / 2275 : ℚ)
  | 3, 2 => (742607766941590464 / 2734375 : ℚ)
  | 3, 3 => (226045040358503155392 / 888671875 : ℚ)
  | 3, 4 => (3294881146365394198747488 / 13885498046875 : ℚ)
  | 4, 0 => (337450846642944 / 1001 : ℚ)
  | 4, 1 => (39668779294763328 / 125125 : ℚ)
  | 4, 2 => (23235699278250858936 / 78203125 : ℚ)
  | 4, 3 => (9683696480830091093259 / 34912109375 : ℚ)
  | 4, 4 => (7875127203784024720557432 / 30548095703125 : ℚ)
  | 5, 0 => (53014802123520 / 143 : ℚ)
  | 5, 1 => (217538790106080312 / 625625 : ℚ)
  | 5, 2 => (18147982604562650277 / 55859375 : ℚ)
  | 5, 3 => (590923653291024000309459 / 1955078125000 : ℚ)
  | 5, 4 => (42737608964856362951692512 / 152740478515625 : ℚ)
  | 6, 0 => (407998873681408 / 1001 : ℚ)
  | 6, 1 => (47699313940296677 / 125125 : ℚ)
  | 6, 2 => (44426117392945569143 / 125125000 : ℚ)
  | 6, 3 => (5147532698802361925782057 / 15640625000000 : ℚ)
  | 6, 4 => (28516931005906714767794639 / 93994140625000 : ℚ)
  | 7, 0 => (64062146583296 / 143 : ℚ)
  | 7, 1 => (597409335786795239 / 1430000 : ℚ)
  | 7, 2 => (1386386549420195576009 / 3575000000 : ℚ)
  | 7, 3 => (2560286075716524486128833 / 7150000000000 : ℚ)
  | 7, 4 => (367122671312184596454075049 / 1117187500000000 : ℚ)
  | 8, 0 => (492736501736064 / 1001 : ℚ)
  | 8, 1 => (2290474424846317221 / 5005000 : ℚ)
  | 8, 2 => (2648371067480483216721 / 6256250000 : ℚ)
  | 8, 3 => (48708734793854730046338591 / 125125000000000 : ℚ)
  | 8, 4 => (6950904819600673208480258079 / 19550781250000000 : ℚ)
  | 9, 0 => (541255890400640 / 1001 : ℚ)
  | 9, 1 => (771684792004255639 / 1540000 : ℚ)
  | 9, 2 => (1155653791993502684147 / 2502500000 : ℚ)
  | 9, 3 => (211627502682268703815460659 / 500500000000000 : ℚ)
  | 9, 4 => (4292137159427323341266742277 / 11171875000000000 : ℚ)
  | 10, 0 => (594376237339264 / 1001 : ℚ)
  | 10, 1 => (2744913025211747387 / 5005000 : ℚ)
  | 10, 2 => (14398946590334877942317 / 28600000000 : ℚ)
  | 10, 3 => (2050525498920688450837799 / 4468750000000 : ℚ)
  | 10, 4 => (16212743980207561717038124567 / 39101562500000000 : ℚ)
  | 11, 0 => (59319410163456 / 91 : ℚ)
  | 11, 1 => (2183903964132671181 / 3640000 : ℚ)
  | 11, 2 => (3993174998361412015119 / 7280000000 : ℚ)
  | 11, 3 => (4527066481182602377835817 / 9100000000000 : ℚ)
  | 11, 4 => (4538562569203739451668457 / 10156250000000 : ℚ)
  | 12, 0 => (65101750935552 / 91 : ℚ)
  | 12, 1 => (298502808346301823 / 455000 : ℚ)
  | 12, 2 => (10868771900186180737317 / 18200000000 : ℚ)
  | 12, 3 => (3064477039827047507515383 / 5687500000000 : ℚ)
  | 12, 4 => (1709526143941261822223629389 / 3554687500000000 : ℚ)
  | 13, 0 => (5494289909760 / 7 : ℚ)
  | 13, 1 => (50191702934982759 / 70000 : ℚ)
  | 13, 2 => (454796441074900492731 / 700000000 : ℚ)
  | 13, 3 => (291476517196212193335129 / 500000000000 : ℚ)
  | 13, 4 => (282600762713444305166316219 / 546875000000000 : ℚ)
  | 14, 0 => 860876688384
  | 14, 1 => (1958201629726779 / 2500 : ℚ)
  | 14, 2 => (14126481218295015957 / 20000000 : ℚ)
  | 14, 3 => (78750843923368596153987 / 125000000000 : ℚ)
  | 14, 4 => (676670604539715374409441 / 1220703125000 : ℚ)
  | _, _ => 0

theorem c4BandCCoeff_floor : ∀ i ∈ Finset.range (14+1), ∀ j ∈ Finset.range (4+1), (1123613034252505850752 / 6103515625 : ℚ) ≤ c4BandCCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4BandCCoeff]

theorem c4BandC_representation (u v : ℝ) :
    PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial ((4 : ℝ)+((1 : ℝ) / 2)*u) (((1 : ℝ) / 160000)*v) = bernsteinBoxEval 14 4 c4BandCCoeff u v := by
  norm_num [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, bernsteinBoxEval, c4BandCCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4BandC_box_pos {x y : ℝ} (hx0 : (4 : ℝ) ≤ x) (hx1 : x ≤ ((9 : ℝ) / 2)) (hy0 : 0 ≤ y) (hy1 : y ≤ ((1 : ℝ) / 160000)) : 0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y := by
  let u := (x-(4 : ℝ))/((1 : ℝ) / 2)
  let v := y/((1 : ℝ) / 160000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 2))]; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 160000))]; exact hy1
  rw [show x=(4 : ℝ)+((1 : ℝ) / 2)*u by dsimp [u]; field_simp; ring, show y=((1 : ℝ) / 160000)*v by dsimp [v]; field_simp; ring, c4BandC_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0:ℚ)<(1123613034252505850752 / 6103515625 : ℚ)) hu0 hu1 hv0 hv1 c4BandCCoeff_floor

def c4BandDCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => 860876688384
  | 0, 1 => (18443697375933558 / 21875 : ℚ)
  | 0, 2 => (315987839796021081957 / 382812500 : ℚ)
  | 0, 3 => (33821349151791355526856573 / 41870117187500 : ℚ)
  | 0, 4 => (361844513503516987641290934459 / 457954406738281250 : ℚ)
  | 1, 0 => (6557983727616 / 7 : ℚ)
  | 1, 1 => (56159907827351373 / 61250 : ℚ)
  | 1, 2 => (12018072796199239011759 / 13398437500 : ℚ)
  | 1, 3 => (2623140530439290369316153 / 2990722656250 : ℚ)
  | 1, 4 => (2748060240624450598710926468547 / 3205680847167968750 : ℚ)
  | 2, 0 => (92757790199808 / 91 : ℚ)
  | 2, 1 => (1984377028099605201 / 1990625 : ℚ)
  | 2, 2 => (339458290450946191846773 / 348359375000 : ℚ)
  | 2, 3 => (1451035890353244660406238097 / 1524072265625000 : ℚ)
  | 2, 4 => (11070361463616296237635080254001 / 11906814575195312500 : ℚ)
  | 3, 0 => (100900098670848 / 91 : ℚ)
  | 3, 1 => (17255254108682576499 / 15925000 : ℚ)
  | 3, 2 => (147470310577017469464897 / 139343750000 : ℚ)
  | 3, 3 => (629841568533315945584552247 / 609628906250000 : ℚ)
  | 3, 4 => (168035430386791793336731494555639 / 166695404052734375000 : ℚ)
  | 4, 0 => (1207060804037248 / 1001 : ℚ)
  | 4, 1 => (1983258475344018308 / 1684375 : ℚ)
  | 4, 2 => (880650393121354864840147 / 766390625000 : ℚ)
  | 4, 3 => (93948671941444975630508177263 / 83823974609375000 : ℚ)
  | 4, 4 => (1001663937893331266769685788783637 / 916824722290039062500 : ℚ)
  | 5, 0 => (187490335574144 / 143 : ℚ)
  | 5, 1 => (112039569215852322817 / 87587500 : ℚ)
  | 5, 2 => (95590772018837750024939 / 76639062500 : ℚ)
  | 5, 3 => (50942252994279554784792414157 / 41911987304687500 : ℚ)
  | 5, 4 => (542618485810981102096123586251459 / 458412361145019531250 : ℚ)
  | 6, 0 => (1426681041720960 / 1001 : ℚ)
  | 6, 1 => (6084418815132993516 / 4379375 : ℚ)
  | 6, 2 => (259324001656506415718409 / 191597656250 : ℚ)
  | 6, 3 => (44181848010829600674027057 / 33529589843750 : ℚ)
  | 6, 4 => (58767562919572734968478053619243 / 45841236114501953125 : ℚ)
  | 7, 0 => (221503359810560 / 143 : ℚ)
  | 7, 1 => (1887627875425631203 / 1251250 : ℚ)
  | 7, 2 => (20094343255262579938018 / 13685546875 : ℚ)
  | 7, 3 => (427520707670437167183375974 / 299371337890625 : ℚ)
  | 7, 4 => (699159599430579875822572754902 / 503749847412109375 : ℚ)
  | 8, 0 => (1684731463390720 / 1001 : ℚ)
  | 8, 1 => (1434386477050045856 / 875875 : ℚ)
  | 8, 2 => (152546228316035767392908 / 95798828125 : ℚ)
  | 8, 3 => (8421289066061149721675548 / 5443115234375 : ℚ)
  | 8, 4 => (68854282356903990098857184863304 / 45841236114501953125 : ℚ)
  | 9, 0 => (261447941433600 / 143 : ℚ)
  | 9, 1 => (62267746720728672 / 35035 : ℚ)
  | 9, 2 => (33077266977731690811096 / 19159765625 : ℚ)
  | 9, 3 => (2160827166395118821242248 / 1289599609375 : ℚ)
  | 9, 4 => (2128165884967522407182379874224 / 1309749603271484375 : ℚ)
  | 10, 0 => (1987629894240000 / 1001 : ℚ)
  | 10, 1 => (13511828534268096 / 7007 : ℚ)
  | 10, 2 => (1434017023535582109168 / 766390625 : ℚ)
  | 10, 3 => (6082393914963886193922096 / 3352958984375 : ℚ)
  | 10, 4 => (644364149640585424662919998624 / 366729888916015625 : ℚ)
  | 11, 0 => (196197835200000 / 91 : ℚ)
  | 11, 1 => (102490085540880 / 49 : ℚ)
  | 11, 2 => (2173088866936961136 / 1071875 : ℚ)
  | 11, 3 => (119684271925957581085392 / 60962890625 : ℚ)
  | 11, 4 => (12663613217281608079391724384 / 6667816162109375 : ℚ)
  | 12, 0 => (30426090000000 / 13 : ℚ)
  | 12, 1 => (1444809352525440 / 637 : ℚ)
  | 12, 2 => (6119874412158788448 / 2786875 : ℚ)
  | 12, 3 => (129480170510339821715808 / 60962890625 : ℚ)
  | 12, 4 => (210498956764405464116677056 / 102581787109375 : ℚ)
  | 13, 0 => (17780702000000 / 7 : ℚ)
  | 13, 1 => (120484968468800 / 49 : ℚ)
  | 13, 2 => (509742871041548096 / 214375 : ℚ)
  | 13, 3 => (2154238620949728439232 / 937890625 : ℚ)
  | 13, 4 => (227335748589636294333064448 / 102581787109375 : ℚ)
  | 14, 0 => 2756110000000
  | 14, 1 => (18654327760000 / 7 : ℚ)
  | 14, 2 => (15764974070110976 / 6125 : ℚ)
  | 14, 3 => (13307424845808652288 / 5359375 : ℚ)
  | 14, 4 => (7011723495493292005793408 / 2930908203125 : ℚ)
  | _, _ => 0

theorem c4BandDCoeff_floor : ∀ i ∈ Finset.range (14+1), ∀ j ∈ Finset.range (4+1), (361844513503516987641290934459 / 457954406738281250 : ℚ) ≤ c4BandDCoeff i j := by
  intro i hi j hj
  interval_cases i <;> interval_cases j <;> norm_num [c4BandDCoeff]

theorem c4BandD_representation (u v : ℝ) :
    PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial (((9 : ℝ) / 2)+((1 : ℝ) / 2)*u) (((1 : ℝ) / 700000)*v) = bernsteinBoxEval 14 4 c4BandDCoeff u v := by
  norm_num [PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial, bernsteinBoxEval, c4BandDCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem c4BandD_box_pos {x y : ℝ} (hx0 : ((9 : ℝ) / 2) ≤ x) (hx1 : x ≤ (5 : ℝ)) (hy0 : 0 ≤ y) (hy1 : y ≤ ((1 : ℝ) / 700000)) : 0 < PF4.CERT12Inequalities.Generated.c4MarginCorePolynomial x y := by
  let u := (x-((9 : ℝ) / 2))/((1 : ℝ) / 2)
  let v := y/((1 : ℝ) / 700000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 2))]; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<((1 : ℝ) / 700000))]; exact hy1
  rw [show x=((9 : ℝ) / 2)+((1 : ℝ) / 2)*u by dsimp [u]; field_simp; ring, show y=((1 : ℝ) / 700000)*v by dsimp [v]; field_simp; ring, c4BandD_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0:ℚ)<(361844513503516987641290934459 / 457954406738281250 : ℚ)) hu0 hu1 hv0 hv1 c4BandDCoeff_floor

noncomputable def baseOuter0UpperPolynomial (x y : ℝ) : ℝ := -32*x*y + 6*x + 12*y - 9

def baseOuter0UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => 21
  | 0, 1 => 6
  | 1, 0 => (15749963 / 750000 : ℚ)
  | 1, 1 => (562499 / 93750 : ℚ)
  | _, _ => 0

theorem baseOuter0UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (15749963 / 750000 : ℚ) ≤ baseOuter0UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter0UpperCoeff]

theorem baseOuter0UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (1+1), 0 ≤ baseOuter0UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter0UpperCoeff]

theorem baseOuter0Upper_representation (v z : ℝ) : baseOuter0UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 1 baseOuter0UpperCoeff v z := by
  norm_num [baseOuter0UpperPolynomial, bernsteinHalfstripEval, baseOuter0UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter0Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter0UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(15749963 / 750000 : ℚ)) hv0 hv1 hz baseOuter0UpperCoeff_const_floor baseOuter0UpperCoeff_nonneg
  rw [← baseOuter0Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter0LowerPolynomial (x y : ℝ) : ℝ := 32*x*y + 10*x - 12*y - 15

def baseOuter0LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => 35
  | 0, 1 => 10
  | 1, 0 => (26250037 / 750000 : ℚ)
  | 1, 1 => (937501 / 93750 : ℚ)
  | _, _ => 0

theorem baseOuter0LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), 35 ≤ baseOuter0LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter0LowerCoeff]

theorem baseOuter0LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (1+1), 0 ≤ baseOuter0LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter0LowerCoeff]

theorem baseOuter0Lower_representation (v z : ℝ) : baseOuter0LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 1 baseOuter0LowerCoeff v z := by
  norm_num [baseOuter0LowerPolynomial, bernsteinHalfstripEval, baseOuter0LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter0Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter0LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<35) hv0 hv1 hz baseOuter0LowerCoeff_const_floor baseOuter0LowerCoeff_nonneg
  rw [← baseOuter0Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter1UpperPolynomial (x y : ℝ) : ℝ := 256*x^2*y + 4*x^2 - 240*x*y + 40*x*(2*x - 3) - 15*x + 30*y + 15/2

def baseOuter1UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (2865 / 2 : ℚ)
  | 0, 1 => 705
  | 0, 2 => 84
  | 1, 0 => (429750523 / 300000 : ℚ)
  | 1, 1 => (26437529 / 37500 : ℚ)
  | 1, 2 => (3937504 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter1UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (2865 / 2 : ℚ) ≤ baseOuter1UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter1UpperCoeff]

theorem baseOuter1UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (2+1), 0 ≤ baseOuter1UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter1UpperCoeff]

theorem baseOuter1Upper_representation (v z : ℝ) : baseOuter1UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 2 baseOuter1UpperCoeff v z := by
  norm_num [baseOuter1UpperPolynomial, bernsteinHalfstripEval, baseOuter1UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter1Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter1UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(2865 / 2 : ℚ)) hv0 hv1 hz baseOuter1UpperCoeff_const_floor baseOuter1UpperCoeff_nonneg
  rw [← baseOuter1Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter1LowerPolynomial (x y : ℝ) : ℝ := -256*x^2*y - 4*x^2 + 240*x*y + 40*x*(2*x - 3) + 15*x - 30*y - 15/2

def baseOuter1LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (2735 / 2 : ℚ)
  | 0, 1 => 655
  | 0, 2 => 76
  | 1, 0 => (410249477 / 300000 : ℚ)
  | 1, 1 => (24562471 / 37500 : ℚ)
  | 1, 2 => (3562496 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter1LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (410249477 / 300000 : ℚ) ≤ baseOuter1LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter1LowerCoeff]

theorem baseOuter1LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (2+1), 0 ≤ baseOuter1LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter1LowerCoeff]

theorem baseOuter1Lower_representation (v z : ℝ) : baseOuter1LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 2 baseOuter1LowerCoeff v z := by
  norm_num [baseOuter1LowerPolynomial, bernsteinHalfstripEval, baseOuter1LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter1Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter1LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(410249477 / 300000 : ℚ)) hv0 hv1 hz baseOuter1LowerCoeff_const_floor baseOuter1LowerCoeff_nonneg
  rw [← baseOuter1Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter2UpperPolynomial (x y : ℝ) : ℝ := -2048*x^3*y - 8*x^3 + 3584*x^2*y + 400*x^2*(2*x - 3) + 56*x^2 - 1320*x*y - 165*x/2 + 75*y + 75/4

def baseOuter2UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (280025 / 4 : ℚ)
  | 0, 1 => (95755 / 2 : ℚ)
  | 0, 2 => 10736
  | 0, 3 => 792
  | 1, 0 => (8400743083 / 120000 : ℚ)
  | 1, 1 => (3590809523 / 75000 : ℚ)
  | 1, 2 => (503249576 / 46875 : ℚ)
  | 1, 3 => (37124968 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter2UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (8400743083 / 120000 : ℚ) ≤ baseOuter2UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter2UpperCoeff]

theorem baseOuter2UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (3+1), 0 ≤ baseOuter2UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter2UpperCoeff]

theorem baseOuter2Upper_representation (v z : ℝ) : baseOuter2UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 3 baseOuter2UpperCoeff v z := by
  norm_num [baseOuter2UpperPolynomial, bernsteinHalfstripEval, baseOuter2UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter2Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter2UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(8400743083 / 120000 : ℚ)) hv0 hv1 hz baseOuter2UpperCoeff_const_floor baseOuter2UpperCoeff_nonneg
  rw [← baseOuter2Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter2LowerPolynomial (x y : ℝ) : ℝ := 2048*x^3*y + 8*x^3 - 3584*x^2*y + 400*x^2*(2*x - 3) - 56*x^2 + 1320*x*y + 165*x/2 - 75*y - 75/4

def baseOuter2LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (279975 / 4 : ℚ)
  | 0, 1 => (96245 / 2 : ℚ)
  | 0, 2 => 10864
  | 0, 3 => 808
  | 1, 0 => (8399256917 / 120000 : ℚ)
  | 1, 1 => (3609190477 / 75000 : ℚ)
  | 1, 2 => (509250424 / 46875 : ℚ)
  | 1, 3 => (37875032 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter2LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (279975 / 4 : ℚ) ≤ baseOuter2LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter2LowerCoeff]

theorem baseOuter2LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (3+1), 0 ≤ baseOuter2LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter2LowerCoeff]

theorem baseOuter2Lower_representation (v z : ℝ) : baseOuter2LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 3 baseOuter2LowerCoeff v z := by
  norm_num [baseOuter2LowerPolynomial, bernsteinHalfstripEval, baseOuter2LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter2Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter2LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(279975 / 4 : ℚ)) hv0 hv1 hz baseOuter2LowerCoeff_const_floor baseOuter2LowerCoeff_nonneg
  rw [← baseOuter2Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter3UpperPolynomial (x y : ℝ) : ℝ := 16384*x^4*y + 16*x^4 - 46080*x^3*y + 4000*x^3*(2*x - 3) - 180*x^3 + 33856*x^2*y + 529*x^2 - 6540*x*y - 1635*x/4 + 375*y/2 + 375/8

def baseOuter3UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (27989825 / 8 : ℚ)
  | 0, 1 => (12397525 / 4 : ℚ)
  | 0, 2 => 1020229
  | 0, 3 => 148140
  | 0, 4 => 8016
  | 1, 0 => (839695173511 / 240000 : ℚ)
  | 1, 1 => (154969146967 / 50000 : ℚ)
  | 1, 2 => (47823262504 / 46875 : ℚ)
  | 1, 3 => (277762676 / 1875 : ℚ)
  | 1, 4 => (375750256 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter3UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (27989825 / 8 : ℚ) ≤ baseOuter3UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter3UpperCoeff]

theorem baseOuter3UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (4+1), 0 ≤ baseOuter3UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter3UpperCoeff]

theorem baseOuter3Upper_representation (v z : ℝ) : baseOuter3UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 4 baseOuter3UpperCoeff v z := by
  norm_num [baseOuter3UpperPolynomial, bernsteinHalfstripEval, baseOuter3UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter3Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter3UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(27989825 / 8 : ℚ)) hv0 hv1 hz baseOuter3UpperCoeff_const_floor baseOuter3UpperCoeff_nonneg
  rw [← baseOuter3Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter3LowerPolynomial (x y : ℝ) : ℝ := -16384*x^4*y - 16*x^4 + 46080*x^3*y + 4000*x^3*(2*x - 3) + 180*x^3 - 33856*x^2*y - 529*x^2 + 6540*x*y + 1635*x/4 - 375*y/2 - 375/8

def baseOuter3LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (28010175 / 8 : ℚ)
  | 0, 1 => (12402475 / 4 : ℚ)
  | 0, 2 => 1019771
  | 0, 3 => 147860
  | 0, 4 => 7984
  | 1, 0 => (840304826489 / 240000 : ℚ)
  | 1, 1 => (155030853033 / 50000 : ℚ)
  | 1, 2 => (47801737496 / 46875 : ℚ)
  | 1, 3 => (277237324 / 1875 : ℚ)
  | 1, 4 => (374249744 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter3LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (840304826489 / 240000 : ℚ) ≤ baseOuter3LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter3LowerCoeff]

theorem baseOuter3LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (4+1), 0 ≤ baseOuter3LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter3LowerCoeff]

theorem baseOuter3Lower_representation (v z : ℝ) : baseOuter3LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 4 baseOuter3LowerCoeff v z := by
  norm_num [baseOuter3LowerPolynomial, bernsteinHalfstripEval, baseOuter3LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter3Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter3LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(840304826489 / 240000 : ℚ)) hv0 hv1 hz baseOuter3LowerCoeff_const_floor baseOuter3LowerCoeff_nonneg
  rw [← baseOuter3Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter4UpperPolynomial (x y : ℝ) : ℝ := -131072*x^5*y - 32*x^5 + 540672*x^4*y + 40000*x^4*(2*x - 3) + 528*x^4 - 662528*x^3*y - 2588*x^3 + 272384*x^2*y + 4256*x^2 - 30930*x*y - 15465*x/8 + 1875*y/4 + 1875/16

def baseOuter4UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (2800053625 / 16 : ℚ)
  | 0, 1 => (1520084215 / 8 : ℚ)
  | 0, 2 => 82004636
  | 0, 3 => 17599972
  | 0, 4 => 1879728
  | 0, 5 => 79968
  | 1, 0 => (28000528365169 / 160000 : ℚ)
  | 1, 1 => (57003139436431 / 300000 : ℚ)
  | 1, 2 => (3843965868676 / 46875 : ℚ)
  | 1, 3 => (824998334108 / 46875 : ℚ)
  | 1, 4 => (88112207248 / 46875 : ℚ)
  | 1, 5 => (3748497952 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter4UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (28000528365169 / 160000 : ℚ) ≤ baseOuter4UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter4UpperCoeff]

theorem baseOuter4UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (5+1), 0 ≤ baseOuter4UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter4UpperCoeff]

theorem baseOuter4Upper_representation (v z : ℝ) : baseOuter4UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 5 baseOuter4UpperCoeff v z := by
  norm_num [baseOuter4UpperPolynomial, bernsteinHalfstripEval, baseOuter4UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter4Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter4UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(28000528365169 / 160000 : ℚ)) hv0 hv1 hz baseOuter4UpperCoeff_const_floor baseOuter4UpperCoeff_nonneg
  rw [← baseOuter4Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter4LowerPolynomial (x y : ℝ) : ℝ := 131072*x^5*y + 32*x^5 - 540672*x^4*y + 40000*x^4*(2*x - 3) - 528*x^4 + 662528*x^3*y + 2588*x^3 - 272384*x^2*y - 4256*x^2 + 30930*x*y + 15465*x/8 - 1875*y/4 - 1875/16

def baseOuter4LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (2799946375 / 16 : ℚ)
  | 0, 1 => (1519915785 / 8 : ℚ)
  | 0, 2 => 81995364
  | 0, 3 => 17600028
  | 0, 4 => 1880272
  | 0, 5 => 80032
  | 1, 0 => (27999471634831 / 160000 : ℚ)
  | 1, 1 => (56996860563569 / 300000 : ℚ)
  | 1, 2 => (3843534131324 / 46875 : ℚ)
  | 1, 3 => (825001665892 / 46875 : ℚ)
  | 1, 4 => (88137792752 / 46875 : ℚ)
  | 1, 5 => (3751502048 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter4LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (2799946375 / 16 : ℚ) ≤ baseOuter4LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter4LowerCoeff]

theorem baseOuter4LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (5+1), 0 ≤ baseOuter4LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter4LowerCoeff]

theorem baseOuter4Lower_representation (v z : ℝ) : baseOuter4LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 5 baseOuter4LowerCoeff v z := by
  norm_num [baseOuter4LowerPolynomial, bernsteinHalfstripEval, baseOuter4LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter4Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter4LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(2799946375 / 16 : ℚ)) hv0 hv1 hz baseOuter4LowerCoeff_const_floor baseOuter4LowerCoeff_nonneg
  rw [← baseOuter4Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter5UpperPolynomial (x y : ℝ) : ℝ := 1048576*x^6*y + 64*x^6 - 5963776*x^5*y + 400000*x^5*(2*x - 3) - 1456*x^5 + 10977280*x^4*y + 10720*x^4 - 7810560*x^3*y - 30510*x^3 + 2017936*x^2*y + 126121*x^2/4 - 142935*x*y - 142935*x/16 + 9375*y/8 + 9375/32

def baseOuter5UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (280002564225 / 32 : ℚ)
  | 0, 1 => (180000449905 / 16 : ℚ)
  | 0, 2 => (23999847521 / 4 : ℚ)
  | 0, 3 => 1699979890
  | 0, 4 => 269998320
  | 0, 5 => 22800464
  | 0, 6 => 800064
  | 1, 0 => (8400078104802767 / 960000 : ℚ)
  | 1, 1 => (1350003612162877 / 120000 : ℚ)
  | 1, 2 => (281248274185649 / 46875 : ℚ)
  | 1, 3 => (15937315663222 / 9375 : ℚ)
  | 1, 4 => (843745015728 / 3125 : ℚ)
  | 1, 5 => (1068772148336 / 46875 : ℚ)
  | 1, 6 => (37503016384 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter5UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (280002564225 / 32 : ℚ) ≤ baseOuter5UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter5UpperCoeff]

theorem baseOuter5UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (6+1), 0 ≤ baseOuter5UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter5UpperCoeff]

theorem baseOuter5Upper_representation (v z : ℝ) : baseOuter5UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 6 baseOuter5UpperCoeff v z := by
  norm_num [baseOuter5UpperPolynomial, bernsteinHalfstripEval, baseOuter5UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter5Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter5UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(280002564225 / 32 : ℚ)) hv0 hv1 hz baseOuter5UpperCoeff_const_floor baseOuter5UpperCoeff_nonneg
  rw [← baseOuter5Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter5LowerPolynomial (x y : ℝ) : ℝ := -1048576*x^6*y - 64*x^6 + 5963776*x^5*y + 400000*x^5*(2*x - 3) + 1456*x^5 - 10977280*x^4*y - 10720*x^4 + 7810560*x^3*y + 30510*x^3 - 2017936*x^2*y - 126121*x^2/4 + 142935*x*y + 142935*x/16 - 9375*y/8 - 9375/32

def baseOuter5LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (279997435775 / 32 : ℚ)
  | 0, 1 => (179999550095 / 16 : ℚ)
  | 0, 2 => (24000152479 / 4 : ℚ)
  | 0, 3 => 1700020110
  | 0, 4 => 270001680
  | 0, 5 => 22799536
  | 0, 6 => 799936
  | 1, 0 => (8399921895197233 / 960000 : ℚ)
  | 1, 1 => (1349996387837123 / 120000 : ℚ)
  | 1, 2 => (281251725814351 / 46875 : ℚ)
  | 1, 3 => (15937684336778 / 9375 : ℚ)
  | 1, 4 => (843754984272 / 3125 : ℚ)
  | 1, 5 => (1068727851664 / 46875 : ℚ)
  | 1, 6 => (37496983616 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter5LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (8399921895197233 / 960000 : ℚ) ≤ baseOuter5LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter5LowerCoeff]

theorem baseOuter5LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (6+1), 0 ≤ baseOuter5LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter5LowerCoeff]

theorem baseOuter5Lower_representation (v z : ℝ) : baseOuter5LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 6 baseOuter5LowerCoeff v z := by
  norm_num [baseOuter5LowerPolynomial, bernsteinHalfstripEval, baseOuter5LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter5Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter5LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(8399921895197233 / 960000 : ℚ)) hv0 hv1 hz baseOuter5LowerCoeff_const_floor baseOuter5LowerCoeff_nonneg
  rw [← baseOuter5Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter6UpperPolynomial (x y : ℝ) : ℝ := -8388608*x^7*y - 128*x^7 + 62914560*x^6*y + 4000000*x^6*(2*x - 3) + 3840*x^6 - 162365440*x^5*y - 39640*x^5 + 177745920*x^4*y + 173580*x^4 - 82533248*x^3*y - 644791*x^3/2 + 14260064*x^2*y + 445627*x^2/2 - 1305165*x*y/2 - 1305165*x/32 + 46875*y/16 + 46875/64

def baseOuter6UpperCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (27999979532825 / 64 : ℚ)
  | 0, 1 => (20799965525955 / 32 : ℚ)
  | 0, 2 => 412499473881
  | 0, 3 => (290000078409 / 2 : ℚ)
  | 0, 4 => 30500062580
  | 0, 5 => 3840008360
  | 0, 6 => 267999360
  | 0, 7 => 7999872
  | 1, 0 => (167999867138170559 / 384000 : ℚ)
  | 1, 1 => (779998642254078283 / 1200000 : ℚ)
  | 1, 2 => (12890607119228639 / 31250 : ℚ)
  | 1, 3 => (13593751696253911 / 93750 : ℚ)
  | 1, 4 => (95312677866052 / 3125 : ℚ)
  | 1, 5 => (36000070003288 / 9375 : ℚ)
  | 1, 6 => (2512493279104 / 9375 : ℚ)
  | 1, 7 => (374993868928 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter6UpperCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (167999867138170559 / 384000 : ℚ) ≤ baseOuter6UpperCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter6UpperCoeff]

theorem baseOuter6UpperCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (7+1), 0 ≤ baseOuter6UpperCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter6UpperCoeff]

theorem baseOuter6Upper_representation (v z : ℝ) : baseOuter6UpperPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 7 baseOuter6UpperCoeff v z := by
  norm_num [baseOuter6UpperPolynomial, bernsteinHalfstripEval, baseOuter6UpperCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter6Upper_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter6UpperPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(167999867138170559 / 384000 : ℚ)) hv0 hv1 hz baseOuter6UpperCoeff_const_floor baseOuter6UpperCoeff_nonneg
  rw [← baseOuter6Upper_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

noncomputable def baseOuter6LowerPolynomial (x y : ℝ) : ℝ := 8388608*x^7*y + 128*x^7 - 62914560*x^6*y + 4000000*x^6*(2*x - 3) - 3840*x^6 + 162365440*x^5*y + 39640*x^5 - 177745920*x^4*y - 173580*x^4 + 82533248*x^3*y + 644791*x^3/2 - 14260064*x^2*y - 445627*x^2/2 + 1305165*x*y/2 + 1305165*x/32 - 46875*y/16 - 46875/64

def baseOuter6LowerCoeff (i k : ℕ) : ℚ :=
  match i, k with
  | 0, 0 => (28000020467175 / 64 : ℚ)
  | 0, 1 => (20800034474045 / 32 : ℚ)
  | 0, 2 => 412500526119
  | 0, 3 => (289999921591 / 2 : ℚ)
  | 0, 4 => 30499937420
  | 0, 5 => 3839991640
  | 0, 6 => 268000640
  | 0, 7 => 8000128
  | 1, 0 => (168000132861829441 / 384000 : ℚ)
  | 1, 1 => (780001357745921717 / 1200000 : ℚ)
  | 1, 2 => (12890642880771361 / 31250 : ℚ)
  | 1, 3 => (13593748303746089 / 93750 : ℚ)
  | 1, 4 => (95312322133948 / 3125 : ℚ)
  | 1, 5 => (35999929996712 / 9375 : ℚ)
  | 1, 6 => (2512506720896 / 9375 : ℚ)
  | 1, 7 => (375006131072 / 46875 : ℚ)
  | _, _ => 0

theorem baseOuter6LowerCoeff_const_floor : ∀ i ∈ Finset.range (1+1), (28000020467175 / 64 : ℚ) ≤ baseOuter6LowerCoeff i 0 := by
  intro i hi
  interval_cases i <;> norm_num [baseOuter6LowerCoeff]

theorem baseOuter6LowerCoeff_nonneg : ∀ i ∈ Finset.range (1+1), ∀ k ∈ Finset.range (7+1), 0 ≤ baseOuter6LowerCoeff i k := by
  intro i hi k hk
  interval_cases i <;> interval_cases k <;> norm_num [baseOuter6LowerCoeff]

theorem baseOuter6Lower_representation (v z : ℝ) : baseOuter6LowerPolynomial (z+5) (v/3000000) = bernsteinHalfstripEval 1 7 baseOuter6LowerCoeff v z := by
  norm_num [baseOuter6LowerPolynomial, bernsteinHalfstripEval, baseOuter6LowerCoeff, bernsteinBasis_eq, Nat.choose]
  ring

theorem baseOuter6Lower_region_pos {x y : ℝ} (hx : 5≤x) (hy0 : 0≤y) (hy1 : y≤1/3000000) : 0 < baseOuter6LowerPolynomial x y := by
  let v:=y/(1/3000000); let z:=x-5
  have hv0 : 0≤v := by dsimp [v]; positivity
  have hv1 : v≤1 := by dsimp [v]; rw [div_le_one (by norm_num : (0:ℝ)<1/3000000)]; exact hy1
  have hz : 0≤z := by dsimp [z]; linarith
  have h:=bernsteinHalfstripEval_pos (by norm_num : (0:ℚ)<(28000020467175 / 64 : ℚ)) hv0 hv1 hz baseOuter6LowerCoeff_const_floor baseOuter6LowerCoeff_nonneg
  rw [← baseOuter6Lower_representation] at h
  dsimp [v,z] at h
  convert h using 1 <;> field_simp <;> ring

end PF4.RobustThreeModeClosure.Generated

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
