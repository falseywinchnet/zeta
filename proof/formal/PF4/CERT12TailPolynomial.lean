/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.KernelSeries
import Mathlib.Tactic

set_option linter.style.header false

/-!
# CERT12 polynomial half-line bounds

Exact sign and envelope bounds for the derivative polynomials occurring in
the positive-mode Riemann-kernel series.  The derivative order is finite
(`j ≤ 6`), but every polynomial statement quantifies over a complete real
half-line.
-/

namespace PF4.CERT12TailPolynomial

theorem certPoly_alternating_pos
    {j : ℕ} (hj : j ≤ 6) {s : ℝ} (hs : 27 ≤ s) :
    0 < (-1 : ℝ) ^ j * (PF4.certPoly j).eval s := by
  let z := s - 27
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hpow : ∀ n : ℕ, 0 ≤ z ^ n := fun n => pow_nonneg hz n
  have hs_eq : s = z + 27 := by dsimp [z]; ring
  rw [hs_eq]
  interval_cases j <;> norm_num [PF4.certPoly]
  all_goals ring_nf
  all_goals try positivity
  all_goals nlinarith [hpow 0, hpow 1, hpow 2, hpow 3, hpow 4, hpow 5, hpow 6]

theorem certPoly_alternating_le_envelope
    {j : ℕ} (hj : j ≤ 6) {s : ℝ} (hs : 27 ≤ s) :
    (-1 : ℝ) ^ j * (PF4.certPoly j).eval s ≤
      2 ^ (j + 1) * s ^ (j + 1) := by
  let z := s - 27
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hpow : ∀ n : ℕ, 0 ≤ z ^ n := fun n => pow_nonneg hz n
  have hs_eq : s = z + 27 := by dsimp [z]; ring
  rw [hs_eq]
  interval_cases j <;> norm_num [PF4.certPoly]
  all_goals ring_nf
  all_goals nlinarith [hpow 0, hpow 1, hpow 2, hpow 3, hpow 4, hpow 5, hpow 6, hpow 7]

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

theorem thirdMode_certPoly_endpoint_le
    {j : ℕ} (hj : j ≤ 6) {x : ℝ} (hx : 3 ≤ x) :
    (-1 : ℝ) ^ j * (PF4.certPoly j).eval 27 ≤
      (-1 : ℝ) ^ j * (PF4.certPoly j).eval (9 * x) := by
  let z := x - 3
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hpow : ∀ n : ℕ, 0 ≤ z ^ n := fun n => pow_nonneg hz n
  have hx_eq : x = z + 3 := by dsimp [z]; ring
  rw [hx_eq]
  interval_cases j <;> norm_num [PF4.certPoly]
  all_goals ring_nf
  all_goals nlinarith [hpow 0, hpow 1, hpow 2, hpow 3, hpow 4, hpow 5, hpow 6, hpow 7]

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

theorem relative_tail_coefficient_lt_1000
    {j : ℕ} (hj : j ≤ 6) :
    (2 : ℝ) * 2 ^ (j + 1) * 4 ^ (2 * j + 4) * 3 ^ (j + 1) <
      1000 * 9 *
        ((-1 : ℝ) ^ j * (PF4.certPoly j).eval 27) := by
  interval_cases j <;> norm_num [PF4.certPoly]

end PF4.CERT12TailPolynomial

#print axioms PF4.CERT12TailPolynomial.certPoly_alternating_pos
#print axioms PF4.CERT12TailPolynomial.certPoly_alternating_le_envelope
#print axioms PF4.CERT12TailPolynomial.abs_certPoly_le_envelope
#print axioms PF4.CERT12TailPolynomial.thirdMode_certPoly_endpoint_le
#print axioms PF4.CERT12TailPolynomial.thirdMode_abs_certPoly_endpoint_le
#print axioms PF4.CERT12TailPolynomial.relative_tail_coefficient_lt_1000
