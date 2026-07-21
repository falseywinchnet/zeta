import PF4.KernelSeries
import Mathlib.Tactic

set_option linter.style.header false

namespace PF4.CERT12ReplayRepair

open Finset Set

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
  all_goals try positivity
  all_goals nlinarith [hpow 0, hpow 1, hpow 2, hpow 3, hpow 4, hpow 5, hpow 6, hpow 7]

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
  all_goals try positivity
  all_goals nlinarith [hpow 0, hpow 1, hpow 2, hpow 3, hpow 4, hpow 5, hpow 6, hpow 7]

end PF4.CERT12ReplayRepair

#print axioms PF4.CERT12ReplayRepair.certPoly_alternating_pos
#print axioms PF4.CERT12ReplayRepair.certPoly_alternating_le_envelope
#print axioms PF4.CERT12ReplayRepair.thirdMode_certPoly_endpoint_le
