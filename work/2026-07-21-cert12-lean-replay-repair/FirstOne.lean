import PF4.KernelSeries
import Mathlib.Tactic

set_option linter.style.header false

namespace PF4.CERT12ReplayRepair

theorem certPoly_alternating_pos_one
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

end PF4.CERT12ReplayRepair

#print axioms PF4.CERT12ReplayRepair.certPoly_alternating_pos_one
