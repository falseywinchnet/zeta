/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CERT12ThetaTail
import PF4.CERT12BaseBounds
import PF4.CERT12PerturbationBounds
import PF4.CERT12ExpBounds
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Literal CERT12 two-mode coordinates

This module identifies the first two terms of the maintained normalized theta
jet with the exact rational-polynomial coordinates consumed by the split
CERT12 certificates.  It then obtains the complete compact coordinate box
from the maintained Bernstein bounds.
-/

namespace PF4.CERT12Coordinates

open PF4.CERT12ThetaTail
open PF4.CERT12Inequalities.Generated
open PF4.CERT12Inequalities.Perturbation.Generated
open PF4.CERT12ExpBounds

noncomputable def certY (t : ℝ) : ℝ := Real.exp (-3 * certX t)

noncomputable def twoModeNormalizedJet (j : ℕ) (x y : ℝ) : ℝ :=
  ((PF4.certPoly j).eval x + 4 * y * (PF4.certPoly j).eval (4 * x)) /
    (2 * x - 3)

noncomputable def twoModeJet (t : ℝ) : Fin 7 → ℝ := fun j =>
  twoModeNormalizedJet j (certX t) (certY t)

theorem certX_ge_157_div_50 {t : ℝ} (ht : 0 ≤ t) :
    (157 / 50 : ℝ) ≤ certX t := by
  have he : (1 : ℝ) ≤ Real.exp (2 * t) :=
    (Real.one_le_exp_iff).2 (by linarith)
  unfold certX PF4.modeX PF4.modeN
  norm_num
  calc
    (157 / 50 : ℝ) ≤ Real.pi :=
      (le_of_lt (Real.pi_gt_d20.trans' (by norm_num)))
    _ ≤ Real.pi * Real.exp (2 * t) :=
      le_mul_of_one_le_right Real.pi_pos.le he

theorem two_mul_certX_sub_three_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < 2 * certX t - 3 := by
  have := certX_ge_157_div_50 ht
  linarith

theorem firstTwoModeJets_eq_twoModeNormalizedJet
    (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    normalizedModeJet j 0 t + normalizedModeJet j 1 t =
      twoModeNormalizedJet j (certX t) (certY t) := by
  rw [normalizedModeJet_eq j 0 ht, normalizedModeJet_eq j 1 ht]
  norm_num [PF4.modeN]
  unfold twoModeNormalizedJet certY
  ring_nf

/-- One exact identity for the complete seven-coordinate first-two-mode jet. -/
theorem firstTwoModeJet_eq {t : ℝ} (ht : 0 ≤ t) :
    (fun j : Fin 7 =>
      normalizedModeJet j 0 t + normalizedModeJet j 1 t) =
      twoModeJet t := by
  funext j
  exact firstTwoModeJets_eq_twoModeNormalizedJet j ht

noncomputable def normalizedSeriesJetVector (t : ℝ) : Fin 7 → ℝ := fun j =>
  normalizedSeriesJet j t

noncomputable def fullTailJet (t : ℝ) : Fin 7 → ℝ := fun j =>
  fullModeTail j t

theorem normalizedSeriesJet_eq_twoModeJet_add_fullTail
    (j : Fin 7) {t : ℝ} (ht : 0 ≤ t) :
    normalizedSeriesJet j t = twoModeJet t j + fullTailJet t j := by
  rw [normalizedSeriesJet_eq_tsum_normalizedModeJet]
  have hs := summable_normalizedModeJet_of_nonneg (j := (j : ℕ)) (by omega) ht
  rw [← hs.sum_add_tsum_nat_add 2]
  rw [show ∑ k ∈ Finset.range 2, normalizedModeJet j k t =
      normalizedModeJet j 0 t + normalizedModeJet j 1 t by
    simp [Finset.sum_range_succ]]
  rw [firstTwoModeJets_eq_twoModeNormalizedJet j ht]
  rfl

/-- Exact seven-coordinate decomposition of the literal infinite theta jet. -/
theorem normalizedSeriesJetVector_eq {t : ℝ} (ht : 0 ≤ t) :
    normalizedSeriesJetVector t =
      fun j => twoModeJet t j + fullTailJet t j := by
  funext j
  exact normalizedSeriesJet_eq_twoModeJet_add_fullTail j ht

private theorem abs_div_le_of_bounds
    {raw den B : ℝ} (hden : 0 < den)
    (hlower : 0 ≤ B * den + raw) (hupper : 0 ≤ B * den - raw) :
    |raw / den| ≤ B := by
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    linarith

/-- The exact first-two-mode vector lies in the complete compact base box. -/
theorem abs_twoModeJet_le_coreB {t : ℝ} (ht : 0 ≤ t)
    (hx5 : certX t ≤ 5) (j : Fin 7) :
    |twoModeJet t j| ≤ coreB j := by
  have hx0 := certX_ge_157_div_50 ht
  have hy0 : 0 ≤ certY t := (Real.exp_pos _).le
  have hy1 : certY t ≤ (1 / 12000 : ℝ) := by
    exact (exp_neg_three_mul_lt_inv_12000 hx0).le
  have hden := two_mul_certX_sub_three_pos ht
  fin_cases j
  · apply abs_div_le_of_bounds hden
    · convert (base0Lower_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base0LowerPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
    · convert (base0Upper_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base0UpperPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
  · apply abs_div_le_of_bounds hden
    · convert (base1Lower_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base1LowerPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
    · convert (base1Upper_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base1UpperPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
  · apply abs_div_le_of_bounds hden
    · convert (base2Lower_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base2LowerPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
    · convert (base2Upper_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base2UpperPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
  · apply abs_div_le_of_bounds hden
    · convert (base3Lower_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base3LowerPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
    · convert (base3Upper_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base3UpperPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
  · apply abs_div_le_of_bounds hden
    · convert (base4Lower_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base4LowerPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
    · convert (base4Upper_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base4UpperPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
  · apply abs_div_le_of_bounds hden
    · convert (base5Lower_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base5LowerPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
    · convert (base5Upper_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base5UpperPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
  · apply abs_div_le_of_bounds hden
    · convert (base6Lower_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base6LowerPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring
    · convert (base6Upper_box_pos hx0 hx5 hy0 hy1).le using 1 <;>
        norm_num [twoModeJet, twoModeNormalizedJet, certY, coreB,
          base6UpperPolynomial, PF4.certPoly] <;> try rfl
      all_goals ring

end PF4.CERT12Coordinates

#print axioms PF4.CERT12Coordinates.firstTwoModeJet_eq
#print axioms PF4.CERT12Coordinates.abs_twoModeJet_le_coreB
#print axioms PF4.CERT12Coordinates.normalizedSeriesJetVector_eq
