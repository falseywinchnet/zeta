/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Constructive density crossing algebra

This file formalizes the algebraic core of PO-0033 through PO-0036. It does
not yet construct the measures or CDFs. Every positivity fact is a theorem
hypothesis corresponding to a prior proof obligation; no conclusion is encoded
in a fresh positive symbol.
-/

namespace PF4.Crossing

/-- The ratio of the left densities after their common positive curvature
factor has been cancelled. -/
noncomputable def densityRatio (p z L δ Λ t : ℝ) : ℝ :=
  Λ * (z - t) / (L * δ * (t - p))

/-- The unique candidate at which the two left densities agree. -/
noncomputable def crossingPoint (p z L δ Λ : ℝ) : ℝ :=
  (Λ * z + L * δ * p) / (Λ + L * δ)

theorem crossingPoint_sub_left
    {p z L δ Λ : ℝ} (hden : Λ + L * δ ≠ 0) :
    crossingPoint p z L δ Λ - p =
      Λ * (z - p) / (Λ + L * δ) := by
  rw [crossingPoint]
  field_simp
  ring

theorem right_sub_crossingPoint
    {p z L δ Λ : ℝ} (hden : Λ + L * δ ≠ 0) :
    z - crossingPoint p z L δ Λ =
      L * δ * (z - p) / (Λ + L * δ) := by
  rw [crossingPoint]
  field_simp
  ring

theorem crossingPoint_mem
    {p z L δ Λ : ℝ}
    (hpz : p < z) (hΛ : 0 < Λ) (hLδ : 0 < L * δ) :
    p < crossingPoint p z L δ Λ ∧
      crossingPoint p z L δ Λ < z := by
  have hden : 0 < Λ + L * δ := add_pos hΛ hLδ
  constructor
  · rw [← sub_pos, crossingPoint_sub_left hden.ne']
    exact div_pos (mul_pos hΛ (sub_pos.mpr hpz)) hden
  · rw [← sub_pos, right_sub_crossingPoint hden.ne']
    exact div_pos (mul_pos hLδ (sub_pos.mpr hpz)) hden

theorem densityRatio_at_crossingPoint
    {p z L δ Λ : ℝ}
    (hpz : p < z) (hΛ : 0 < Λ) (hL : 0 < L) (hδ : 0 < δ) :
    densityRatio p z L δ Λ (crossingPoint p z L δ Λ) = 1 := by
  have hLδ : 0 < L * δ := mul_pos hL hδ
  have hden : 0 < Λ + L * δ := add_pos hΛ hLδ
  have hcp : p < crossingPoint p z L δ Λ :=
    (crossingPoint_mem hpz hΛ hLδ).1
  have hzp : z - p ≠ 0 := sub_ne_zero.mpr hpz.ne'
  rw [densityRatio, right_sub_crossingPoint hden.ne',
    crossingPoint_sub_left hden.ne']
  field_simp [hzp]

theorem densityRatio_sub_one
    {p z L δ Λ t : ℝ}
    (ht : p < t) (hL : 0 < L) (hδ : 0 < δ)
    (hden : Λ + L * δ ≠ 0) :
    densityRatio p z L δ Λ t - 1 =
      (Λ + L * δ) * (crossingPoint p z L δ Λ - t) /
        (L * δ * (t - p)) := by
  have htp : t - p ≠ 0 := sub_ne_zero.mpr ht.ne'
  rw [densityRatio, crossingPoint]
  field_simp [htp, hden]
  ring

theorem densityRatio_gt_one_iff
    {p z L δ Λ t : ℝ}
    (ht : p < t) (hΛ : 0 < Λ) (hL : 0 < L) (hδ : 0 < δ) :
    1 < densityRatio p z L δ Λ t ↔
      t < crossingPoint p z L δ Λ := by
  have hLδ : 0 < L * δ := mul_pos hL hδ
  have hsum : 0 < Λ + L * δ := add_pos hΛ hLδ
  have hbase : 0 < L * δ * (t - p) :=
    mul_pos hLδ (sub_pos.mpr ht)
  rw [← sub_pos, densityRatio_sub_one ht hL hδ hsum.ne']
  exact (div_pos_iff_of_pos_right hbase).trans
    ((mul_pos_iff_of_pos_left hsum).trans sub_pos)

theorem densityRatio_lt_one_iff
    {p z L δ Λ t : ℝ}
    (ht : p < t) (hΛ : 0 < Λ) (hL : 0 < L) (hδ : 0 < δ) :
    densityRatio p z L δ Λ t < 1 ↔
      crossingPoint p z L δ Λ < t := by
  have hLδ : 0 < L * δ := mul_pos hL hδ
  have hsum : 0 < Λ + L * δ := add_pos hΛ hLδ
  have hbase : 0 < L * δ * (t - p) :=
    mul_pos hLδ (sub_pos.mpr ht)
  rw [← sub_neg, densityRatio_sub_one ht hL hδ hsum.ne']
  constructor
  · intro h
    rcases div_neg_iff.mp h with hbad | hgood
    · exact False.elim ((not_lt_of_ge hbase.le) hbad.2)
    · rcases mul_neg_iff.mp hgood.1 with hcross | hbad
      · exact sub_neg.mp hcross.2
      · exact False.elim ((not_lt_of_ge hsum.le) hbad.1)
  · intro hcross
    apply div_neg_iff.mpr
    right
    exact ⟨mul_neg_of_pos_of_neg hsum (sub_neg.mpr hcross), hbase⟩

theorem densityRatio_eq_one_iff
    {p z L δ Λ t : ℝ}
    (ht : p < t) (hΛ : 0 < Λ) (hL : 0 < L) (hδ : 0 < δ) :
    densityRatio p z L δ Λ t = 1 ↔
      t = crossingPoint p z L δ Λ := by
  have hLδ : 0 < L * δ := mul_pos hL hδ
  have hsum : 0 < Λ + L * δ := add_pos hΛ hLδ
  constructor
  · intro hr
    by_contra hne
    rcases lt_or_gt_of_ne hne with hleft | hright
    · have hgt :=
        (densityRatio_gt_one_iff ht hΛ hL hδ).2 hleft
      exact hgt.ne hr.symm
    · have hlt :=
        (densityRatio_lt_one_iff ht hΛ hL hδ).2 hright
      exact hlt.ne hr
  · intro htstar
    subst t
    have h := densityRatio_sub_one (z := z) ht hL hδ hsum.ne'
    have hzero :
        densityRatio p z L δ Λ (crossingPoint p z L δ Λ) - 1 = 0 := by
      simpa using h
    exact sub_eq_zero.mp hzero

end PF4.Crossing
