/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CERT12TailBounds
import PF4.CERT12TwoModeMargins
import PF4.CERT12PerturbationBounds
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Literal CERT12 closure on the compact band

The exact normalized theta-series jet is the first-two-mode vector plus its
literal infinite tail.  The maintained coordinate boxes and perturbation
budgets therefore transfer the exact two-mode margins into strict q, F2, and
C4 signs throughout `t >= 0`, `certX t <= 5`.
-/

namespace PF4.CERT12CompactClosure

open PF4.CERT12ThetaTail
open PF4.CERT12Coordinates
open PF4.CERT12TailBounds
open PF4.CERT12TwoModeMargins
open PF4.CERT12Inequalities.Perturbation.Generated

theorem twoModeJet_clearedQ_gt_ten {t : ℝ} (ht : 0 ≤ t)
    (hx5 : certX t ≤ 5) :
    10 < PF4.ClearedJetCertificateBridge.clearedQ
      (twoModeJet t 0) (twoModeJet t 1) (twoModeJet t 2) := by
  simpa [twoModeJet, certY] using
    clearedQ_twoMode_gt_ten_to_five (certX_ge_157_div_50 ht) hx5

theorem twoModeJet_clearedF2_gt_thousand {t : ℝ} (ht : 0 ≤ t)
    (hx5 : certX t ≤ 5) :
    1000 < PF4.ClearedJetCertificateBridge.clearedF2
      (twoModeJet t 0) (twoModeJet t 1) (twoModeJet t 2)
      (twoModeJet t 3) (twoModeJet t 4) := by
  simpa [twoModeJet, certY] using
    clearedF2_twoMode_gt_thousand_to_five (certX_ge_157_div_50 ht) hx5

theorem twoModeJet_clearedC4_gt_margin {t : ℝ} (ht : 0 ≤ t)
    (hx5 : certX t ≤ 5) :
    50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (twoModeJet t 0) (twoModeJet t 1) (twoModeJet t 2)
      (twoModeJet t 3) (twoModeJet t 4) (twoModeJet t 5)
      (twoModeJet t 6) := by
  simpa [twoModeJet, certY] using
    clearedC4_twoMode_gt_margin_to_five (certX_ge_157_div_50 ht) hx5

/-- Literal normalized cleared-q positivity on the complete compact band. -/
theorem normalized_clearedQ_pos_of_certX_le_five
    {t : ℝ} (ht : 0 ≤ t) (hx5 : certX t ≤ 5) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (normalizedSeriesJet 0 t) (normalizedSeriesJet 1 t)
      (normalizedSeriesJet 2 t) := by
  have h := clearedQ_pos_of_base_margin_and_core_error
    (twoModeJet t) (fullTailJet t) (abs_twoModeJet_le_coreB ht hx5)
    (abs_fullTailJet_le_coreE ht) (twoModeJet_clearedQ_gt_ten ht hx5)
  simpa only [← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 0 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 1 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 2 ht,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

/-- Literal normalized cleared-F2 positivity on the complete compact band. -/
theorem normalized_clearedF2_pos_of_certX_le_five
    {t : ℝ} (ht : 0 ≤ t) (hx5 : certX t ≤ 5) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (normalizedSeriesJet 0 t) (normalizedSeriesJet 1 t)
      (normalizedSeriesJet 2 t) (normalizedSeriesJet 3 t)
      (normalizedSeriesJet 4 t) := by
  have h := clearedF2_pos_of_base_margin_and_core_error
    (twoModeJet t) (fullTailJet t) (abs_twoModeJet_le_coreB ht hx5)
    (abs_fullTailJet_le_coreE ht) (twoModeJet_clearedF2_gt_thousand ht hx5)
  simpa only [← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 0 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 1 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 2 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 3 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 4 ht,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

/-- Literal normalized cleared-C4 positivity on the complete compact band. -/
theorem normalized_clearedC4_pos_of_certX_le_five
    {t : ℝ} (ht : 0 ≤ t) (hx5 : certX t ≤ 5) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (normalizedSeriesJet 0 t) (normalizedSeriesJet 1 t)
      (normalizedSeriesJet 2 t) (normalizedSeriesJet 3 t)
      (normalizedSeriesJet 4 t) (normalizedSeriesJet 5 t)
      (normalizedSeriesJet 6 t) := by
  have h := clearedC4_pos_of_base_margin_and_core_error
    (twoModeJet t) (fullTailJet t) (abs_twoModeJet_le_coreB ht hx5)
    (abs_fullTailJet_le_coreE ht) (twoModeJet_clearedC4_gt_margin ht hx5)
  simpa only [← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 0 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 1 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 2 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 3 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 4 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 5 ht,
    ← normalizedSeriesJet_eq_twoModeJet_add_fullTail (t := t) 6 ht,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod] using h

/-- Complete literal q/F2/C4 sign package on `t >= 0`, `certX t <= 5`. -/
theorem normalized_compact_band_signs
    {t : ℝ} (ht : 0 ≤ t) (hx5 : certX t ≤ 5) :
    (0 < PF4.ClearedJetCertificateBridge.clearedQ
      (normalizedSeriesJet 0 t) (normalizedSeriesJet 1 t)
      (normalizedSeriesJet 2 t)) ∧
    (0 < PF4.ClearedJetCertificateBridge.clearedF2
      (normalizedSeriesJet 0 t) (normalizedSeriesJet 1 t)
      (normalizedSeriesJet 2 t) (normalizedSeriesJet 3 t)
      (normalizedSeriesJet 4 t)) ∧
    (0 < PF4.ClearedJetCertificateBridge.clearedC4
      (normalizedSeriesJet 0 t) (normalizedSeriesJet 1 t)
      (normalizedSeriesJet 2 t) (normalizedSeriesJet 3 t)
      (normalizedSeriesJet 4 t) (normalizedSeriesJet 5 t)
      (normalizedSeriesJet 6 t)) := by
  exact ⟨normalized_clearedQ_pos_of_certX_le_five ht hx5,
    normalized_clearedF2_pos_of_certX_le_five ht hx5,
    normalized_clearedC4_pos_of_certX_le_five ht hx5⟩

end PF4.CERT12CompactClosure

#print axioms PF4.CERT12CompactClosure.normalized_compact_band_signs
