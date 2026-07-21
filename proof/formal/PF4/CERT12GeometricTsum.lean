/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import PF4.CERT12TailExponential
import Mathlib.Analysis.SpecificLimits.Basic

set_option linter.style.header false

/-!
# Geometric control of the complete CERT12 tail

These lemmas consume pointwise bounds for every natural index and conclude a
bound on the actual infinite sum.  They contain no finite cutoff.
-/

namespace PF4.CERT12GeometricTsum

theorem norm_tsum_le_of_geometric_bound
    (f : ℕ → ℝ) (A q : ℝ)
    (_hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ r, ‖f r‖ ≤ A * q ^ r) :
    ‖∑' r, f r‖ ≤ A * (1 - q)⁻¹ := by
  have hgeom : HasSum (fun r : ℕ => A * q ^ r) (A * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left A
  exact tsum_of_norm_bounded hgeom hbound

theorem norm_tsum_lt_relative_of_geometric_bound
    (f : ℕ → ℝ) (A q reference ε : ℝ)
    (hA : 0 ≤ A) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound : ∀ r, ‖f r‖ ≤ A * q ^ r)
    (henvelope : A * (1 - q)⁻¹ < ε * ‖reference‖) :
    ‖∑' r, f r‖ < ε * ‖reference‖ :=
  (norm_tsum_le_of_geometric_bound f A q hA hq0 hq1 hbound).trans_lt
    henvelope

theorem signed_tsum_nonneg
    (f : ℕ → ℝ) (sign : ℝ)
    (hterm : ∀ r, 0 ≤ sign * f r) :
    0 ≤ sign * ∑' r, f r := by
  rw [← tsum_mul_left]
  exact tsum_nonneg hterm

end PF4.CERT12GeometricTsum

#print axioms PF4.CERT12GeometricTsum.norm_tsum_le_of_geometric_bound
#print axioms PF4.CERT12GeometricTsum.norm_tsum_lt_relative_of_geometric_bound
#print axioms PF4.CERT12GeometricTsum.signed_tsum_nonneg
