/-
Copyright (c) 2026 ultimussaeculi. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: Joshuah Rainstar
-/

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Monotone.Basic

set_option linter.style.header false

/-!
# Target-level definitions

This file fixes the first Lean representation of translation minors and finite
Pólya-frequency order. It proves only definitional infrastructure; it does not
assume any property of the Riemann kernel.
-/

namespace PF4

/-- The translation-kernel matrix at two indexed node families. -/
def translationMatrix {n : ℕ} (f : ℝ → ℝ) (x y : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ f (x i - y j)

/-- The determinant of the translation-kernel matrix. -/
def translationMinor {n : ℕ} (f : ℝ → ℝ) (x y : Fin n → ℝ) : ℝ :=
  (translationMatrix f x y).det

/-- Nonnegative translation minors at every strictly ordered pair of node
families of orders `1, …, r`. -/
def PFUpTo (f : ℝ → ℝ) (r : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ r →
    ∀ x y : Fin k → ℝ, StrictMono x → StrictMono y →
      0 ≤ translationMinor f x y

/-- Strictly positive translation minors at every strictly ordered pair of
node families of orders `1, …, r`. -/
def StrictPFUpTo (f : ℝ → ℝ) (r : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ r →
    ∀ x y : Fin k → ℝ, StrictMono x → StrictMono y →
      0 < translationMinor f x y

/-- Exact finite PF order: nonnegative through `r`, but not through `r+1`. -/
def PFOrderExactly (f : ℝ → ℝ) (r : ℕ) : Prop :=
  PFUpTo f r ∧ ¬PFUpTo f (r + 1)

theorem StrictPFUpTo.pfUpTo {f : ℝ → ℝ} {r : ℕ}
    (h : StrictPFUpTo f r) : PFUpTo f r := by
  intro k hk₁ hkr x y hx hy
  exact (h k hk₁ hkr x y hx hy).le

/-- The signed grid difference used in Toeplitz witnesses. The explicit
integer coercions prevent truncated natural-number subtraction. -/
def signedIndexDifference {n : ℕ} (i j : Fin n) : ℤ :=
  ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)

/-- An equally spaced Toeplitz translation matrix with signed index
differences. -/
def equallySpacedMatrix {n : ℕ} (f : ℝ → ℝ) (u h : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ f (u + ((signedIndexDifference i j : ℤ) : ℝ) * h)

end PF4
