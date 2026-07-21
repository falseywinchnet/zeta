import PF4.ClearedJetCertificateBridge
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

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
