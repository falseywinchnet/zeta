import PF4.ClearedJetCertificateBridge
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact finite-polynomial perturbation semantics

Coordinatewise bounds imply a deterministic error budget for every monomial
and hence every finite rational polynomial.  No numerical approximation enters
these theorems.
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
      have hprod_x : |∏ i ∈ s, x i| ≤ ∏ i ∈ s, M i := by
        rw [abs_prod]
        exact prod_le_prod (fun i hi => abs_nonneg _) hxs
      have htail := ih hxs hys hMs
      have hbudget_nonneg :
          0 ≤ ∑ i ∈ s, |x i - y i| * ∏ j ∈ s.erase i, M j := by
        apply sum_nonneg
        intro i hi
        exact mul_nonneg (abs_nonneg _)
          (prod_nonneg fun j hj => hMs j (mem_of_mem_erase hj))
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
              |y a| * (∑ i ∈ s,
                |x i - y i| * ∏ j ∈ s.erase i, M j) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hprod_x (abs_nonneg _))
                  (mul_le_mul_of_nonneg_left htail (abs_nonneg _))
        _ ≤ |x a - y a| * ∏ i ∈ s, M i +
              M a * (∑ i ∈ s,
                |x i - y i| * ∏ j ∈ s.erase i, M j) := by
                exact add_le_add_right
                  (mul_le_mul_of_nonneg_right hya hbudget_nonneg) _
        _ = ∑ i ∈ insert a s,
              |x i - y i| * ∏ j ∈ (insert a s).erase i, M j := by
                rw [sum_insert ha]
                rw [erase_insert ha]
                apply congrArg (fun z => |x a - y a| * ∏ i ∈ s, M i + z)
                rw [mul_sum]
                apply sum_congr rfl
                intro i hi
                have hai : a ≠ i := fun h => ha (h ▸ hi)
                rw [erase_insert_of_ne hai]
                rw [prod_insert]
                · ring
                · exact fun hmem => ha (mem_of_mem_erase hmem)

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

/-- A normalization form for erased products.  It lets the kernel reduce a
fixed finite product coordinate by coordinate without trusting an evaluator. -/
theorem prod_univ_erase_eq_prod_ite {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i, f j) =
      ∏ j, if j = i then 1 else f j := by
  classical
  simpa [Finset.mem_erase] using
    (Fintype.prod_ite_mem (Finset.univ.erase i) f).symm

/-- Fully explicit seven-coordinate erased product used by CERT12. -/
theorem prod_fin7_erase (f : Fin 7 → ℝ) (i : Fin 7) :
    (∏ j ∈ Finset.univ.erase i, f j) =
      ![f 1 * f 2 * f 3 * f 4 * f 5 * f 6,
        f 0 * f 2 * f 3 * f 4 * f 5 * f 6,
        f 0 * f 1 * f 3 * f 4 * f 5 * f 6,
        f 0 * f 1 * f 2 * f 4 * f 5 * f 6,
        f 0 * f 1 * f 2 * f 3 * f 5 * f 6,
        f 0 * f 1 * f 2 * f 3 * f 4 * f 6,
        f 0 * f 1 * f 2 * f 3 * f 4 * f 5] i := by
  fin_cases i <;> rw [prod_univ_erase_eq_prod_ite] <;>
    simp [Fin.prod_univ_succ] <;> ring

@[simp] theorem vec7_apply_five {α : Type*}
    (a0 a1 a2 a3 a4 a5 a6 : α) :
    (![a0, a1, a2, a3, a4, a5, a6] : Fin 7 → α) 5 = a5 := rfl

@[simp] theorem vec7_apply_six {α : Type*}
    (a0 a1 a2 a3 a4 a5 a6 : α) :
    (![a0, a1, a2, a3, a4, a5, a6] : Fin 7 → α) 6 = a6 := rfl

theorem abs_pow_add_sub_pow_le
    {a e B E : ℝ} {p : ℕ}
    (_hB : 0 ≤ B) (hE : 0 ≤ E) (ha : |a| ≤ B) (he : |e| ≤ E) :
    |(a + e) ^ p - a ^ p| ≤ E * p * (B + E) ^ (p - 1) := by
  have hae : |a + e| ≤ B + E :=
    (abs_add_le a e).trans (add_le_add ha he)
  have ha' : |a| ≤ B + E := ha.trans (le_add_of_nonneg_right hE)
  calc
    |(a + e) ^ p - a ^ p| ≤
        |a + e - a| * p * max |a + e| |a| ^ (p - 1) :=
      abs_pow_sub_pow_le (a + e) a p
    _ ≤ E * p * (B + E) ^ (p - 1) := by
      simp only [add_sub_cancel_left]
      have hmax : max |a + e| |a| ≤ B + E := max_le hae ha'
      have hmax0 : 0 ≤ max |a + e| |a| :=
        (abs_nonneg _).trans (le_max_left _ _)
      have hpow : max |a + e| |a| ^ (p - 1) ≤
          (B + E) ^ (p - 1) :=
        pow_le_pow_left₀ hmax0 hmax _
      calc
        |e| * (p : ℝ) * max |a + e| |a| ^ (p - 1) ≤
            E * (p : ℝ) * max |a + e| |a| ^ (p - 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg p))
            (pow_nonneg hmax0 _)
        _ ≤ E * (p : ℝ) * (B + E) ^ (p - 1) := by
          exact mul_le_mul_of_nonneg_left hpow
            (mul_nonneg hE (Nat.cast_nonneg p))

theorem abs_monomialValue_add_sub_le
    {n : ℕ} (p : Fin n → ℕ) (a e B E : Fin n → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hE : ∀ i, 0 ≤ E i)
    (ha : ∀ i, |a i| ≤ B i) (he : ∀ i, |e i| ≤ E i) :
    |monomialValue p (fun i => a i + e i) - monomialValue p a| ≤
      monomialErrorBudget p B E := by
  classical
  unfold monomialValue monomialErrorBudget
  have hxpow : ∀ i ∈ Finset.univ,
      |(a i + e i) ^ p i| ≤ (B i + E i) ^ p i := by
    intro i hi
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans
      (add_le_add (ha i) (he i))) _
  have hapow : ∀ i ∈ Finset.univ,
      |a i ^ p i| ≤ (B i + E i) ^ p i := by
    intro i hi
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) ((ha i).trans
      (le_add_of_nonneg_right (hE i))) _
  have hMpow : ∀ i ∈ Finset.univ, 0 ≤ (B i + E i) ^ p i := by
    intro i hi
    exact pow_nonneg (add_nonneg (hB i) (hE i)) _
  have hprod := abs_prod_sub_prod_le Finset.univ
    (fun i => (a i + e i) ^ p i)
    (fun i => a i ^ p i)
    (fun i => (B i + E i) ^ p i) hxpow hapow hMpow
  apply hprod.trans
  apply sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right
  · exact abs_pow_add_sub_pow_le (hB i) (hE i) (ha i) (he i)
  · exact prod_nonneg fun j hj =>
      pow_nonneg (add_nonneg (hB j) (hE j)) _

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
  have habs := abs_sum_le_sum_abs
    (fun r => ((terms r).coeff : ℝ) *
      monomialValue (terms r).powers (fun i => a i + e i) -
      ((terms r).coeff : ℝ) * monomialValue (terms r).powers a)
    Finset.univ
  apply habs.trans
  apply sum_le_sum
  intro r hr
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_monomialValue_add_sub_le _ _ _ _ _ hB hE ha he)
    (abs_nonneg _)

end PF4.CERT12Inequalities.Perturbation
