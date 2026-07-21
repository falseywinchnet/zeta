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


namespace PF4.CERT12Inequalities.Perturbation.Generated

open PF4.CERT12Inequalities.Perturbation

def coreB : Fin 7 → ℝ := ![2, 5, 20, 200, 2000, 60000, 1000000]
def coreE : Fin 7 → ℝ := ![(7 / 1000000000 : ℝ), (1 / 2500000 : ℝ), (1 / 5000 : ℝ), (7 / 10000 : ℝ), (3 / 100 : ℝ), (11 / 10 : ℝ), 41]
def outerB : Fin 7 → ℝ := ![4, 40, 400, 4000, 40000, 400000, 4000000]
def outerE : Fin 7 → ℝ := ![(81 / 50000000000000000 : ℝ), (729 / 5000000000000000 : ℝ), (6561 / 500000000000000 : ℝ), (59049 / 50000000000000 : ℝ), (531441 / 5000000000000 : ℝ), (4782969 / 500000000000 : ℝ), (43046721 / 50000000000 : ℝ)]
def qTerms : Fin 2 → Monomial 7 :=
  ![{ coeff := -1; powers := ![1, 0, 1, 0, 0, 0, 0] }, { coeff := 1; powers := ![0, 2, 0, 0, 0, 0, 0] }]
theorem qTerms_value (a : Fin 7 → ℝ) :
    polynomialValue qTerms a =
      PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2) := by
  simp [polynomialValue, qTerms, monomialValue, Fin.sum_univ_succ, Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.clearedQ]
  ring

theorem qCoreBudget_lt :
    polynomialErrorBudget qTerms coreB coreE < 10 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, qTerms, coreB, coreE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_q_perturbation_lt_core
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i) :
    |PF4.ClearedJetCertificateBridge.clearedQ (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) - PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2)| < 10 := by
  have h := abs_polynomialValue_add_sub_le qTerms a e coreB coreE
    (by intro i; fin_cases i <;> norm_num [coreB])
    (by intro i; fin_cases i <;> norm_num [coreE]) ha he
  rw [qTerms_value, qTerms_value] at h
  exact h.trans_lt qCoreBudget_lt

theorem qOuterBudget_lt :
    polynomialErrorBudget qTerms outerB outerE < 10 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, qTerms, outerB, outerE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_q_perturbation_lt_outer
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ outerB i) (he : ∀ i, |e i| ≤ outerE i) :
    |PF4.ClearedJetCertificateBridge.clearedQ (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) - PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2)| < 10 := by
  have h := abs_polynomialValue_add_sub_le qTerms a e outerB outerE
    (by intro i; fin_cases i <;> norm_num [outerB])
    (by intro i; fin_cases i <;> norm_num [outerE]) ha he
  rw [qTerms_value, qTerms_value] at h
  exact h.trans_lt qOuterBudget_lt

def f2Terms : Fin 8 → Monomial 7 :=
  ![{ coeff := -1; powers := ![4, 0, 1, 0, 1, 0, 0] }, { coeff := 1; powers := ![4, 0, 0, 2, 0, 0, 0] }, { coeff := 1; powers := ![3, 2, 0, 0, 1, 0, 0] }, { coeff := -2; powers := ![3, 1, 1, 1, 0, 0, 0] }, { coeff := 2; powers := ![3, 0, 3, 0, 0, 0, 0] }, { coeff := -3; powers := ![2, 2, 2, 0, 0, 0, 0] }, { coeff := 3; powers := ![1, 4, 1, 0, 0, 0, 0] }, { coeff := -1; powers := ![0, 6, 0, 0, 0, 0, 0] }]
theorem f2Terms_value (a : Fin 7 → ℝ) :
    polynomialValue f2Terms a =
      PF4.ClearedJetCertificateBridge.clearedF2 (a 0) (a 1) (a 2) (a 3) (a 4) := by
  simp [polynomialValue, f2Terms, monomialValue, Fin.sum_univ_succ, Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.clearedF2]
  ring

theorem f2CoreBudget_lt :
    polynomialErrorBudget f2Terms coreB coreE < 1000 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, f2Terms, coreB, coreE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_f2_perturbation_lt_core
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i) :
    |PF4.ClearedJetCertificateBridge.clearedF2 (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) - PF4.ClearedJetCertificateBridge.clearedF2 (a 0) (a 1) (a 2) (a 3) (a 4)| < 1000 := by
  have h := abs_polynomialValue_add_sub_le f2Terms a e coreB coreE
    (by intro i; fin_cases i <;> norm_num [coreB])
    (by intro i; fin_cases i <;> norm_num [coreE]) ha he
  rw [f2Terms_value, f2Terms_value] at h
  exact h.trans_lt f2CoreBudget_lt

theorem f2OuterBudget_lt :
    polynomialErrorBudget f2Terms outerB outerE < 1000 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, f2Terms, outerB, outerE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_f2_perturbation_lt_outer
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ outerB i) (he : ∀ i, |e i| ≤ outerE i) :
    |PF4.ClearedJetCertificateBridge.clearedF2 (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) - PF4.ClearedJetCertificateBridge.clearedF2 (a 0) (a 1) (a 2) (a 3) (a 4)| < 1000 := by
  have h := abs_polynomialValue_add_sub_le f2Terms a e outerB outerE
    (by intro i; fin_cases i <;> norm_num [outerB])
    (by intro i; fin_cases i <;> norm_num [outerE]) ha he
  rw [f2Terms_value, f2Terms_value] at h
  exact h.trans_lt f2OuterBudget_lt

def c4Terms : Fin 16 → Monomial 7 :=
  ![{ coeff := 1; powers := ![1, 0, 1, 0, 1, 0, 1] }, { coeff := -1; powers := ![1, 0, 1, 0, 0, 2, 0] }, { coeff := -1; powers := ![1, 0, 0, 2, 0, 0, 1] }, { coeff := 2; powers := ![1, 0, 0, 1, 1, 1, 0] }, { coeff := -1; powers := ![1, 0, 0, 0, 3, 0, 0] }, { coeff := -1; powers := ![0, 2, 0, 0, 1, 0, 1] }, { coeff := 1; powers := ![0, 2, 0, 0, 0, 2, 0] }, { coeff := 2; powers := ![0, 1, 1, 1, 0, 0, 1] }, { coeff := -2; powers := ![0, 1, 1, 0, 1, 1, 0] }, { coeff := -2; powers := ![0, 1, 0, 2, 0, 1, 0] }, { coeff := 2; powers := ![0, 1, 0, 1, 2, 0, 0] }, { coeff := -1; powers := ![0, 0, 3, 0, 0, 0, 1] }, { coeff := 2; powers := ![0, 0, 2, 1, 0, 1, 0] }, { coeff := 1; powers := ![0, 0, 2, 0, 2, 0, 0] }, { coeff := -3; powers := ![0, 0, 1, 2, 1, 0, 0] }, { coeff := 1; powers := ![0, 0, 0, 4, 0, 0, 0] }]
theorem c4Terms_value (a : Fin 7 → ℝ) :
    polynomialValue c4Terms a =
      PF4.ClearedJetCertificateBridge.clearedC4 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) := by
  simp [polynomialValue, c4Terms, monomialValue, Fin.sum_univ_succ, Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.clearedC4]
  ring

theorem c4CoreBudget_lt :
    polynomialErrorBudget c4Terms coreB coreE < 50000000 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, c4Terms, coreB, coreE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_c4_perturbation_lt_core
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i) :
    |PF4.ClearedJetCertificateBridge.clearedC4 (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) (a 5 + e 5) (a 6 + e 6) - PF4.ClearedJetCertificateBridge.clearedC4 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)| < 50000000 := by
  have h := abs_polynomialValue_add_sub_le c4Terms a e coreB coreE
    (by intro i; fin_cases i <;> norm_num [coreB])
    (by intro i; fin_cases i <;> norm_num [coreE]) ha he
  rw [c4Terms_value, c4Terms_value] at h
  exact h.trans_lt c4CoreBudget_lt

theorem c4OuterBudget_lt :
    polynomialErrorBudget c4Terms outerB outerE < 50000000 := by
  norm_num [polynomialErrorBudget, monomialErrorBudget, c4Terms, outerB, outerE, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem abs_c4_perturbation_lt_outer
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ outerB i) (he : ∀ i, |e i| ≤ outerE i) :
    |PF4.ClearedJetCertificateBridge.clearedC4 (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) (a 5 + e 5) (a 6 + e 6) - PF4.ClearedJetCertificateBridge.clearedC4 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)| < 50000000 := by
  have h := abs_polynomialValue_add_sub_le c4Terms a e outerB outerE
    (by intro i; fin_cases i <;> norm_num [outerB])
    (by intro i; fin_cases i <;> norm_num [outerE]) ha he
  rw [c4Terms_value, c4Terms_value] at h
  exact h.trans_lt c4OuterBudget_lt


theorem clearedQ_pos_of_base_margin_and_core_error
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i)
    (hbase : 10 < PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2)) :
    0 < PF4.ClearedJetCertificateBridge.clearedQ
      (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) := by
  have h := abs_q_perturbation_lt_core a e ha he
  rw [abs_lt] at h
  linarith

theorem clearedF2_pos_of_base_margin_and_core_error
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i)
    (hbase : 1000 < PF4.ClearedJetCertificateBridge.clearedF2
      (a 0) (a 1) (a 2) (a 3) (a 4)) :
    0 < PF4.ClearedJetCertificateBridge.clearedF2
      (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3) (a 4 + e 4) := by
  have h := abs_f2_perturbation_lt_core a e ha he
  rw [abs_lt] at h
  linarith

theorem clearedC4_pos_of_base_margin_and_core_error
    (a e : Fin 7 → ℝ)
    (ha : ∀ i, |a i| ≤ coreB i) (he : ∀ i, |e i| ≤ coreE i)
    (hbase : 50000000 < PF4.ClearedJetCertificateBridge.clearedC4
      (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6)) :
    0 < PF4.ClearedJetCertificateBridge.clearedC4
      (a 0 + e 0) (a 1 + e 1) (a 2 + e 2) (a 3 + e 3)
      (a 4 + e 4) (a 5 + e 5) (a 6 + e 6) := by
  have h := abs_c4_perturbation_lt_core a e ha he
  rw [abs_lt] at h
  linarith

end PF4.CERT12Inequalities.Perturbation.Generated
