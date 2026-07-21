import PF4.CERT12Perturbation
import Mathlib.Tactic

set_option linter.style.header false

set_option linter.style.longLine false
set_option linter.style.setOption false

set_option maxHeartbeats 2000000

set_option maxRecDepth 100000

/-! Exact generated perturbation budgets; promoted from the replayable CERT12 artifact. -/

namespace PF4.CERT12Inequalities.Perturbation.Generated

open PF4.CERT12Inequalities.Perturbation

def coreB : Fin 7 → ℝ := ![2, 5, 20, 200, 2000, 60000, 1000000]
noncomputable def coreE : Fin 7 → ℝ := ![(7 / 1000000000 : ℝ), (1 / 2500000 : ℝ), (1 / 5000 : ℝ), (7 / 10000 : ℝ), (3 / 100 : ℝ), (11 / 10 : ℝ), 41]
def outerB : Fin 7 → ℝ := ![4, 40, 400, 4000, 40000, 400000, 4000000]
noncomputable def outerE : Fin 7 → ℝ := ![(81 / 50000000000000000 : ℝ), (729 / 5000000000000000 : ℝ), (6561 / 500000000000000 : ℝ), (59049 / 50000000000000 : ℝ), (531441 / 5000000000000 : ℝ), (4782969 / 500000000000 : ℝ), (43046721 / 50000000000 : ℝ)]
def qTerms : Fin 2 → Monomial 7 :=
  ![{ coeff := -1, powers := ![1, 0, 1, 0, 0, 0, 0] }, { coeff := 1, powers := ![0, 2, 0, 0, 0, 0, 0] }]
theorem qTerms_value (a : Fin 7 → ℝ) :
    polynomialValue qTerms a =
      PF4.ClearedJetCertificateBridge.clearedQ (a 0) (a 1) (a 2) := by
  simp [polynomialValue, qTerms, monomialValue, Fin.sum_univ_succ, Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.clearedQ]
  ring

theorem qCoreBudget_lt :
    polynomialErrorBudget qTerms coreB coreE < 10 := by
  norm_num (config := { maxSteps := 10000000 }) [polynomialErrorBudget, monomialErrorBudget, qTerms, coreB, coreE, Fin.sum_univ_succ, prod_fin7_erase, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.prod_univ_succ]

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
  norm_num (config := { maxSteps := 10000000 }) [polynomialErrorBudget, monomialErrorBudget, qTerms, outerB, outerE, Fin.sum_univ_succ, prod_fin7_erase, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.prod_univ_succ]

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
  ![{ coeff := -1, powers := ![4, 0, 1, 0, 1, 0, 0] }, { coeff := 1, powers := ![4, 0, 0, 2, 0, 0, 0] }, { coeff := 1, powers := ![3, 2, 0, 0, 1, 0, 0] }, { coeff := -2, powers := ![3, 1, 1, 1, 0, 0, 0] }, { coeff := 2, powers := ![3, 0, 3, 0, 0, 0, 0] }, { coeff := -3, powers := ![2, 2, 2, 0, 0, 0, 0] }, { coeff := 3, powers := ![1, 4, 1, 0, 0, 0, 0] }, { coeff := -1, powers := ![0, 6, 0, 0, 0, 0, 0] }]
theorem f2Terms_value (a : Fin 7 → ℝ) :
    polynomialValue f2Terms a =
      PF4.ClearedJetCertificateBridge.clearedF2 (a 0) (a 1) (a 2) (a 3) (a 4) := by
  simp [polynomialValue, f2Terms, monomialValue, Fin.sum_univ_succ, Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.clearedF2]
  ring

theorem f2CoreBudget_lt :
    polynomialErrorBudget f2Terms coreB coreE < 1000 := by
  norm_num (config := { maxSteps := 10000000 }) [polynomialErrorBudget, monomialErrorBudget, f2Terms, coreB, coreE, Fin.sum_univ_succ, prod_fin7_erase, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.prod_univ_succ]

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
  norm_num (config := { maxSteps := 10000000 }) [polynomialErrorBudget, monomialErrorBudget, f2Terms, outerB, outerE, Fin.sum_univ_succ, prod_fin7_erase, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.prod_univ_succ]

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
  ![{ coeff := 1, powers := ![1, 0, 1, 0, 1, 0, 1] }, { coeff := -1, powers := ![1, 0, 1, 0, 0, 2, 0] }, { coeff := -1, powers := ![1, 0, 0, 2, 0, 0, 1] }, { coeff := 2, powers := ![1, 0, 0, 1, 1, 1, 0] }, { coeff := -1, powers := ![1, 0, 0, 0, 3, 0, 0] }, { coeff := -1, powers := ![0, 2, 0, 0, 1, 0, 1] }, { coeff := 1, powers := ![0, 2, 0, 0, 0, 2, 0] }, { coeff := 2, powers := ![0, 1, 1, 1, 0, 0, 1] }, { coeff := -2, powers := ![0, 1, 1, 0, 1, 1, 0] }, { coeff := -2, powers := ![0, 1, 0, 2, 0, 1, 0] }, { coeff := 2, powers := ![0, 1, 0, 1, 2, 0, 0] }, { coeff := -1, powers := ![0, 0, 3, 0, 0, 0, 1] }, { coeff := 2, powers := ![0, 0, 2, 1, 0, 1, 0] }, { coeff := 1, powers := ![0, 0, 2, 0, 2, 0, 0] }, { coeff := -3, powers := ![0, 0, 1, 2, 1, 0, 0] }, { coeff := 1, powers := ![0, 0, 0, 4, 0, 0, 0] }]
theorem c4Terms_value (a : Fin 7 → ℝ) :
    polynomialValue c4Terms a =
      PF4.ClearedJetCertificateBridge.clearedC4 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) := by
  simp [polynomialValue, c4Terms, monomialValue, Fin.sum_univ_succ, Fin.prod_univ_succ, PF4.ClearedJetCertificateBridge.clearedC4]
  ring

theorem c4CoreBudget_lt :
    polynomialErrorBudget c4Terms coreB coreE < 50000000 := by
  norm_num (config := { maxSteps := 10000000 }) [polynomialErrorBudget, monomialErrorBudget, c4Terms, coreB, coreE, Fin.sum_univ_succ, prod_fin7_erase, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.prod_univ_succ]

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
  norm_num (config := { maxSteps := 10000000 }) [polynomialErrorBudget, monomialErrorBudget, c4Terms, outerB, outerE, Fin.sum_univ_succ, prod_fin7_erase, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Fin.prod_univ_succ]

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
