import PF4.TranslationQuotientAssembly
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Fixed order-three and order-four quotient/Wronskian identities

These are the two literal Wronskian equations printed in S05.  They are
finite algebraic identities for the maintained quotient tower; arbitrary-order
Wronskian algebra is deliberately not part of this module.
-/

namespace PF4.FixedOrderQuotientWronskian

open PF4.TranslationQuotientTower

/-- The order-three translate Wronskian at one row point. -/
noncomputable def translateWronskian3
    (Φ Φ1 Φ2 : ℝ → ℝ) (t y₁ y₂ y₃ : ℝ) : ℝ :=
  (!![Φ (t - y₁), Φ (t - y₂), Φ (t - y₃);
      Φ1 (t - y₁), Φ1 (t - y₂), Φ1 (t - y₃);
      Φ2 (t - y₁), Φ2 (t - y₂), Φ2 (t - y₃)] :
    Matrix (Fin 3) (Fin 3) ℝ).det

/-- The order-two Wronskian of the first quotient derivatives. -/
noncomputable def firstQuotWronskian2
    (Φ Φ1 Φ2 : ℝ → ℝ) (t y₁ y₂ y₃ : ℝ) : ℝ :=
  (!![firstQuotD Φ Φ1 y₁ y₂ t, firstQuotD Φ Φ1 y₁ y₃ t;
      firstQuotD2 Φ Φ1 Φ2 y₁ y₂ t,
        firstQuotD2 Φ Φ1 Φ2 y₁ y₃ t] :
    Matrix (Fin 2) (Fin 2) ℝ).det

/-- S05 equation `W3 = u₁³ W(v₂,v₃)`, with no sign hypothesis. -/
theorem translateWronskian3_eq_firstQuotWronskian2
    {Φ Φ1 Φ2 : ℝ → ℝ} {t y₁ y₂ y₃ : ℝ}
    (hΦ : Φ (t - y₁) ≠ 0) :
    translateWronskian3 Φ Φ1 Φ2 t y₁ y₂ y₃ =
      Φ (t - y₁) ^ 3 * firstQuotWronskian2 Φ Φ1 Φ2 t y₁ y₂ y₃ := by
  unfold translateWronskian3 firstQuotWronskian2 firstQuotD firstQuotD2
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  field_simp [hΦ]
  ring

/-- The order-four translate Wronskian at one row point. -/
noncomputable def translateWronskian4
    (Φ Φ1 Φ2 Φ3 : ℝ → ℝ) (t y₁ y₂ y₃ y₄ : ℝ) : ℝ :=
  (!![Φ (t - y₁), Φ (t - y₂), Φ (t - y₃), Φ (t - y₄);
      Φ1 (t - y₁), Φ1 (t - y₂), Φ1 (t - y₃), Φ1 (t - y₄);
      Φ2 (t - y₁), Φ2 (t - y₂), Φ2 (t - y₃), Φ2 (t - y₄);
      Φ3 (t - y₁), Φ3 (t - y₂), Φ3 (t - y₃), Φ3 (t - y₄)] :
    Matrix (Fin 4) (Fin 4) ℝ).det

/-- The order-three Wronskian of `v₂,v₃,v₄`. -/
noncomputable def firstQuotWronskian3
    (Φ Φ1 Φ2 Φ3 : ℝ → ℝ) (t y₁ y₂ y₃ y₄ : ℝ) : ℝ :=
  (!![firstQuotD Φ Φ1 y₁ y₂ t, firstQuotD Φ Φ1 y₁ y₃ t,
        firstQuotD Φ Φ1 y₁ y₄ t;
      firstQuotD2 Φ Φ1 Φ2 y₁ y₂ t,
        firstQuotD2 Φ Φ1 Φ2 y₁ y₃ t,
        firstQuotD2 Φ Φ1 Φ2 y₁ y₄ t;
      firstQuotD3 Φ Φ1 Φ2 Φ3 y₁ y₂ t,
        firstQuotD3 Φ Φ1 Φ2 Φ3 y₁ y₃ t,
        firstQuotD3 Φ Φ1 Φ2 Φ3 y₁ y₄ t] :
    Matrix (Fin 3) (Fin 3) ℝ).det

/-- First fixed-order quotient extraction at order four. -/
theorem translateWronskian4_eq_firstQuotWronskian3
    {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {t y₁ y₂ y₃ y₄ : ℝ}
    (hΦ : Φ (t - y₁) ≠ 0) :
    translateWronskian4 Φ Φ1 Φ2 Φ3 t y₁ y₂ y₃ y₄ =
      Φ (t - y₁) ^ 4 *
        firstQuotWronskian3 Φ Φ1 Φ2 Φ3 t y₁ y₂ y₃ y₄ := by
  unfold translateWronskian4 firstQuotWronskian3 firstQuotD firstQuotD2
    firstQuotD3
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove]
  field_simp [hΦ]
  ring

/-- The order-two Wronskian of `w₃,w₄`. -/
noncomputable def secondQuotWronskian2
    (Φ Φ1 Φ2 Φ3 : ℝ → ℝ) (t y₁ y₂ y₃ y₄ : ℝ) : ℝ :=
  (!![secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t,
        secondQuotD Φ Φ1 Φ2 y₁ y₂ y₄ t;
      secondQuotD2 Φ Φ1 Φ2 Φ3 y₁ y₂ y₃ t,
        secondQuotD2 Φ Φ1 Φ2 Φ3 y₁ y₂ y₄ t] :
    Matrix (Fin 2) (Fin 2) ℝ).det

/-- Second fixed-order quotient extraction:
`W(v₂,v₃,v₄)=v₂³W(w₃,w₄)`. -/
theorem firstQuotWronskian3_eq_secondQuotWronskian2
    {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {t y₁ y₂ y₃ y₄ : ℝ}
    (hv₂ : firstQuotD Φ Φ1 y₁ y₂ t ≠ 0) :
    firstQuotWronskian3 Φ Φ1 Φ2 Φ3 t y₁ y₂ y₃ y₄ =
      firstQuotD Φ Φ1 y₁ y₂ t ^ 3 *
        secondQuotWronskian2 Φ Φ1 Φ2 Φ3 t y₁ y₂ y₃ y₄ := by
  unfold firstQuotWronskian3 secondQuotWronskian2 secondQuotD secondQuotD2
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  field_simp [hv₂]
  ring

/-- Terminal quotient extraction:
`W(w₃,w₄)=w₃² (w₄/w₃)'`. -/
theorem secondQuotWronskian2_eq_terminal
    {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {t y₁ y₂ y₃ y₄ : ℝ}
    (hw₃ : secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t ≠ 0) :
    secondQuotWronskian2 Φ Φ1 Φ2 Φ3 t y₁ y₂ y₃ y₄ =
      secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t ^ 2 *
        terminalQuotD Φ Φ1 Φ2 Φ3 y₁ y₂ y₃ y₄ t := by
  unfold secondQuotWronskian2 terminalQuotD
  simp [Matrix.det_fin_two]
  field_simp [hw₃]

/-- S05 equation `W4 = u₁⁴ v₂³ w₃² (w₄/w₃)'`, assembled from the
three exact finite quotient extractions. -/
theorem translateWronskian4_eq_terminalProduct
    {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {t y₁ y₂ y₃ y₄ : ℝ}
    (hΦ : Φ (t - y₁) ≠ 0)
    (hv₂ : firstQuotD Φ Φ1 y₁ y₂ t ≠ 0)
    (hw₃ : secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t ≠ 0) :
    translateWronskian4 Φ Φ1 Φ2 Φ3 t y₁ y₂ y₃ y₄ =
      Φ (t - y₁) ^ 4 * firstQuotD Φ Φ1 y₁ y₂ t ^ 3 *
        secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t ^ 2 *
          terminalQuotD Φ Φ1 Φ2 Φ3 y₁ y₂ y₃ y₄ t := by
  rw [translateWronskian4_eq_firstQuotWronskian3 hΦ,
    firstQuotWronskian3_eq_secondQuotWronskian2 hv₂,
    secondQuotWronskian2_eq_terminal hw₃]
  ring

/-- Increasing translate columns give the reversed original arguments used by
the paper: `p₄<p₃<p₂<p₁`. -/
theorem translateArguments_reverse
    {t y₁ y₂ y₃ y₄ : ℝ}
    (hy₁₂ : y₁ < y₂) (hy₂₃ : y₂ < y₃) (hy₃₄ : y₃ < y₄) :
    t - y₄ < t - y₃ ∧ t - y₃ < t - y₂ ∧ t - y₂ < t - y₁ := by
  constructor
  · linarith
  constructor <;> linarith

/-- PO-0017 at the paper's actual fixed order: the two displayed Wronskian
factorizations and their endpoint orientation. -/
theorem fixedOrderFour_quotientWronskian_package
    {Φ Φ1 Φ2 Φ3 : ℝ → ℝ} {t y₁ y₂ y₃ y₄ : ℝ}
    (hy₁₂ : y₁ < y₂) (hy₂₃ : y₂ < y₃) (hy₃₄ : y₃ < y₄)
    (hΦ : Φ (t - y₁) ≠ 0)
    (hv₂ : firstQuotD Φ Φ1 y₁ y₂ t ≠ 0)
    (hw₃ : secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t ≠ 0) :
    (t - y₄ < t - y₃ ∧ t - y₃ < t - y₂ ∧ t - y₂ < t - y₁) ∧
    translateWronskian3 Φ Φ1 Φ2 t y₁ y₂ y₃ =
      Φ (t - y₁) ^ 3 * firstQuotWronskian2 Φ Φ1 Φ2 t y₁ y₂ y₃ ∧
    translateWronskian4 Φ Φ1 Φ2 Φ3 t y₁ y₂ y₃ y₄ =
      Φ (t - y₁) ^ 4 * firstQuotD Φ Φ1 y₁ y₂ t ^ 3 *
        secondQuotD Φ Φ1 Φ2 y₁ y₂ y₃ t ^ 2 *
          terminalQuotD Φ Φ1 Φ2 Φ3 y₁ y₂ y₃ y₄ t := by
  exact ⟨translateArguments_reverse hy₁₂ hy₂₃ hy₃₄,
    translateWronskian3_eq_firstQuotWronskian2 hΦ,
    translateWronskian4_eq_terminalProduct hΦ hv₂ hw₃⟩

end PF4.FixedOrderQuotientWronskian
