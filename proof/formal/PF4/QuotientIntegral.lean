import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.header false

namespace PF4.ContinuousQuotientBox

open Matrix Set intervalIntegral

/-- The explicit determinant of three row vectors. -/
def rowDet3
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ : ℝ) : ℝ :=
  a₀ * (b₁*c₂-c₁*b₂) - b₀ * (a₁*c₂-c₁*a₂) +
    c₀ * (a₁*b₂-b₁*a₂)

/-- The determinant formula agrees with Mathlib's matrix determinant. -/
theorem rowDet3_eq_matrixDet
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ : ℝ) :
    rowDet3 a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ =
      (!![a₀,b₀,c₀; a₁,b₁,c₁; a₂,b₂,c₂] :
        Matrix (Fin 3) (Fin 3) ℝ).det := by
  simp [rowDet3, Matrix.det_fin_three]
  ring

theorem hasDerivAt_rowDet3_third
    {A B C A' B' C' : ℝ → ℝ} {t : ℝ}
    (a₀ b₀ c₀ a₁ b₁ c₁ : ℝ)
    (hA : HasDerivAt A (A' t) t)
    (hB : HasDerivAt B (B' t) t)
    (hC : HasDerivAt C (C' t) t) :
    HasDerivAt
      (fun s => rowDet3 a₀ b₀ c₀ a₁ b₁ c₁ (A s) (B s) (C s))
      (rowDet3 a₀ b₀ c₀ a₁ b₁ c₁ (A' t) (B' t) (C' t)) t := by
  unfold rowDet3
  convert
    (((hC.const_mul b₁).sub (hB.const_mul c₁)).const_mul a₀).sub
      (((hC.const_mul a₁).sub (hA.const_mul c₁)).const_mul b₀) |>.add
      (((hB.const_mul a₁).sub (hA.const_mul b₁)).const_mul c₀) using 1 <;> ring

theorem hasDerivAt_rowDet3_second
    {A B C A' B' C' : ℝ → ℝ} {t : ℝ}
    (a₀ b₀ c₀ a₂ b₂ c₂ : ℝ)
    (hA : HasDerivAt A (A' t) t)
    (hB : HasDerivAt B (B' t) t)
    (hC : HasDerivAt C (C' t) t) :
    HasDerivAt
      (fun s => rowDet3 a₀ b₀ c₀ (A s) (B s) (C s) a₂ b₂ c₂)
      (rowDet3 a₀ b₀ c₀ (A' t) (B' t) (C' t) a₂ b₂ c₂) t := by
  unfold rowDet3
  convert
    (((hB.const_mul c₂).sub (hC.const_mul b₂)).const_mul a₀).sub
      (((hA.const_mul c₂).sub (hC.const_mul a₂)).const_mul b₀) |>.add
      (((hA.const_mul b₂).sub (hB.const_mul a₂)).const_mul c₀) using 1 <;> ring

theorem hasDerivAt_rowDet3_first
    {A B C A' B' C' : ℝ → ℝ} {t : ℝ}
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ)
    (hA : HasDerivAt A (A' t) t)
    (hB : HasDerivAt B (B' t) t)
    (hC : HasDerivAt C (C' t) t) :
    HasDerivAt
      (fun s => rowDet3 (A s) (B s) (C s) a₁ b₁ c₁ a₂ b₂ c₂)
      (rowDet3 (A' t) (B' t) (C' t) a₁ b₁ c₁ a₂ b₂ c₂) t := by
  unfold rowDet3
  convert
    (hA.const_mul (b₁*c₂-c₁*b₂)).sub
      (hB.const_mul (a₁*c₂-c₁*a₂)) |>.add
      (hC.const_mul (a₁*b₂-b₁*a₂)) using 1 <;> ring

/-- Integrating the derivative row in the third slot replaces that row by
its oriented endpoint difference. -/
theorem integral_rowDet3_third
    {A B C A' B' C' : ℝ → ℝ} {x y : ℝ}
    (a₀ b₀ c₀ a₁ b₁ c₁ : ℝ)
    (hA : ∀ t ∈ uIcc x y, HasDerivAt A (A' t) t)
    (hB : ∀ t ∈ uIcc x y, HasDerivAt B (B' t) t)
    (hC : ∀ t ∈ uIcc x y, HasDerivAt C (C' t) t)
    (hA' : Continuous A') (hB' : Continuous B') (hC' : Continuous C') :
    (∫ t in x..y,
      rowDet3 a₀ b₀ c₀ a₁ b₁ c₁ (A' t) (B' t) (C' t)) =
      rowDet3 a₀ b₀ c₀ a₁ b₁ c₁
        (A y-A x) (B y-B x) (C y-C x) := by
  have hint : IntervalIntegrable
      (fun t => rowDet3 a₀ b₀ c₀ a₁ b₁ c₁ (A' t) (B' t) (C' t))
      volume x y := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_rowDet3_third a₀ b₀ c₀ a₁ b₁ c₁
      (hA t ht) (hB t ht) (hC t ht)) hint]
  unfold rowDet3
  ring

theorem integral_rowDet3_second
    {A B C A' B' C' : ℝ → ℝ} {x y : ℝ}
    (a₀ b₀ c₀ a₂ b₂ c₂ : ℝ)
    (hA : ∀ t ∈ uIcc x y, HasDerivAt A (A' t) t)
    (hB : ∀ t ∈ uIcc x y, HasDerivAt B (B' t) t)
    (hC : ∀ t ∈ uIcc x y, HasDerivAt C (C' t) t)
    (hA' : Continuous A') (hB' : Continuous B') (hC' : Continuous C') :
    (∫ t in x..y,
      rowDet3 a₀ b₀ c₀ (A' t) (B' t) (C' t) a₂ b₂ c₂) =
      rowDet3 a₀ b₀ c₀
        (A y-A x) (B y-B x) (C y-C x) a₂ b₂ c₂ := by
  have hint : IntervalIntegrable
      (fun t => rowDet3 a₀ b₀ c₀ (A' t) (B' t) (C' t) a₂ b₂ c₂)
      volume x y := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_rowDet3_second a₀ b₀ c₀ a₂ b₂ c₂
      (hA t ht) (hB t ht) (hC t ht)) hint]
  unfold rowDet3
  ring

theorem integral_rowDet3_first
    {A B C A' B' C' : ℝ → ℝ} {x y : ℝ}
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ)
    (hA : ∀ t ∈ uIcc x y, HasDerivAt A (A' t) t)
    (hB : ∀ t ∈ uIcc x y, HasDerivAt B (B' t) t)
    (hC : ∀ t ∈ uIcc x y, HasDerivAt C (C' t) t)
    (hA' : Continuous A') (hB' : Continuous B') (hC' : Continuous C') :
    (∫ t in x..y,
      rowDet3 (A' t) (B' t) (C' t) a₁ b₁ c₁ a₂ b₂ c₂) =
      rowDet3 (A y-A x) (B y-B x) (C y-C x)
        a₁ b₁ c₁ a₂ b₂ c₂ := by
  have hint : IntervalIntegrable
      (fun t => rowDet3 (A' t) (B' t) (C' t) a₁ b₁ c₁ a₂ b₂ c₂)
      volume x y := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_rowDet3_first a₁ b₁ c₁ a₂ b₂ c₂
      (hA t ht) (hB t ht) (hC t ht)) hint]
  unfold rowDet3
  ring

/-- The normalized four-row collocation determinant. -/
noncomputable def normalizedDet4
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ) : ℝ :=
  (!![1,a₀,b₀,c₀;
      1,a₁,b₁,c₁;
      1,a₂,b₂,c₂;
      1,a₃,b₃,c₃] : Matrix (Fin 4) (Fin 4) ℝ).det

/-- The normalized determinant is the determinant of the three consecutive
forward-difference rows. -/
theorem normalizedDet4_eq_rowDet3_forwardDiff
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ) :
    normalizedDet4 a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ =
      rowDet3
        (a₁-a₀) (b₁-b₀) (c₁-c₀)
        (a₂-a₁) (b₂-b₁) (c₂-c₁)
        (a₃-a₂) (b₃-b₂) (c₃-c₂) := by
  unfold normalizedDet4 rowDet3
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Fixed order-four iterated quotient integral, first stage. The normalized
collocation determinant is exactly the triple integral of the derivative-row
determinant over the three adjacent intervals. -/
theorem normalizedDet4_eq_tripleIntegral
    {A B C A' B' C' : ℝ → ℝ} (t₀ t₁ t₂ t₃ : ℝ)
    (hA : ∀ t, HasDerivAt A (A' t) t)
    (hB : ∀ t, HasDerivAt B (B' t) t)
    (hC : ∀ t, HasDerivAt C (C' t) t)
    (hA' : Continuous A') (hB' : Continuous B') (hC' : Continuous C') :
    normalizedDet4
        (A t₀) (B t₀) (C t₀)
        (A t₁) (B t₁) (C t₁)
        (A t₂) (B t₂) (C t₂)
        (A t₃) (B t₃) (C t₃) =
      ∫ s₀ in t₀..t₁, ∫ s₁ in t₁..t₂, ∫ s₂ in t₂..t₃,
        rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A' s₁) (B' s₁) (C' s₁)
          (A' s₂) (B' s₂) (C' s₂) := by
  rw [normalizedDet4_eq_rowDet3_forwardDiff]
  symm
  calc
    (∫ s₀ in t₀..t₁, ∫ s₁ in t₁..t₂, ∫ s₂ in t₂..t₃,
        rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A' s₁) (B' s₁) (C' s₁)
          (A' s₂) (B' s₂) (C' s₂)) =
      ∫ s₀ in t₀..t₁, ∫ s₁ in t₁..t₂,
        rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A' s₁) (B' s₁) (C' s₁)
          (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂) := by
        apply intervalIntegral.integral_congr
        intro s₀ _
        apply intervalIntegral.integral_congr
        intro s₁ _
        exact integral_rowDet3_third
          (A' s₀) (B' s₀) (C' s₀) (A' s₁) (B' s₁) (C' s₁)
          (fun t _ => hA t) (fun t _ => hB t) (fun t _ => hC t)
          hA' hB' hC'

/-- Strict positivity of the ordered triple integral from pointwise strict
positivity on the open box. All three interval-length hypotheses are used. -/
theorem tripleIntegral_rowDet3_pos
    {A B C A' B' C' : ℝ → ℝ} {t₀ t₁ t₂ t₃ : ℝ}
    (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃)
    (hA : ∀ t, HasDerivAt A (A' t) t)
    (hB : ∀ t, HasDerivAt B (B' t) t)
    (hC : ∀ t, HasDerivAt C (C' t) t)
    (hA' : Continuous A') (hB' : Continuous B') (hC' : Continuous C')
    (hpos : ∀ s₀ ∈ Ioo t₀ t₁, ∀ s₁ ∈ Ioo t₁ t₂,
      ∀ s₂ ∈ Ioo t₂ t₃,
        0 < rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A' s₁) (B' s₁) (C' s₁)
          (A' s₂) (B' s₂) (C' s₂)) :
    0 < ∫ s₀ in t₀..t₁, ∫ s₁ in t₁..t₂, ∫ s₂ in t₂..t₃,
      rowDet3
        (A' s₀) (B' s₀) (C' s₀)
        (A' s₁) (B' s₁) (C' s₁)
        (A' s₂) (B' s₂) (C' s₂) := by
  have hinner_eq (s₀ s₁ : ℝ) :
      (∫ s₂ in t₂..t₃,
        rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A' s₁) (B' s₁) (C' s₁)
          (A' s₂) (B' s₂) (C' s₂)) =
        rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A' s₁) (B' s₁) (C' s₁)
          (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂) :=
    integral_rowDet3_third
      (A' s₀) (B' s₀) (C' s₀) (A' s₁) (B' s₁) (C' s₁)
      (fun t _ => hA t) (fun t _ => hB t) (fun t _ => hC t)
      hA' hB' hC'
  have hinner_pos (s₀ : ℝ) (hs₀ : s₀ ∈ Ioo t₀ t₁)
      (s₁ : ℝ) (hs₁ : s₁ ∈ Ioo t₁ t₂) :
      0 < ∫ s₂ in t₂..t₃,
        rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A' s₁) (B' s₁) (C' s₁)
          (A' s₂) (B' s₂) (C' s₂) := by
    apply intervalIntegral_pos_of_pos_on
    · apply Continuous.intervalIntegrable
      fun_prop
    · intro s₂ hs₂
      exact hpos s₀ hs₀ s₁ hs₁ s₂ hs₂
    · exact ht₂₃
  have hmiddle_eq (s₀ : ℝ) :
      (∫ s₁ in t₁..t₂, ∫ s₂ in t₂..t₃,
        rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A' s₁) (B' s₁) (C' s₁)
          (A' s₂) (B' s₂) (C' s₂)) =
        rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A t₂-A t₁) (B t₂-B t₁) (C t₂-C t₁)
          (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂) := by
    calc
      (∫ s₁ in t₁..t₂, ∫ s₂ in t₂..t₃,
          rowDet3
            (A' s₀) (B' s₀) (C' s₀)
            (A' s₁) (B' s₁) (C' s₁)
            (A' s₂) (B' s₂) (C' s₂)) =
        ∫ s₁ in t₁..t₂,
          rowDet3
            (A' s₀) (B' s₀) (C' s₀)
            (A' s₁) (B' s₁) (C' s₁)
            (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂) := by
          apply intervalIntegral.integral_congr
          intro s₁ _
          exact hinner_eq s₀ s₁
      _ = rowDet3
            (A' s₀) (B' s₀) (C' s₀)
            (A t₂-A t₁) (B t₂-B t₁) (C t₂-C t₁)
            (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂) := by
          exact integral_rowDet3_second
            (A' s₀) (B' s₀) (C' s₀)
            (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂)
            (fun t _ => hA t) (fun t _ => hB t) (fun t _ => hC t)
            hA' hB' hC'
  apply intervalIntegral_pos_of_pos_on
  · have heq :
        (fun s₀ => ∫ s₁ in t₁..t₂, ∫ s₂ in t₂..t₃,
          rowDet3
            (A' s₀) (B' s₀) (C' s₀)
            (A' s₁) (B' s₁) (C' s₁)
            (A' s₂) (B' s₂) (C' s₂)) =
        (fun s₀ => rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A t₂-A t₁) (B t₂-B t₁) (C t₂-C t₁)
          (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂)) := by
      funext s₀
      exact hmiddle_eq s₀
    rw [heq]
    apply Continuous.intervalIntegrable
    fun_prop
  · intro s₀ hs₀
    apply intervalIntegral_pos_of_pos_on
    · have heq :
          (fun s₁ => ∫ s₂ in t₂..t₃,
            rowDet3
              (A' s₀) (B' s₀) (C' s₀)
              (A' s₁) (B' s₁) (C' s₁)
              (A' s₂) (B' s₂) (C' s₂)) =
          (fun s₁ => rowDet3
            (A' s₀) (B' s₀) (C' s₀)
            (A' s₁) (B' s₁) (C' s₁)
            (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂)) := by
        funext s₁
        exact hinner_eq s₀ s₁
      rw [heq]
      apply Continuous.intervalIntegrable
      fun_prop
    · intro s₁ hs₁
      exact hinner_pos s₀ hs₀ s₁ hs₁
    · exact ht₁₂
  · exact ht₀₁

/-- End-to-end first-stage strictness: a pointwise-positive derivative
determinant on the nondegenerate ordered box forces the original normalized
four-row determinant to be strictly positive. -/
theorem normalizedDet4_pos_of_derivativeDet_pos
    {A B C A' B' C' : ℝ → ℝ} {t₀ t₁ t₂ t₃ : ℝ}
    (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃)
    (hA : ∀ t, HasDerivAt A (A' t) t)
    (hB : ∀ t, HasDerivAt B (B' t) t)
    (hC : ∀ t, HasDerivAt C (C' t) t)
    (hA' : Continuous A') (hB' : Continuous B') (hC' : Continuous C')
    (hpos : ∀ s₀ ∈ Ioo t₀ t₁, ∀ s₁ ∈ Ioo t₁ t₂,
      ∀ s₂ ∈ Ioo t₂ t₃,
        0 < rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A' s₁) (B' s₁) (C' s₁)
          (A' s₂) (B' s₂) (C' s₂)) :
    0 < normalizedDet4
      (A t₀) (B t₀) (C t₀)
      (A t₁) (B t₁) (C t₁)
      (A t₂) (B t₂) (C t₂)
      (A t₃) (B t₃) (C t₃) := by
  rw [normalizedDet4_eq_tripleIntegral t₀ t₁ t₂ t₃ hA hB hC hA' hB' hC']
  exact tripleIntegral_rowDet3_pos ht₀₁ ht₁₂ ht₂₃ hA hB hC hA' hB' hC' hpos


/-- The explicit determinant of two row vectors. -/
def rowDet2 (a₀ b₀ a₁ b₁ : ℝ) : ℝ := a₀*b₁-b₀*a₁

theorem hasDerivAt_rowDet2_second
    {A B A' B' : ℝ → ℝ} {t : ℝ} (a₀ b₀ : ℝ)
    (hA : HasDerivAt A (A' t) t)
    (hB : HasDerivAt B (B' t) t) :
    HasDerivAt (fun s => rowDet2 a₀ b₀ (A s) (B s))
      (rowDet2 a₀ b₀ (A' t) (B' t)) t := by
  unfold rowDet2
  convert (hB.const_mul a₀).sub (hA.const_mul b₀) using 1 <;> ring

theorem hasDerivAt_rowDet2_first
    {A B A' B' : ℝ → ℝ} {t : ℝ} (a₁ b₁ : ℝ)
    (hA : HasDerivAt A (A' t) t)
    (hB : HasDerivAt B (B' t) t) :
    HasDerivAt (fun s => rowDet2 (A s) (B s) a₁ b₁)
      (rowDet2 (A' t) (B' t) a₁ b₁) t := by
  unfold rowDet2
  convert (hA.const_mul b₁).sub (hB.const_mul a₁) using 1 <;> ring

theorem integral_rowDet2_second
    {A B A' B' : ℝ → ℝ} {x y : ℝ} (a₀ b₀ : ℝ)
    (hA : ∀ t ∈ uIcc x y, HasDerivAt A (A' t) t)
    (hB : ∀ t ∈ uIcc x y, HasDerivAt B (B' t) t)
    (hA' : Continuous A') (hB' : Continuous B') :
    (∫ t in x..y, rowDet2 a₀ b₀ (A' t) (B' t)) =
      rowDet2 a₀ b₀ (A y-A x) (B y-B x) := by
  have hint : IntervalIntegrable
      (fun t => rowDet2 a₀ b₀ (A' t) (B' t)) volume x y := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_rowDet2_second a₀ b₀ (hA t ht) (hB t ht)) hint]
  unfold rowDet2
  ring

theorem integral_rowDet2_first
    {A B A' B' : ℝ → ℝ} {x y : ℝ} (a₁ b₁ : ℝ)
    (hA : ∀ t ∈ uIcc x y, HasDerivAt A (A' t) t)
    (hB : ∀ t ∈ uIcc x y, HasDerivAt B (B' t) t)
    (hA' : Continuous A') (hB' : Continuous B') :
    (∫ t in x..y, rowDet2 (A' t) (B' t) a₁ b₁) =
      rowDet2 (A y-A x) (B y-B x) a₁ b₁ := by
  have hint : IntervalIntegrable
      (fun t => rowDet2 (A' t) (B' t) a₁ b₁) volume x y := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_rowDet2_first a₁ b₁ (hA t ht) (hB t ht)) hint]
  unfold rowDet2
  ring

/-- The normalized three-row determinant. -/
noncomputable def normalizedDet3
    (a₀ b₀ a₁ b₁ a₂ b₂ : ℝ) : ℝ :=
  (!![1,a₀,b₀; 1,a₁,b₁; 1,a₂,b₂] :
    Matrix (Fin 3) (Fin 3) ℝ).det

theorem normalizedDet3_eq_rowDet2_forwardDiff
    (a₀ b₀ a₁ b₁ a₂ b₂ : ℝ) :
    normalizedDet3 a₀ b₀ a₁ b₁ a₂ b₂ =
      rowDet2 (a₁-a₀) (b₁-b₀) (a₂-a₁) (b₂-b₁) := by
  simp [normalizedDet3, rowDet2, Matrix.det_fin_three]
  ring

/-- Fixed order-three iterated quotient integral. -/
theorem normalizedDet3_eq_doubleIntegral
    {A B A' B' : ℝ → ℝ} (t₀ t₁ t₂ : ℝ)
    (hA : ∀ t, HasDerivAt A (A' t) t)
    (hB : ∀ t, HasDerivAt B (B' t) t)
    (hA' : Continuous A') (hB' : Continuous B') :
    normalizedDet3 (A t₀) (B t₀) (A t₁) (B t₁) (A t₂) (B t₂) =
      ∫ s₀ in t₀..t₁, ∫ s₁ in t₁..t₂,
        rowDet2 (A' s₀) (B' s₀) (A' s₁) (B' s₁) := by
  rw [normalizedDet3_eq_rowDet2_forwardDiff]
  symm
  calc
    (∫ s₀ in t₀..t₁, ∫ s₁ in t₁..t₂,
        rowDet2 (A' s₀) (B' s₀) (A' s₁) (B' s₁)) =
      ∫ s₀ in t₀..t₁,
        rowDet2 (A' s₀) (B' s₀) (A t₂-A t₁) (B t₂-B t₁) := by
      apply intervalIntegral.integral_congr
      intro s₀ _
      exact integral_rowDet2_second (A' s₀) (B' s₀)
        (fun t _ => hA t) (fun t _ => hB t) hA' hB'
    _ = rowDet2 (A t₁-A t₀) (B t₁-B t₀)
        (A t₂-A t₁) (B t₂-B t₁) := by
      exact integral_rowDet2_first
        (A t₂-A t₁) (B t₂-B t₁)
        (fun t _ => hA t) (fun t _ => hB t) hA' hB'

/-- Strict order-three lifting from a positive derivative determinant on the
nondegenerate adjacent rectangle. -/
theorem normalizedDet3_pos_of_derivativeDet_pos
    {A B A' B' : ℝ → ℝ} {t₀ t₁ t₂ : ℝ}
    (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂)
    (hA : ∀ t, HasDerivAt A (A' t) t)
    (hB : ∀ t, HasDerivAt B (B' t) t)
    (hA' : Continuous A') (hB' : Continuous B')
    (hpos : ∀ s₀ ∈ Ioo t₀ t₁, ∀ s₁ ∈ Ioo t₁ t₂,
      0 < rowDet2 (A' s₀) (B' s₀) (A' s₁) (B' s₁)) :
    0 < normalizedDet3 (A t₀) (B t₀) (A t₁) (B t₁) (A t₂) (B t₂) := by
  rw [normalizedDet3_eq_doubleIntegral t₀ t₁ t₂ hA hB hA' hB']
  apply intervalIntegral_pos_of_pos_on
  · have heq :
        (fun s₀ => ∫ s₁ in t₁..t₂,
          rowDet2 (A' s₀) (B' s₀) (A' s₁) (B' s₁)) =
        (fun s₀ => rowDet2 (A' s₀) (B' s₀)
          (A t₂-A t₁) (B t₂-B t₁)) := by
      funext s₀
      exact integral_rowDet2_second (A' s₀) (B' s₀)
        (fun t _ => hA t) (fun t _ => hB t) hA' hB'
    rw [heq]
    apply Continuous.intervalIntegrable
    fun_prop
  · intro s₀ hs₀
    apply intervalIntegral_pos_of_pos_on
    · apply Continuous.intervalIntegrable
      fun_prop
    · intro s₁ hs₁
      exact hpos s₀ hs₀ s₁ hs₁
    · exact ht₁₂
  · exact ht₀₁

/-- Exact factor extraction from a three-row derivative determinant. -/
theorem rowDet3_factored
    (r₀ r₁ r₂ a₀ b₀ a₁ b₁ a₂ b₂ : ℝ) :
    rowDet3
      r₀ (r₀*a₀) (r₀*b₀)
      r₁ (r₁*a₁) (r₁*b₁)
      r₂ (r₂*a₂) (r₂*b₂) =
      (r₀*r₁*r₂) * normalizedDet3 a₀ b₀ a₁ b₁ a₂ b₂ := by
  simp [rowDet3, normalizedDet3, Matrix.det_fin_three]
  ring

/-- Exact terminal quotient factorization. -/
theorem rowDet2_factored (r₀ r₁ q₀ q₁ : ℝ) :
    rowDet2 r₀ (r₀*q₀) r₁ (r₁*q₁) = (r₀*r₁)*(q₁-q₀) := by
  unfold rowDet2
  ring

theorem forwardDiff_pos_of_global_deriv_pos
    {q q' : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hq : ∀ t, HasDerivAt q (q' t) t)
    (hq' : Continuous q') (hqpos : ∀ t, 0 < q' t) :
    0 < q y-q x := by
  have hint : IntervalIntegrable q' volume x y := hq'.intervalIntegrable
  rw [← integral_eq_sub_of_hasDerivAt (fun t _ => hq t) hint]
  exact intervalIntegral_pos_of_pos_on hint (fun t _ => hqpos t) hxy

/-- Complete strict quotient-integral transfer through order four. The first
column derivative `A'`, the second-stage derivative `V'`, and the terminal
quotient derivative `q'` are assumed pointwise positive. Exact factor
identities connect `B',C',W'` to those quotient coordinates. Positivity of the
original determinant is a conclusion, never a hypothesis. -/
theorem normalizedDet4_pos_of_full_quotient_chain
    {A B C A' B' C' V W V' W' q q' : ℝ → ℝ}
    {t₀ t₁ t₂ t₃ : ℝ}
    (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃)
    (hA : ∀ t, HasDerivAt A (A' t) t)
    (hB : ∀ t, HasDerivAt B (B' t) t)
    (hC : ∀ t, HasDerivAt C (C' t) t)
    (hV : ∀ t, HasDerivAt V (V' t) t)
    (hW : ∀ t, HasDerivAt W (W' t) t)
    (hq : ∀ t, HasDerivAt q (q' t) t)
    (hA' : Continuous A') (hB' : Continuous B') (hC' : Continuous C')
    (hV' : Continuous V') (hW' : Continuous W') (hq' : Continuous q')
    (hBfactor : ∀ t, B' t = A' t * V t)
    (hCfactor : ∀ t, C' t = A' t * W t)
    (hWfactor : ∀ t, W' t = V' t * q t)
    (hApos : ∀ t, 0 < A' t)
    (hVpos : ∀ t, 0 < V' t)
    (hqpos : ∀ t, 0 < q' t) :
    0 < normalizedDet4
      (A t₀) (B t₀) (C t₀)
      (A t₁) (B t₁) (C t₁)
      (A t₂) (B t₂) (C t₂)
      (A t₃) (B t₃) (C t₃) := by
  apply normalizedDet4_pos_of_derivativeDet_pos
    ht₀₁ ht₁₂ ht₂₃ hA hB hC hA' hB' hC'
  intro s₀ hs₀ s₁ hs₁ s₂ hs₂
  have hs₀₁ : s₀ < s₁ := hs₀.2.trans hs₁.1
  have hs₁₂ : s₁ < s₂ := hs₁.2.trans hs₂.1
  have hminor3 :
      0 < normalizedDet3
        (V s₀) (W s₀) (V s₁) (W s₁) (V s₂) (W s₂) := by
    apply normalizedDet3_pos_of_derivativeDet_pos
      hs₀₁ hs₁₂ hV hW hV' hW'
    intro r₀ hr₀ r₁ hr₁
    have hr₀₁ : r₀ < r₁ := hr₀.2.trans hr₁.1
    rw [hWfactor r₀, hWfactor r₁, rowDet2_factored]
    have hqdiff : 0 < q r₁-q r₀ :=
      forwardDiff_pos_of_global_deriv_pos hr₀₁ hq hq' hqpos
    positivity
  rw [hBfactor s₀, hCfactor s₀,
    hBfactor s₁, hCfactor s₁,
    hBfactor s₂, hCfactor s₂,
    rowDet3_factored]
  positivity

/-- The original four-row determinant after writing each row as its positive
first entry times the three normalized quotients. -/
noncomputable def rawFactoredDet4
    (r₀ r₁ r₂ r₃ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ) : ℝ :=
  (!![r₀,r₀*a₀,r₀*b₀,r₀*c₀;
      r₁,r₁*a₁,r₁*b₁,r₁*c₁;
      r₂,r₂*a₂,r₂*b₂,r₂*c₂;
      r₃,r₃*a₃,r₃*b₃,r₃*c₃] : Matrix (Fin 4) (Fin 4) ℝ).det

theorem rawFactoredDet4_eq
    (r₀ r₁ r₂ r₃ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ) :
    rawFactoredDet4 r₀ r₁ r₂ r₃
      a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ =
      (r₀*r₁*r₂*r₃) *
        normalizedDet4 a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ := by
  unfold rawFactoredDet4 normalizedDet4
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Full fixed-order generic boundary: the original unnormalized order-four
minor is strictly positive from positive first-column values and the complete
continuous quotient chain. -/
theorem rawFactoredDet4_pos_of_full_quotient_chain
    {A B C A' B' C' V W V' W' q q' : ℝ → ℝ}
    {t₀ t₁ t₂ t₃ r₀ r₁ r₂ r₃ : ℝ}
    (ht₀₁ : t₀ < t₁) (ht₁₂ : t₁ < t₂) (ht₂₃ : t₂ < t₃)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hA : ∀ t, HasDerivAt A (A' t) t)
    (hB : ∀ t, HasDerivAt B (B' t) t)
    (hC : ∀ t, HasDerivAt C (C' t) t)
    (hV : ∀ t, HasDerivAt V (V' t) t)
    (hW : ∀ t, HasDerivAt W (W' t) t)
    (hq : ∀ t, HasDerivAt q (q' t) t)
    (hA' : Continuous A') (hB' : Continuous B') (hC' : Continuous C')
    (hV' : Continuous V') (hW' : Continuous W') (hq' : Continuous q')
    (hBfactor : ∀ t, B' t = A' t * V t)
    (hCfactor : ∀ t, C' t = A' t * W t)
    (hWfactor : ∀ t, W' t = V' t * q t)
    (hApos : ∀ t, 0 < A' t)
    (hVpos : ∀ t, 0 < V' t)
    (hqpos : ∀ t, 0 < q' t) :
    0 < rawFactoredDet4 r₀ r₁ r₂ r₃
      (A t₀) (B t₀) (C t₀)
      (A t₁) (B t₁) (C t₁)
      (A t₂) (B t₂) (C t₂)
      (A t₃) (B t₃) (C t₃) := by
  rw [rawFactoredDet4_eq]
  have hnormalized := normalizedDet4_pos_of_full_quotient_chain
    ht₀₁ ht₁₂ ht₂₃ hA hB hC hV hW hq hA' hB' hC' hV' hW' hq'
    hBfactor hCfactor hWfactor hApos hVpos hqpos
  positivity
    _ = ∫ s₀ in t₀..t₁,
        rowDet3
          (A' s₀) (B' s₀) (C' s₀)
          (A t₂-A t₁) (B t₂-B t₁) (C t₂-C t₁)
          (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂) := by
        apply intervalIntegral.integral_congr
        intro s₀ _
        exact integral_rowDet3_second
          (A' s₀) (B' s₀) (C' s₀)
          (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂)
          (fun t _ => hA t) (fun t _ => hB t) (fun t _ => hC t)
          hA' hB' hC'
    _ = rowDet3
          (A t₁-A t₀) (B t₁-B t₀) (C t₁-C t₀)
          (A t₂-A t₁) (B t₂-B t₁) (C t₂-C t₁)
          (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂) := by
        exact integral_rowDet3_first
          (A t₂-A t₁) (B t₂-B t₁) (C t₂-C t₁)
          (A t₃-A t₂) (B t₃-B t₂) (C t₃-C t₂)
          (fun t _ => hA t) (fun t _ => hB t) (fun t _ => hC t)
          hA' hB' hC'

end PF4.ContinuousQuotientBox
