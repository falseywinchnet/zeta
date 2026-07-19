import Mathlib

set_option linter.style.header false

namespace PF4.GenericQuotientIntegral

open Matrix Set intervalIntegral

/-- A normalized order-four collocation determinant. -/
noncomputable def normalizedDet4
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ) : ℝ :=
  (!![1, a₀, b₀, c₀;
      1, a₁, b₁, c₁;
      1, a₂, b₂, c₂;
      1, a₃, b₃, c₃] : Matrix (Fin 4) (Fin 4) ℝ).det

/-- The three-by-three determinant of consecutive forward differences. -/
noncomputable def forwardDiffDet3
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ) : ℝ :=
  (!![a₁ - a₀, b₁ - b₀, c₁ - c₀;
      a₂ - a₁, b₂ - b₁, c₂ - c₁;
      a₃ - a₂, b₃ - b₂, c₃ - c₂] : Matrix (Fin 3) (Fin 3) ℝ).det

/-- Exact orientation of the first quotient reduction: increasing rows produce
consecutive forward differences and no hidden minus sign. -/
theorem normalizedDet4_eq_forwardDiffDet3
    (a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ) :
    normalizedDet4 a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ =
      forwardDiffDet3 a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ := by
  unfold normalizedDet4 forwardDiffDet3
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- A raw collocation determinant whose rows have been factored into a
nonzero leading value and three ratios. -/
noncomputable def factoredDet4
    (r₀ r₁ r₂ r₃ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ) : ℝ :=
  (!![r₀, r₀*a₀, r₀*b₀, r₀*c₀;
      r₁, r₁*a₁, r₁*b₁, r₁*c₁;
      r₂, r₂*a₂, r₂*b₂, r₂*c₂;
      r₃, r₃*a₃, r₃*b₃, r₃*c₃] : Matrix (Fin 4) (Fin 4) ℝ).det

/-- Row normalization extracts exactly the product of leading values. -/
theorem factoredDet4_eq
    (r₀ r₁ r₂ r₃ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ) :
    factoredDet4 r₀ r₁ r₂ r₃ a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ =
      (r₀*r₁*r₂*r₃) *
        normalizedDet4 a₀ b₀ c₀ a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ := by
  unfold factoredDet4 normalizedDet4
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- The normalized size-three quotient determinant. -/
noncomputable def normalizedDet3
    (a₀ b₀ a₁ b₁ a₂ b₂ : ℝ) : ℝ :=
  (!![1, a₀, b₀; 1, a₁, b₁; 1, a₂, b₂] :
    Matrix (Fin 3) (Fin 3) ℝ).det

/-- Size-three forward-difference reduction, again with forward orientation. -/
theorem normalizedDet3_eq_forwardDiffDet2
    (a₀ b₀ a₁ b₁ a₂ b₂ : ℝ) :
    normalizedDet3 a₀ b₀ a₁ b₁ a₂ b₂ =
      (a₁-a₀)*(b₂-b₁) - (b₁-b₀)*(a₂-a₁) := by
  unfold normalizedDet3
  simp [Matrix.det_fin_three]
  ring

/-- Row normalization at size three. -/
noncomputable def factoredDet3
    (r₀ r₁ r₂ a₀ b₀ a₁ b₁ a₂ b₂ : ℝ) : ℝ :=
  (!![r₀, r₀*a₀, r₀*b₀;
      r₁, r₁*a₁, r₁*b₁;
      r₂, r₂*a₂, r₂*b₂] : Matrix (Fin 3) (Fin 3) ℝ).det

theorem factoredDet3_eq
    (r₀ r₁ r₂ a₀ b₀ a₁ b₁ a₂ b₂ : ℝ) :
    factoredDet3 r₀ r₁ r₂ a₀ b₀ a₁ b₁ a₂ b₂ =
      (r₀*r₁*r₂) * normalizedDet3 a₀ b₀ a₁ b₁ a₂ b₂ := by
  unfold factoredDet3 normalizedDet3
  simp [Matrix.det_fin_three]
  ring

/-- The terminal size-two quotient identity. -/
theorem factoredDet2_eq
    (r₀ r₁ a₀ a₁ : ℝ) :
    (!![r₀, r₀*a₀; r₁, r₁*a₁] : Matrix (Fin 2) (Fin 2) ℝ).det =
      (r₀*r₁) * (a₁-a₀) := by
  simp [Matrix.det_fin_two]
  ring

/-- A four-row collocation determinant written in cumulative quotient
coordinates. Each consecutive first quotient difference is `vᵢ`; each
consecutive second quotient difference is `wᵢ`; and `q₁-q₀` is the terminal
third quotient difference. -/
noncomputable def quotientChainDet4
    (r₀ r₁ r₂ r₃ v₀ v₁ v₂ w₀ w₁ q₀ q₁ A B C a b : ℝ) : ℝ :=
  factoredDet4 r₀ r₁ r₂ r₃
    A B C
    (A + v₀)
      (B + v₀*a)
      (C + v₀*b)
    (A + v₀ + v₁)
      (B + v₀*a + v₁*(a+w₀))
      (C + v₀*b + v₁*(b+w₀*q₀))
    (A + v₀ + v₁ + v₂)
      (B + v₀*a + v₁*(a+w₀) + v₂*(a+w₀+w₁))
      (C + v₀*b + v₁*(b+w₀*q₀) + v₂*(b+w₀*q₀+w₁*q₁))

/-- Complete fixed-order quotient cascade. This is the exact discrete algebra
under the iterated-integral proof: no determinant sign occurs among the
hypotheses. -/
theorem quotientChainDet4_eq_terminalProduct
    (r₀ r₁ r₂ r₃ v₀ v₁ v₂ w₀ w₁ q₀ q₁ A B C a b : ℝ) :
    quotientChainDet4 r₀ r₁ r₂ r₃ v₀ v₁ v₂ w₀ w₁ q₀ q₁ A B C a b =
      (r₀*r₁*r₂*r₃) * (v₀*v₁*v₂) * (w₀*w₁) * (q₁-q₀) := by
  unfold quotientChainDet4
  rw [factoredDet4_eq, normalizedDet4_eq_forwardDiffDet3]
  unfold forwardDiffDet3
  simp [Matrix.det_fin_three]
  ring

/-- Every forward difference used by the quotient reduction is an exact
oriented integral, under explicit derivative and integrability hypotheses. -/
theorem forwardDiff_eq_integral
    {f f' : ℝ → ℝ} {x y : ℝ}
    (hderiv : ∀ t ∈ uIcc x y, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume x y) :
    f y - f x = ∫ t in x..y, f' t := by
  exact (integral_eq_sub_of_hasDerivAt hderiv hint).symm

/-- Non-vacuous strictness bridge: positivity of the derivative on the open,
nondegenerate interval forces a strictly positive forward difference. -/
theorem forwardDiff_pos_of_deriv_pos
    {f f' : ℝ → ℝ} {x y : ℝ} (hxy : x < y)
    (hderiv : ∀ t ∈ uIcc x y, HasDerivAt f (f' t) t)
    (hint : IntervalIntegrable f' volume x y)
    (hpos : ∀ t ∈ Ioo x y, 0 < f' t) :
    0 < f y - f x := by
  rw [forwardDiff_eq_integral hderiv hint]
  exact intervalIntegral_pos_of_pos_on hint hpos hxy

/-- The algebraic strictness endpoint: once all extracted factors and the
terminal quotient difference are proved positive, their exact product is
positive. This lemma does not assume positivity of the original determinant. -/
theorem quotientProduct_pos
    {r₀ r₁ r₂ r₃ v₀ v₁ v₂ w₀ w₁ d : ℝ}
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hv₀ : 0 < v₀) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) (hd : 0 < d) :
    0 < (r₀*r₁*r₂*r₃) * (v₀*v₁*v₂) * (w₀*w₁) * d := by
  positivity

/-- End-to-end non-vacuous strictness theorem for the discrete quotient chain.
The terminal factor is not assumed positive: it is proved positive from a
derivative theorem on a nondegenerate interval and the fundamental theorem of
calculus. -/
theorem quotientChainDet4_pos_of_terminal_deriv
    {q q' : ℝ → ℝ} {x y : ℝ}
    {r₀ r₁ r₂ r₃ v₀ v₁ v₂ w₀ w₁ A B C a b : ℝ}
    (hxy : x < y)
    (hderiv : ∀ t ∈ uIcc x y, HasDerivAt q (q' t) t)
    (hint : IntervalIntegrable q' volume x y)
    (hqpos : ∀ t ∈ Ioo x y, 0 < q' t)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃)
    (hv₀ : 0 < v₀) (hv₁ : 0 < v₁) (hv₂ : 0 < v₂)
    (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) :
    0 < quotientChainDet4 r₀ r₁ r₂ r₃ v₀ v₁ v₂ w₀ w₁
      (q x) (q y) A B C a b := by
  rw [quotientChainDet4_eq_terminalProduct]
  exact quotientProduct_pos hr₀ hr₁ hr₂ hr₃ hv₀ hv₁ hv₂ hw₀ hw₁
    (forwardDiff_pos_of_deriv_pos hxy hderiv hint hqpos)

#print axioms normalizedDet4_eq_forwardDiffDet3
#print axioms factoredDet4_eq
#print axioms normalizedDet3_eq_forwardDiffDet2
#print axioms factoredDet3_eq
#print axioms factoredDet2_eq
#print axioms quotientChainDet4_eq_terminalProduct
#print axioms forwardDiff_eq_integral
#print axioms forwardDiff_pos_of_deriv_pos
#print axioms quotientProduct_pos
#print axioms quotientChainDet4_pos_of_terminal_deriv

end PF4.GenericQuotientIntegral
