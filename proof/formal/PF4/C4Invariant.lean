import PF4.Transport

set_option linter.style.header false

namespace PF4.C4Invariant

open Matrix
open Set
open PF4.Curvature PF4.Transport

/-- Central moments through order six, independently generated from the five
logarithmic cumulants needed by the order-four Hankel determinant. -/
def moment2 (c2 : ℝ) : ℝ := c2
def moment3 (c3 : ℝ) : ℝ := c3
def moment4 (c2 c4 : ℝ) : ℝ := c4 + 3 * c2 ^ 2
def moment5 (c2 c3 c5 : ℝ) : ℝ := c5 + 10 * c2 * c3
def moment6 (c2 c3 c4 c6 : ℝ) : ℝ :=
  c6 + 15 * c2 * c4 + 10 * c3 ^ 2 + 15 * c2 ^ 3

/-- The primary `4 × 4` central-moment Hankel matrix. -/
def centralMomentHankel (c2 c3 c4 c5 c6 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, moment2 c2, moment3 c3;
     0, moment2 c2, moment3 c3, moment4 c2 c4;
     moment2 c2, moment3 c3, moment4 c2 c4, moment5 c2 c3 c5;
     moment3 c3, moment4 c2 c4, moment5 c2 c3 c5,
       moment6 c2 c3 c4 c6]

/-- The independently defined confluent invariant. -/
noncomputable def determinantC4 (c2 c3 c4 c5 c6 : ℝ) : ℝ :=
  (centralMomentHankel c2 c3 c4 c5 c6).det

/-- The thirteen-term cumulant polynomial, introduced only as a comparison
object rather than as the definition of `C4`. -/
def cumulantC4Polynomial (c2 c3 c4 c5 c6 : ℝ) : ℝ :=
  12 * c2 ^ 6 + 24 * c2 ^ 4 * c4 - 24 * c2 ^ 3 * c3 ^ 2 +
  2 * c2 ^ 3 * c6 - 12 * c2 ^ 2 * c3 * c5 + 7 * c2 ^ 2 * c4 ^ 2 +
  12 * c2 * c3 ^ 2 * c4 + c2 * c4 * c6 - c2 * c5 ^ 2 -
  9 * c3 ^ 4 - c3 ^ 2 * c6 + 2 * c3 * c4 * c5 - c4 ^ 3

theorem determinantC4_eq_cumulantC4Polynomial
    (c2 c3 c4 c5 c6 : ℝ) :
    determinantC4 c2 c3 c4 c5 c6 =
      cumulantC4Polynomial c2 c3 c4 c5 c6 := by
  unfold determinantC4 centralMomentHankel moment2 moment3 moment4 moment5
    moment6 cumulantC4Polynomial
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Coordinate cumulants obtained by repeatedly applying `Q d/dy` to
`c₂ = -Q`. -/
def coordinateC2 (Q : ℝ) : ℝ := -Q
def coordinateC3 (Q Q1 : ℝ) : ℝ := -Q * Q1
def coordinateC4 (Q Q1 Q2 : ℝ) : ℝ := -Q * (Q1 ^ 2 + Q * Q2)
def coordinateC5 (Q Q1 Q2 Q3 : ℝ) : ℝ :=
  -Q * (Q1 ^ 3 + 4 * Q * Q1 * Q2 + Q ^ 2 * Q3)
def coordinateC6 (Q Q1 Q2 Q3 Q4 : ℝ) : ℝ :=
  -Q * (Q1 ^ 4 + 11 * Q * Q1 ^ 2 * Q2 + 4 * Q ^ 2 * Q2 ^ 2 +
    7 * Q ^ 2 * Q1 * Q3 + Q ^ 3 * Q4)

/-- The displayed coordinate cumulants really are obtained by repeatedly
applying the transport operator `Q d/dy`, starting from `c₂ = -Q`. -/
theorem coordinateCumulant_derivative_tower
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ} {y : ℝ}
    (hQ : HasDerivAt Q (Q1 y) y)
    (hQ1 : HasDerivAt Q1 (Q2 y) y)
    (hQ2 : HasDerivAt Q2 (Q3 y) y)
    (hQ3 : HasDerivAt Q3 (Q4 y) y) :
    HasDerivAt (fun x => coordinateC2 (Q x)) (-Q1 y) y ∧
    HasDerivAt (fun x => coordinateC3 (Q x) (Q1 x))
      (-(Q1 y ^ 2 + Q y * Q2 y)) y ∧
    HasDerivAt (fun x => coordinateC4 (Q x) (Q1 x) (Q2 x))
      (-(Q1 y ^ 3 + 4 * Q y * Q1 y * Q2 y + Q y ^ 2 * Q3 y)) y ∧
    HasDerivAt (fun x => coordinateC5 (Q x) (Q1 x) (Q2 x) (Q3 x))
      (-(Q1 y ^ 4 + 11 * Q y * Q1 y ^ 2 * Q2 y +
        4 * Q y ^ 2 * Q2 y ^ 2 + 7 * Q y ^ 2 * Q1 y * Q3 y +
        Q y ^ 3 * Q4 y)) y := by
  have hnegQ : HasDerivAt (fun x => -Q x) (-Q1 y) y :=
    hQ.neg.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  constructor
  · exact hnegQ.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp [coordinateC2])
  constructor
  · have hraw := hnegQ.mul hQ1
    apply hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp [coordinateC3]) |>.congr_deriv
    ring
  constructor
  · have hinner := (hQ1.pow 2).add (hQ.mul hQ2)
    have hraw := hnegQ.mul hinner
    apply hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp [coordinateC4]) |>.congr_deriv
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · have hinner := (hQ1.pow 3).add
      (((hQ.const_mul 4).mul hQ1).mul hQ2) |>.add ((hQ.pow 2).mul hQ3)
    have hraw := hnegQ.mul hinner
    apply hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp [coordinateC5]) |>.congr_deriv
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring

theorem coordinateCumulant_transport_recurrence
    (Q Q1 Q2 Q3 Q4 : ℝ) :
    Q * (-Q1) = coordinateC3 Q Q1 ∧
    Q * (-(Q1 ^ 2 + Q * Q2)) = coordinateC4 Q Q1 Q2 ∧
    Q * (-(Q1 ^ 3 + 4 * Q * Q1 * Q2 + Q ^ 2 * Q3)) =
      coordinateC5 Q Q1 Q2 Q3 ∧
    Q * (-(Q1 ^ 4 + 11 * Q * Q1 ^ 2 * Q2 + 4 * Q ^ 2 * Q2 ^ 2 +
      7 * Q ^ 2 * Q1 * Q3 + Q ^ 3 * Q4)) =
      coordinateC6 Q Q1 Q2 Q3 Q4 := by
  simp only [coordinateC3, coordinateC4, coordinateC5, coordinateC6]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The determinant-defined `C4` evaluated on the coordinate cumulants. -/
noncomputable def coordinateDeterminantC4
    (Q Q1 Q2 Q3 Q4 : ℝ) : ℝ :=
  determinantC4 (coordinateC2 Q) (coordinateC3 Q Q1)
    (coordinateC4 Q Q1 Q2) (coordinateC5 Q Q1 Q2 Q3)
    (coordinateC6 Q Q1 Q2 Q3 Q4)

/-- Exact determinant-to-curvature identity at one point. Strict curvature is
used only to justify the denominator in the independently derived rate. -/
theorem coordinateDeterminantC4_eq_derivedC4
    (Q Q1 Q2 Q3 Q4 : ℝ) (hκ : 2 - Q2 ≠ 0) :
    coordinateDeterminantC4 Q Q1 Q2 Q3 Q4 =
      Q ^ 6 * (2 - Q2) ^ 2 *
        (3 * (1 - Q2) - Q1 * ((-Q3) / (2 - Q2)) -
          Q * (((-Q4) * (2 - Q2) - (-Q3) ^ 2) / (2 - Q2) ^ 2)) := by
  rw [coordinateDeterminantC4, determinantC4_eq_cumulantC4Polynomial]
  unfold coordinateC2 coordinateC3 coordinateC4 coordinateC5 coordinateC6
    cumulantC4Polynomial
  field_simp [hκ]
  ring

/-- The determinant-defined invariant as a function of the coordinate jet. -/
noncomputable def determinantC4Function
    (Q Q1 Q2 Q3 Q4 : ℝ → ℝ) (y : ℝ) : ℝ :=
  coordinateDeterminantC4 (Q y) (Q1 y) (Q2 y) (Q3 y) (Q4 y)

/-- The exact primitive-derived numerator used by the transport boundary. -/
noncomputable def primitiveDerivedC4
    (Q Q1 Q2 Q3 Q4 : ℝ → ℝ) (y : ℝ) : ℝ :=
  Q y ^ 6 * (2 - Q2 y) ^ 2 *
    (3 * (1 - Q2 y) - Q1 y * ((-Q3 y) / (2 - Q2 y)) -
      Q y * (((-Q4 y) * (2 - Q2 y) - (-Q3 y) ^ 2) /
        (2 - Q2 y) ^ 2))

/-- Exact pointwise identification in precisely the shape required by the
P000101 independent-`C4` adapter. -/
theorem determinantC4Function_eq_primitiveDerivedC4
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ}
    (hκ : ∀ y, 0 < 2 - Q2 y) :
    determinantC4Function Q Q1 Q2 Q3 Q4 =
      primitiveDerivedC4 Q Q1 Q2 Q3 Q4 := by
  funext y
  exact coordinateDeterminantC4_eq_derivedC4
    (Q y) (Q1 y) (Q2 y) (Q3 y) (Q4 y) (hκ y).ne'

theorem determinantC4_exact_adapter
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ} {p w : ℝ}
    (hκ : ∀ y, 0 < 2 - Q2 y) :
    ∀ y ∈ Icc p w,
      determinantC4Function Q Q1 Q2 Q3 Q4 y =
        primitiveDerivedC4 Q Q1 Q2 Q3 Q4 y := by
  intro y _
  exact congrFun (determinantC4Function_eq_primitiveDerivedC4 hκ) y

/-- The determinant-defined and primitive-derived weights give literally the
same transport integral. This is the exact join to the P000101 theorem. -/
theorem transportIntegral_determinantC4_eq_primitiveDerivedC4
    {Q Q1 Q2 Q3 Q4 gap : ℝ → ℝ} {p w : ℝ}
    (hκ : ∀ y, 0 < 2 - Q2 y) :
    transportIntegral gap Q (curvature Q2)
        (determinantC4Function Q Q1 Q2 Q3 Q4) p w =
      transportIntegral gap Q (curvature Q2)
        (primitiveDerivedC4 Q Q1 Q2 Q3 Q4) p w := by
  rw [determinantC4Function_eq_primitiveDerivedC4 hκ]


end PF4.C4Invariant

