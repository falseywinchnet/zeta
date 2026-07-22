import PF4.Definitions
import Mathlib.Tactic

namespace PF4.PF5Scratch

noncomputable def toeplitz5 (a0 a1 a2 a3 a4 : ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  !![a0, a1, a2, a3, a4;
     a1, a0, a1, a2, a3;
     a2, a1, a0, a1, a2;
     a3, a2, a1, a0, a1;
     a4, a3, a2, a1, a0]

noncomputable def oddFactor (a0 a1 a2 a3 a4 : ℝ) : ℝ :=
  a0^2 - a0*a2 - a0*a4 - a1^2 + 2*a1*a3 + a2*a4 - a3^2

noncomputable def evenFactor (a0 a1 a2 a3 a4 : ℝ) : ℝ :=
  a0^3 + a0^2*a2 + a0^2*a4 - 3*a0*a1^2 - 2*a0*a1*a3 -
  2*a0*a2^2 + a0*a2*a4 - a0*a3^2 + 4*a1^2*a2 -
  2*a1^2*a4 + 4*a1*a2*a3 - 2*a2^3

theorem toeplitz5_det_eq_factors (a0 a1 a2 a3 a4 : ℝ) :
    (toeplitz5 a0 a1 a2 a3 a4).det =
      oddFactor a0 a1 a2 a3 a4 * evenFactor a0 a1 a2 a3 a4 := by
  unfold toeplitz5 oddFactor evenFactor
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove]
  ring

structure NonnegBound (x lower upper : ℝ) : Prop where
  lower_nonneg : 0 ≤ lower
  lower_le : lower ≤ x
  le_upper : x ≤ upper

namespace NonnegBound

theorem mul {x l u y m v : ℝ} (hx : NonnegBound x l u)
    (hy : NonnegBound y m v) : NonnegBound (x*y) (l*m) (u*v) := by
  have hx0 := hx.lower_nonneg.trans hx.lower_le
  have hy0 := hy.lower_nonneg.trans hy.lower_le
  have hu0 := hx0.trans hx.le_upper
  constructor
  · exact mul_nonneg hx.lower_nonneg hy.lower_nonneg
  · exact mul_le_mul hx.lower_le hy.lower_le hy.lower_nonneg hx0
  · exact mul_le_mul hx.le_upper hy.le_upper hy0 hu0

end NonnegBound

theorem nonnegBound_of_interval {x l u : ℝ} (hl0 : 0 ≤ l)
    (hl : l ≤ x) (hu : x ≤ u) : NonnegBound x l u := ⟨hl0, hl, hu⟩

theorem toeplitz5_neg_of_bounds
    {a0 a1 a2 a3 a4 : ℝ}
    (h0l : (893393799 / 1000000000 : ℝ) ≤ a0)
    (h0u : a0 ≤ (893393802 / 1000000000 : ℝ))
    (h1l : (804382231 / 1000000000 : ℝ) ≤ a1)
    (h1u : a1 ≤ (804382232 / 1000000000 : ℝ))
    (h2l : (582025473 / 1000000000 : ℝ) ≤ a2)
    (h2u : a2 ≤ (582025474 / 1000000000 : ℝ))
    (h3l : (329951899 / 1000000000 : ℝ) ≤ a3)
    (h3u : a3 ≤ (329951900 / 1000000000 : ℝ))
    (h4l : (140676936 / 1000000000 : ℝ) ≤ a4)
    (h4u : a4 ≤ (140676937 / 1000000000 : ℝ)) :
    (toeplitz5 a0 a1 a2 a3 a4).det < 0 := by
  let h0 := nonnegBound_of_interval (by norm_num) h0l h0u
  let h1 := nonnegBound_of_interval (by norm_num) h1l h1u
  let h2 := nonnegBound_of_interval (by norm_num) h2l h2u
  let h3 := nonnegBound_of_interval (by norm_num) h3l h3u
  let h4 := nonnegBound_of_interval (by norm_num) h4l h4u
  have h00 := h0.mul h0
  have h000 := h00.mul h0
  have h02 := h0.mul h2
  have h04 := h0.mul h4
  have h11 := h1.mul h1
  have h13 := h1.mul h3
  have h24 := h2.mul h4
  have h33 := h3.mul h3
  have h002 := h00.mul h2
  have h004 := h00.mul h4
  have h011 := h0.mul h11
  have h013 := h02.mul h3
  have h022 := h02.mul h2
  have h024 := h02.mul h4
  have h033 := h0.mul h33
  have h112 := h11.mul h2
  have h114 := h11.mul h4
  have h123 := h13.mul h2
  have h222 := (h2.mul h2).mul h2
  have hodd : 0 < oddFactor a0 a1 a2 a3 a4 := by
    unfold oddFactor
    have hmargin : (0 : ℝ) <
        (893393799/1000000000)^2 -
        (893393802/1000000000)*(582025474/1000000000) -
        (893393802/1000000000)*(140676937/1000000000) -
        (804382232/1000000000)^2 +
        2*(804382231/1000000000)*(329951899/1000000000) +
        (582025473/1000000000)*(140676936/1000000000) -
        (329951900/1000000000)^2 := by norm_num
    nlinarith [h00.lower_le, h02.le_upper, h04.le_upper, h11.le_upper,
      h13.lower_le, h24.lower_le, h33.le_upper]
  have heven : evenFactor a0 a1 a2 a3 a4 < 0 := by
    unfold evenFactor
    have hmargin :
        (893393802/1000000000)^3 +
        (893393802/1000000000)^2*(582025474/1000000000) +
        (893393802/1000000000)^2*(140676937/1000000000) -
        3*(893393799/1000000000)*(804382231/1000000000)^2 -
        2*(893393799/1000000000)*(804382231/1000000000)*(329951899/1000000000) -
        2*(893393799/1000000000)*(582025473/1000000000)^2 +
        (893393802/1000000000)*(582025474/1000000000)*(140676937/1000000000) -
        (893393799/1000000000)*(329951899/1000000000)^2 +
        4*(804382232/1000000000)^2*(582025474/1000000000) -
        2*(804382231/1000000000)^2*(140676936/1000000000) +
        4*(804382232/1000000000)*(582025474/1000000000)*(329951900/1000000000) -
        2*(582025473/1000000000)^3 < (0 : ℝ) := by norm_num
    nlinarith [h000.le_upper, h002.le_upper, h004.le_upper,
      h011.lower_le, h013.lower_le, h022.lower_le, h024.le_upper,
      h033.lower_le, h112.le_upper, h114.lower_le, h123.le_upper,
      h222.lower_le]
  rw [toeplitz5_det_eq_factors]
  exact mul_neg_of_pos_of_neg hodd heven

end PF4.PF5Scratch
