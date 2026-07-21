import PF4.CERT12Bernstein
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-! Independently checked q continuum margins from the CERT12 tables. -/

namespace PF4.CERT12Inequalities.Generated

noncomputable def qCorePolynomial (x y : ℝ) : ℝ :=
  (((-48 : ℝ) * (x ^ 2)) + ((16 : ℝ) * (x ^ 3)) + ((60 : ℝ) * x) + ((-12288 : ℝ) * (x ^ 2) * (y ^ 2)) + ((-5424 : ℝ) * y * (x ^ 2)) + ((-2304 : ℝ) * y * (x ^ 4)) + ((1200 : ℝ) * x * y) + ((3840 : ℝ) * x * (y ^ 2)) + ((5600 : ℝ) * y * (x ^ 3)) + ((16384 : ℝ) * (x ^ 3) * (y ^ 2)))

def qCoreCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (3288836 / 15625 : ℚ)
  | 0, 1 => (241764504257 / 1171875000 : ℚ)
  | 0, 2 => (3553043228473 / 17578125000 : ℚ)
  | 1, 0 => (3463909 / 15625 : ℚ)
  | 1, 1 => (16290238639 / 75000000 : ℚ)
  | 1, 2 => (7478405528869 / 35156250000 : ℚ)
  | 2, 0 => (1313633 / 5625 : ℚ)
  | 2, 1 => (15438429017 / 67500000 : ℚ)
  | 2, 2 => (1416887598031 / 6328125000 : ℚ)
  | 3, 0 => (66433 / 270 : ℚ)
  | 3, 1 => (390218657 / 1620000 : ℚ)
  | 3, 2 => (143191685311 / 607500000 : ℚ)
  | 4, 0 => (7000 / 27 : ℚ)
  | 4, 1 => (205501 / 810 : ℚ)
  | 4, 2 => (75376769 / 303750 : ℚ)
  | _, _ => 0

theorem qCoreCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (2 + 1), (3553043228473 / 17578125000 : ℚ) ≤ qCoreCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [qCoreCoeff]

theorem qCore_representation (u v : ℝ) :
    qCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 4 2 qCoreCoeff u v := by
  norm_num [qCorePolynomial, bernsteinBoxEval, qCoreCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem qCore_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < qCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [qCore_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (3553043228473 / 17578125000 : ℚ)) hu0 hu1 hv0 hv1 qCoreCoeff_floor

theorem qCore_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ ((10 : ℝ) / 3))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < qCorePolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((29 : ℝ) / 150)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((29 : ℝ) / 150))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := qCore_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def qMidPolynomial (x y : ℝ) : ℝ :=
  (((-48 : ℝ) * (x ^ 2)) + ((16 : ℝ) * (x ^ 3)) + ((60 : ℝ) * x) + ((-12288 : ℝ) * (x ^ 2) * (y ^ 2)) + ((-5424 : ℝ) * y * (x ^ 2)) + ((-2304 : ℝ) * y * (x ^ 4)) + ((1200 : ℝ) * x * y) + ((3840 : ℝ) * x * (y ^ 2)) + ((5600 : ℝ) * y * (x ^ 3)) + ((16384 : ℝ) * (x ^ 3) * (y ^ 2)))

def qMidCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (7000 / 27 : ℚ)
  | 0, 1 => (34591 / 135 : ℚ)
  | 0, 2 => (517004788 / 2041875 : ℚ)
  | 1, 0 => (10075 / 27 : ℚ)
  | 1, 1 => (875135 / 2376 : ℚ)
  | 1, 2 => (742219267 / 2041875 : ℚ)
  | 2, 0 => (4850 / 9 : ℚ)
  | 2, 1 => (262936 / 495 : ℚ)
  | 2, 2 => (712588153 / 1361250 : ℚ)
  | 3, 0 => 775
  | 3, 1 => (67115 / 88 : ℚ)
  | 3, 2 => (56744734 / 75625 : ℚ)
  | 4, 0 => 1100
  | 4, 1 => (59413 / 55 : ℚ)
  | 4, 2 => (291631 / 275 : ℚ)
  | _, _ => 0

theorem qMidCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (2 + 1), (517004788 / 2041875 : ℚ) ≤ qMidCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [qMidCoeff]

theorem qMid_representation (u v : ℝ) :
    qMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) =
      bernsteinBoxEval 4 2 qMidCoeff u v := by
  norm_num [qMidPolynomial, bernsteinBoxEval, qMidCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem qMid_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < qMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) := by
  rw [qMid_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (517004788 / 2041875 : ℚ)) hu0 hu1 hv0 hv1 qMidCoeff_floor

theorem qMid_box_pos {x y : ℝ}
    (hx0 : ((10 : ℝ) / 3) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 22000)) :
    0 < qMidPolynomial x y := by
  let u := (x - ((10 : ℝ) / 3)) / ((5 : ℝ) / 3)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 22000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((5 : ℝ) / 3))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 22000))]
    linarith
  have h := qMid_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def qMarginCorePolynomial (x y : ℝ) : ℝ :=
  ((-90 : ℝ) + ((-88 : ℝ) * (x ^ 2)) + ((16 : ℝ) * (x ^ 3)) + ((180 : ℝ) * x) + ((-12288 : ℝ) * (x ^ 2) * (y ^ 2)) + ((-5424 : ℝ) * y * (x ^ 2)) + ((-2304 : ℝ) * y * (x ^ 4)) + ((1200 : ℝ) * x * y) + ((3840 : ℝ) * x * (y ^ 2)) + ((5600 : ℝ) * y * (x ^ 3)) + ((16384 : ℝ) * (x ^ 3) * (y ^ 2)))

def qMarginCoreCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (1607836 / 15625 : ℚ)
  | 0, 1 => (115689504257 / 1171875000 : ℚ)
  | 0, 2 => (1661918228473 / 17578125000 : ℚ)
  | 1, 0 => (5051477 / 46875 : ℚ)
  | 1, 1 => (2581946213 / 25000000 : ℚ)
  | 1, 2 => (3473218028869 / 35156250000 : ℚ)
  | 2, 0 => (1907194 / 16875 : ℚ)
  | 2, 1 => (811512113 / 7500000 : ℚ)
  | 2, 2 => (654248223031 / 6328125000 : ℚ)
  | 3, 0 => (32047 / 270 : ℚ)
  | 3, 1 => (183902657 / 1620000 : ℚ)
  | 3, 2 => (65823185311 / 607500000 : ℚ)
  | 4, 0 => (3370 / 27 : ℚ)
  | 4, 1 => (96601 / 810 : ℚ)
  | 4, 2 => (34539269 / 303750 : ℚ)
  | _, _ => 0

theorem qMarginCoreCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (2 + 1), (1661918228473 / 17578125000 : ℚ) ≤ qMarginCoreCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [qMarginCoreCoeff]

theorem qMarginCore_representation (u v : ℝ) :
    qMarginCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 4 2 qMarginCoreCoeff u v := by
  norm_num [qMarginCorePolynomial, bernsteinBoxEval, qMarginCoreCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem qMarginCore_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < qMarginCorePolynomial (((157 : ℝ) / 50) + (((29 : ℝ) / 150)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [qMarginCore_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (1661918228473 / 17578125000 : ℚ)) hu0 hu1 hv0 hv1 qMarginCoreCoeff_floor

theorem qMarginCore_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ ((10 : ℝ) / 3))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < qMarginCorePolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((29 : ℝ) / 150)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((29 : ℝ) / 150))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := qMarginCore_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def qMarginMidPolynomial (x y : ℝ) : ℝ :=
  ((-90 : ℝ) + ((-88 : ℝ) * (x ^ 2)) + ((16 : ℝ) * (x ^ 3)) + ((180 : ℝ) * x) + ((-12288 : ℝ) * (x ^ 2) * (y ^ 2)) + ((-5424 : ℝ) * y * (x ^ 2)) + ((-2304 : ℝ) * y * (x ^ 4)) + ((1200 : ℝ) * x * y) + ((3840 : ℝ) * x * (y ^ 2)) + ((5600 : ℝ) * y * (x ^ 3)) + ((16384 : ℝ) * (x ^ 3) * (y ^ 2)))

def qMarginMidCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (3370 / 27 : ℚ)
  | 0, 1 => (16441 / 135 : ℚ)
  | 0, 2 => (242486038 / 2041875 : ℚ)
  | 1, 0 => (4795 / 27 : ℚ)
  | 1, 1 => (410495 / 2376 : ℚ)
  | 1, 2 => (342919267 / 2041875 : ℚ)
  | 2, 0 => (7120 / 27 : ℚ)
  | 2, 1 => (380158 / 1485 : ℚ)
  | 2, 2 => (1013976959 / 4083750 : ℚ)
  | 3, 0 => (1205 / 3 : ℚ)
  | 3, 1 => (102785 / 264 : ℚ)
  | 3, 2 => (85534202 / 226875 : ℚ)
  | 4, 0 => 610
  | 4, 1 => (32463 / 55 : ℚ)
  | 4, 2 => (156881 / 275 : ℚ)
  | _, _ => 0

theorem qMarginMidCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (2 + 1), (242486038 / 2041875 : ℚ) ≤ qMarginMidCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [qMarginMidCoeff]

theorem qMarginMid_representation (u v : ℝ) :
    qMarginMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) =
      bernsteinBoxEval 4 2 qMarginMidCoeff u v := by
  norm_num [qMarginMidPolynomial, bernsteinBoxEval, qMarginMidCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem qMarginMid_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < qMarginMidPolynomial (((10 : ℝ) / 3) + (((5 : ℝ) / 3)) * u) ((0 : ℝ) + (((1 : ℝ) / 22000)) * v) := by
  rw [qMarginMid_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (242486038 / 2041875 : ℚ)) hu0 hu1 hv0 hv1 qMarginMidCoeff_floor

theorem qMarginMid_box_pos {x y : ℝ}
    (hx0 : ((10 : ℝ) / 3) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 22000)) :
    0 < qMarginMidPolynomial x y := by
  let u := (x - ((10 : ℝ) / 3)) / ((5 : ℝ) / 3)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 22000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((5 : ℝ) / 3))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 22000))]
    linarith
  have h := qMarginMid_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

end PF4.CERT12Inequalities.Generated
