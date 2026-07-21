import PF4.CERT12Bernstein
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-! Seven independently checked compact three-mode jet coordinate bounds. -/

namespace PF4.CERT12Inequalities.Generated

noncomputable def base0UpperPolynomial (x y : ℝ) : ℝ :=
  ((-3 : ℝ) + ((2 : ℝ) * x) + ((12 : ℝ) * y) + ((-32 : ℝ) * x * y))

def base0UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (82 / 25 : ℚ)
  | 0, 1 => (245447 / 75000 : ℚ)
  | 1, 0 => 7
  | 1, 1 => (20963 / 3000 : ℚ)
  | _, _ => 0

theorem base0UpperCoeff_floor : ∀ i ∈ Finset.range (1 + 1), ∀ j ∈ Finset.range (1 + 1), (245447 / 75000 : ℚ) ≤ base0UpperCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base0UpperCoeff]

theorem base0Upper_representation (u v : ℝ) :
    base0UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 1 1 base0UpperCoeff u v := by
  norm_num [base0UpperPolynomial, bernsteinBoxEval, base0UpperCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base0Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base0UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base0Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (245447 / 75000 : ℚ)) hu0 hu1 hv0 hv1 base0UpperCoeff_floor

theorem base0Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base0UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base0Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base0LowerPolynomial (x y : ℝ) : ℝ :=
  ((-9 : ℝ) + ((-12 : ℝ) * y) + ((6 : ℝ) * x) + ((32 : ℝ) * x * y))

def base0LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (246 / 25 : ℚ)
  | 0, 1 => (738553 / 75000 : ℚ)
  | 1, 0 => 21
  | 1, 1 => (63037 / 3000 : ℚ)
  | _, _ => 0

theorem base0LowerCoeff_floor : ∀ i ∈ Finset.range (1 + 1), ∀ j ∈ Finset.range (1 + 1), (246 / 25 : ℚ) ≤ base0LowerCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base0LowerCoeff]

theorem base0Lower_representation (u v : ℝ) :
    base0LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 1 1 base0LowerCoeff u v := by
  norm_num [base0LowerPolynomial, bernsteinBoxEval, base0LowerCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base0Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base0LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base0Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (246 / 25 : ℚ)) hu0 hu1 hv0 hv1 base0LowerCoeff_floor

theorem base0Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base0LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base0Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base1UpperPolynomial (x y : ℝ) : ℝ :=
  (((-15 : ℝ) / 2) + ((-5 : ℝ) * x) + ((4 : ℝ) * (x ^ 2)) + ((30 : ℝ) * y) + ((-240 : ℝ) * x * y) + ((256 : ℝ) * y * (x ^ 2)))

def base1UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (10149 / 625 : ℚ)
  | 0, 1 => (61456643 / 3750000 : ℚ)
  | 1, 0 => (699 / 20 : ℚ)
  | 1, 1 => (1056181 / 30000 : ℚ)
  | 2, 0 => (135 / 2 : ℚ)
  | 2, 1 => (81523 / 1200 : ℚ)
  | _, _ => 0

theorem base1UpperCoeff_floor : ∀ i ∈ Finset.range (2 + 1), ∀ j ∈ Finset.range (1 + 1), (10149 / 625 : ℚ) ≤ base1UpperCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base1UpperCoeff]

theorem base1Upper_representation (u v : ℝ) :
    base1UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 2 1 base1UpperCoeff u v := by
  norm_num [base1UpperPolynomial, bernsteinBoxEval, base1UpperCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base1Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base1UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base1Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (10149 / 625 : ℚ)) hu0 hu1 hv0 hv1 base1UpperCoeff_floor

theorem base1Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base1UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base1Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base1LowerPolynomial (x y : ℝ) : ℝ :=
  (((-45 : ℝ) / 2) + ((-30 : ℝ) * y) + ((-4 : ℝ) * (x ^ 2)) + ((25 : ℝ) * x) + ((-256 : ℝ) * y * (x ^ 2)) + ((240 : ℝ) * x * y))

def base1LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (10351 / 625 : ℚ)
  | 0, 1 => (61543357 / 3750000 : ℚ)
  | 1, 0 => (329 / 20 : ℚ)
  | 1, 1 => (485819 / 30000 : ℚ)
  | 2, 0 => (5 / 2 : ℚ)
  | 2, 1 => (2477 / 1200 : ℚ)
  | _, _ => 0

theorem base1LowerCoeff_floor : ∀ i ∈ Finset.range (2 + 1), ∀ j ∈ Finset.range (1 + 1), (2477 / 1200 : ℚ) ≤ base1LowerCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base1LowerCoeff]

theorem base1Lower_representation (u v : ℝ) :
    base1LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 2 1 base1LowerCoeff u v := by
  norm_num [base1LowerPolynomial, bernsteinBoxEval, base1LowerCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base1Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base1LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base1Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (2477 / 1200 : ℚ)) hu0 hu1 hv0 hv1 base1LowerCoeff_floor

theorem base1Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base1LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base1Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base2UpperPolynomial (x y : ℝ) : ℝ :=
  (((-165 : ℝ) / 4) + ((-8 : ℝ) * (x ^ 3)) + ((56 : ℝ) * (x ^ 2)) + ((75 : ℝ) * y) + (((-85 : ℝ) / 2) * x) + ((-2048 : ℝ) * y * (x ^ 3)) + ((-1320 : ℝ) * x * y) + ((3584 : ℝ) * y * (x ^ 2)))

def base2UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (4055139 / 31250 : ℚ)
  | 0, 1 => (23828688367 / 187500000 : ℚ)
  | 1, 0 => (436863 / 2500 : ℚ)
  | 1, 1 => (1275239603 / 7500000 : ℚ)
  | 2, 0 => (987 / 5 : ℚ)
  | 2, 1 => (3782841 / 20000 : ℚ)
  | 3, 0 => (585 / 4 : ℚ)
  | 3, 1 => (63283 / 480 : ℚ)
  | _, _ => 0

theorem base2UpperCoeff_floor : ∀ i ∈ Finset.range (3 + 1), ∀ j ∈ Finset.range (1 + 1), (23828688367 / 187500000 : ℚ) ≤ base2UpperCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base2UpperCoeff]

theorem base2Upper_representation (u v : ℝ) :
    base2UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 3 1 base2UpperCoeff u v := by
  norm_num [base2UpperPolynomial, bernsteinBoxEval, base2UpperCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base2Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base2UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base2Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (23828688367 / 187500000 : ℚ)) hu0 hu1 hv0 hv1 base2UpperCoeff_floor

theorem base2Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base2UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base2Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base2LowerPolynomial (x y : ℝ) : ℝ :=
  (((-315 : ℝ) / 4) + ((-75 : ℝ) * y) + ((-56 : ℝ) * (x ^ 2)) + ((8 : ℝ) * (x ^ 3)) + (((245 : ℝ) / 2) * x) + ((-3584 : ℝ) * y * (x ^ 2)) + ((1320 : ℝ) * x * y) + ((2048 : ℝ) * y * (x ^ 3)))

def base2LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (44861 / 31250 : ℚ)
  | 0, 1 => (771311633 / 187500000 : ℚ)
  | 1, 0 => (15137 / 2500 : ℚ)
  | 1, 1 => (80760397 / 7500000 : ℚ)
  | 2, 0 => 33
  | 2, 1 => (825159 / 20000 : ℚ)
  | 3, 0 => (535 / 4 : ℚ)
  | 3, 1 => (71117 / 480 : ℚ)
  | _, _ => 0

theorem base2LowerCoeff_floor : ∀ i ∈ Finset.range (3 + 1), ∀ j ∈ Finset.range (1 + 1), (44861 / 31250 : ℚ) ≤ base2LowerCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base2LowerCoeff]

theorem base2Lower_representation (u v : ℝ) :
    base2LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 3 1 base2LowerCoeff u v := by
  norm_num [base2LowerPolynomial, bernsteinBoxEval, base2LowerCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base2Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base2LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base2Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (44861 / 31250 : ℚ)) hu0 hu1 hv0 hv1 base2LowerCoeff_floor

theorem base2Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base2LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base2Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base3UpperPolynomial (x y : ℝ) : ℝ :=
  (((-4425 : ℝ) / 8) + ((-180 : ℝ) * (x ^ 3)) + ((16 : ℝ) * (x ^ 4)) + ((529 : ℝ) * (x ^ 2)) + (((-35 : ℝ) / 4) * x) + (((375 : ℝ) / 2) * y) + ((-46080 : ℝ) * y * (x ^ 3)) + ((-6540 : ℝ) * x * y) + ((16384 : ℝ) * y * (x ^ 4)) + ((33856 : ℝ) * y * (x ^ 2)))

def base3UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (965421679 / 1562500 : ℚ)
  | 0, 1 => (6167200272523 / 9375000000 : ℚ)
  | 1, 0 => (60418549 / 100000 : ℚ)
  | 1, 1 => (5084559029 / 7500000 : ℚ)
  | 2, 0 => (4636039 / 10000 : ℚ)
  | 2, 1 => (8977379137 / 15000000 : ℚ)
  | 3, 0 => (7355 / 32 : ℚ)
  | 3, 1 => (7119229 / 15000 : ℚ)
  | 4, 0 => (1025 / 8 : ℚ)
  | 4, 1 => (546511 / 960 : ℚ)
  | _, _ => 0

theorem base3UpperCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (1 + 1), (1025 / 8 : ℚ) ≤ base3UpperCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base3UpperCoeff]

theorem base3Upper_representation (u v : ℝ) :
    base3UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 4 1 base3UpperCoeff u v := by
  norm_num [base3UpperPolynomial, bernsteinBoxEval, base3UpperCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base3Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base3UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base3Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (1025 / 8 : ℚ)) hu0 hu1 hv0 hv1 base3UpperCoeff_floor

theorem base3Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base3UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base3Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base3LowerPolynomial (x y : ℝ) : ℝ :=
  (((-5175 : ℝ) / 8) + ((-529 : ℝ) * (x ^ 2)) + ((-16 : ℝ) * (x ^ 4)) + ((180 : ℝ) * (x ^ 3)) + (((-375 : ℝ) / 2) * y) + (((3235 : ℝ) / 4) * x) + ((-33856 : ℝ) * y * (x ^ 2)) + ((-16384 : ℝ) * y * (x ^ 4)) + ((6540 : ℝ) * x * y) + ((46080 : ℝ) * y * (x ^ 3)))

def base3LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (1084578321 / 1562500 : ℚ)
  | 0, 1 => (6132799727477 / 9375000000 : ℚ)
  | 1, 0 => (107981451 / 100000 : ℚ)
  | 1, 1 => (7545440971 / 7500000 : ℚ)
  | 2, 0 => (15923961 / 10000 : ℚ)
  | 2, 1 => (21862620863 / 15000000 : ℚ)
  | 3, 0 => (70341 / 32 : ℚ)
  | 3, 1 => (29300771 / 15000 : ℚ)
  | 4, 0 => (21375 / 8 : ℚ)
  | 4, 1 => (2141489 / 960 : ℚ)
  | _, _ => 0

theorem base3LowerCoeff_floor : ∀ i ∈ Finset.range (4 + 1), ∀ j ∈ Finset.range (1 + 1), (6132799727477 / 9375000000 : ℚ) ≤ base3LowerCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base3LowerCoeff]

theorem base3Lower_representation (u v : ℝ) :
    base3LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 4 1 base3LowerCoeff u v := by
  norm_num [base3LowerPolynomial, bernsteinBoxEval, base3LowerCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base3Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base3LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base3Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (6132799727477 / 9375000000 : ℚ)) hu0 hu1 hv0 hv1 base3LowerCoeff_floor

theorem base3Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base3LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base3Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base4UpperPolynomial (x y : ℝ) : ℝ :=
  (((-94125 : ℝ) / 16) + ((-2588 : ℝ) * (x ^ 3)) + ((-32 : ℝ) * (x ^ 5)) + ((528 : ℝ) * (x ^ 4)) + ((4256 : ℝ) * (x ^ 2)) + (((1875 : ℝ) / 4) * y) + (((16535 : ℝ) / 8) * x) + ((-662528 : ℝ) * y * (x ^ 3)) + ((-131072 : ℝ) * y * (x ^ 5)) + ((-30930 : ℝ) * x * y) + ((272384 : ℝ) * y * (x ^ 2)) + ((540672 : ℝ) * y * (x ^ 4)))

def base4UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (313071805519 / 78125000 : ℚ)
  | 0, 1 => (556198996631229 / 156250000000 : ℚ)
  | 1, 0 => (149367555553 / 31250000 : ℚ)
  | 1, 1 => (121166256277781 / 31250000000 : ℚ)
  | 2, 0 => (932687387 / 156250 : ℚ)
  | 2, 1 => (5240154495193 / 1250000000 : ℚ)
  | 3, 0 => (407371903 / 50000 : ℚ)
  | 3, 1 => (235576193181 / 50000000 : ℚ)
  | 4, 0 => (2389513 / 200 : ℚ)
  | 4, 1 => (2160639181 / 400000 : ℚ)
  | 5, 0 => (277625 / 16 : ℚ)
  | 5, 1 => (3220169 / 640 : ℚ)
  | _, _ => 0

theorem base4UpperCoeff_floor : ∀ i ∈ Finset.range (5 + 1), ∀ j ∈ Finset.range (1 + 1), (556198996631229 / 156250000000 : ℚ) ≤ base4UpperCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base4UpperCoeff]

theorem base4Upper_representation (u v : ℝ) :
    base4UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 5 1 base4UpperCoeff u v := by
  norm_num [base4UpperPolynomial, bernsteinBoxEval, base4UpperCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base4Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base4UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base4Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (556198996631229 / 156250000000 : ℚ)) hu0 hu1 hv0 hv1 base4UpperCoeff_floor

theorem base4Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base4UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base4Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base4LowerPolynomial (x y : ℝ) : ℝ :=
  (((-97875 : ℝ) / 16) + ((-4256 : ℝ) * (x ^ 2)) + ((-528 : ℝ) * (x ^ 4)) + ((32 : ℝ) * (x ^ 5)) + ((2588 : ℝ) * (x ^ 3)) + (((-1875 : ℝ) / 4) * y) + (((47465 : ℝ) / 8) * x) + ((-540672 : ℝ) * y * (x ^ 4)) + ((-272384 : ℝ) * y * (x ^ 2)) + ((30930 : ℝ) * x * y) + ((131072 : ℝ) * y * (x ^ 5)) + ((662528 : ℝ) * y * (x ^ 3)))

def base4LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (711928194481 / 78125000 : ℚ)
  | 0, 1 => (1493801003368771 / 156250000000 : ℚ)
  | 1, 0 => (353632444447 / 31250000 : ℚ)
  | 1, 1 => (381833743722219 / 31250000000 : ℚ)
  | 2, 0 => (2047312613 / 156250 : ℚ)
  | 2, 1 => (18599845504807 / 1250000000 : ℚ)
  | 3, 0 => (695028097 / 50000 : ℚ)
  | 3, 1 => (866823806819 / 50000000 : ℚ)
  | 4, 0 => (2615287 / 200 : ℚ)
  | 4, 1 => (7848960819 / 400000 : ℚ)
  | 5, 0 => (170375 / 16 : ℚ)
  | 5, 1 => (14699831 / 640 : ℚ)
  | _, _ => 0

theorem base4LowerCoeff_floor : ∀ i ∈ Finset.range (5 + 1), ∀ j ∈ Finset.range (1 + 1), (711928194481 / 78125000 : ℚ) ≤ base4LowerCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base4LowerCoeff]

theorem base4Lower_representation (u v : ℝ) :
    base4LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 5 1 base4LowerCoeff u v := by
  norm_num [base4LowerPolynomial, bernsteinBoxEval, base4LowerCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base4Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base4LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base4Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (711928194481 / 78125000 : ℚ)) hu0 hu1 hv0 hv1 base4LowerCoeff_floor

theorem base4Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base4LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base4Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base5UpperPolynomial (x y : ℝ) : ℝ :=
  (((-5750625 : ℝ) / 32) + ((-30510 : ℝ) * (x ^ 3)) + ((-1456 : ℝ) * (x ^ 5)) + ((64 : ℝ) * (x ^ 6)) + ((10720 : ℝ) * (x ^ 4)) + (((9375 : ℝ) / 8) * y) + (((126121 : ℝ) / 4) * (x ^ 2)) + (((1777065 : ℝ) / 16) * x) + ((-7810560 : ℝ) * y * (x ^ 3)) + ((-5963776 : ℝ) * y * (x ^ 5)) + ((-142935 : ℝ) * x * y) + ((1048576 : ℝ) * y * (x ^ 6)) + ((2017936 : ℝ) * y * (x ^ 2)) + ((10977280 : ℝ) * y * (x ^ 4)))

def base5UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (759255058262659 / 3906250000 : ℚ)
  | 0, 1 => (4612905402561614003 / 23437500000000 : ℚ)
  | 1, 0 => (149316517017191 / 625000000 : ℚ)
  | 1, 1 => (230207290574921197 / 937500000000 : ℚ)
  | 2, 0 => (3603165506751 / 12500000 : ℚ)
  | 2, 1 => (3801352452260157 / 12500000000 : ℚ)
  | 3, 0 => (342475733413 / 1000000 : ℚ)
  | 3, 1 => (566511307739201 / 1500000000 : ℚ)
  | 4, 0 => (4993828417 / 12500 : ℚ)
  | 4, 1 => (142239066278951 / 300000000 : ℚ)
  | 5, 0 => (145348839 / 320 : ℚ)
  | 5, 1 => (19435899167 / 32000 : ℚ)
  | 6, 0 => (16004225 / 32 : ℚ)
  | 6, 1 => (3098559767 / 3840 : ℚ)
  | _, _ => 0

theorem base5UpperCoeff_floor : ∀ i ∈ Finset.range (6 + 1), ∀ j ∈ Finset.range (1 + 1), (759255058262659 / 3906250000 : ℚ) ≤ base5UpperCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base5UpperCoeff]

theorem base5Upper_representation (u v : ℝ) :
    base5UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 6 1 base5UpperCoeff u v := by
  norm_num [base5UpperPolynomial, bernsteinBoxEval, base5UpperCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base5Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base5UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base5Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (759255058262659 / 3906250000 : ℚ)) hu0 hu1 hv0 hv1 base5UpperCoeff_floor

theorem base5Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base5UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base5Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base5LowerPolynomial (x y : ℝ) : ℝ :=
  (((-5769375 : ℝ) / 32) + ((-10720 : ℝ) * (x ^ 4)) + ((-64 : ℝ) * (x ^ 6)) + ((1456 : ℝ) * (x ^ 5)) + ((30510 : ℝ) * (x ^ 3)) + (((-126121 : ℝ) / 4) * (x ^ 2)) + (((-9375 : ℝ) / 8) * y) + (((2062935 : ℝ) / 16) * x) + ((-10977280 : ℝ) * y * (x ^ 4)) + ((-2017936 : ℝ) * y * (x ^ 2)) + ((-1048576 : ℝ) * y * (x ^ 6)) + ((142935 : ℝ) * x * y) + ((5963776 : ℝ) * y * (x ^ 5)) + ((7810560 : ℝ) * y * (x ^ 3)))

def base5LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (778244941737341 / 3906250000 : ℚ)
  | 0, 1 => (4612094597438385997 / 23437500000000 : ℚ)
  | 1, 0 => (143183482982809 / 625000000 : ℚ)
  | 1, 1 => (208542709425078803 / 937500000000 : ℚ)
  | 2, 0 => (3176834493249 / 12500000 : ℚ)
  | 2, 1 => (2978647547739843 / 12500000000 : ℚ)
  | 3, 0 => (274324266587 / 1000000 : ℚ)
  | 3, 1 => (358688692260799 / 1500000000 : ℚ)
  | 4, 0 => (3646171583 / 12500 : ℚ)
  | 4, 1 => (65120933721049 / 300000000 : ℚ)
  | 5, 0 => (99643161 / 320 : ℚ)
  | 5, 1 => (5063300833 / 32000 : ℚ)
  | 6, 0 => (10875775 / 32 : ℚ)
  | 6, 1 => (127040233 / 3840 : ℚ)
  | _, _ => 0

theorem base5LowerCoeff_floor : ∀ i ∈ Finset.range (6 + 1), ∀ j ∈ Finset.range (1 + 1), (127040233 / 3840 : ℚ) ≤ base5LowerCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base5LowerCoeff]

theorem base5Lower_representation (u v : ℝ) :
    base5LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 6 1 base5LowerCoeff u v := by
  norm_num [base5LowerPolynomial, bernsteinBoxEval, base5LowerCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base5Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base5LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base5Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (127040233 / 3840 : ℚ)) hu0 hu1 hv0 hv1 base5LowerCoeff_floor

theorem base5Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base5LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base5Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base6UpperPolynomial (x y : ℝ) : ℝ :=
  (((-191953125 : ℝ) / 64) + ((-39640 : ℝ) * (x ^ 5)) + ((-128 : ℝ) * (x ^ 7)) + ((3840 : ℝ) * (x ^ 6)) + ((173580 : ℝ) * (x ^ 4)) + (((-644791 : ℝ) / 2) * (x ^ 3)) + (((46875 : ℝ) / 16) * y) + (((445627 : ℝ) / 2) * (x ^ 2)) + (((62694835 : ℝ) / 32) * x) + ((-162365440 : ℝ) * y * (x ^ 5)) + ((-82533248 : ℝ) * y * (x ^ 3)) + ((-8388608 : ℝ) * y * (x ^ 7)) + ((14260064 : ℝ) * y * (x ^ 2)) + ((62914560 : ℝ) * y * (x ^ 6)) + ((177745920 : ℝ) * y * (x ^ 4)) + (((-1305165 : ℝ) / 2) * x * y))

def base6UpperCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (671450032219849099 / 195312500000 : ℚ)
  | 0, 1 => (4063516997096216777407 / 1171875000000000 : ℚ)
  | 1, 0 => (88133202951909553 / 21875000000 : ℚ)
  | 1, 1 => (265890923140351255361 / 65625000000000 : ℚ)
  | 2, 0 => (1009238743628659 / 218750000 : ℚ)
  | 2, 1 => (1722914281303027547 / 375000000000 : ℚ)
  | 3, 0 => (905106931643699 / 175000000 : ℚ)
  | 3, 1 => (2637142194366888349 / 525000000000 : ℚ)
  | 4, 0 => (99355494941099 / 17500000 : ℚ)
  | 4, 1 => (545674256679275597 / 105000000000 : ℚ)
  | 5, 0 => (1708891601393 / 280000 : ℚ)
  | 5, 1 => (4074230191398133 / 840000000 : ℚ)
  | 6, 0 => (225226033 / 35 : ℚ)
  | 6, 1 => (23404793410349 / 6720000 : ℚ)
  | 7, 0 => (427532825 / 64 : ℚ)
  | 7, 1 => (202008359 / 1536 : ℚ)
  | _, _ => 0

theorem base6UpperCoeff_floor : ∀ i ∈ Finset.range (7 + 1), ∀ j ∈ Finset.range (1 + 1), (202008359 / 1536 : ℚ) ≤ base6UpperCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base6UpperCoeff]

theorem base6Upper_representation (u v : ℝ) :
    base6UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 7 1 base6UpperCoeff u v := by
  norm_num [base6UpperPolynomial, bernsteinBoxEval, base6UpperCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base6Upper_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base6UpperPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base6Upper_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (202008359 / 1536 : ℚ)) hu0 hu1 hv0 hv1 base6UpperCoeff_floor

theorem base6Upper_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base6UpperPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base6Upper_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

noncomputable def base6LowerPolynomial (x y : ℝ) : ℝ :=
  (((-192046875 : ℝ) / 64) + ((-173580 : ℝ) * (x ^ 4)) + ((-3840 : ℝ) * (x ^ 6)) + ((128 : ℝ) * (x ^ 7)) + ((39640 : ℝ) * (x ^ 5)) + (((-445627 : ℝ) / 2) * (x ^ 2)) + (((-46875 : ℝ) / 16) * y) + (((644791 : ℝ) / 2) * (x ^ 3)) + (((65305165 : ℝ) / 32) * x) + ((-177745920 : ℝ) * y * (x ^ 4)) + ((-62914560 : ℝ) * y * (x ^ 6)) + ((-14260064 : ℝ) * y * (x ^ 2)) + ((8388608 : ℝ) * y * (x ^ 7)) + ((82533248 : ℝ) * y * (x ^ 3)) + ((162365440 : ℝ) * y * (x ^ 5)) + (((1305165 : ℝ) / 2) * x * y))

def base6LowerCoeff (i j : ℕ) : ℚ :=
  match i, j with
  | 0, 0 => (609799967780150901 / 195312500000 : ℚ)
  | 0, 1 => (3623983002903783222593 / 1171875000000000 : ℚ)
  | 1, 0 => (78616797048090447 / 21875000000 : ℚ)
  | 1, 1 => (234359076859648744639 / 65625000000000 : ℚ)
  | 2, 0 => (890761256371341 / 218750000 : ℚ)
  | 2, 1 => (10739600030878807171 / 2625000000000 : ℚ)
  | 3, 0 => (800893068356301 / 175000000 : ℚ)
  | 3, 1 => (2480857805633111651 / 525000000000 : ℚ)
  | 4, 0 => (89844505058901 / 17500000 : ℚ)
  | 4, 1 => (589525743320724403 / 105000000000 : ℚ)
  | 5, 0 => (1615908398607 / 280000 : ℚ)
  | 5, 1 => (5900169808601867 / 840000000 : ℚ)
  | 6, 0 => (227573967 / 35 : ℚ)
  | 6, 1 => (9076115227093 / 960000 : ℚ)
  | 7, 0 => (468467175 / 64 : ℚ)
  | 7, 1 => (21301991641 / 1536 : ℚ)
  | _, _ => 0

theorem base6LowerCoeff_floor : ∀ i ∈ Finset.range (7 + 1), ∀ j ∈ Finset.range (1 + 1), (3623983002903783222593 / 1171875000000000 : ℚ) ≤ base6LowerCoeff i j := by
  intro i hi j hj
  simp only [Finset.mem_range] at hi hj
  interval_cases i <;> interval_cases j <;> norm_num [base6LowerCoeff]

theorem base6Lower_representation (u v : ℝ) :
    base6LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) =
      bernsteinBoxEval 7 1 base6LowerCoeff u v := by
  norm_num [base6LowerPolynomial, bernsteinBoxEval, base6LowerCoeff, bernsteinBasis_eq, Nat.choose, Finset.sum_range_succ]
  ring

theorem base6Lower_pos {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 < base6LowerPolynomial (((157 : ℝ) / 50) + (((93 : ℝ) / 50)) * u) ((0 : ℝ) + (((1 : ℝ) / 12000)) * v) := by
  rw [base6Lower_representation]
  exact bernsteinBoxEval_pos (by norm_num : (0 : ℚ) < (3623983002903783222593 / 1171875000000000 : ℚ)) hu0 hu1 hv0 hv1 base6LowerCoeff_floor

theorem base6Lower_box_pos {x y : ℝ}
    (hx0 : ((157 : ℝ) / 50) ≤ x) (hx1 : x ≤ (5 : ℝ))
    (hy0 : (0 : ℝ) ≤ y) (hy1 : y ≤ ((1 : ℝ) / 12000)) :
    0 < base6LowerPolynomial x y := by
  let u := (x - ((157 : ℝ) / 50)) / ((93 : ℝ) / 50)
  let v := (y - (0 : ℝ)) / ((1 : ℝ) / 12000)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((93 : ℝ) / 50))]
    linarith
  have hv0 : 0 ≤ v := by dsimp [v]; positivity
  have hv1 : v ≤ 1 := by
    dsimp [v]
    rw [div_le_one (by norm_num : (0 : ℝ) < ((1 : ℝ) / 12000))]
    linarith
  have h := base6Lower_pos hu0 hu1 hv0 hv1
  dsimp [u, v] at h
  convert h using 1 <;> field_simp <;> ring_nf

end PF4.CERT12Inequalities.Generated
