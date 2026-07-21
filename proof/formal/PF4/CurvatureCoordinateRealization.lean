import PF4.TranslationQuotientPsi
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Curvature-coordinate realization on the actual coordinate range

Maintained realization. The global `invFun` extension is differentiated only
at points in the open range of the coordinate map. No surjectivity is assumed.
-/

namespace PF4.CurvatureCoordinateRealization

open Filter Set
open scoped Topology
open PF4.Curvature PF4.TranslationQuotientPsi
open PF4.C4Invariant

/-- The canonical inverse extension of the curvature coordinate. Its values
outside the coordinate range are deliberately left unspecified. -/
noncomputable def coordinateInverse (S : ℝ → ℝ) : ℝ → ℝ :=
  Function.invFun (kernelCoordinate S)

/-- The coordinate curvature function obtained from the actual kernel
curvature through the canonical inverse extension. -/
noncomputable def coordinateQ (S q : ℝ → ℝ) : ℝ → ℝ :=
  fun y => q (coordinateInverse S y)

/-- First coordinate derivative, expressed in the original variable. -/
noncomputable def coordinateQ1 (S q q1 : ℝ → ℝ) : ℝ → ℝ :=
  fun y => q1 (coordinateInverse S y) / q (coordinateInverse S y)

/-- Second coordinate derivative, expressed in the original variable. -/
noncomputable def coordinateQ2 (S q q1 q2 : ℝ → ℝ) : ℝ → ℝ :=
  fun y =>
    (q2 (coordinateInverse S y) * q (coordinateInverse S y) -
      q1 (coordinateInverse S y) ^ 2) /
      q (coordinateInverse S y) ^ 3

/-- Third coordinate derivative, obtained by applying `(1/q) d/du` once
more. -/
noncomputable def coordinateQ3 (S q q1 q2 q3 : ℝ → ℝ) : ℝ → ℝ :=
  fun y =>
    (q3 (coordinateInverse S y) * q (coordinateInverse S y) ^ 2 -
      4 * q (coordinateInverse S y) * q1 (coordinateInverse S y) *
        q2 (coordinateInverse S y) +
      3 * q1 (coordinateInverse S y) ^ 3) /
      q (coordinateInverse S y) ^ 5

/-- Fourth coordinate derivative. -/
noncomputable def coordinateQ4 (S q q1 q2 q3 q4 : ℝ → ℝ) : ℝ → ℝ :=
  fun y =>
    (q4 (coordinateInverse S y) * q (coordinateInverse S y) ^ 3 -
      7 * q (coordinateInverse S y) ^ 2 * q1 (coordinateInverse S y) *
        q3 (coordinateInverse S y) +
      25 * q (coordinateInverse S y) * q1 (coordinateInverse S y) ^ 2 *
        q2 (coordinateInverse S y) -
      4 * q (coordinateInverse S y) ^ 2 * q2 (coordinateInverse S y) ^ 2 -
      15 * q1 (coordinateInverse S y) ^ 4) /
      q (coordinateInverse S y) ^ 7

/-- The S03 numerator whose quotient by `q³` is the coordinate-curvature
excess above one. -/
noncomputable def kernelF2 (q q1 q2 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => q u ^ 3 - (q u * q2 u - q1 u ^ 2)

/-- The paper's primary central-moment determinant expressed through the
actual logarithmic-curvature jet `c₂=-q,...,c₆=-q₄`. -/
noncomputable def kernelDeterminantC4
    (q q1 q2 q3 q4 : ℝ → ℝ) : ℝ → ℝ :=
  fun u => determinantC4 (-q u) (-q1 u) (-q2 u) (-q3 u) (-q4 u)

/-- The derivative of `y=-S` is the actual curvature `q`. -/
theorem hasDerivAt_kernelCoordinate
    {S q : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u) (u : ℝ) :
    HasDerivAt (kernelCoordinate S) (q u) u := by
  change HasDerivAt (fun x => -S x) (q u) u
  simpa using (hS u).const_mul (-1)

/-- Positive curvature constructs strict coordinate monotonicity. -/
theorem kernelCoordinate_strictMono
    {S q : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) :
    StrictMono (kernelCoordinate S) := by
  exact strictMono_of_hasDerivAt_pos (hasDerivAt_kernelCoordinate hS) hqpos

/-- The actual coordinate is an equivalence with its range, not with all of
`ℝ`. -/
noncomputable def coordinateRangeEquiv
    (S : ℝ → ℝ) (hS : Function.Injective (kernelCoordinate S)) :
    ℝ ≃ Set.range (kernelCoordinate S) :=
  Equiv.ofInjective (kernelCoordinate S) hS

@[simp]
theorem coordinateRangeEquiv_apply
    (S : ℝ → ℝ) (hS : Function.Injective (kernelCoordinate S)) (u : ℝ) :
    coordinateRangeEquiv S hS u =
      ⟨kernelCoordinate S u, Set.mem_range_self u⟩ := by
  rfl

@[simp]
theorem coordinateRangeEquiv_symm_apply
    (S : ℝ → ℝ) (hS : Function.Injective (kernelCoordinate S)) (u : ℝ) :
    (coordinateRangeEquiv S hS).symm
      ⟨kernelCoordinate S u, Set.mem_range_self u⟩ = u := by
  exact Equiv.ofInjective_symm_apply hS u

/-- The global inverse extension is a genuine left inverse at every original
point. -/
theorem coordinateInverse_apply_kernelCoordinate
    {S q : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    coordinateInverse S (kernelCoordinate S u) = u := by
  exact Function.leftInverse_invFun
    (kernelCoordinate_strictMono hS hqpos).injective u

/-- Differentiability of `q` makes the coordinate derivative strict, which is
the input needed by the inverse-function theorem. -/
theorem hasStrictDerivAt_kernelCoordinate
    {S q q1 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u) (u : ℝ) :
    HasStrictDerivAt (kernelCoordinate S) (q u) u := by
  apply hasStrictDerivAt_of_hasDerivAt_of_continuousAt
  · exact Filter.Eventually.of_forall (hasDerivAt_kernelCoordinate hS)
  · exact (hq u).continuousAt

/-- The range is open because the coordinate derivative is everywhere
nonzero. Thus off-range values of `coordinateInverse` cannot affect local
calculus at any coordinate point. -/
theorem isOpen_range_kernelCoordinate
    {S q q1 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u) (hqpos : ∀ u, 0 < q u) :
    IsOpen (Set.range (kernelCoordinate S)) := by
  exact (isOpenMap_of_hasStrictDerivAt
    (hasStrictDerivAt_kernelCoordinate hS hq)
    (fun u => (hqpos u).ne')).isOpen_range

/-- The canonical inverse extension has derivative `1/q(u)` at every actual
coordinate point. The proof uses only the global left-inverse identity and a
local inverse theorem. -/
theorem hasDerivAt_coordinateInverse
    {S q q1 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u) (hqpos : ∀ u, 0 < q u)
    (u : ℝ) :
    HasDerivAt (coordinateInverse S) (q u)⁻¹
      (kernelCoordinate S u) := by
  have hstrict := hasStrictDerivAt_kernelCoordinate hS hq u
  have hleft : ∀ᶠ x in 𝓝 u,
      coordinateInverse S (kernelCoordinate S x) = x :=
    Filter.Eventually.of_forall
      (coordinateInverse_apply_kernelCoordinate hS hqpos)
  exact (hstrict.to_local_left_inverse (hqpos u).ne' hleft).hasDerivAt

/-- Object identity `Q(y(u))=q(u)`, derived from the constructed inverse. -/
theorem coordinateQ_apply_kernelCoordinate
    {S q : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    coordinateQ S q (kernelCoordinate S u) = q u := by
  rw [coordinateQ, coordinateInverse_apply_kernelCoordinate hS hqpos]

/-- The constructed `Q` has the required first coordinate derivative at every
point of the actual coordinate range. -/
theorem hasDerivAt_coordinateQ
    {S q q1 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u) (hqpos : ∀ u, 0 < q u)
    (u : ℝ) :
    HasDerivAt (coordinateQ S q) (q1 u / q u)
      (kernelCoordinate S u) := by
  have hinv := hasDerivAt_coordinateInverse hS hq hqpos u
  have hinvValue := coordinateInverse_apply_kernelCoordinate hS hqpos u
  have hqAt : HasDerivAt q (q1 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq u
  have hcomp := hqAt.comp (kernelCoordinate S u) hinv
  have hcomp' : HasDerivAt (coordinateQ S q) (q1 u * (q u)⁻¹)
      (kernelCoordinate S u) := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [] with y
    rfl
  exact hcomp'.congr_deriv (by rw [div_eq_mul_inv])

/-- Object identity `Q₁(y(u))=q₁(u)/q(u)`. -/
theorem coordinateQ1_apply_kernelCoordinate
    {S q q1 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    coordinateQ1 S q q1 (kernelCoordinate S u) = q1 u / q u := by
  rw [coordinateQ1, coordinateInverse_apply_kernelCoordinate hS hqpos]

/-- The first coordinate derivative itself has the stated second coordinate
derivative at every range point. -/
theorem hasDerivAt_coordinateQ1
    {S q q1 q2 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    HasDerivAt (coordinateQ1 S q q1)
      ((q2 u * q u - q1 u ^ 2) / q u ^ 3)
      (kernelCoordinate S u) := by
  have hinv := hasDerivAt_coordinateInverse hS hq hqpos u
  have hinvValue := coordinateInverse_apply_kernelCoordinate hS hqpos u
  have hqAt : HasDerivAt q (q1 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq u
  have hq1At : HasDerivAt q1 (q2 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq1 u
  have hratio := hq1At.fun_div hqAt (by simpa [hinvValue] using (hqpos u).ne')
  have hcomp := hratio.comp (kernelCoordinate S u) hinv
  simp only [hinvValue] at hcomp
  have hcomp' : HasDerivAt (coordinateQ1 S q q1)
      (((q2 u * q u - q1 u * q1 u) / q u ^ 2) * (q u)⁻¹)
      (kernelCoordinate S u) := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [] with y
    rfl
  apply hcomp'.congr_deriv
  field_simp [(hqpos u).ne']

/-- Object identity for the constructed second coordinate derivative. -/
theorem coordinateQ2_apply_kernelCoordinate
    {S q q1 q2 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    coordinateQ2 S q q1 q2 (kernelCoordinate S u) =
      (q2 u * q u - q1 u ^ 2) / q u ^ 3 := by
  rw [coordinateQ2, coordinateInverse_apply_kernelCoordinate hS hqpos]

/-- The second coordinate derivative has the constructed third derivative at
every range point. -/
theorem hasDerivAt_coordinateQ2
    {S q q1 q2 q3 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    HasDerivAt (coordinateQ2 S q q1 q2)
      ((q3 u * q u ^ 2 - 4 * q u * q1 u * q2 u + 3 * q1 u ^ 3) /
        q u ^ 5)
      (kernelCoordinate S u) := by
  have hinv := hasDerivAt_coordinateInverse hS hq hqpos u
  have hinvValue := coordinateInverse_apply_kernelCoordinate hS hqpos u
  have hqAt : HasDerivAt q (q1 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq u
  have hq1At : HasDerivAt q1 (q2 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq1 u
  have hq2At : HasDerivAt q2 (q3 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq2 u
  have hnum := (hq2At.mul hqAt).sub (hq1At.pow 2)
  have hden := hqAt.pow 3
  have hratio := hnum.fun_div hden
    (pow_ne_zero 3 (by simpa [hinvValue] using (hqpos u).ne'))
  have hcomp := hratio.comp (kernelCoordinate S u) hinv
  simp only [hinvValue, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply] at hcomp
  have hfun : coordinateQ2 S q q1 q2 =ᶠ[𝓝 (kernelCoordinate S u)]
      ((fun y => (q2 * q - q1 ^ 2) y / (q ^ 3) y) ∘
        coordinateInverse S) :=
    Filter.Eventually.of_forall fun y => rfl
  have hcomp' := hcomp.congr_of_eventuallyEq hfun
  apply hcomp'.congr_deriv
  field_simp [(hqpos u).ne']
  ring

/-- Object identity for the third coordinate derivative. -/
theorem coordinateQ3_apply_kernelCoordinate
    {S q q1 q2 q3 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    coordinateQ3 S q q1 q2 q3 (kernelCoordinate S u) =
      (q3 u * q u ^ 2 - 4 * q u * q1 u * q2 u + 3 * q1 u ^ 3) /
        q u ^ 5 := by
  rw [coordinateQ3, coordinateInverse_apply_kernelCoordinate hS hqpos]

/-- The third coordinate derivative has the constructed fourth derivative at
every range point. -/
theorem hasDerivAt_coordinateQ3
    {S q q1 q2 q3 q4 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hq3 : ∀ u, HasDerivAt q3 (q4 u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    HasDerivAt (coordinateQ3 S q q1 q2 q3)
      ((q4 u * q u ^ 3 - 7 * q u ^ 2 * q1 u * q3 u +
        25 * q u * q1 u ^ 2 * q2 u - 4 * q u ^ 2 * q2 u ^ 2 -
        15 * q1 u ^ 4) / q u ^ 7)
      (kernelCoordinate S u) := by
  have hinv := hasDerivAt_coordinateInverse hS hq hqpos u
  have hinvValue := coordinateInverse_apply_kernelCoordinate hS hqpos u
  have hqAt : HasDerivAt q (q1 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq u
  have hq1At : HasDerivAt q1 (q2 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq1 u
  have hq2At : HasDerivAt q2 (q3 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq2 u
  have hq3At : HasDerivAt q3 (q4 u)
      (coordinateInverse S (kernelCoordinate S u)) := by
    simpa [hinvValue] using hq3 u
  have hnum :=
    ((hq3At.mul (hqAt.pow 2)).sub
      ((((hqAt.const_mul 4).mul hq1At).mul hq2At))).add
      ((hq1At.pow 3).const_mul 3)
  have hden := hqAt.pow 5
  have hratio := hnum.fun_div hden
    (pow_ne_zero 5 (by simpa [hinvValue] using (hqpos u).ne'))
  have hcomp := hratio.comp (kernelCoordinate S u) hinv
  simp only [hinvValue, Pi.add_apply, Pi.mul_apply, Pi.sub_apply,
    Pi.pow_apply] at hcomp
  have hfun : coordinateQ3 S q q1 q2 q3 =ᶠ[𝓝 (kernelCoordinate S u)]
      ((fun y =>
        (q3 * q ^ 2 - (fun x => 4 * q x) * q1 * q2 +
          fun x => 3 * (q1 ^ 3) x) y / (q ^ 5) y) ∘
        coordinateInverse S) :=
    Filter.Eventually.of_forall fun y => rfl
  have hcomp' := hcomp.congr_of_eventuallyEq hfun
  apply hcomp'.congr_deriv
  field_simp [(hqpos u).ne']
  ring

/-- Object identity for the fourth coordinate derivative. -/
theorem coordinateQ4_apply_kernelCoordinate
    {S q q1 q2 q3 q4 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    coordinateQ4 S q q1 q2 q3 q4 (kernelCoordinate S u) =
      (q4 u * q u ^ 3 - 7 * q u ^ 2 * q1 u * q3 u +
        25 * q u * q1 u ^ 2 * q2 u - 4 * q u ^ 2 * q2 u ^ 2 -
        15 * q1 u ^ 4) / q u ^ 7 := by
  rw [coordinateQ4, coordinateInverse_apply_kernelCoordinate hS hqpos]

/-- The maintained coordinate curvature is exactly `1 + F₂/q³` on the
actual coordinate range. -/
theorem curvature_coordinateQ2_apply_kernelCoordinate
    {S q q1 q2 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    curvature (coordinateQ2 S q q1 q2) (kernelCoordinate S u) =
      1 + kernelF2 q q1 q2 u / q u ^ 3 := by
  unfold curvature
  rw [coordinateQ2_apply_kernelCoordinate hS hqpos]
  unfold kernelF2
  field_simp [(hqpos u).ne']
  ring

/-- Positive S03 `F₂` gives positive maintained coordinate curvature at every
actual coordinate point. -/
theorem curvature_coordinateQ2_pos_on_range
    {S q q1 q2 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) (hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u)
    (u : ℝ) :
    0 < curvature (coordinateQ2 S q q1 q2) (kernelCoordinate S u) := by
  rw [curvature_coordinateQ2_apply_kernelCoordinate hS hqpos]
  have hrho : 0 < kernelF2 q q1 q2 u / q u ^ 3 :=
    div_pos (hF2pos u) (pow_pos (hqpos u) 3)
  linarith

/-- The coordinate cumulants recover the original logarithmic cumulants, so
the maintained determinant is exactly the paper determinant on the actual
coordinate range. -/
theorem determinantC4Function_apply_kernelCoordinate
    {S q q1 q2 q3 q4 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u) (u : ℝ) :
    determinantC4Function
        (coordinateQ S q) (coordinateQ1 S q q1)
        (coordinateQ2 S q q1 q2) (coordinateQ3 S q q1 q2 q3)
        (coordinateQ4 S q q1 q2 q3 q4) (kernelCoordinate S u) =
      kernelDeterminantC4 q q1 q2 q3 q4 u := by
  unfold determinantC4Function coordinateDeterminantC4 kernelDeterminantC4
  rw [coordinateQ_apply_kernelCoordinate hS hqpos,
    coordinateQ1_apply_kernelCoordinate hS hqpos,
    coordinateQ2_apply_kernelCoordinate hS hqpos,
    coordinateQ3_apply_kernelCoordinate hS hqpos,
    coordinateQ4_apply_kernelCoordinate hS hqpos]
  unfold coordinateC2 coordinateC3 coordinateC4 coordinateC5 coordinateC6
  congr 1 <;> field_simp [(hqpos u).ne'] <;> ring

/-- The entire constructed coordinate jet is valid at every point of the
actual coordinate range. This is the honest local replacement for a global
jet premise on an arbitrary inverse extension. -/
theorem coordinateJet_on_range
    {S q q1 q2 q3 q4 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (hq1 : ∀ u, HasDerivAt q1 (q2 u) u)
    (hq2 : ∀ u, HasDerivAt q2 (q3 u) u)
    (hq3 : ∀ u, HasDerivAt q3 (q4 u) u)
    (hqpos : ∀ u, 0 < q u) :
    ∀ y ∈ Set.range (kernelCoordinate S),
      HasDerivAt (coordinateQ S q) (coordinateQ1 S q q1 y) y ∧
      HasDerivAt (coordinateQ1 S q q1) (coordinateQ2 S q q1 q2 y) y ∧
      HasDerivAt (coordinateQ2 S q q1 q2)
        (coordinateQ3 S q q1 q2 q3 y) y ∧
      HasDerivAt (coordinateQ3 S q q1 q2 q3)
        (coordinateQ4 S q q1 q2 q3 q4 y) y := by
  rintro y ⟨u, rfl⟩
  constructor
  · rw [coordinateQ1_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ hS hq hqpos u
  constructor
  · rw [coordinateQ2_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ1 hS hq hq1 hqpos u
  constructor
  · rw [coordinateQ3_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ2 hS hq hq1 hq2 hqpos u
  · rw [coordinateQ4_apply_kernelCoordinate hS hqpos]
    exact hasDerivAt_coordinateQ3 hS hq hq1 hq2 hq3 hqpos u

/-- The three sign inputs needed by the coordinate transport assembly hold on
the coordinate range when supplied by the actual `q`, `F₂`, and `C₄` signs. -/
theorem coordinateSigns_on_range
    {S q q1 q2 q3 q4 : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (hqpos : ∀ u, 0 < q u)
    (hF2pos : ∀ u, 0 < kernelF2 q q1 q2 u)
    (hC4pos : ∀ u, 0 < kernelDeterminantC4 q q1 q2 q3 q4 u) :
    ∀ y ∈ Set.range (kernelCoordinate S),
      0 < coordinateQ S q y ∧
      0 < curvature (coordinateQ2 S q q1 q2) y ∧
      0 < determinantC4Function
        (coordinateQ S q) (coordinateQ1 S q q1)
        (coordinateQ2 S q q1 q2) (coordinateQ3 S q q1 q2 q3)
        (coordinateQ4 S q q1 q2 q3 q4) y := by
  rintro y ⟨u, rfl⟩
  constructor
  · rw [coordinateQ_apply_kernelCoordinate hS hqpos]
    exact hqpos u
  constructor
  · exact curvature_coordinateQ2_pos_on_range hS hqpos hF2pos u
  · rw [determinantC4Function_apply_kernelCoordinate hS hqpos]
    exact hC4pos u

/-! ## Specialization to the maintained kernel objects -/

open PF4.TranslationQuotientSigns

/-- The constructed coordinate `Q` realizes the maintained exact kernel
curvature, with no realization premise. -/
theorem actualCoordinateQ_apply
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ u, HasDerivAt Φ (Φ1 u) u)
    (hΦ1 : ∀ u, HasDerivAt Φ1 (Φ2 u) u)
    (hΦpos : ∀ u, 0 < Φ u)
    (hqpos : ∀ u, 0 < kernelCurvature Φ Φ1 Φ2 u) (u : ℝ) :
    coordinateQ (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2)
        (kernelCoordinate (logSlope Φ Φ1) u) =
      kernelCurvature Φ Φ1 Φ2 u := by
  exact coordinateQ_apply_kernelCoordinate
    (fun x => hasDerivAt_logSlope hΦ hΦ1 hΦpos x) hqpos u

/-- The constructed first coordinate derivative realizes `q₁/q` for the
maintained exact kernel curvature. -/
theorem actualCoordinateQ1_apply
    {Φ Φ1 Φ2 q1 : ℝ → ℝ}
    (hΦ : ∀ u, HasDerivAt Φ (Φ1 u) u)
    (hΦ1 : ∀ u, HasDerivAt Φ1 (Φ2 u) u)
    (hΦpos : ∀ u, 0 < Φ u)
    (hqpos : ∀ u, 0 < kernelCurvature Φ Φ1 Φ2 u) (u : ℝ) :
    coordinateQ1 (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2) q1
        (kernelCoordinate (logSlope Φ Φ1) u) =
      q1 u / kernelCurvature Φ Φ1 Φ2 u := by
  exact coordinateQ1_apply_kernelCoordinate
    (fun x => hasDerivAt_logSlope hΦ hΦ1 hΦpos x) hqpos u

end PF4.CurvatureCoordinateRealization

