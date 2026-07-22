import PF4.GlobalStrictPF4
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Literal paper-object closure for the global Riemann kernel

This leaf module packages the logarithmic kernel objects, the ordered chord
objects, and the actual-range curvature objects used in the manuscript.  The
coordinate inverse is used only on the range of the actual coordinate map.
-/

namespace PF4.PaperObjectClosure

open MeasureTheory Set
open PF4.C4Invariant
open PF4.CentralIdentity
open PF4.ClearedJetCertificateBridge
open PF4.Curvature
open PF4.CurvatureCoordinateRealization
open PF4.GlobalKernelJetIdentification
open PF4.GlobalStrictPF4
open PF4.TranslationQuotientPsi
open PF4.TranslationQuotientSigns

/-! ## PO-0009: global logarithmic objects -/

/-- The paper's literal `ell = log Phi` for the maintained global kernel. -/
noncomputable def actualKernelLog : ℝ → ℝ :=
  fun t => Real.log (kernelJet 0 t)

/-- The paper's literal logarithmic slope `s`. -/
noncomputable def actualKernelSlope : ℝ → ℝ :=
  logSlope (kernelJet 0) (kernelJet 1)

/-- The paper's literal logarithmic curvature `q = -s'`. -/
noncomputable def actualKernelCurvature : ℝ → ℝ :=
  kernelCurvature (kernelJet 0) (kernelJet 1) (kernelJet 2)

/-- Successive ordinary derivatives of the actual logarithmic curvature. -/
noncomputable def actualKernelCurvature1 : ℝ → ℝ :=
  jetQ1 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)

noncomputable def actualKernelCurvature2 : ℝ → ℝ :=
  jetQ2 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3) (kernelJet 4)

noncomputable def actualKernelCurvature3 : ℝ → ℝ :=
  jetQ3 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
    (kernelJet 4) (kernelJet 5)

noncomputable def actualKernelCurvature4 : ℝ → ℝ :=
  jetQ4 (kernelJet 0) (kernelJet 1) (kernelJet 2) (kernelJet 3)
    (kernelJet 4) (kernelJet 5) (kernelJet 6)

theorem actualKernelValue_pos (t : ℝ) : 0 < kernelJet 0 t := by
  simpa [kernelJet, iteratedDeriv_zero] using globalRiemannKernel_pos t

theorem actualKernelLog_exp (t : ℝ) :
    Real.exp (actualKernelLog t) = kernelJet 0 t := by
  exact Real.exp_log (actualKernelValue_pos t)

theorem hasDerivAt_actualKernelLog (t : ℝ) :
    HasDerivAt actualKernelLog (actualKernelSlope t) t := by
  change HasDerivAt (fun y => Real.log (kernelJet 0 y))
    (actualKernelSlope t) t
  simpa [actualKernelSlope, logSlope] using
    (hasDerivAt_kernelJet 0 t).log (actualKernelValue_pos t).ne'

theorem hasDerivAt_actualKernelSlope (t : ℝ) :
    HasDerivAt actualKernelSlope (-actualKernelCurvature t) t := by
  simpa [actualKernelSlope, actualKernelCurvature] using
    hasDerivAt_logSlope (hasDerivAt_kernelJet 0) (hasDerivAt_kernelJet 1)
      actualKernelValue_pos t

theorem actualKernelCurvature_pos (t : ℝ) :
    0 < actualKernelCurvature t := by
  simpa [actualKernelCurvature] using actualKernelSigns.1 t

theorem actualKernelF2_pos (t : ℝ) :
    0 < kernelF2 actualKernelCurvature actualKernelCurvature1
      actualKernelCurvature2 t := by
  simpa [actualKernelCurvature, actualKernelCurvature1,
    actualKernelCurvature2] using actualKernelSigns.2.1 t

theorem actualKernelC4_pos (t : ℝ) :
    0 < kernelDeterminantC4 actualKernelCurvature actualKernelCurvature1
      actualKernelCurvature2 actualKernelCurvature3 actualKernelCurvature4 t := by
  simpa [actualKernelCurvature, actualKernelCurvature1,
    actualKernelCurvature2, actualKernelCurvature3,
    actualKernelCurvature4] using actualKernelSigns.2.2 t

theorem actualKernelCurvature_derivativeTower :
    (∀ t, HasDerivAt actualKernelCurvature (actualKernelCurvature1 t) t) ∧
    (∀ t, HasDerivAt actualKernelCurvature1 (actualKernelCurvature2 t) t) ∧
    (∀ t, HasDerivAt actualKernelCurvature2 (actualKernelCurvature3 t) t) ∧
    (∀ t, HasDerivAt actualKernelCurvature3 (actualKernelCurvature4 t) t) := by
  simpa [actualKernelCurvature, actualKernelCurvature1,
    actualKernelCurvature2, actualKernelCurvature3,
    actualKernelCurvature4] using curvatureDerivativeTower_of_rawJet
      (hasDerivAt_kernelJet 0) (hasDerivAt_kernelJet 1)
      (hasDerivAt_kernelJet 2) (hasDerivAt_kernelJet 3)
      (hasDerivAt_kernelJet 4) (hasDerivAt_kernelJet 5)
      actualKernelValue_pos

theorem continuous_actualKernelCurvature : Continuous actualKernelCurvature :=
  continuous_iff_continuousAt.mpr fun t =>
    (actualKernelCurvature_derivativeTower.1 t).continuousAt

/-- PO-0009 in one public statement: the actual logarithm recovers the
positive kernel, and its first two derivatives are the maintained `s` and
`-q`, with `q` strictly positive on the whole real line. -/
theorem actualLogSlopeCurvature_globally_wellDefined :
    (∀ t, Real.exp (actualKernelLog t) = kernelJet 0 t) ∧
    (∀ t, HasDerivAt actualKernelLog (actualKernelSlope t) t) ∧
    (∀ t, HasDerivAt actualKernelSlope (-actualKernelCurvature t) t) ∧
    (∀ t, 0 < actualKernelCurvature t) :=
  ⟨actualKernelLog_exp, hasDerivAt_actualKernelLog,
    hasDerivAt_actualKernelSlope, actualKernelCurvature_pos⟩

/-! ## PO-0010: ordered chord objects and legal denominators -/

/-- The paper's `A(a,b)=s(a)-s(b)`. -/
noncomputable def actualA (a b : ℝ) : ℝ :=
  slopeChord actualKernelSlope a b

/-- The paper's `M(a,b)=(q(b)-q(a))/A(a,b)`. -/
noncomputable def actualM (a b : ℝ) : ℝ :=
  curvatureMean actualKernelSlope actualKernelCurvature a b

theorem actualKernelSlope_strictAnti : StrictAnti actualKernelSlope := by
  simpa [actualKernelSlope, actualKernelCurvature] using
    logSlope_strictAnti_of_kernelCurvature_pos
      (hasDerivAt_kernelJet 0) (hasDerivAt_kernelJet 1)
      actualKernelValue_pos (fun t => by
        simpa [actualKernelCurvature] using actualKernelCurvature_pos t)

theorem actualA_pos {a b : ℝ} (hab : a < b) : 0 < actualA a b := by
  exact slopeChord_pos_of_lt actualKernelSlope_strictAnti hab

/-- The chord denominator is exactly the positive curvature mass on the
ordered interval. -/
theorem actualA_eq_intervalIntegral (a b : ℝ) :
    actualA a b = ∫ t in a..b, actualKernelCurvature t := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (f := kernelCoordinate actualKernelSlope)
    (f' := actualKernelCurvature)
    (fun t _ => hasDerivAt_kernelCoordinate hasDerivAt_actualKernelSlope t)
    (continuous_actualKernelCurvature.intervalIntegrable a b)
  rw [hftc]
  unfold actualA slopeChord kernelCoordinate
  ring

/-- PO-0010 in one public statement. Ordered arguments make the denominator
strictly positive and nonzero, `M` is the displayed quotient, and `A` has its
exact integral provenance. -/
theorem actualAM_wellDefined_on_ordered {a b : ℝ} (hab : a < b) :
    0 < actualA a b ∧ actualA a b ≠ 0 ∧
    actualM a b =
      (actualKernelCurvature b - actualKernelCurvature a) / actualA a b ∧
    actualA a b = ∫ t in a..b, actualKernelCurvature t := by
  have hA := actualA_pos hab
  exact ⟨hA, hA.ne', rfl, actualA_eq_intervalIntegral a b⟩

/-! ## PO-0022: actual coordinate rho and kappa -/

noncomputable def actualCoordinateQ : ℝ → ℝ :=
  coordinateQ actualKernelSlope actualKernelCurvature

noncomputable def actualCoordinateQ1 : ℝ → ℝ :=
  coordinateQ1 actualKernelSlope actualKernelCurvature actualKernelCurvature1

noncomputable def actualCoordinateQ2 : ℝ → ℝ :=
  coordinateQ2 actualKernelSlope actualKernelCurvature actualKernelCurvature1
    actualKernelCurvature2

noncomputable def actualCoordinateQ3 : ℝ → ℝ :=
  coordinateQ3 actualKernelSlope actualKernelCurvature actualKernelCurvature1
    actualKernelCurvature2 actualKernelCurvature3

noncomputable def actualCoordinateQ4 : ℝ → ℝ :=
  coordinateQ4 actualKernelSlope actualKernelCurvature actualKernelCurvature1
    actualKernelCurvature2 actualKernelCurvature3 actualKernelCurvature4

/-- The paper's `rho=1-Q''` on the maintained coordinate object. -/
noncomputable def actualCoordinateRho (y : ℝ) : ℝ :=
  1 - actualCoordinateQ2 y

/-- The paper's `kappa=2-Q''`. -/
noncomputable def actualCoordinateKappa (y : ℝ) : ℝ :=
  curvature actualCoordinateQ2 y

theorem actualCoordinateKappa_eq_one_add_rho (y : ℝ) :
    actualCoordinateKappa y = 1 + actualCoordinateRho y := by
  unfold actualCoordinateKappa actualCoordinateRho curvature
  ring

theorem actualCoordinateKappa_apply_kernelCoordinate (u : ℝ) :
    actualCoordinateKappa (kernelCoordinate actualKernelSlope u) =
      1 + kernelF2 actualKernelCurvature actualKernelCurvature1
        actualKernelCurvature2 u / actualKernelCurvature u ^ 3 := by
  simpa [actualCoordinateKappa, actualCoordinateQ2] using
    curvature_coordinateQ2_apply_kernelCoordinate
      hasDerivAt_actualKernelSlope actualKernelCurvature_pos u

theorem actualCoordinateRho_apply_kernelCoordinate (u : ℝ) :
    actualCoordinateRho (kernelCoordinate actualKernelSlope u) =
      kernelF2 actualKernelCurvature actualKernelCurvature1
        actualKernelCurvature2 u / actualKernelCurvature u ^ 3 := by
  have hk := actualCoordinateKappa_apply_kernelCoordinate u
  rw [actualCoordinateKappa_eq_one_add_rho] at hk
  linarith

theorem actualCoordinateRho_pos (u : ℝ) :
    0 < actualCoordinateRho (kernelCoordinate actualKernelSlope u) := by
  rw [actualCoordinateRho_apply_kernelCoordinate]
  exact div_pos (actualKernelF2_pos u)
    (pow_pos (actualKernelCurvature_pos u) 3)

theorem actualCoordinateKappa_gt_one (u : ℝ) :
    1 < actualCoordinateKappa (kernelCoordinate actualKernelSlope u) := by
  rw [actualCoordinateKappa_eq_one_add_rho]
  linarith [actualCoordinateRho_pos u]

/-- PO-0022 on the complete actual coordinate range. -/
theorem actualCoordinateRhoKappa_pos_on_range :
    ∀ y ∈ Set.range (kernelCoordinate actualKernelSlope),
      0 < actualCoordinateRho y ∧
      actualCoordinateKappa y = 1 + actualCoordinateRho y ∧
      1 < actualCoordinateKappa y := by
  rintro y ⟨u, rfl⟩
  exact ⟨actualCoordinateRho_pos u,
    actualCoordinateKappa_eq_one_add_rho _, actualCoordinateKappa_gt_one u⟩

/-! ## PO-0029: pointwise primitive-rate positivity -/

/-- Pointwise legal form of the determinant-to-rate sign transfer. Unlike the
older global wrapper, it requires positivity only at the point being used. -/
theorem primitiveRate_pos_at_of_determinantC4_pos
    {Q Q1 Q2 Q3 Q4 : ℝ → ℝ} {y : ℝ}
    (hQ : 0 < Q y) (hKappa : 0 < curvature Q2 y)
    (hdet : 0 < determinantC4Function Q Q1 Q2 Q3 Q4 y) :
    0 < primitiveRate Q Q1 Q2 (curvature Q2)
      (fun x => -Q3 x) (fun x => -Q4 x) y := by
  have heq := coordinateDeterminantC4_eq_derivedC4
    (Q y) (Q1 y) (Q2 y) (Q3 y) (Q4 y) hKappa.ne'
  unfold determinantC4Function at hdet
  rw [heq] at hdet
  have hfactor : 0 < Q y ^ 6 * curvature Q2 y ^ 2 :=
    mul_pos (pow_pos hQ 6) (pow_pos hKappa 2)
  change 0 < (Q y ^ 6 * curvature Q2 y ^ 2) *
    primitiveRate Q Q1 Q2 (curvature Q2)
      (fun x => -Q3 x) (fun x => -Q4 x) y at hdet
  exact pos_of_mul_pos_right hdet hfactor.le

/-- The paper's primitive rate `D` for the maintained coordinate jet. -/
noncomputable def actualCoordinateD (y : ℝ) : ℝ :=
  primitiveRate actualCoordinateQ actualCoordinateQ1 actualCoordinateQ2
    actualCoordinateKappa (fun x => -actualCoordinateQ3 x)
      (fun x => -actualCoordinateQ4 x) y

/-- PO-0029 on the complete actual coordinate range. No property of the
arbitrary inverse extension is used off that range. -/
theorem actualCoordinateD_pos_on_range :
    ∀ y ∈ Set.range (kernelCoordinate actualKernelSlope),
      0 < actualCoordinateD y := by
  intro y hy
  have hsigns := coordinateSigns_on_range
    hasDerivAt_actualKernelSlope actualKernelCurvature_pos actualKernelF2_pos
      actualKernelC4_pos y hy
  change 0 < primitiveRate actualCoordinateQ actualCoordinateQ1
    actualCoordinateQ2 (curvature actualCoordinateQ2)
      (fun x => -actualCoordinateQ3 x) (fun x => -actualCoordinateQ4 x) y
  exact primitiveRate_pos_at_of_determinantC4_pos
    hsigns.1 hsigns.2.1 hsigns.2.2

end PF4.PaperObjectClosure
