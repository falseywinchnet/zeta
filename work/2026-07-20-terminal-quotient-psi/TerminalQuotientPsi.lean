import PF4.TranslationQuotientSigns
import PF4.CoordinateSignBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Terminal translation quotient and the maintained coordinate Psi

Advancement candidate only. Every coordinate realization and remaining
strict-decrease input is exposed literally.
-/

namespace PF4.Advancement.TerminalQuotientPsi

open PF4.TranslationQuotientTower PF4.TranslationQuotientSigns
open PF4.Curvature PF4.TransportObject PF4.CoordinateSignBridge

/-- The curvature coordinate used by the paper, before constructing an
inverse-coordinate function: `y=-S`. -/
noncomputable def kernelCoordinate (S : ℝ → ℝ) (x : ℝ) : ℝ :=
  -S x

/-- The second divided mean needed to differentiate a curvature mean under
simultaneous translation. -/
noncomputable def secondMean
    (S q1 : ℝ → ℝ) (x r : ℝ) : ℝ :=
  (q1 r - q1 x) / slopeChord S x r

/-- Closed simultaneous-translation derivative of the S05 lower Lambda. -/
noncomputable def lowerTLambda
    (S q q1 : ℝ → ℝ) (x m r : ℝ) : ℝ :=
  q r - q x +
    (secondMean S q1 x m - curvatureMean S q x m ^ 2) -
    (secondMean S q1 m r - curvatureMean S q m r ^ 2)

/-- The S05 terminal endpoint object before its coordinate realization. -/
noncomputable def lowerPsi
    (S q q1 : ℝ → ℝ) (x m r : ℝ) : ℝ :=
  lowerLambda S q x m r +
    lowerTLambda S q q1 x m r / lowerLambda S q x m r

/-- The exact positive factor multiplying the second quotient in the checked
second-level derivative identity. -/
noncomputable def levelThreeFactor
    (S q : ℝ → ℝ) (x m r : ℝ) : ℝ :=
  slopeChord S x m / slopeChord S x r * lowerLambda S q x m r

/-- Weighted-mean splitting over `x<m<r`, stated algebraically. -/
theorem curvatureMean_split
    (S q : ℝ → ℝ) (x m r : ℝ)
    (hxm : slopeChord S x m ≠ 0)
    (hmr : slopeChord S m r ≠ 0)
    (hxr : slopeChord S x r ≠ 0) :
    curvatureMean S q x r =
      (slopeChord S x m * curvatureMean S q x m +
        slopeChord S m r * curvatureMean S q m r) /
        slopeChord S x r := by
  unfold curvatureMean slopeChord at *
  field_simp [hxm, hmr, hxr]
  ring

/-- The non-Psi terms in the logarithmic derivative collapse to one common
chord independent of the moving left endpoint. -/
theorem levelThree_rate_collapse
    (S q : ℝ → ℝ) (x m r : ℝ)
    (hxm : slopeChord S x m ≠ 0)
    (hmr : slopeChord S m r ≠ 0)
    (hxr : slopeChord S x r ≠ 0) :
    levelThreeFactor S q x m r +
        curvatureMean S q x m - curvatureMean S q x r =
      lowerLambda S q x m r - slopeChord S m r := by
  rw [curvatureMean_split S q x m r hxm hmr hxr]
  unfold levelThreeFactor lowerLambda
  field_simp [hxm, hmr, hxr]
  unfold slopeChord
  ring

/-- The paper lower Lambda is literally the maintained coordinate Lambda
under `y=-S` and `Q(y(x))=q(x)`. -/
theorem lowerLambda_eq_coordinateLambda
    {S q Q : ℝ → ℝ} (hQ : ∀ u, Q (kernelCoordinate S u) = q u)
    (x m r : ℝ) :
    lowerLambda S q x m r =
      coordinateLambda Q (kernelCoordinate S x)
        (kernelCoordinate S m) (kernelCoordinate S r) := by
  unfold lowerLambda curvatureMean slopeChord coordinateLambda chordSlope
    kernelCoordinate
  rw [show Q (-S x) = q x by simpa [kernelCoordinate] using hQ x,
    show Q (-S m) = q m by simpa [kernelCoordinate] using hQ m,
    show Q (-S r) = q r by simpa [kernelCoordinate] using hQ r]
  ring

/-- The closed simultaneous derivative of lower Lambda is literally the
maintained coordinate `T Lambda`. The relation for `Q1` is the chain-rule
identity `Q'(y(u))=q'(u)/q(u)`. -/
theorem lowerTLambda_eq_coordinateTLambda
    {S q q1 Q Q1 : ℝ → ℝ}
    (hq : ∀ u, q u ≠ 0)
    (hQ : ∀ u, Q (kernelCoordinate S u) = q u)
    (hQ1 : ∀ u, Q1 (kernelCoordinate S u) = q1 u / q u)
    (x m r : ℝ) :
    lowerTLambda S q q1 x m r =
      coordinateTLambda Q Q1 (kernelCoordinate S x)
        (kernelCoordinate S m) (kernelCoordinate S r) := by
  unfold lowerTLambda secondMean curvatureMean slopeChord coordinateTLambda
    chordMoment kernelCoordinate
  rw [show Q (-S x) = q x by simpa [kernelCoordinate] using hQ x,
    show Q (-S m) = q m by simpa [kernelCoordinate] using hQ m,
    show Q (-S r) = q r by simpa [kernelCoordinate] using hQ r,
    show Q1 (-S x) = q1 x / q x by simpa [kernelCoordinate] using hQ1 x,
    show Q1 (-S m) = q1 m / q m by simpa [kernelCoordinate] using hQ1 m,
    show Q1 (-S r) = q1 r / q r by simpa [kernelCoordinate] using hQ1 r]
  have hx : q x * (q1 x / q x) = q1 x := by field_simp [hq x]
  have hm : q m * (q1 m / q m) = q1 m := by field_simp [hq m]
  have hr : q r * (q1 r / q r) = q1 r := by field_simp [hq r]
  rw [hx, hm, hr]
  ring_nf
  simp only [inv_pow]
  ring

/-- The endpoint object used by the quotient calculation is the already
maintained coordinate Psi, not a detached lookalike. -/
theorem lowerPsi_eq_coordinatePsi
    {S q q1 Q Q1 : ℝ → ℝ}
    (hq : ∀ u, q u ≠ 0)
    (hQ : ∀ u, Q (kernelCoordinate S u) = q u)
    (hQ1 : ∀ u, Q1 (kernelCoordinate S u) = q1 u / q u)
    (x m r : ℝ) :
    lowerPsi S q q1 x m r =
      coordinatePsi Q Q1 (kernelCoordinate S x)
        (kernelCoordinate S m) (kernelCoordinate S r) := by
  unfold lowerPsi coordinatePsi
  rw [lowerLambda_eq_coordinateLambda hQ,
    lowerTLambda_eq_coordinateTLambda hq hQ hQ1]

/-! ## Simultaneous-translation calculus -/

theorem hasDerivAt_slopeChord_translate
    {S q : ℝ → ℝ} (hS : ∀ u, HasDerivAt S (-q u) u)
    (a b t : ℝ) :
    HasDerivAt (fun s => slopeChord S (s - b) (s - a))
      (q (t - a) - q (t - b)) t := by
  have hb := (hS (t - b)).comp t ((hasDerivAt_id t).sub_const b)
  have ha := (hS (t - a)).comp t ((hasDerivAt_id t).sub_const a)
  exact (hb.sub ha).congr_deriv (by ring)

theorem hasDerivAt_curvatureMean_translate
    {S q q1 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (a b t : ℝ)
    (hA : slopeChord S (t - b) (t - a) ≠ 0) :
    HasDerivAt (fun s => curvatureMean S q (s - b) (s - a))
      (secondMean S q1 (t - b) (t - a) -
        curvatureMean S q (t - b) (t - a) ^ 2) t := by
  have hqb := (hq (t - b)).comp t ((hasDerivAt_id t).sub_const b)
  have hqa := (hq (t - a)).comp t ((hasDerivAt_id t).sub_const a)
  have hnum := hqa.sub hqb
  have hden := hasDerivAt_slopeChord_translate hS a b t
  have hraw := hnum.fun_div hden hA
  apply hraw.congr_deriv
  simp only [Function.comp_apply, id_eq, Pi.sub_apply]
  unfold secondMean curvatureMean
  field_simp [hA]

theorem hasDerivAt_lowerLambda_translate
    {S q q1 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (a c b t : ℝ)
    (hAbc : slopeChord S (t - b) (t - c) ≠ 0)
    (hAca : slopeChord S (t - c) (t - a) ≠ 0) :
    HasDerivAt
      (fun s => lowerLambda S q (s - b) (s - c) (s - a))
      (lowerTLambda S q q1 (t - b) (t - c) (t - a)) t := by
  have hA := hasDerivAt_slopeChord_translate hS a b t
  have hMbc := hasDerivAt_curvatureMean_translate hS hq c b t hAbc
  have hMca := hasDerivAt_curvatureMean_translate hS hq a c t hAca
  exact ((hA.add hMbc).sub hMca).congr_deriv (by
    unfold lowerTLambda
    rfl)

theorem hasDerivAt_levelThreeFactor_translate
    {S q q1 : ℝ → ℝ}
    (hS : ∀ u, HasDerivAt S (-q u) u)
    (hq : ∀ u, HasDerivAt q (q1 u) u)
    (a c b t : ℝ)
    (hAbc : slopeChord S (t - b) (t - c) ≠ 0)
    (hAca : slopeChord S (t - c) (t - a) ≠ 0)
    (hAba : slopeChord S (t - b) (t - a) ≠ 0)
    (hLambda : lowerLambda S q (t - b) (t - c) (t - a) ≠ 0) :
    HasDerivAt
      (fun s => levelThreeFactor S q (s - b) (s - c) (s - a))
      (levelThreeFactor S q (t - b) (t - c) (t - a) *
        (curvatureMean S q (t - b) (t - c) -
          curvatureMean S q (t - b) (t - a) +
          lowerTLambda S q q1 (t - b) (t - c) (t - a) /
            lowerLambda S q (t - b) (t - c) (t - a))) t := by
  have hAbcD := hasDerivAt_slopeChord_translate hS c b t
  have hAbaD := hasDerivAt_slopeChord_translate hS a b t
  have hratio := hAbcD.fun_div hAbaD hAba
  have hLam := hasDerivAt_lowerLambda_translate hS hq a c b t hAbc hAca
  have hraw := hratio.mul hLam
  apply hraw.congr_deriv
  unfold levelThreeFactor curvatureMean
  field_simp [hAbc, hAba, hLambda]

/-! ## Conversion of the maintained second-level derivative -/

theorem secondQuotD_eq_secondQuot_mul_levelThreeFactor
    {Φ Φ1 Φ2 : ℝ → ℝ}
    (hΦ : ∀ u, HasDerivAt Φ (Φ1 u) u)
    (hΦ1 : ∀ u, HasDerivAt Φ1 (Φ2 u) u)
    (hΦpos : ∀ u, 0 < Φ u)
    (a c b : ℝ)
    (hfirst : ∀ t, 0 < firstQuotD Φ Φ1 a c t)
    (hAb : ∀ t,
      slopeChord (logSlope Φ Φ1) (t - b) (t - a) ≠ 0)
    (hAc : ∀ t,
      slopeChord (logSlope Φ Φ1) (t - c) (t - a) ≠ 0)
    (hAbc : ∀ t,
      slopeChord (logSlope Φ Φ1) (t - b) (t - c) ≠ 0)
    (t : ℝ) :
    secondQuotD Φ Φ1 Φ2 a c b t =
      secondQuot Φ Φ1 a c b t *
        levelThreeFactor (logSlope Φ Φ1)
          (kernelCurvature Φ Φ1 Φ2) (t - b) (t - c) (t - a) := by
  rw [secondQuotD_eq_lambdaProduct hΦ hΦ1 hΦpos a c b hfirst
    hAb hAc hAbc]
  unfold levelThreeFactor
  ring

/-- The logarithmic rate of the maintained second-level derivative is the
actual lower Psi minus one chord independent of the moving left endpoint.
The proof differentiates the checked product identity and invokes derivative
uniqueness against `hasDerivAt_secondQuotD`. -/
theorem secondQuotD2_eq_secondQuotD_mul_lowerRate
    {Φ Φ1 Φ2 Φ3 q1 : ℝ → ℝ}
    (hΦ : ∀ u, HasDerivAt Φ (Φ1 u) u)
    (hΦ1 : ∀ u, HasDerivAt Φ1 (Φ2 u) u)
    (hΦ2 : ∀ u, HasDerivAt Φ2 (Φ3 u) u)
    (hΦpos : ∀ u, 0 < Φ u)
    (hq : ∀ u, HasDerivAt (kernelCurvature Φ Φ1 Φ2) (q1 u) u)
    (a c b : ℝ)
    (hfirst : ∀ t, 0 < firstQuotD Φ Φ1 a c t)
    (hAb : ∀ t,
      slopeChord (logSlope Φ Φ1) (t - b) (t - a) ≠ 0)
    (hAc : ∀ t,
      slopeChord (logSlope Φ Φ1) (t - c) (t - a) ≠ 0)
    (hAbc : ∀ t,
      slopeChord (logSlope Φ Φ1) (t - b) (t - c) ≠ 0)
    (hLambda : ∀ t,
      lowerLambda (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2)
        (t - b) (t - c) (t - a) ≠ 0)
    (t : ℝ) :
    secondQuotD2 Φ Φ1 Φ2 Φ3 a c b t =
      secondQuotD Φ Φ1 Φ2 a c b t *
        (lowerPsi (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2) q1
            (t - b) (t - c) (t - a) -
          slopeChord (logSlope Φ Φ1) (t - c) (t - a)) := by
  let S := logSlope Φ Φ1
  let q := kernelCurvature Φ Φ1 Φ2
  let x := t - b
  let m := t - c
  let r := t - a
  have hS : ∀ u, HasDerivAt S (-q u) u := by
    intro u
    simpa [S, q] using hasDerivAt_logSlope hΦ hΦ1 hΦpos u
  have hfactor := hasDerivAt_levelThreeFactor_translate hS hq a c b t
    (hAbc t) (hAc t) (hAb t) (hLambda t)
  have hsecond := hasDerivAt_secondQuot hΦ hΦ1 hΦpos hfirst b t
  have hproduct := hsecond.mul hfactor
  have hpoint : secondQuotD Φ Φ1 Φ2 a c b t =
      secondQuot Φ Φ1 a c b t * levelThreeFactor S q x m r := by
    simpa [S, q, x, m, r] using
      secondQuotD_eq_secondQuot_mul_levelThreeFactor hΦ hΦ1 hΦpos
        a c b hfirst hAb hAc hAbc t
  have hrate : HasDerivAt
      (fun s => secondQuot Φ Φ1 a c b s *
        levelThreeFactor S q (s - b) (s - c) (s - a))
      (secondQuotD Φ Φ1 Φ2 a c b t *
        (lowerPsi S q q1 x m r - slopeChord S m r)) t := by
    apply hproduct.congr_deriv
    calc
      secondQuotD Φ Φ1 Φ2 a c b t * levelThreeFactor S q x m r +
          secondQuot Φ Φ1 a c b t *
            (levelThreeFactor S q x m r *
              (curvatureMean S q x m - curvatureMean S q x r +
                lowerTLambda S q q1 x m r / lowerLambda S q x m r)) =
        secondQuotD Φ Φ1 Φ2 a c b t *
          (levelThreeFactor S q x m r +
            curvatureMean S q x m - curvatureMean S q x r +
            lowerTLambda S q q1 x m r / lowerLambda S q x m r) := by
              rw [hpoint]
              ring
      _ = secondQuotD Φ Φ1 Φ2 a c b t *
          (lowerLambda S q x m r - slopeChord S m r +
            lowerTLambda S q q1 x m r / lowerLambda S q x m r) := by
              rw [levelThree_rate_collapse S q x m r
                (hAbc t) (hAc t) (hAb t)]
      _ = secondQuotD Φ Φ1 Φ2 a c b t *
          (lowerPsi S q q1 x m r - slopeChord S m r) := by
              unfold lowerPsi
              ring
  have hfactored : HasDerivAt (secondQuotD Φ Φ1 Φ2 a c b)
      (secondQuotD Φ Φ1 Φ2 a c b t *
        (lowerPsi S q q1 x m r - slopeChord S m r)) t := by
    apply hrate.congr_of_eventuallyEq
    filter_upwards [] with s
    exact secondQuotD_eq_secondQuot_mul_levelThreeFactor hΦ hΦ1 hΦpos
      a c b hfirst hAb hAc hAbc s
  have hmaintained := hasDerivAt_secondQuotD hΦ hΦ1 hΦ2 hΦpos hfirst b t
  have hunique := hmaintained.unique hfactored
  simpa [S, q, x, m, r] using hunique

/-! ## Terminal quotient identity and strict sign -/

theorem terminalQuotD_eq_terminalQuot_mul_lowerPsi_sub
    {Φ Φ1 Φ2 Φ3 q1 : ℝ → ℝ}
    (hΦ : ∀ u, HasDerivAt Φ (Φ1 u) u)
    (hΦ1 : ∀ u, HasDerivAt Φ1 (Φ2 u) u)
    (hΦ2 : ∀ u, HasDerivAt Φ2 (Φ3 u) u)
    (hΦpos : ∀ u, 0 < Φ u)
    (hq : ∀ u, HasDerivAt (kernelCurvature Φ Φ1 Φ2) (q1 u) u)
    (a c b d : ℝ)
    (hfirst : ∀ t, 0 < firstQuotD Φ Φ1 a c t)
    (hAb : ∀ t, slopeChord (logSlope Φ Φ1) (t - b) (t - a) ≠ 0)
    (hAd : ∀ t, slopeChord (logSlope Φ Φ1) (t - d) (t - a) ≠ 0)
    (hAc : ∀ t, slopeChord (logSlope Φ Φ1) (t - c) (t - a) ≠ 0)
    (hAbc : ∀ t, slopeChord (logSlope Φ Φ1) (t - b) (t - c) ≠ 0)
    (hAdc : ∀ t, slopeChord (logSlope Φ Φ1) (t - d) (t - c) ≠ 0)
    (hLambdaB : ∀ t, lowerLambda (logSlope Φ Φ1)
      (kernelCurvature Φ Φ1 Φ2) (t - b) (t - c) (t - a) ≠ 0)
    (hLambdaD : ∀ t, lowerLambda (logSlope Φ Φ1)
      (kernelCurvature Φ Φ1 Φ2) (t - d) (t - c) (t - a) ≠ 0)
    (hsecondB : ∀ t, 0 < secondQuotD Φ Φ1 Φ2 a c b t)
    (t : ℝ) :
    terminalQuotD Φ Φ1 Φ2 Φ3 a c b d t =
      terminalQuot Φ Φ1 Φ2 a c b d t *
        (lowerPsi (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2) q1
            (t - d) (t - c) (t - a) -
          lowerPsi (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2) q1
            (t - b) (t - c) (t - a)) := by
  have hd := secondQuotD2_eq_secondQuotD_mul_lowerRate hΦ hΦ1 hΦ2
    hΦpos hq a c d hfirst hAd hAc hAdc hLambdaD t
  have hb := secondQuotD2_eq_secondQuotD_mul_lowerRate hΦ hΦ1 hΦ2
    hΦpos hq a c b hfirst hAb hAc hAbc hLambdaB t
  unfold terminalQuotD terminalQuot
  rw [hd, hb]
  field_simp [(hsecondB t).ne']
  ring

/-- Exact terminal quotient identity with the already maintained coordinate
Psi under the explicit curvature-coordinate realization. -/
theorem terminalQuotD_eq_terminalQuot_mul_coordinatePsi_sub
    {Φ Φ1 Φ2 Φ3 q1 Q Q1 : ℝ → ℝ}
    (hΦ : ∀ u, HasDerivAt Φ (Φ1 u) u)
    (hΦ1 : ∀ u, HasDerivAt Φ1 (Φ2 u) u)
    (hΦ2 : ∀ u, HasDerivAt Φ2 (Φ3 u) u)
    (hΦpos : ∀ u, 0 < Φ u)
    (hqpos : ∀ u, 0 < kernelCurvature Φ Φ1 Φ2 u)
    (hq : ∀ u, HasDerivAt (kernelCurvature Φ Φ1 Φ2) (q1 u) u)
    (hQ : ∀ u, Q (kernelCoordinate (logSlope Φ Φ1) u) =
      kernelCurvature Φ Φ1 Φ2 u)
    (hQ1 : ∀ u, Q1 (kernelCoordinate (logSlope Φ Φ1) u) =
      q1 u / kernelCurvature Φ Φ1 Φ2 u)
    (a c b d : ℝ)
    (hfirst : ∀ t, 0 < firstQuotD Φ Φ1 a c t)
    (hAb : ∀ t, slopeChord (logSlope Φ Φ1) (t - b) (t - a) ≠ 0)
    (hAd : ∀ t, slopeChord (logSlope Φ Φ1) (t - d) (t - a) ≠ 0)
    (hAc : ∀ t, slopeChord (logSlope Φ Φ1) (t - c) (t - a) ≠ 0)
    (hAbc : ∀ t, slopeChord (logSlope Φ Φ1) (t - b) (t - c) ≠ 0)
    (hAdc : ∀ t, slopeChord (logSlope Φ Φ1) (t - d) (t - c) ≠ 0)
    (hLambdaB : ∀ t, lowerLambda (logSlope Φ Φ1)
      (kernelCurvature Φ Φ1 Φ2) (t - b) (t - c) (t - a) ≠ 0)
    (hLambdaD : ∀ t, lowerLambda (logSlope Φ Φ1)
      (kernelCurvature Φ Φ1 Φ2) (t - d) (t - c) (t - a) ≠ 0)
    (hsecondB : ∀ t, 0 < secondQuotD Φ Φ1 Φ2 a c b t)
    (t : ℝ) :
    terminalQuotD Φ Φ1 Φ2 Φ3 a c b d t =
      terminalQuot Φ Φ1 Φ2 a c b d t *
        (coordinatePsi Q Q1
            (kernelCoordinate (logSlope Φ Φ1) (t - d))
            (kernelCoordinate (logSlope Φ Φ1) (t - c))
            (kernelCoordinate (logSlope Φ Φ1) (t - a)) -
          coordinatePsi Q Q1
            (kernelCoordinate (logSlope Φ Φ1) (t - b))
            (kernelCoordinate (logSlope Φ Φ1) (t - c))
            (kernelCoordinate (logSlope Φ Φ1) (t - a))) := by
  rw [terminalQuotD_eq_terminalQuot_mul_lowerPsi_sub hΦ hΦ1 hΦ2 hΦpos
    hq a c b d hfirst hAb hAd hAc hAbc hAdc hLambdaB hLambdaD hsecondB]
  rw [lowerPsi_eq_coordinatePsi (fun u => (hqpos u).ne') hQ hQ1,
    lowerPsi_eq_coordinatePsi (fun u => (hqpos u).ne') hQ hQ1]

theorem kernelCoordinate_strictMono_of_strictAnti
    {S : ℝ → ℝ} (hS : StrictAnti S) : StrictMono (kernelCoordinate S) := by
  intro x y hxy
  unfold kernelCoordinate
  linarith [hS hxy]

/-- Strongest honest wrapper in this round. The analytic inputs are exactly
positive kernel curvature, positive lower Lambda, its derivative/coordinate
realization, and strict decrease of the maintained coordinate Psi on ordered
triples. The target terminal sign is not a premise. -/
theorem terminalQuotD_pos_of_coordinatePsi_decrease
    {Φ Φ1 Φ2 Φ3 q1 Q Q1 : ℝ → ℝ}
    (hΦ : ∀ u, HasDerivAt Φ (Φ1 u) u)
    (hΦ1 : ∀ u, HasDerivAt Φ1 (Φ2 u) u)
    (hΦ2 : ∀ u, HasDerivAt Φ2 (Φ3 u) u)
    (hΦpos : ∀ u, 0 < Φ u)
    (hqpos : ∀ u, 0 < kernelCurvature Φ Φ1 Φ2 u)
    (hq : ∀ u, HasDerivAt (kernelCurvature Φ Φ1 Φ2) (q1 u) u)
    (hLambda : ∀ x m r, x < m → m < r →
      0 < lowerLambda (logSlope Φ Φ1) (kernelCurvature Φ Φ1 Φ2) x m r)
    (hQ : ∀ u, Q (kernelCoordinate (logSlope Φ Φ1) u) =
      kernelCurvature Φ Φ1 Φ2 u)
    (hQ1 : ∀ u, Q1 (kernelCoordinate (logSlope Φ Φ1) u) =
      q1 u / kernelCurvature Φ Φ1 Φ2 u)
    (hPsiDecrease : ∀ p₁ p₂ z w, p₁ < p₂ → p₂ < z → z < w →
      coordinatePsi Q Q1 p₂ z w < coordinatePsi Q Q1 p₁ z w)
    {a c b d : ℝ} (hac : a < c) (hcb : c < b) (hbd : b < d) :
    ∀ t, 0 < terminalQuotD Φ Φ1 Φ2 Φ3 a c b d t := by
  have hSanti := logSlope_strictAnti_of_kernelCurvature_pos
    hΦ hΦ1 hΦpos hqpos
  have hYmono := kernelCoordinate_strictMono_of_strictAnti hSanti
  have hfirst := firstQuotD_pos_of_kernelCurvature_pos
    hΦ hΦ1 hΦpos hqpos hac
  have hsecondB := secondQuotD_pos_of_lowerLambda_pos
    hΦ hΦ1 hΦpos hqpos hLambda hac hcb
  have hsecondD := secondQuotD_pos_of_lowerLambda_pos
    hΦ hΦ1 hΦpos hqpos hLambda hac (hcb.trans hbd)
  have hchord : ∀ {u v : ℝ}, u < v →
      slopeChord (logSlope Φ Φ1) u v ≠ 0 := by
    intro u v huv
    exact (slopeChord_pos_of_lt hSanti huv).ne'
  intro t
  have hAb : ∀ s, slopeChord (logSlope Φ Φ1) (s - b) (s - a) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAd : ∀ s, slopeChord (logSlope Φ Φ1) (s - d) (s - a) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAc : ∀ s, slopeChord (logSlope Φ Φ1) (s - c) (s - a) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAbc : ∀ s, slopeChord (logSlope Φ Φ1) (s - b) (s - c) ≠ 0 :=
    fun s => hchord (by linarith)
  have hAdc : ∀ s, slopeChord (logSlope Φ Φ1) (s - d) (s - c) ≠ 0 :=
    fun s => hchord (by linarith)
  have hLambdaB : ∀ s, lowerLambda (logSlope Φ Φ1)
      (kernelCurvature Φ Φ1 Φ2) (s - b) (s - c) (s - a) ≠ 0 :=
    fun s => (hLambda _ _ _ (by linarith) (by linarith)).ne'
  have hLambdaD : ∀ s, lowerLambda (logSlope Φ Φ1)
      (kernelCurvature Φ Φ1 Φ2) (s - d) (s - c) (s - a) ≠ 0 :=
    fun s => (hLambda _ _ _ (by linarith) (by linarith)).ne'
  rw [terminalQuotD_eq_terminalQuot_mul_coordinatePsi_sub hΦ hΦ1 hΦ2
    hΦpos hqpos hq hQ hQ1 a c b d hfirst hAb hAd hAc hAbc hAdc
    hLambdaB hLambdaD hsecondB]
  have hpdb : t - d < t - b := by linarith
  have hpbc : t - b < t - c := by linarith
  have hpca : t - c < t - a := by linarith
  exact mul_pos (div_pos (hsecondD t) (hsecondB t))
    (sub_pos.mpr (hPsiDecrease _ _ _ _ (hYmono hpdb)
      (hYmono hpbc) (hYmono hpca)))

end PF4.Advancement.TerminalQuotientPsi

#print axioms PF4.Advancement.TerminalQuotientPsi.lowerPsi_eq_coordinatePsi
#print axioms PF4.Advancement.TerminalQuotientPsi.terminalQuotD_eq_terminalQuot_mul_coordinatePsi_sub
#print axioms PF4.Advancement.TerminalQuotientPsi.terminalQuotD_pos_of_coordinatePsi_decrease
