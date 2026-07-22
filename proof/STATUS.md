# Proof obligation status

Target: `PF4-CORE-v1`

Active formal completion: **38/41 obligations**. The original ledger contains
46 records; PO-0032 through PO-0036 are now `DEPRECATED_OPTIONAL` because the
deterministic closed-gap route bypasses the crossing chain.

Current strongest target result: T3, exact global PF order four for the actual
Riemann kernel, is kernel-checked in Lean from the maintained T1 strict PF4
theorem and T2 exact negative order-five minor. The frozen `PF4-CORE-v1`
target is complete. Lean 4.32.0 and mathlib
4.32.0 are pinned. The analytic
foundation now constructs the literal real integer theta sum, proves its
summability by an elementary exponential comparison, splits off its positive
modes, constructs the positive-mode kernel jet through order six on `t ≥ 0`,
and proves the `H''-H/4` kernel equals that series there. The integrated
mathlib Gaussian/Poisson theorem proves the exact theta transformation; a
Jacobi-theta realization proves global real analyticity, and parity gives the
exact reflected representation `Φ(t)=thetaSeries |t|`. The real kernel
definitions remain unchanged (`R185`--`R188`, `R191`, `CERT21`). The global
jet and sign closure is recorded by `R195`--`R202` and `CERT22`; exact T1 is
recorded by `R203` and `CERT23`, exact T2/T3 by `R204`--`R205` and `CERT24`,
the literal transport exports by `CERT25`, the literal paper-object closures
by `CERT26`, simultaneous coordinate translation by `CERT27`, the literal
S04 weighted-mean route by `CERT28`, and the fixed-order paper
quotient/Wronskian equations and endpoint orientation by `R206`--`R208` and
`CERT29`. Target
definitions, signed PF5 indices, constructive crossing algebra, and the actual
left-density identity/sign bridge are kernel-checked. The actual restricted-
density measures, mass-one interfaces, strict right mass, all three interior
CDF-gap regions, the weighted transport theorem, and the final sign bridge are
now also kernel-checked. PO-0038 and PO-0039
are complete atomic obligations promoted to `FORMALLY_PROVED`: the paper
primitive, elementary
primitives, actual Bochner expectations, retained boundary terms, cleared
endpoint cancellation, CDF formulas, and final integration identity are
checked. PO-0037 is now proved directly on the closed coordinate gap without
measures or CDF complement identities, and PO-0040 derives continuity of its
displayed weighted integrand and strict positivity of the coordinate transport
numerator. The literal actual-kernel numerator and negative coordinate-`Psi`
derivative are exported by
`PF4.GlobalStrictPF4.globalRiemannKernel_coordinateNumerator_pos` and
`globalRiemannKernel_coordinatePartialXiPsi_neg`, closing PO-0040 and PO-0041.
PO-0023, PO-0024, PO-0030, and PO-0031 are complete atomic
obligations: the coordinate normalizers, endpoint derivative, strict
positivity, integrability, and concrete normalized laws are constructed in
Lean and connected to PO-0038. PO-0026 through PO-0028 are complete identity
obligations: `Psi` is differentiated as an actual function, the exact sign
orientation is checked, and the primary determinant `C₄` is identified with
the curvature numerator. `PF4.PaperObjectClosure` now also closes the literal
global logarithmic objects, ordered `A,M` denominators, actual-range `ρ,κ`
signs, and actual-range primitive rate `D`. PO-0040 and PO-0041 have no
actual-kernel instance gap.

The fixed order-four generic quotient engine is also maintained and
kernel-checked: the paper's exact `W3` and `W4` quotient factorizations,
reversed translation-endpoint orientation, exact discrete factor extraction,
the `4→3` triple-integral identity, the `3→2` double-integral identity,
terminal strictness, and transfer
to the original unnormalized minor close PO-0017 and remain formal fragments
of PO-0018 and PO-0020. The actual translation quotient object layer,
derivative ladder,
factor identities, and minor identity are maintained. The first quotient sign
is derived from positive exact kernel curvature, and the second quotient sign
from the exact S05 lower-order `Lambda`. The terminal logarithmic-rate identity
is now checked, its endpoint object is proved equal to the maintained
coordinate `Psi`, and determinant positivity supplies strict `Psi` decrease
and hence the terminal sign with the correct ordered-point orientation. The
actual global Riemann-kernel jet through order six and the canonical cleared
`q`, `F₂`, and `C₄` signs are now instantiated. The resulting terminal quotient
is strictly positive for every real translation parameter and every ordered
quadruple `a<c<b<d`. `PF4.GlobalStrictPF4` derives the actual lower-`Lambda`,
first-quotient, and second-quotient signs, proves minors separately at orders
one through four, and exports the exact arbitrary-node theorem
`PF4.globalRiemannKernel_strictPFUpTo_four`.

The cleared raw-jet interface is also maintained. It reconstructs the
curvature derivative tower from seven ordinary kernel jets, proves that the
three cleared polynomials are exactly the denominators-cleared `q`, `F₂`, and
raw-Hankel `C₄` propositions, and derives the terminal quotient sign from
their strict positivity. The compact and unbounded CERT12 regions now replay
as a single universal Lean theorem. Integration corrected the outer
perturbation coefficients to include every binomial multiplicity.

## Analytic foundation

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0001 | Theta series is well-defined for `x > 0` | FORMALLY_PROVED | none; `PF4.summable_int_thetaTerms` and the literal `riemannTheta` construction close it |
| PO-0002 | Required derivative series converge locally uniformly | FORMALLY_PROVED | none; `iteratedDeriv_globalRiemannKernel_eq_thetaSeriesJet` identifies the global derivative jet through order six, including the origin and reflected half-line |
| PO-0003 | Theta transformation in the chosen normalization | FORMALLY_PROVED | none; `PF4.riemannTheta_modular` is the exact real specialization of mathlib's Gaussian Poisson theorem |
| PO-0004 | `H` is real analytic and even | FORMALLY_PROVED | none; `PF4.contDiff_riemannH` and `PF4.riemannH_even` close the global statement |
| PO-0005 | Primary `Φ` equals the displayed positive-side series | FORMALLY_PROVED | none; `PF4.globalRiemannKernel_eq_thetaSeries_abs` proves the global reflected formula without defining the kernel using `abs` |
| PO-0006 | `Φ` has all derivatives used through the PF5 witness | FORMALLY_PROVED | none; `PF4.contDiff_globalRiemannKernel` proves global smoothness to every finite order |
| PO-0007 | `Φ` is even on `ℝ` | FORMALLY_PROVED | none; `PF4.globalRiemannKernel_even` |
| PO-0008 | `Φ(t) > 0` for every real `t` | FORMALLY_PROVED | none; `PF4.GlobalKernelJetIdentification.globalRiemannKernel_pos` |
| PO-0009 | `ℓ,s,q` are globally well-defined | FORMALLY_PROVED | none; `PF4.PaperObjectClosure.actualLogSlopeCurvature_globally_wellDefined` proves the literal log and derivative identities globally |
| PO-0010 | `A,M` are well-defined on ordered arguments when used | FORMALLY_PROVED | none; `actualAM_wellDefined_on_ordered` proves `A>0`, nonvanishing, the quotient identity, and `A=∫q` for every `a<b` |

## Exact sign inputs

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0011 | `q(t) > 0` globally | FORMALLY_PROVED | none; universal canonical `normalized_clearedQ_pos` plus the exact cleared-sign transfer |
| PO-0012 | `F₂(t) > 0` globally | FORMALLY_PROVED | none; universal canonical `normalized_clearedF2_pos` plus the exact cleared-sign transfer |
| PO-0013 | `C₄(t) > 0` globally | FORMALLY_PROVED | none; universal canonical `normalized_clearedC4_pos` and `clearedC4_eq_rawHankel4_det` |

## Generic PF machinery

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0014 | Weighted-mean identities and variation bound | FORMALLY_PROVED | none; literal weighted means, compact extrema, positive variation, and the strict displayed `min(q³,F₂)/q²` lower integral are checked |
| PO-0015 | `Λ(ξ;m,r) > 0` for `ξ < m < r` | FORMALLY_PROVED | none; `PF4.GlobalStrictPF4.actual_lowerLambda_pos` instantiates the actual kernel from its global jet and `q,F₂` signs |
| PO-0016 | Strict order-three Wronskian sign | FORMALLY_PROVED | none; `actual_firstQuotD_pos` and `actual_secondQuotD_pos` close the actual-kernel quotient signs |
| PO-0017 | Quotient/Wronskian algebra through order four | FORMALLY_PROVED | none; exact `W3` and three-stage `W4` factorizations, discrete cascade, and reversed endpoint orientation are checked at the paper's fixed orders |
| PO-0018 | Iterated quotient-integral determinant identity | FORMAL_FRAGMENT | arbitrary finite `k`; exact sizes two through four and strict boxes are checked |
| PO-0019 | One- and two-sided confluent limits | CONVENTIONALLY_PROVED | divided differences and limits |
| PO-0020 | PF4 iff weak `∂ξΨ≤0`; strict sign implies strict PF4 | FORMAL_FRAGMENT | strict direction is connected through the maintained coordinate `Psi`; actual-kernel instances and the confluent converse remain |

## Curvature and transport algebra

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0021 | `y=-s` is strictly increasing on its image | FORMALLY_PROVED | none; inverse-on-range calculus and derivative transport checked |
| PO-0022 | `ρ=F₂/q³>0`, `κ=1+ρ>1` | FORMALLY_PROVED | none; `actualCoordinateRhoKappa_pos_on_range` covers the complete actual coordinate range without a surjectivity claim |
| PO-0023 | Triangular integral formula for `Λ` | FORMALLY_PROVED | none; explicit primitives and endpoint algebra checked |
| PO-0024 | Triangular formula and positivity for `δ` | FORMALLY_PROVED | none; endpoint derivative, integral identity, and midpoint strictness checked |
| PO-0025 | Simultaneous translation operator in coordinates | FORMALLY_PROVED | none; literal actual-endpoint curves differentiate to the coordinate vector field, with exact `TΛ`, `Tδ`, and `Ψ` connections |
| PO-0026 | Definition/expansion of `N` from differentiating `Ψ` | FORMALLY_PROVED | none; endpoint translation objects and actual derivative checked |
| PO-0027 | `∂ξΨ = -Q(p)N/Λ²` | FORMALLY_PROVED | none; coordinate speed and exact negative orientation checked |
| PO-0028 | `C₄ = Q⁶κ²D` | FORMALLY_PROVED | none; primary Hankel determinant, cumulant expansion, and curvature factorization checked |
| PO-0029 | `D > 0` on the actual coordinate domain | FORMALLY_PROVED | none; `actualCoordinateD_pos_on_range` uses the pointwise determinant factorization at every actual coordinate point |

## Non-vacuous normalization and crossing layer

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0030 | `μ` is a probability measure | FORMALLY_PROVED | none; derived `δ`, continuity, integrability, and mass checked |
| PO-0031 | `ν` is a probability measure | FORMALLY_PROVED | none; derived `Λ`, piecewise integrability, and mass checked |
| PO-0032 | `ν((z,w]) > 0` | DEPRECATED_OPTIONAL | retained as measure-theoretic interpretation; the deterministic route does not use it |
| PO-0033 | Actual density ratio equals displayed rational function | DEPRECATED_OPTIONAL | retained as an independent density identity; not an active blocker |
| PO-0034 | Ratio is strictly decreasing with endpoint limits `∞,0` | DEPRECATED_OPTIONAL | crossing analysis is no longer on the required proof path |
| PO-0035 | The explicit strict-convex-combination crossing exists | DEPRECATED_OPTIONAL | explicit crossing retained for interpretation only |
| PO-0036 | Crossing is unique and `Δ'` has the claimed sign pattern | DEPRECATED_OPTIONAL | no longer required for strict gap or transport positivity |
| PO-0037 | `Δ>0` on `(p,w)` with endpoint zeros | FORMALLY_PROVED | none; direct closed-gap positivity, endpoint zeros, and branch matching checked without measures |

## Assembly

| ID | Claim | Present status | Formal blocker |
|---|---|---|---|
| PO-0038 | `K=Eν[A₀]-Eμ[A₀]` | FORMALLY_PROVED | none; independent primitive, expectations, and endpoint object identity checked |
| PO-0039 | Expectation difference equals `∫ΔD` | FORMALLY_PROVED | none; actual measures, expectations, CDFs, and boundary terms checked |
| PO-0040 | Coordinate transport numerator `N` is strictly positive | FORMALLY_PROVED | none; `PF4.GlobalStrictPF4.globalRiemannKernel_coordinateNumerator_pos` covers every `x<m<r` |
| PO-0041 | `∂ξΨ<0` globally | FORMALLY_PROVED | none; `PF4.GlobalStrictPF4.globalRiemannKernel_coordinatePartialXiPsi_neg` has only the ordered-triple hypotheses |
| PO-0042 | Strict global order-four minors | FORMALLY_PROVED | none; `PF4.GlobalStrictPF4.translationMinor_four_pos` and the exported T1 theorem cover arbitrary strictly ordered nodes |
| PO-0043 | Strict minors of orders one through three | FORMALLY_PROVED | none; exact order-one, order-two, and order-three minor theorems are assembled into T1 |
| PO-0044 | CERT17 evaluator denotes T2's exact determinant | FORMALLY_PROVED | none; `translationMatrix_pf5WitnessNodes_eq_equallySpaced` and `equallySpacedMatrix_pf5Witness_eq_toeplitz5` close signed orientation and primary-kernel fidelity |
| PO-0045 | Exact rational finite determinant is negative | FORMALLY_PROVED | none; `globalRiemannKernel_orderFive_translationMinor_neg` uses exact Taylor bounds, the maintained infinite theta-tail theorem, and a rational parity-factor sign certificate |
| PO-0046 | Exact global PF order is four | FORMALLY_PROVED | none; `globalRiemannKernel_pfOrderExactly_four` converts T1 to `PFUpTo 4` and refutes `PFUpTo 5` at T2's proved-strict exact witness nodes |

## Immediate next work

1. Reconcile PO-0018's maintained fixed-size iterated quotient-integral
   identities with the paper's active order-four denominator.
2. Keep deprecated crossing refinements and optional arbitrary-order work
   separate from the completed T1–T3 classification.
3. Execute the paper backport series recorded in `backport/README.md` as
   dedicated refine rounds.
