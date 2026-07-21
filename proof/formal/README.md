# Lean 4 formalization

The first project is active and pinned:

- Lean `v4.32.0`, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
- Lake `5.0.0-src+8c9756b`;
- mathlib tag `v4.32.0`, resolved commit
  `81a5d257c8e410db227a6665ed08f64fea08e997`.

Build with `lake build` in this directory. Run
`lake env lean PF4/Audit.lean` to print the axioms of the first exported
infrastructure and crossing theorems.

## Intended modules

```text
PF4/Definitions.lean
PF4/Theta.lean
PF4/Kernel.lean
PF4/OrderedNodes.lean
PF4/DeterminantIntegral.lean
PF4/QuotientWronskian.lean
PF4/CertifiedSigns.lean
PF4/Measures.lean
PF4/Curvature.lean
PF4/Cumulative.lean
PF4/Crossing.lean
PF4/CDF.lean
PF4/Expectation.lean
PF4/TransportObject.lean
PF4/Transport.lean
PF4/CoordinateSignBridge.lean
PF4/CentralIdentity.lean
PF4/C4Invariant.lean
PF4/FinalAssembly.lean
PF4/Main.lean
PF4/PF5Witness.lean
PF4/ExactOrder.lean
PF4/TranslationQuotientTower.lean
PF4/TranslationQuotientSigns.lean
PF4/TranslationQuotientAssembly.lean
```

Implemented modules:

- `PF4.Definitions`: translation matrices/minors, PF order, strict PF order,
  and signed equally spaced matrices;
- `PF4.Crossing`: explicit crossing-point algebra and exact ratio sign regions;
- `PF4.Densities`: positivity and object-identity bridge for the actual left
  densities, including their unique crossing and strict sign pattern.
- `PF4.Normalization`: exact interval-mass cancellation for the triangular
  `μ` and two-piece `ν` densities.
- `PF4.Measures`: concrete restricted-density measures, mass-one interfaces,
  probability instances, support lemmas, and strict right-tail mass from a
  positive integral on a nonempty interval;
- `PF4.Curvature`: the coordinate secant, `Λ` and derivative-defined `δ`,
  explicit triangular antiderivatives, strict normalizer positivity, density
  integrability, and the resulting concrete probability measures;
- `PF4.Cumulative`: endpoint primitives, the two closed cumulative weights,
  the piecewise coordinate gap, exact normalized-integral identities, direct
  strict interior positivity, and continuity from exact branch matching;
- `PF4.CDF`: concrete measure CDFs, their identification with mathlib's
  probability CDF, thin equality bridges to `PF4.Cumulative`, and
  kernel-checked strict gap proofs before the crossing, from the crossing
  through `z`, and on the right interval;
- `PF4.Expectation`: actual Bochner expectations for the concrete measures,
  compact-support integration by parts with explicit boundary terms, and the
  exact expectation-difference/CDF-gap identity;
- `PF4.TransportObject`: the paper primitive `A₀`, its two elementary
  primitives, the independent endpoint transport object, and the exact
  object-level equality with the concrete Bochner expectation difference,
  including the specialization to the coordinate-derived normalizers;
- `PF4.Transport`: both the measure/CDF and deterministic closed-coordinate
  routes to the positive curvature-weighted numerator, plus the exact final
  negative-sign bridge.
- `PF4.CoordinateSignBridge`: independent endpoint translation objects,
  actual differentiation of `Psi`, and the exact PO-0026/0027 orientation;
- `PF4.CentralIdentity`: exact expectation/CDF/closed-coordinate transport
  composition and the primitive-derived curvature weight;
- `PF4.C4Invariant`: primary central-moment Hankel determinant, its thirteen-
  term cumulant expansion, coordinate recurrence, and curvature factorization;
- `PF4.FinalAssembly`: determinant positivity through the central transport
  identity to strict negativity of the actual coordinate derivative.
- `PF4.QuotientAlgebra`: fixed-size determinant normalization, forward-
  difference orientation, and terminal discrete quotient factorization;
- `PF4.QuotientIntegral`: exact fixed-order adjacent-box integral identities
  and strict quotient-sign transfer to an unnormalized order-four minor.
- `PF4.TranslationQuotientTower`: the actual translate quotients, their exact
  derivative ladder and factor identities, independent of the integral
  determinant engine.
- `PF4.TranslationQuotientSigns`: the exact logarithmic-slope and curvature
  objects, derivation of the first quotient sign from positive curvature, and
  factorization of the second quotient derivative through the S05
  lower-order `Lambda`, with its analytic positivity retained as a literal
  premise.
- `PF4.TranslationQuotientAssembly`: the isolated connection to the integral
  determinant engine: object identity with `translationMinor` and the
  conditional transfer theorem from three explicit quotient-level sign
  premises. The theorem namespace and public names remain unchanged.

No stub theorem with `sorry` is used. The proof-facing cumulative object is
`PF4.Cumulative.coordinateGap`; the measure-backed CDF is retained as a
validation interface. The identities and conditional implications represented
by PO-0026 through PO-0029 and PO-0041 are maintained kernel-checked theorems;
this does not construct the Riemann kernel or discharge its global `C₄` sign.
The translate quotient object layer and its first two sign-conversion
mechanisms are checked. This does not instantiate the actual Riemann-kernel
`q > 0` or `Lambda > 0` proofs. The next algebraic conversion boundary is to
identify the terminal quotient derivative with the same `Psi` object used by
the conditional coordinate-sign assembly and verify the `p₄<p₃` orientation.

## Resource discipline

Lean checks are serialized. Before starting a Lean or Lake command, verify that
no existing Lean or Lake process is active. Never launch parallel Lean
compilations. Prefer one directly targeted module check over a full rebuild;
use the full `lake build` gate only once at the end of an epoch. The quotient
modules use narrow imports rather than the `Mathlib` umbrella and contain no
diagnostic `#print` commands, enlarged heartbeat limits, `native_decide`, or
unsafe evaluation. If a single check sustains heavy resource use, stop it and
refine the theorem/module structure before retrying.

## Required build gates

- no `sorry` or `admit` in project sources or generated sources;
- no undeclared custom axioms;
- no `unsafe` theorem bridge;
- `#print axioms` output recorded for T1–T3;
- exact target statement comparison;
- clean certificate availability;
- clean `lake build`.
