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
PF4/Curvature.lean
PF4/Measures.lean
PF4/Crossing.lean
PF4/CDF.lean
PF4/Transport.lean
PF4/Main.lean
PF4/PF5Witness.lean
PF4/ExactOrder.lean
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
- `PF4.CDF`: concrete measure CDFs, their identification with mathlib's
  probability CDF, and kernel-checked strict gap proofs before the crossing,
  from the crossing through `z`, and on the right interval;
- `PF4.Expectation`: actual Bochner expectations for the concrete measures,
  compact-support integration by parts with explicit boundary terms, and the
  exact expectation-difference/CDF-gap identity;
- `PF4.Transport`: the positive curvature-weighted CDF integral, positive
  numerator assembly, and the exact final negative-sign bridge.

No stub theorem with `sorry` is used. The next conversion boundary is the
paper's primitive/endpoint object identity in PO-0038 and the upstream
derivation of the triangular normalizers from the curvature coordinate.

## Required build gates

- no `sorry` or `admit` in project sources or generated sources;
- no undeclared custom axioms;
- no `unsafe` theorem bridge;
- `#print axioms` output recorded for T1–T3;
- exact target statement comparison;
- clean certificate availability;
- clean `lake build`.
