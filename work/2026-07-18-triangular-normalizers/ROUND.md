# Triangular normalizers

- Date: 2026-07-18
- Mode: advancement
- Model: OpenAI Codex (Sydney)
- Starting MIND references: R101, R111, R112, R113, R137, R138, R153, R83, R94
- Starting certificate: CERT9
- Proof obligations: PO-0023, PO-0024; handoff to PO-0030 and PO-0031
- Status: complete advancement candidate; awaiting refine-round audit

## Question

Can the curvature-coordinate identities for `Lambda` and `delta` be derived in
Lean from an actual twice-differentiable coordinate function, including the
endpoint derivative defining `delta`, strict positivity, and the analytic
inputs needed by the existing probability-measure construction?

## Evidence boundary

Everything in this directory is advancement work. A Lean file must compile
without `sorry`, axioms, or vacuous hypotheses before it can be proposed for a
later refine-round integration. No statement here is an established MIND
factoid merely because it appears or compiles here.

## Planned boundary

1. Derive the two weighted curvature integrals by explicit antiderivatives.
2. Prove `delta = -partial_p Lambda` rather than naming an unrelated positive
   quantity `delta`.
3. Derive strict positivity from `kappa > 0` on nondegenerate intervals.
4. Supply continuity and interval-integrability interfaces for the existing
   triangular density and measure layer.
5. Record the exact remaining handoff to PO-0030 and PO-0031.

## Result

`TriangularNormalizers.lean` compiles without `sorry`, `admit`, or new axioms.
It proves:

- explicit antiderivatives for both triangular curvature weights;
- the PO-0023 formula expressing `Lambda` as the sum of the two normalized
  triangular integrals;
- the endpoint derivative identity `partial_p Lambda = -delta`;
- the PO-0024 decreasing-triangle formula for that same `delta`;
- strict positivity of `delta` and `Lambda` from continuity, positive
  curvature, and the nondegenerate endpoint order;
- exact mass-one identities for the existing left and two-piece densities;
- interval integrability through continuous density representatives;
- `IsProbabilityMeasure` for the existing concrete `muMeasure` and
  `nuMeasure`, with the derived normalizers substituted;
- a direct specialization of the existing PO-0038 transport theorem in which
  its free endpoint-normalizer identities and positivity hypotheses are
  discharged by these constructions.

The central non-vacuity property is structural: `coordinateDelta` is not an
arbitrary positive parameter. It is defined from the endpoint jet of `Q`, is
proved to be the negative left-endpoint derivative of the same
`coordinateLambda`, and is then proved equal to the positive triangular
integral.

## Exact assumptions retained

- `p < z < w`;
- `Q'` and `Q''` are actual first and second derivatives on the relevant
  interval (globally in the transport specialization);
- `curvature = 2 - Q''` is continuous and strictly positive;
- the third-jet and primitive-continuity assumptions already required by the
  PO-0038 transport theorem.

No manuscript file was changed.

## Next refine edge

Audit the candidate for placement in `proof/formal/PF4/`, remove the duplicate
local chord-slope name in favor of the transport namespace, update the PO-0023,
PO-0024, PO-0030, and PO-0031 ledgers, and add the candidate to the formal
build. The later mathematical boundary remains positivity of the transport
expectation difference; this round only makes its probability laws and
normalizers constructive.
