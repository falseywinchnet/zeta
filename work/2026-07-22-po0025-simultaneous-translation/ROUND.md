# PO-0025 simultaneous coordinate translation

- Mode: advancement
- Date: 2026-07-22
- Model: OpenAI Codex
- Starting MIND IDs: R153, R181, R202–R205, CERT9, CERT19, CERT25, CERT26
- Question: can simultaneous translation of the literal original endpoints be
  identified exactly with the coordinate vector field, including the
  derivative of its `Q(p)` coefficient?
- Status: closed; focused compilation, standard-axiom audit, full build, and
  CERT27 replay complete

## Exact target

For the actual coordinate curve `a ↦ y(u+a)`, prove the endpoint velocity is
`Q(y(u+a))`.  Prove the induced derivatives of `Lambda` and `delta` are the
maintained `T Lambda` and `T delta` endpoint formulas, and connect the
maintained `Psi` to the resulting derivative of `Lambda`.

## Gates

- actual coordinate range only; no surjectivity;
- unbounded exact real parameters; no sampling;
- the derivative of `Q(p)` must occur in the `T delta` calculation;
- no derivative value may be assumed in the public actual-kernel theorem.

## Result

- `actualEndpointCurve` is the literal curve `a ↦ y(u+a)`.
- `hasDerivAt_actualEndpointCurve` proves its velocity is `Q` at every real
  parameter.
- `hasDerivAt_coordinateLambda_along_translation` proves the exact `T Lambda`
  formula.
- `hasDerivAt_coordinateDelta_along_translation` proves the exact `T delta`
  formula and retains the `-Q(p)(2-Q''(p))` correction.
- `actual_simultaneousCoordinateTranslation` packages the actual ordered
  triple and the maintained `Psi` identity without analytic premises.
- The focused build passes 3729 jobs; the full build passes 3735 jobs.
- Every audited theorem uses exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- CERT27 records and replays the five-theorem public audit.
