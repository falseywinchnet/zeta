# CERT12 literal coordinate seam

- Date: 2026-07-21
- Model: Sydney (OpenAI Codex)
- Mode: advancement
- Starting MIND references: R101, R111, R112, R113, R137, R138, R83, R94
- Starting progress: P000143
- Status: complete; the literal first-two-mode vector and compact base box are
  maintained, and the exact infinite-tail vector is exposed for perturbation

## Question

Can the maintained literal theta-series jet be identified, coordinatewise and
as one `Fin 7` vector, with the exact two-mode rational-polynomial coordinates
used by the split CERT12 continuum certificates?

## Acceptance

- The first two literal normalized modes equal the exact CERT12 coordinate for
  every derivative order through six and every `t >= 0`.
- The seven equalities are packaged as one finite-vector identity.
- On `certX t <= 5`, the exact two-mode vector satisfies the maintained
  `coreB` coordinate box through `CERT12BaseBounds`.
- Exponential comparisons are proved from finite Taylor lower sums, not a
  numerical oracle.
- No sampled range, `sorry`, added axiom, or complex arithmetic.

## Result

- `PF4.CERT12ExpBounds` proves the required natural-curve bound
  `exp (-3*x) < 1/12000` from a finite Taylor lower sum for
  `exp (471/50)`.
- `PF4.CERT12Coordinates.twoModeNormalizedJet` is the exact CERT12 coordinate
  `(P_j(x) + 4*y*P_j(4*x))/(2*x-3)`.
- `firstTwoModeJet_eq` identifies all seven first-two-mode literal theta
  coordinates with one `Fin 7` vector.
- `normalizedSeriesJetVector_eq` identifies the complete literal infinite
  theta jet with `twoModeJet + fullTailJet` as one vector equality.
- `abs_twoModeJet_le_coreB` consumes all fourteen maintained base Bernstein
  bounds and proves the full compact coordinate box whenever `t >= 0` and
  `certX t <= 5`.

The lower endpoint `157/50 <= certX t` is derived from the maintained decimal
lower bound for pi and monotonicity of the real exponential.  The weaker fact
`3 <= certX t` is intentionally not used for this sharper endpoint.

## Verification

`lake build PF4.CERT12Coordinates` completed successfully with 3427 jobs.
The exported axiom prints contain only `propext`, `Classical.choice`, and
`Quot.sound`.  A textual audit found no `sorry`, `axiom`, or `Complex` in the
new modules.
