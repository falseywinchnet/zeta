# Central transport identity

- Date: 2026-07-18
- Mode: advancement
- Model: OpenAI Codex (Sydney)
- Starting MIND references: R101, R111, R112, R113, R137, R138, R153, R83, R94
- Starting progress: P000100
- Target: remove the central-identity premise left by P000100
- Status: complete candidate; preserved through MIND progress below

## Question

Can `expandedTransportK` be proved equal to the deterministic closed-gap
transport integral by joining the existing object identities, without assuming
either side or any sign?

## Required joins

1. `expandedTransportK =` concrete expectation difference.
2. expectation difference `=` measure-backed CDF-gap integral.
3. measure-backed CDF gap `=` closed `coordinateGap` on `[p,w]`.
4. derivative of the paper primitive `=` the displayed curvature weight.

## Result

All four joins are proved as exact equalities in
`CentralTransportIdentity.lean`.

- `cdfGap_eq_coordinateGap` identifies the measure-backed CDF difference with
  its deterministic closed form at every point of `[p,w]`.
- `expandedTransportK_eq_coordinateTransportIntegral` removes the central
  identity premise when the curvature numerator is defined by clearing the
  derivative of the paper primitive.
- `expandedTransportK_eq_coordinateTransportIntegral_of_C4_eq` transfers the
  result to an independently supplied `C4` under exact pointwise identity on
  `[p,w]`.

Here *gap* means the signed mathematical difference `F_μ - F_ν`. It is the
integrand object whose closed form is derived. It is not an error bound,
tolerance, slack, or permitted proof defect. No approximation or inequality is
used in the central identity.

## Boundary

The next statement boundary is exact identification of the independently
defined determinant/cumulant `C4` with `derivedC4`. That obligation is an
equality, not a bounded residual. The central transport composition itself no
longer remains a premise.

## Preservation

- Progress: P000101
- Commit: delegated to `MIND PROGRESS COMMIT`
