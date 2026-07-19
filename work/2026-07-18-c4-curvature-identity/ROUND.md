# Determinant-to-curvature identity

- Date: 2026-07-18
- Mode: advancement
- Model: OpenAI Codex (Sydney)
- Starting MIND references: R101, R111, R112, R113, R137, R138, R153, R156, R164, R83, R94
- Starting progress: P000101
- Target: close the exact pointwise `C4 = derivedC4` boundary
- Status: complete candidate; preserved through P000102

## Question

Can the independently defined central-moment Hankel determinant be proved
equal to the primitive-derived curvature numerator by kernel-checked polynomial
algebra, without importing positivity, numerical evaluation, or the desired
transport identity?

## Required joins

1. Define the central moments independently from coordinate cumulants.
2. Prove the `4 × 4` Hankel determinant equals the thirteen-term polynomial.
3. Prove the coordinate cumulant substitution equals the cleared curvature
   derivative expression.
4. Instantiate the P000101 central transport theorem with that exact identity.

## Result

All four joins are now represented by kernel-checked exact equalities in
`C4CurvatureIdentity.lean`.

- The primary object is the determinant of the independently constructed
  `4 × 4` central-moment Hankel matrix.
- Its determinant is proved equal to the thirteen-term cumulant polynomial.
- The five coordinate cumulants are linked to repeated application of
  `Q d/dy`, rather than merely postulated as convenient expressions.
- Exact substitution proves the determinant equals the primitive-derived
  numerator whenever curvature is nonzero; strict curvature supplies only
  this denominator fact.
- The function equality is lifted directly to equality of the two transport
  integrals, discharging the P000101 adapter boundary.

No positivity of `C4`, numerical evaluation, transport sign, or desired final
identity is used to prove the determinant factorization.

## Boundary

The determinant-to-curvature interface is closed as an exact equality
candidate. The next assembly boundary is PO-0027: identify the coordinate
transport numerator with the derivative of `Psi`, including its orientation
and commuting-derivative hypotheses.

## Preservation

- Progress: P000102
- Commit: delegated to `MIND PROGRESS COMMIT`
