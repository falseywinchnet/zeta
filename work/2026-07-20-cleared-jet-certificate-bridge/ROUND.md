# Cleared-jet certificate bridge

- Mode: advancement
- Date: 2026-07-20
- Model: OpenAI Codex
- Starting progress: P000123
- Starting references: R171, R181
- Starting certificates: CERT12, CERT19
- Status: complete advancement candidate; compiled and ready for refinement audit

## Question

Can the exact raw-derivative polynomials certified by CERT12 be connected to
the maintained Lean objects `kernelCurvature`, `kernelF2`, and
`kernelDeterminantC4` by explicit positive-denominator identities, while also
constructing the required curvature derivative tower from one ordinary kernel
jet?

## Intended boundary

Use normalized raw moments `m_j = Phi_j/Phi_0` and their closed recurrence

```text
m_j' = m_(j+1) - m_1 m_j
```

to derive the logarithmic cumulants through order six.  Prove that the three
cleared CERT12 polynomials are exactly `Phi_0^2 q`, `Phi_0^6 F2`, and
`Phi_0^4 C4`.  Feed their strict signs into the maintained actual-coordinate
proof mechanism without assuming any downstream sign or coordinate object.

The literal theta series and the analytic proof of the three cleared signs
remain separate unless they can be constructed honestly in this round.

## Result

The normalized recurrence, cumulant tower through order six, all three cleared
identities, and the raw-Hankel determinant identity are kernel-checked.  The
raw derivative tower plus the three cleared signs now feed the maintained
actual-coordinate theorem and the terminal translation-quotient cascade.

The final theorem does not assume `q > 0`, `F2 > 0`, `C4 > 0`, lower-Lambda
positivity, coordinate realization, Psi monotonicity, or the terminal sign.
It derives all of them from positivity of `Phi0`, the ordinary raw derivative
tower, continuity of `Phi6`, and the three CERT12-shaped cleared polynomial
signs.

This is an exact proposition bridge, not yet a literal Riemann-kernel
instantiation: the theta series and its certified cleared signs have not been
reconstructed as Lean theorems in this round.
