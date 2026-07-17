# Exact PF5 confluent-threshold certificate

## Claim

For

\[
 C_5(u)=\det[\Phi^{(i+j)}(u)]_{i,j=0}^4,
\]

there is a unique positive zero `u_*`, with

\[
 0.0622795266356<u_*<0.0622795266357.
\]

The sign is negative on `[0,u_*)` and positive on `(u_*,infinity)`. In
addition,

\[
 -1.08\,10^{-7}
 <\det[\Phi((i-j)211/2000)]_{i,j=0}^4
 <-1.05\,10^{-7}.
\]

## Algebra

With `x=pi exp(2u)`, remove the positive first-mode amplitude
`2x exp(5u/2-x)`. The normalized derivative polynomials satisfy

\[
 P_0=2x-3,\qquad
 P_{j+1}=(5/2-2x)P_j+2xP_j'.
\]

For `y=exp(-3x)` and `z=exp(-8x)`, the first three modes are

\[
 b_j=P_j(x)+4yP_j(4x)+9zP_j(9x).
\]

The symbolic verifier independently reconstructs
`det[b_(i+j)]_(i,j=0)^4` and checks the preserved exact expression has 231
monomials.

## Rational sign cover

The arithmetic verifier uses a `10^-50` rational lattice with outward
rounding. It preserves the correlation between `x`, `exp(-3x)`, and
`exp(-8x)` by local alternating Taylor polynomials in the same cell variable,
then converts the result to the Bernstein basis.

- two cells prove `C5<0` through `u=1/50`;
- 22 cells prove `C5'>0` from `u=3/200` through `x=4`;
- direct four-mode endpoint boxes prove opposite signs at the two printed
  root endpoints;
- four cells prove `C5>0` on `4<=x<=40`;
- an exact one-mode determinant and geometric perturbation prove positivity
  for `x>=40`;
- direct rational theta enclosures prove the finite witness interval.

The overlaps give existence, uniqueness, and the complete sign
classification. No floating-point sign decision, FLINT, Arb, or numerical
root finder enters either replay.

## Replay

- `scripts/verify_pf5_threshold_symbolic.py`
- `scripts/verify_pf5_threshold.py`

