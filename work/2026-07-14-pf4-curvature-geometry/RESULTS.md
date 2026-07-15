# Results

## Exact identities derived

- Exact PF4 defines an odd global transport coordinate
  `a(t)=A(y(t))` with `a'(t)=Q D>0`.
- Pullback by `a(t)/a(R)` gives the exact orthonormal basis (3) in
  `GEOMETRIC_OBJECT.md`.
- The Dimitrov--Xu correlation admits the pair-score representation (5)--(7),
  with global curvature `eta_x'=q(x-r)+q(x+r)`.
- The Wronskian identity (8) places the exact Fourier-real-rootedness criterion
  directly on the two-point lift of the PF4 score geometry.
- `Q''>=0` is equivalent to log-convexity of `q`, and this property propagates
  to every pair curvature `q(x-r)+q(x+r)`.

## Exploratory computation

High-precision, non-interval samples on `0<=t<=1.2` found:

- Riemann `Q''` remained positive, with sampled minimum
  `0.000175486360964`;
- `D` rose without a sampled decrease from `1.21069015694` to
  `2.99949984144`, approaching its analytic tail limit `3`;
- the CERT9 crossing CDF gap was nonnegative to floating error
  (`-2.3e-16`) for the displayed triple;
- the numerical `A`-pullback basis had Gram error `2.7e-4`, dominated by
  interpolation rather than a failure of the exact change-of-variables proof.

The sigma-two Gaussian realization of the repository separator had 23 sampled
points with `Q''<0`.  This is structurally expected: a non-Gaussian kernel with
asymptotically constant Gaussian curvature cannot have `Q'` increase from zero
and also return to zero.

## Adversarial family

The family

`exp(-c t^2/2-a cosh(t)-b cosh(2t))`

has log-convex curvature by construction.  Four sampled parameter sets also
had positive, outward-increasing `D` on `0<=t<=4`.  Initial double-precision
complex-zero candidates were false cancellation artifacts; high-precision
integration moved them to real zeros.  No nonreal zero was retained.  This is
weak supporting evidence for the candidate geometry, not a real-rootedness or
PF4 theorem.

## Status boundary

No implication toward RH has been proved.  The advance is the exact geometric
placement of an RH-equivalent correlation object one lift above the PF4
transport coordinate, plus a concrete candidate closure property and a
falsification program.

