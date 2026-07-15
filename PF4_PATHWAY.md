# PF4 pathway

## Resolved classification

The Riemann kernel is strictly PF4 (`R164`, `CERT9`) and is not PF5 (`R14`).
Its exact global Polya-frequency order is therefore four (`R145`).

The global three-point criterion is strict:

\[
\partial_\xi\Psi(\xi;m,r)<0\qquad(\xi<m<r).             \tag{1}
\]

## Certified proof chain

1. `CERT2` gives `q>0`, so `y=-s(t)` is a strictly increasing coordinate and
   `Q(y(t))=q(t)>0`.
2. `CERT3` proves the direct central-moment invariant `C4(t)>0` for every real
   `t`.
3. In the curvature coordinate,

   \[
   C_4=Q^6\kappa^2
   \left[3(\kappa-1)-\{Q(\log\kappa)'\}'\right],
   \qquad \kappa=2-Q''>0.
   \]

4. The exact `delta` and `Lambda` triangular weights normalize to probability
   measures `mu` and `nu`. Their CDF crossing kernel `W=F_mu-F_nu` is strictly
   positive in the interior: the left density ratio decreases once from
   infinity to zero, while the right triangular component supplies a strict
   endpoint gap.
5. Two exact primitives remove every transport remainder and give

   \[
   \mathcal N=\delta\Lambda\int_p^w
   W(t)\frac{C_4(t)}{Q(t)^6\kappa(t)^2}\,dt>0.
   \]

6. The sign bridge audited against `CERT5` is

   \[
   \partial_\xi\Psi=-\frac{Q(p)}{\Lambda^2}\mathcal N<0.
   \]

   `CERT5` then converts (1) through the quotient-Wronskian and generic
   iterated-integral identities to strict positivity of every order-four
   translation minor.

The checked derivation is in
`sources/pf4-transport-kernel-certificate.md`; its replay boundary is `CERT9`.

## Retired spatial atlas

The escape thresholds, collision cones, Hermite boxes, mixed-sign charts, and
regional joins are no longer proof obligations (`R163`). `CERT6`--`CERT8`
remain valid independent positive-tail results, and their work directories
remain durable evidence, but the global theorem does not depend on completing
that atlas.

The raw independent coupling has sign-indefinite fibers when its two left
samples occur in reverse order. They cancel in the positive CDF crossing
kernel. Treating those fibers as separate spatial regions would recreate the
discarded subdivision problem.

## RH boundary

Exact PF order four is RH-neutral (`R81`). PF4 is not PF-infinity, and the
repository contains an exact PF4 separator whose Fourier transform has
nonreal zeros. No RH conclusion is inferred from this classification.

## Replay

`CERT9` is a short exact-symbolic audit with independent 70-digit Riemann-kernel
checks. It depends on `CERT3` for global `C4>0` and on `CERT5` for the global
PF4 equivalence. Routine replay does not execute any abandoned atlas generator
or numerical scan.
