# Collision-regularized PF4 certificate target

## Vandermonde normalization

For ordered nodes, set

```text
D4_tilde(X,Y) = det[Phi(x_i-y_j)] / (Delta(X) Delta(Y)).
```

The quotient extends through coincident nodes by confluent divided differences.
It is the correct interval target: the unnormalized determinant contains zeros
forced by geometry, not by failure of PF4.

The current three-point reduction has the analogous local target.  Write

```text
rho   = a+b,
theta = b/rho,
x     = m-theta*rho,
r     = m+(1-theta)*rho,
Jhat  = J/(theta*rho^3) = J/[b(a+b)^2].
```

The exact leading collision identity is

```text
lim_(rho -> 0) Jhat(m,rho,theta) = C4(m)/(12 q(m)^3),
```

independent of `theta`.  Thus the already-certified strict positivity of `C4`
supplies the radial collision face.  `verify_blowup_identity.py` checks this
algebraically.  For the exact exponential-curvature model, `Jhat` also reduces
to a manifestly positive expression, giving the correct local comparison
model.

## Remove gap divisions before branching

Let `s'=-q`, and consider the left interval of length `b`.  Define exact
integral means

```text
QL = average(q),   PL = average(q'),   UL = average(q''),
B  = b QL,         ML = PL/QL,         NL = UL/QL.
```

Define `QR, PR, UR, C, MR, NR` similarly on the right interval.  These formulas
replace quantities such as `(q(m)-q(x))/B` by ratios of nonsingular integral
means.  Symmetric Taylor formulas for the means contain only even powers of the
half-gap.  They are the local divided-difference form of Vandermonde removal.

## Directed experiments

`certify_jhat_cells.py` uses Arb and a centered mean-value enclosure.  It proves
positivity on three complete three-dimensional cells, including angularly
skewed cells.  These are continuum certificates, not point samples.

Two deliberately preserved failures define the next obligation:

- Direct interval substitution loses shared-variable cancellation on broad
  cells.  The adaptive rectangle prototype exhausts its safety budget without
  certifying a cell.
- Rewriting the gap quotients as integral means is algebraically correct, but
  evaluating high theta cumulants directly on broad Arb balls creates unusably
  wide intervals and eventually `NaN` enclosures.

Neither failure is evidence against PF4.  They show that the production proof
must use centered Taylor models, not natural ball extensions.

## Finite certificate architecture

A credible global certificate now has six components:

1. Compactify the domain using analytic theta-tail and large-separation bounds.
2. Treat `rho=0`, `theta=0`, `theta=1`, and reflection boundaries with exact
   limiting formulas.
3. Generate certified one-variable Taylor jets for `Phi`, `q`, and the required
   derivatives on compact argument intervals.
4. Evaluate `Jhat` with multivariate Taylor models that preserve dependencies
   among `m`, `rho`, and `theta`.
5. Adaptively cover the remaining compact core with directed cells and store a
   replayable cell manifest.
6. Resolve every leftover cell by subdivision or an explicit analytic lemma;
   no sampled sign is promoted.

This reduces the distance to PF4 from an unconditioned global inequality to a
specific certificate construction.  The global covering and its face/tail
lemmas remain open.
