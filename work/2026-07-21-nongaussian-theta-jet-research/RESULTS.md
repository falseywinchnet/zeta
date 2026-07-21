# Result: use polynomial-geometric normal convergence

Yes.  The Gaussian is intrinsic to the summand but need not be the comparison
series used by the proof.

Put

\[
q(t)=\exp(-\pi e^{2t}).
\]

On a bounded interval `a < t < b`, let

\[
\rho=\exp(-\pi e^{2a}).
\]

Then `0 < q(t) <= rho < 1`.  Since every summation index is a positive integer,

\[
q(t)^{n^2}\le \rho^{n^2}\le \rho^n.
\]

The recursive jet mode at level `j` is a polynomial of degree at most `2j+4`
in `n`, times `q(t)^{n^2}`, with interval-bounded coefficients.  Therefore

\[
|\operatorname{mode}_j(n,t)|\le C_j(a,b)n^{2j+4}\rho^n.
\]

The right side is polynomial times a geometric sequence.  Mathlib already has
`summable_pow_mul_geometric_of_norm_lt_one`; the existing theta-jet file also
already has the equivalent real-exponential comparison theorem.  This supplies
the summable locally uniform majorants required by `ThetaJetControl`.

## Recommended formal route

1. Prove one finite-support evaluation lemma
   `|p.eval x| <= coeffL1 p * max 1 x ^ p.natDegree` for `x >= 0`.
2. Prove `natDegree (certPoly j) <= j + 1` by the recurrence.
3. On `Set.Ioo a b`, bound `modeX` above by `pi * exp (2*b) * n^2`.
4. Replace the exact decay by `rho^n` using `n <= n^2`.
5. Instantiate `ThetaJetControl` and obtain the six derivatives from the theorem
   already proved in P000125.

This is elementary real analysis and remains close to the current narrow import
graph.  It avoids a new Gaussian integral or Gaussian summability library.

## Alternatives considered

### Jacobi-theta holomorphy

Mathlib's two-variable Jacobi theta development proves locally uniform
convergence and holomorphy on the upper half-plane, including differentiation in
the modular parameter.  In principle the Riemann kernel can be expressed using
the theta function and its parameter derivatives.  This route is mathematically
clean but formally expensive: it introduces complex variables, an integer-indexed
theta series, normalization translations, repeated parameter derivatives, and
imports Gaussian Poisson summation and finite-dimensional complex analysis.

### Sparse power-series analyticity

One can define `Theta(q) = sum q^(n^2)` as a power series on `|q| < 1` and express
the modes using powers of `q d/dq`.  This eliminates interval majorants from the
conceptual proof, but formalizing the sparse coefficients and translating six
derivatives is more machinery than the direct geometric comparison.

### Exact ratio test

The ratios of polynomial-geometric majorants tend to `rho < 1`.  This also works,
but Mathlib's existing polynomial-times-geometric theorem makes a custom ratio
test unnecessary.

## Evidence consulted

- NIST DLMF, theta functions: https://dlmf.nist.gov/20.2 and
  https://dlmf.nist.gov/20.5
- Mathlib Jacobi theta documentation:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.html
- Mathlib geometric summability documentation:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecificLimits/Normed.html
- Local Mathlib source for the same theorems, inspected at the pinned repository
  dependency revision.

## Decision

Use the direct polynomial-geometric majorant.  Keep Jacobi-theta holomorphy as a
later abstraction/refactor, not as the shortest closure of the present boundary.
