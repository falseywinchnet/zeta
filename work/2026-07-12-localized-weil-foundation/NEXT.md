# Proof-directed continuation

## Gate A status

The operator normalization, closed-form nesting argument, and four numerical
representations now exist. The piecewise-adaptive one-dimensional reduction is
the convergent reference computation at prime thresholds. Gate A is not closed:
the adaptive integrals are not interval-certified. The small-`a` constant has
been reproduced numerically (`mu_1` extrapolates to roughly `0.250` at `N=20`),
but its quadrature, `a -> 0`, and trial-space errors are not enclosed.

## Package A next steps

1. Replace the adaptive floating-point integrals by directed interval
   enclosures on each `log(n)/a` piece.
2. Derive analytic or interval-stable evaluations of the archimedean kernel so
   the Lerch cancellation near zero is enclosed, not merely high precision.
3. Diagonalize the limiting `L` form directly and enclose `mu_1`, simplicity,
   and even parity rather than extrapolating from positive `a`.
4. Turn the closed-domain nesting note into a lemma with all form-norm constants
   explicit.

## Package B certification architecture

Write the fixed-interval form as

\[
q_a=L+B_a,
\]

where `L` is the positive logarithmic form and `B_a` is a bounded finite sum of
translations plus a continuous-kernel operator and scalar shift. Use a basis
adapted to `L`, not the Dirichlet Laplacian, so the unresolved complement has a
known coercive cost.

For a trial projection `P_N`, certification needs:

- an interval enclosure of `P_N q_a P_N`;
- a lower bound for `(I-P_N)L(I-P_N)`;
- norm bounds for the off-diagonal block `P_N B_a(I-P_N)`;
- a lower bound for the tail block of `B_a` relative to `L`.

A Schur-complement estimate can then turn these into a lower bound for the full
form. Ordinary Ritz values supply only the upper side.

The immediate feasibility test is whether the bounded perturbation is relatively
compact or has off-diagonal decay in an `L`-eigenbasis strong enough to beat the
small ground-state scale. The current sine basis is convenient but likely poorly
conditioned for that proof.

## Conditional calibration via zeros

For a fixed sine mode `n`, two integrations by parts give

\[
\left|\int_{-1}^1\phi_n(x)e^{i\omega x}\,dx\right|
\le \frac{\pi n(n+1)}{|\omega|^2}.
\]

Combined with an explicit zero-counting bound, this yields a computable tail
matrix bound for the conditional zero-sum calibration. That would validate the
continuous-kernel implementation for each fixed `N`; it is not a route to RH,
because positivity of the zero sum already assumes critical-line zeros.

## Package C obstruction exposed by crude norms

Bounding every prime translation independently by Cauchy--Schwarz gives

\[
|P_a(w)|\le
2\sum_{n\le e^{2a}}\frac{\Lambda(n)}{\sqrt n}\,\|w\|_2^2.
\]

This loses all arithmetic and support correlation and grows far too quickly to
compete with the logarithmic coercivity. Therefore a scale-uniform lower bound
cannot come from termwise translation norms. It must exploit at least one of:

- cancellation in the combined prime symbol;
- uncertainty forced by support in `(-a,a)`;
- a positive or factored representation of the full archimedean-plus-prime form;
- renormalized comparison across consecutive prime-power thresholds.

The next advancement round should first construct the `L`-adapted basis and
measure the off-diagonal perturbation blocks. That experiment directly tests
whether the proposed Schur-complement route can ever certify a lower bound.
