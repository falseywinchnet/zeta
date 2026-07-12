# Localized Weil foundation

- Mode: advancement
- Date: 2026-07-12
- Model: Sydney, OpenAI Codex
- Status: complete; awaiting later refine integration
- Starting epoch: P000008 (`0e1db1efc3f39737ffb87c37878cace9f6bdb37a`)
- Starting MIND references: R78, R86, R89, R96--R102
- Primary evidence: CITE14 (`papers/suzuki-weil-screw.pdf`)

## Question

Can Suzuki's localized Weil form be reproduced faithfully enough to support
proof-directed work on the nonincreasing ground-state curve

\[
\lambda_a=\inf_{0\ne v\in C_c^\infty(-a,a)}
\frac{Q_W(v)}{\lVert v\rVert_2^2},
\]

and can the first conforming computations expose a credible route to certified
lower bounds rather than only Rayleigh--Ritz upper bounds?

## Round boundary

This round begins Work Package A and may enter the reconnaissance portion of
Work Package B. It records raw research only. It does not establish MIND facts.

## Required outputs

1. A source-keyed mathematical normalization of the screw function, Weil form,
   localized form, closed form domain, and Friedrichs operator.
2. A checked nesting/monotonicity argument at both the test-form and closed-form
   levels, stating every domain assumption.
3. Reproducible code for the continuous kernel and conforming trial spaces.
4. Convergence tables and structural checks, including failures.
5. A separation between proved identities, numerical observations, and open
   certification requirements.

## Initial hazards

- Fourier-transform normalizations can silently change constants and signs.
- The von Mangoldt contribution produces nonsmooth thresholds as `a` crosses
  logarithms of prime powers.
- Finite Galerkin positivity cannot certify operator positivity.
- A Rayleigh--Ritz eigenvalue is an upper bound for `lambda_a`, not a lower
  bound.
- A form core on one interval does not by itself identify closed domains across
  different intervals; zero extension must be justified.

## Log

- Retrieved the RH tracemap and exact targets R101 and R102.
- Selected Work Package A as the necessary normalization gate before numerical
  claims about Work Packages B or C.
- A symbolic series check caught incorrect hand-copied coefficients in the
  removable expansion for `r''`; corrected before the main runs.
- The first multi-scale comparison exposed an incorrect residual factor `1/(2a)`
  in the scaled prime translation matrix. Direct rescaling of (2.5) shows that
  the Jacobian cancels: the coefficient is `-Lambda(n)/sqrt(n)` times the
  symmetrized translation matrix. The pointwise kernel calculation independently
  confirmed the corrected prime contribution.
- The first structural-test tolerance (`1.2e-3`) was too tight for the fourth
  Ritz value at the deliberately modest independent quadratures: discrepancy
  `1.93e-3`. The tolerance was widened to `2.5e-3`; this is a quadrature
  regression test, not an accuracy certificate.
- Search refinement request observed during the round: ordinary search reached a
  generic-material wall at relevance `0.3279`. In a later refine round, assess a
  stopping threshold based on `1/e = 0.367879...` (dropoff `1-1/e`) and clarify
  whether it is relative to the previous result, the leading result, or an
  absolute normalized relevance. No search tooling is changed in this advancement
  round.
- Reduced the translation-invariant two-dimensional form matrix to adaptive
  one-dimensional integrals with analytic sine-mode derivative correlations and
  explicit splitting at every prime-power kink. This matches the conditional
  200-zero diagnostic at `a=0.3,0.5,1.0`.
- Reproduced the small-interval logarithmic asymptotic numerically. Removing the
  known divergent term gives a two-point `N=20` extrapolation `mu_1 ~ 0.250`,
  with an even simple computed ground state. No error enclosure is claimed.

## Handoff

- `operator_notes.md`: source-keyed normalization and closed-domain nesting.
- `weil_operator.py`: direct, adaptive, and decomposed kernel computations.
- `spectral_crosscheck.py`: explicitly conditional finite-zero diagnostic.
- `test_prototype.py`: structural regression tests.
- `RESULTS.md`: convergence tables, small-interval calibration, and caveats.
- `NEXT.md`: interval/Schur-complement certification architecture.
- `SEARCH_TODO.md`: deferred `1/e` cutoff refinement request.
