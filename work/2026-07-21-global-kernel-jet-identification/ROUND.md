# Global kernel jet identification

- Mode: advancement
- Date: 2026-07-21
- Model: OpenAI Codex
- Starting MIND records: P000124, P000128--P000133, R181--R194,
  CERT12, CERT19--CERT21
- Question: identify `iteratedDeriv j globalRiemannKernel t` with
  `thetaSeriesJet j t` through order six on the nonnegative half-line,
  including the origin, without redefining the global kernel by reflection.
- Status: completed candidate; ready for a refine-round audit

## Evidence boundary

Maintained Lean already proves global analyticity and evenness of the real
kernel, its value equality with `thetaSeries` on `t >= 0`, and a genuine
ordinary derivative tower for `thetaSeriesJet 0,...,6` on intervals containing
the origin. This round must prove derivative-value identification rather than
assuming it from matching notation.

## Initial observation

The existing interval theorem is stronger near the origin than its summary
suggests: for each positive bound it supplies the entire series derivative
tower on `(-1,B)`. The origin seam can therefore be treated as uniqueness of
derivatives on the right half-line between two differentiable functions, not
as a new convergence problem.

## Outcome

The candidate proves the full order-six jet identification, global derivative
parity, strict kernel positivity, alternating-parity invariance and common
scaling of the three cleared polynomials, exact first-mode normalization, and
the conditional terminal quotient sign from only the three normalized
nonnegative-axis CERT12 propositions. It compiles without `sorry`.
