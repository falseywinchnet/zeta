# Certified localized-Weil matrix

- Mode: advancement
- Date: 2026-07-12
- Model: Sydney, OpenAI Codex
- Status: complete; awaiting later refine integration
- Starting epoch: P000010 (`1b96fa6d05275b93616d29f6a242f5e6628c0de3`)
- Starting MIND references: R101, R104, R106, R109--R113
- Primary local evidence: CITE14 and CITE15

## Question

Can the exact one-dimensional Dirichlet-basis reduction from R104 be evaluated
with directed enclosures tight enough to certify finite-dimensional localized-
Weil Ritz matrices, including the prime-power breakpoints and the removable
archimedean singularity?

If so, which part of a full lower bound remains genuinely infinite-dimensional?

## Scope

The primary target is R112. Work on R113 is limited to identifying and testing
the complement estimates required after the projected matrix is certified. This
round does not modify MIND and does not claim an RH consequence from any finite
matrix.

## Required outputs

1. A locally available directed interval or ball-arithmetic backend assessment.
2. A cancellation-free representation of the archimedean screw kernel near zero.
3. Reproducible interval enclosures for every projected matrix entry.
4. Certified finite-matrix eigenvalue intervals or a precise failure report.
5. A proof-level statement of the remaining complement obstruction.

## Certification standard

- Every input constant and transcendental evaluation must carry an enclosure.
- Integration must have a proved remainder bound, not a library error estimate.
- Prime-power breakpoints are exact objects or outward-rounded intervals.
- Matrix symmetrization may widen but never narrow intervals.
- Eigenvalue bounds must account for every entry radius.
- A certified positive projected matrix is still only an upper-side
  reconnaissance result for the full operator.

## Initial route

Use

\[
g(u)=\frac12u\log u+A u
+\sum_{\log n\le u}\frac{\Lambda(n)}{\sqrt n}(u-\log n)+r(u),
\]

with `r(0)=r'(0)=0` and the explicit smooth `r''`. This avoids subtracting two
nearly equal Hurwitz--Lerch values. Integrate the singular, linear, and prime-ramp
parts analytically or piecewise; enclose the smooth remainder independently.

## Log

- Retrieved R111--R113 and selected R112 as the active gate.
- Installed and pinned `python-flint==0.9.0`; Arb/Acb supplies directed balls,
  validated integration, and enclosed eigenvalue isolation.
- Replaced the origin Lerch cancellation by a proved local magnitude enclosure
  and used a dyadic analytic mesh leading away from zero.
- Split every prime-power ramp into a fixed analytic callback and inserted exact
  parity zeros instead of numerical cancellation.
- Certified positive `N=8` projected matrices at `a=0.3`, `0.5`, and `1`; the
  tightest `a=1` interval is `1.4167316571e-12 +/- 4.08e-23`.
- Repeated the sensitive `a=1` run with independent precision, cutoff, and
  tolerance settings; the enclosures overlap and both have positive lower ends.
- Tested the R113 low-`L`-mode Schur design in 32- and 64-mode floating
  truncations. Coupling does not decay over the tested cutoffs, so the simplest
  one-block complement strategy is not viable.

## Preserved failures

- A nonexistent `arb.euler` constant name failed before any main run;
  `arb.const_euler()` is correct.
- One large analytic integration interval failed safely; the dyadic origin mesh
  repairs its complex domain geometry.
- Arb requested coarse nonanalytic balls touching zero; direct Lerch evaluation
  became nonfinite, prompting the proved local range enclosure.
- Rounded subtraction obscured the exact zero difference frequency for equal
  modes; equality is now handled symbolically.

## Handoff

- `CERTIFICATION.md`: proof of every enclosure layer and its scope.
- `certified_matrix.py`: reproducible Arb matrix and eigenvalue enclosures.
- `RESULTS.md`: main intervals, independent repeat, and failure record.
- `test_certified_matrix.py`: low-cost structural certification tests.
- `complement_probe.py`: explicitly uncertified L-adapted block experiment.
- `R113_FINDINGS.md`: failure of the naïve one-block Schur architecture and
  candidate replacements.
