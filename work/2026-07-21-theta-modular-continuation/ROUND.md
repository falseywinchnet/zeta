# Theta modular continuation

- Date: 2026-07-21
- Mode: advancement
- Model: OpenAI Codex
- Starting progress: P000128
- Starting boundary: `work/2026-07-21-theta-jet-majorant/NEXT.md`
- Status: complete advancement candidate; kernel-checked

## Question

Can the literal positive-side theta jet be attached to a global smooth even
Riemann kernel without defining the latter as `thetaSeries |t|`?

## Immediate target

Fix the exact theta normalization against mathlib, prove the modular identity,
and use it to construct the global even `H` continuation.  Then determine the
narrowest derivative bridge from this global object to the positive-side
kernel series.

## Evidence boundary

The modular equation is imported from mathlib's Jacobi theta development,
whose proof uses Poisson summation.  The normalization equality and every
substitution used here are proved in Lean.  This round does not establish the
three CERT12 strict signs.

## Outcome

The alternate legal form works.  The global object is the real restriction of
a locally holomorphic Jacobi-theta expression, not an absolute-value extension.
Lean proves that `riemannH` is smooth to all orders and even, then defines the
global kernel by the paper's second-order operator and proves it even and
continuous.

The remaining equality with the positive-side theta-series kernel is now a
representation theorem between two independently well-defined smooth objects;
it is no longer responsible for smoothness at zero.
