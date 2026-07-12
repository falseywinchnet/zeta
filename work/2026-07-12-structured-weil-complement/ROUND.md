# Structured localized-Weil complement

- Mode: advancement
- Date: 2026-07-12
- Model: Sydney, OpenAI Codex
- Status: complete; awaiting later refine integration
- Starting epoch: P000013 (`ac0d5ab5e1839f326c0b14fc65858357af0b9798`)
- Starting targets: R101, R111, R112, R113

## Question

Can the certified finite localized-Weil matrices be extended to a full-operator
lower bound by a structure-preserving complement decomposition, after the naive
low-`L` one-block Schur estimate failed?

## Rules

Everything in this directory is raw advancement support. Numerical observations
are uncertified unless explicitly accompanied by directed enclosures. No result
here is a MIND fact until a later refinement round audits it.

## Candidate mechanisms

1. quantitative spectral lower bounds for the positive logarithmic reference
   form;
2. parity-separated and prime-scale multiblock decompositions;
3. approximate invariant subspaces for the combined form, controlled by
   residuals rather than global perturbation norms;
4. analytic decay bounds for retained-to-tail translation and smooth-kernel
   matrix elements.

## Outcome

- Derived and implemented Suzuki's exact localized Fourier multiplier.
- Reproduced the P000011 certified eight-mode centers independently and found a
  sign trap in the raw truncated (r_0'') transform.
- Proved the natural arithmetic perturbation is relatively compact against the
  positive logarithmic reference form.
- Found positive compact-negative-part margins at `a=0.3` and `a=0.5`, while
  rejecting that sufficient bound at `a=1` for the tested thresholds.
- Identified a domain-aligned periodic/Yoshida trial basis and measured faster
  convergence than the Dirichlet basis at (a=0.3).
- Preserved an explicit logarithmic-Laplacian eigenvalue bound and a concrete
  interval-certification handoff.

No full-operator lower bound is claimed. R113 remains open.
