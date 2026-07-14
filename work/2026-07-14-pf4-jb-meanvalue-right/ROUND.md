# PF4 J_b right region by the mean-value tail model

Mode: advancement

Date: 2026-07-14

Model: Claude Fable 5, Anthropic

Starting records: R157-R161, P000041, P000042

## Question

Close the right separated region {d1 >= 0, d2 >= (w1+3) 2^-34, w0 >= 43} for
the full-theta J_b >= 0, completing (with the P000041 collision cone and the
P000042 left box) the positive-tail three-point obligation R161.

## Method

P000042 diagnosed the failure of the independent endpoint-error model on the
d1=0 face: it breaks the first Peano cancellation. This round replaces it by
the mean-value tail model, in which the left-interval tail data are one
common x-jet plus integrated differences:

    B_tail       = d1 tau0(w0)/(2(w0+3)) + O(d1^2),
    (qm-qx)_tail = d1 tau1(w0)/(2(w0+3)) + O(d1^2),
    (pm-px)_tail = d1 tau2(w0)/(2(w0+3)) + O(d1^2),

with tau_k(w0) the SAME quantities as the x-jet errors ec0..ec2, and the
O(d1^2) remainders carrying the independent symbols eB, eL0, eL1 with
explicit envelopes. Verified abstractly before implementation:

1. The cleared numerator has ideal degree exactly one in the left collision
   ideal (B, qm-qx, pm-px) — so an independent first-order error model can
   never certify the face (P000042's failure was necessary, not accidental).
2. The first Peano cancellation c0 qx + c1 px + c2 ux = 0 holds identically,
   where c_i are the numerator's linear coefficients on the collision
   manifold. Since the mean-value model's d1-linear direction is exactly
   (qx, px, ux)/(2(w0+3)) including the shared error parametrization, the
   d1-linear part of the numerator vanishes for every error assignment:
   d1^2 divides the full comparison, and the face is healed structurally.

The mean-value remainder bounds are valid for all d1 >= 0, but the
quadratic remainder envelope grows with d1 and the coefficient certificate
needs the strip bound d1 < (w0+3) 2^-34 (the strip-free attempt failed
exactly at the top d1-degree); the complement is the P000042 left box.

## Outcome

All gates passed:

- rdec cross-check exact; block expansion 7171 pieces / 617 blocks in 1.7 s;
  exact end-to-end validation of the mean-value model at random rational
  points with random errors.
- Common face factors d1^2 d2: the first Peano cancellation is manifest in
  the blocks, exactly as the abstract identity predicts. Face negatives: 0.
- A strip-free attempt failed only at the top d1-degree (35), confirming the
  quadratic mean-value remainder overruns the clean part for large d1; the
  P000042 left box covers that complement, so the strip bound is the right
  domain, entered by the Moebius substitution d1 = (w0+3) 2^-34 t/(1+t).
- Strip certificate: 53001 geometry monomials, ZERO negative residuals
  (error blocks collapsed to 423 lcd-class absolute envelopes; 15 min,
  modest memory, pure Python integer kernels).

**Positive-tail J_b >= 0 is closed**: collision cone (P000041) + left box
(P000042) + this strip cover every positive-tail configuration (join lemma
in `MATHEMATICS.md`). With S_r > 0 (R160), both sufficient densities of the
one-sided Peano reduction are settled on the positive tail. Remaining for
global PF4: the regimes with the left point below the tail threshold
(compact core, negative side, mixed).

Status: complete as an advancement round; raw research pending refine audit.
