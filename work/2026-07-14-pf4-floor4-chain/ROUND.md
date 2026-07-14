# PF4 floor-4 chain attempt: architecture floor discovered

Mode: advancement

Date: 2026-07-14

Model: Claude Fable 5, Anthropic

Starting records: P000041-P000046; completion map item 2

## Question

Rerun the separated positive-branch certificates (S_r transfer, J_b left box,
J_b mean-value strip) at the floor-4 anchor with the P000046 ERROR4 table.

## Outcome: three findings in layers

1. The direct rerun fails hard (S_r: 1714 of 2553 coefficients negative),
   with or without the transfer target, at every gap floor from 2^-2 to
   2^-22, and Polya lifting makes it worse. Root cause measured: the
   P000046 majorization's HIGHER orders are catastrophically loose at low
   floors (order 5: envelope 3.1e8 vs true 592 x z^4-normalized -- up to
   1e5x), invisible at floor 23 behind the 2^-99 scale.

2. `band_envelopes.py`: tight band-certified envelopes. Certifies
   H_j(z) = z^4 |D^j log(1+R)(z)| <= E_j on z in [4,23] by first-order
   Taylor cells over the audited order-8 arb jet (tight midpoint differences
   of full and one-term cumulants; h^2-suppressed crude bound from the
   loose table extended to order 8; 875 cells). Joined with the pointwise
   floor-23 table for z >= 23 via X <= z => X^4 G(z) <= H_j(z):

     E4_tight = (0.92, 21.5, 495, 1.89e4, 3.45e6, 1.33e9)

   60-90x tighter than P000046 at the high orders.

3. The decisive discovery: even the TRUE tails break the one-term
   architecture at z = 4. Measured |D^5 w(4)| = 592 against the one-term
   ell_5 scale 2^5 z = 128: the theta tail DOMINATES the one-term value at
   cumulant order 5 near z = 4 (the D-operator amplifies the n=2 term by
   (2n^2 z)^j / (2z)^j = 4^j per order). One-term dominance at all orders
   <= 6 requires roughly z >= 6 (4^6 e^{-3z} <= 6e-5 at z=6), is marginal
   at z = 5, and fails at z = 4. No envelope tightening can rescue the
   floor-4 chain; the architecture floor is z ~ 6 (u >= 0.323).

## Consequences for the completion map

- Item 2 splits: (2a) rerun the chain at floor 6 with the band-certified
  tight table (expected to pass; envelopes ~1e-4 relative there at all
  orders); (2b) the band z in [pi, 6] (u in [0, 0.323]) needs a TWO-TERM
  dominant model (n = 1,2 exact, n >= 3 tails) or the compact interval
  treatment -- the same block machinery with two-term Laurent forms is the
  natural extension, since w-frame jets of the n=2 term are Laurent in the
  same base with e^{-3z}-weighted second components.

Status: complete as an advancement round; raw research pending refine audit.
