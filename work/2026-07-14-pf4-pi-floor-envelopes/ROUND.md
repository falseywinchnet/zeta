# PF4 pi-floor envelope tables

Mode: advancement

Date: 2026-07-14

Model: Claude Fable 5, Anthropic

Starting records: R157-R161, P000041-P000045; NEXT.md of
work/2026-07-14-pf4-jb-meanvalue-right (completion map item 1)

## Question

Extend the CERT6/7 theta-tail envelope construction from the floor X >= 23
down toward the origin, so the positive-branch certificates can cover all of
u >= 0 (completion map items 1-2).

## Outcome

`pi_floor_envelopes.py` parametrizes the audited tail_error_coefficients
construction by its floor-dependent constants: t = 2z/(2z-3) with
t_max = 2F/(2F-3) at floor F, exponential block evaluated at 3F, prefactor
ratio t_max - 1, normalization F^4 exp(-3F) (rational upper bounds for
exp(-9), exp(-12) used exactly).

- Regression gate: the floor-23 instance reproduces the audited ERROR table
  EXACTLY, term by term.
- Tables derived and validated pointwise against mpmath evaluation of
  D^j log(1+R) (24 checks per table, all passing with margin):
  floor 3 (covers u >= -0.024), floor 4 (covers u >= 0.121), floor 5.
- Tightness finding (order-2 envelope relative to q at the floor):
  floor 3: 35.7%; floor 4: 2.7%; floor 5: 0.2%. Against the ~25% criterion
  margins, floor 4 is the production anchor; the floor-3 table is valid but
  too loose for direct use.
- The remaining band z in [pi, 4] (u in [0, 0.121]) needs a sharpened
  majorization: the TRUE tail there is ~9% relative (|D^2 w| = 1.235 at z=3
  vs envelope 7.14), so the required tightening factor is about 4-6; the
  looseness lives in the absolute-coefficient sums of the K and E blocks.
  Alternatively the band is one bounded-w0 Moebius certificate away once the
  sharpened table exists.

Next consumers (completion map item 2): rerun S_r separated transfer, J_b
cone/box/strip, and the collision radii with W_FLOOR = 5 (w = 2z-3 at z=4)
and the ERROR4 table, extending partial_xi Psi <= 0 from xi >= 1 down to
xi >= 0.121.

Status: complete as an advancement round; raw research pending refine audit.
