# Riemann-kernel PF3/PF4 classification

Mode: advancement

Date: 2026-07-12

Model: Sydney, OpenAI Codex; continued by Claude Fable 5, Anthropic

Question: determine whether the Riemann/de Bruijn-Newman kernel is globally
PF3, PF4, or neither.

## Two distinct classifications

The original conversation did cover PF3 and PF4. It reached different endpoints
for two different questions:

| Question | PF3 | PF4 |
| --- | --- | --- |
| Can membership alone force Fourier real-rootedness or RH? | No | No |
| Is the Riemann kernel itself globally in the class? | Open | Open |

The first row is certified by the exact PF4 separator: a positive, even,
Schwartz PF4 kernel with nonreal Fourier zeros. Since PF4 implies PF3, it closes
both membership-only implications. The second row is the subject of this round.

The conversation supplied substantial evidence for the second row: positive
high-precision PF3/PF4 subminors of the PF5 witness, broad ordered and confluent
searches, partial-collision searches, and positive local differential
invariants. The conversation itself repeatedly states that these computations
do not establish global membership. Accordingly, they are retained as evidence,
not promoted to a theorem.

Starting MIND: R4, R13-R16, R23, R27, R38, R48, R50, R71, R72, R81.

Decision order:

1. Search for a certified negative order-three minor. Failure closes PF3 and
   PF4.
2. If none is found, reduce global PF3 to a recognized analytic criterion and
   test every boundary and interior regime.
3. Only after PF3 is settled, repeat at order four.

## Outcome

Step 1 found nothing: `sobol-order-3.json` and `sobol-order-4.json` (2^20
unrestricted configurations each) and the 2^22-sample slope-criterion scan
(`pf3-criterion-scan.json`) contain no negative value. The criterion scan's
floor sits at the collision boundary `a,b -> 0`, where the sufficiency bound
`L >= \int F_2/q^2` degenerates to zero, exactly as the reduction predicts.

Step 2 closed positively. The chain, in `MATHEMATICS.md`:

1. Global PF3 is equivalent to the three-variable slope inequality
   `L(t,a,b) >= 0`.
2. Sufficiency lemma: `q>0` and `F2=q^3-(q q''-(q')^2) >= 0` pointwise on `R`
   imply `L >= \int min(q^3,F2)/q^2 >= 0`, covering every interior, collision,
   and escape configuration at once.
3. Compact core: `certify_pf3_curvature.py` proves `q>0`, `F1>0`, `F2>0` on
   `[0,1]` by directed interval arithmetic (7731 adaptive second-order cells,
   certified lower bounds `q>=18.726`, `F1>=0.181`, `F2>=3889.2`, output
   `pf3-curvature-certificate.txt`); evenness gives `[-1,1]`.
4. Tail: hand-derived enclosures at `x=pi e^{2u}>=pi e^2` give `q>=4x-0.86`,
   `|F1|<=11596`, `F2>=(4x-0.86)^3-11596>0` for `|u|>=1`; grid-verified with
   directed rounding in `verify_tail_bounds.py` (`tail-bounds-check.txt`).

Conclusion of this round: the Riemann kernel is globally PF3. With the
certified non-PF5 result (R14, R16), its exact global Polya-frequency order is
3 or 4. Step 3 (global PF4) remains open; the planar-curve convexity reduction
has no direct order-four analogue, and the Sobol evidence at order four is
positive but uncertified.

The first interrupted certificate attempt on `[0,2]` failed structurally: the
interval jet's dependency width grows like `x^6`, so first-order Lipschitz
cells near `u=2` would need about `2^{23}`-fold bisection. The repair was to
shorten the compact range to `[0,1]` where the tail lemma already holds, and
to move the ball evaluation into the second Taylor term
(`F1''=q q''''-(q'')^2`), damping the blow-up by the squared cell radius.

Status: raw advancement research, complete at order three. The sufficiency
lemma and tail derivation are hand-checked and grid-verified but not yet
audited; nothing here is an established MIND fact until a refine round
integrates it.
