# PF4 pathway

## Final objective

Prove

\[
\partial_\xi\Psi(\xi;m,r)\le 0\qquad(\xi<m<r)
\]

for the full Riemann kernel.  By `R156` and `CERT5`, this is equivalent to
global PF4.  Together with global PF3 and the certified PF5 counterexample,
it would make the exact global Polya-frequency order four.

## Secured boundary

- Global PF3: `R144`, `CERT2`.
- Global PF4 reduction: `R156`, `CERT5`.
- Every fully confluent order-four minor is positive: `R152`, `CERT3`.
- Positive-tail edge density `S_r>0` for `pi exp(2m)>=23`: `R160`, `CERT7`.
- Positive-tail three-point density `J_b>=0` for
  `X_xi=pi exp(2xi)>=23`: `CERT8`, including the collision cone, both
  angular faces, the left separated box, and the mean-value strip.

The positive-tail seam is fixed at 23.  Lowering it is optional optimization,
not a prerequisite for global PF4.  The floor-6, floor-18, and error-threshold
runs from 2026-07-14 remain raw diagnostics; they must not turn the proof into
an indefinite sequence of lower tail anchors.

## Finite completion atlas

1. **Uniform escape lemmas.** Prove the right-escape and left-escape signs
   with explicit uniform thresholds on bounded anchor intervals.  This turns
   the apparently unbounded central and mixed-sign regimes into compact boxes.
2. **Positive central chart.** Certify the regularized criterion for
   `0<=xi<x_23`, bounded gaps, with the full theta jet.  Use collision-divided
   coordinates; do not force the one-term tail model below its useful seam.
3. **Mixed chart `(-,+,+)`.** Derive and certify the parity-correct density or
   regularized criterion for `xi<0<m<r`, joined to the escape and collision
   charts.
4. **Mixed chart `(-,-,+)`.** Do the same for `xi<m<0<r`.  This is a distinct
   sign pattern; evenness alone does not prove it.
5. **Origin collision cone.** Turn the global `C4>0` certificate into a
   quantitative cone covering collisions that meet or cross zero, with
   explicit overlap into both mixed charts.
6. **Mirror and exhaustive join.** Prove the all-negative reflection and
   determinant-orientation lemma, list every ordered sign/collision/escape
   cell, verify overlaps, and replay the final implication through `CERT5`.

The immediate next advancement round is item 1 (`R163`).  Its deliverable is an exact
uniform escape threshold and a compact residual domain, not a scan.

## Replay policy

`CERT8` uses a fast proof-carrying replay: every final exact integer residual
is stored and checked on each CI run.  The manifest also names the deep
generator, which reconstructs those residuals from the 74-term symbolic
numerator.  This keeps routine replay bounded while retaining a from-scratch
audit path.

Historical `work/**/NEXT.md` files describe the state at their own epochs.
This file is the only live PF4 completion plan.
