# Results

## Closed boundary

`ThetaJetMajorant.lean` implements the deferred five-step route from P000126.
It proves a concrete `ThetaJetControl` on every bounded interval containing the
nonnegative point under consideration, so termwise differentiation no longer
depends on a caller-supplied majorant.

The main theorem is

```text
derivativeTowerThroughSix_at_nonneg
```

For every `t >= 0`, it proves the six statements

```text
HasDerivAt thetaSeriesJet_0 thetaSeriesJet_1
...
HasDerivAt thetaSeriesJet_5 thetaSeriesJet_6
```

at `t`. Together with the pre-existing theorem
`thetaSeriesJet_zero_eq`, this is the ordinary six-derivative jet of the
literal positive-side Riemann theta series.

## Mechanism

For a finite real polynomial `p`, define

```text
coeffL1 p = sum_{i=0}^{natDegree p} |p.coeff i|.
```

The reusable theorem `abs_eval_le_coeffL1_mul_max` proves, for `x >= 0`,

\[
 |p(x)|\le \|p\|_1\max(1,x)^{\deg p}.
\]

On `-1 < t < B`, the proof then bounds

\[
 X=\pi n^2e^{2t}
 \le \max(1,\pi e^{2B})n^2
\]

and weakens the exact Gaussian decay to

\[
 e^{-X}\le e^{-\pi e^{-2}n}.
\]

Thus every recursive mode has a locally uniform bound of the form

\[
 K_{B,j}n^{2+2\deg P_{j+1}}e^{-\pi e^{-2}n}.
\]

This is polynomial-times-geometric. Its summability follows from the existing
real exponential comparison theorem already used by the P000125 artifact. No
six-polynomial expansion or separate derivative estimate is used.

## Non-vacuity and scope

- `onIoo` constructs the control data; it does not assume differentiation or
  summability of the infinite sum.
- Level-zero convergence remains the explicit central theorem from P000125.
- Higher-level convergence is derived from the displayed comparison sequence.
- The final derivative tower has only `t >= 0` as a mathematical premise.
- No theta modular identity, negative-side continuation, or cleared strict sign
  is asserted in this round.

## Replay

From `proof/formal/`, one Lean process checked the artifact:

```sh
lake env lean ../../work/2026-07-21-theta-jet-majorant/ThetaJetMajorant.lean
```

The process exited successfully with no output. A textual audit found no
`sorry`, `admit`, or custom `axiom`.
