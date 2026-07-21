# Results

`PF4.CERT12ThetaTail` is now a maintained, importable Lean module.  It proves
for every natural derivative order `j <= 6` and every real `t >= 0` that there
exists a real `delta` with

```text
0 <= delta < 1/1000
```

and

```text
normalizedSeriesJet j t
  = normalizedModeJet j 0 t
  + normalizedModeJet j 1 t
  + thirdModeJet j t * (1 + delta).
```

The left side is defined from the literal `PF4.thetaSeriesJet` `tsum`.  Lean
proves summability from the maintained local-uniform kernel-series bounds,
proves a pointwise geometric majorant for every natural tail index, invokes
the complete `tsum` theorem from P000140, and constructs `delta` from the
actual infinite remainder.  No truncation, grid, or assumed tail estimate is
present in the exported theorem.

`lake build PF4.CERT12ThetaTail` completed successfully through 3417 build
jobs.  The axiom audits of the closed relative tail, the full-tail
factorization, and the literal normalized-series decomposition contain only
`propext`, `Classical.choice`, and `Quot.sound`; none contains `sorryAx`.

The module is real-valued throughout.  It introduces no `ℂ`, Fourier, or
complex-analytic object.  Its analytic inputs are the maintained real
exponential kernel series, real polynomial inequalities, and real infinite
sums.
