# Next boundary

The legal global kernel and the literal positive theta series are now joined
on `t ≥ 0`. Do not revisit the two-derivative convergence bridge and do not
define the global kernel using `abs` or a sign branch.

## Immediate refinement

Audit and integrate the global theta normalization, the positive-series
bridge, and their narrow imports into maintained Lean modules. Keep the
six-derivative majorant and the strict sign certificates as separate evidence
boundaries.

## Next mathematical advancement

Prove the global raw-jet transport theorem through order six:

1. combine `globalRiemannKernel_eq_thetaSeries_of_nonneg` with
   `derivativeTowerThroughSix_at_nonneg` from P000128;
2. identify `iteratedDeriv j globalRiemannKernel t` with `thetaSeriesJet j t`
   for `j ≤ 6` and `t > 0`;
3. use global smoothness and evenness to extend the identities to `t = 0` and
   transport them to negative `t`, with the expected parity factor `(-1)^j`;
4. package the resulting values as the raw `Phi0,...,Phi6` inputs of the
   cleared certificate bridge.

The three strict CERT12 signs remain an independent later boundary. Do not
infer them from convergence, parity, or the derivative recurrence.
