# Next boundary

The global analytic definition is now independent of the positive-side series.
Do not return to an `abs` or piecewise definition.

## Immediate refinement

Audit the imported Jacobi-theta dependency and integrate the normalization,
modular identity, `riemannH`, and `globalRiemannKernel` into narrow maintained
modules. Keep the positive-side majorant artifact separate until the equality
bridge is checked.

## Next mathematical advancement

Prove the representation theorem

```text
globalRiemannKernel t = thetaSeries t    for 0 ≤ t.
```

The shortest route is:

1. use `hasSum_nat_jacobiTheta` at `I * exp (2*t)` to write `riemannH` as its
   constant mode plus twice the positive Gaussian modes;
2. apply the second-order operator termwise on a bounded interval, using the
   same polynomial-geometric majorant mechanism as P000128;
3. prove that the constant mode is annihilated and each positive mode becomes
   `thetaMode` by exact differentiation;
4. conclude equality with `thetaSeries` for `t ≥ 0`;
5. combine that equality with `derivativeTowerThroughSix_at_nonneg` to identify
   the global raw jet through level six;
6. transport across zero using global smoothness and evenness, not by unfolding
   an absolute value.

After this, identify the raw derivatives with the `Phi0,...,Phi6` inputs of the
cleared certificate bridge. The three strict CERT12 signs remain a separate
boundary.
