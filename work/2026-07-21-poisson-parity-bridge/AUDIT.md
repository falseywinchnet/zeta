# Lean audit

Command:

```sh
cd proof/formal
lake env lean ../../work/2026-07-21-poisson-parity-bridge/PoissonParityBridge.lean
```

Result: exit code 0.

The printed axiom audit for each of the following declarations is exactly
`[propext, Classical.choice, Quot.sound]`:

- `riemannTheta_modular`;
- `contDiff_riemannH`;
- `contDiff_globalRiemannKernel`;
- `globalRiemannKernel_even`;
- `globalRiemannKernel_eq_thetaSeries_abs`.

The source contains no `sorry`, `admit`, custom `axiom`, or unsafe declaration.

