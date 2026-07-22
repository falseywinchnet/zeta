# Next advancement cycle — actual-range curvature-rate exports

Mode: advancement

Starting evidence: R181, R202–R205, CERT19, CERT22–CERT24, the public
`PF4.GlobalStrictPF4.actualKernelSigns`, and the newly closed literal transport
theorems:

```lean
PF4.GlobalStrictPF4.globalRiemannKernel_coordinateNumerator_pos
PF4.GlobalStrictPF4.globalRiemannKernel_coordinatePartialXiPsi_neg
```

## Maintained boundary

The frozen T1–T3 classification and the independent determinant/transport
route are complete. The next useful work is statement packaging for two paper
objects that are already used internally but are not exported in their exact
actual-range forms.

## Next exact theorem family

1. Export the literal identity
   `rho = kernelF2 q q1 q2 / q^3 > 0` and hence `kappa = 1 + rho > 1` at every
   actual coordinate point.
2. Export positivity of the paper primitive rate `D` at every actual
   coordinate point from the exact determinant identity and the public actual
   `q`, `F2`, and `C4` signs.
3. Close PO-0022 and PO-0029 only if the public statements name the maintained
   paper objects and quantify over the complete actual coordinate range.

## No-cheating gates

- Do not claim that the curvature coordinate is onto all of `ℝ`.
- Do not use properties of the arbitrary `invFun` extension off the actual
  coordinate range.
- No positivity or determinant premise may remain in the actual-kernel public
  statements.
- No bounded or sampled domain.
- Do not reopen T1–T3 or claim an RH consequence.

## Exit condition

The round closes when the literal `rho`, `kappa`, and primitive-rate statements
are kernel-checked with standard axioms only, or when the remaining mismatch
with the paper's notation is isolated as a precise backport decision.
