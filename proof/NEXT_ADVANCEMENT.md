# Next advancement cycle — actual-kernel transport-route closure

Mode: advancement

Starting evidence: R181, R202–R205, CERT19, CERT22–CERT24, the maintained
actual-kernel jet/sign package in `PF4.GlobalStrictPF4`, and the local closed
transport theorem
`PF4.LocalFinalAssembly.actualCoordinatePartialXiPsi_neg`.

## Maintained boundary

The frozen `PF4-CORE-v1` target is complete:

```lean
PF4.globalRiemannKernel_pfOrderExactly_four :
  PF4.PFOrderExactly PF4.globalRiemannKernel 4
```

This next round does not reopen T1–T3. It closes the still-useful paper route
whose generic and range-local components are already checked but whose literal
global Riemann-kernel instance has not been exported.

## Next exact theorem family

Export the actual-kernel specialization of
`PF4.LocalFinalAssembly.actualCoordinatePartialXiPsi_neg`, using:

- `kernelJet 0, …, kernelJet 6` for the maintained derivative tower;
- `logSlope (kernelJet 0) (kernelJet 1)` for `S`;
- the maintained `kernelCurvature`, `jetQ1`, …, `jetQ4` objects;
- the universal exact `q`, `F₂`, and determinant-`C₄` signs already assembled
  inside `PF4.GlobalStrictPF4`.

The public theorem must quantify over every ordered triple `x < m < r` and
state the literal negative coordinate-`Psi` derivative expression obtained by
that specialization. No fresh abstract functions or positivity premises may
remain.

## Proof order

1. Refactor the existing private actual-kernel sign bundle into a narrowly
   exported theorem without changing its proof or duplicating CERT12.
2. Instantiate the derivative tower and top-jet continuity from the maintained
   global kernel jet theorems.
3. Apply `actualCoordinatePartialXiPsi_neg` and export the literal
   actual-kernel result.
4. Compare it two ways with PO-0022, PO-0029, PO-0040, and PO-0041; promote
   only the atomic obligations whose exact statements are now closed.
5. Keep T1–T3 and their certificate graph unchanged.

## No-cheating gates

- No positivity, differentiability, continuity, or coordinate-range premise
  may remain in the public actual-kernel theorem.
- Do not assume the curvature coordinate is surjective onto `ℝ`.
- Do not replace the actual range by a bounded or sampled domain.
- Preserve the original-variable ordering `x < m < r` and the proved
  orientation of the coordinate derivative.
- Do not claim an RH consequence.

## Exit condition

The round closes when the literal global-kernel transport-route derivative
theorem is kernel-checked with standard axioms only and the status ledger
distinguishes the newly closed actual instance from broader generic converse,
confluent, or endpoint-limit claims.
