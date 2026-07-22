# Next advancement cycle — simultaneous coordinate translation

Mode: advancement

Starting evidence: CERT9, CERT19, CERT25, the actual coordinate jet in
`PF4.CurvatureCoordinateRealization`, and the literal paper objects in
`PF4.PaperObjectClosure`.

## Maintained boundary

PO-0009, PO-0010, PO-0022, and PO-0029 are closed. The remaining support
obligation in the curvature-coordinate frame is PO-0025: explicitly identify
simultaneous translation in the original variable with the coordinate vector
field used by the endpoint formulas.

## Next exact theorem family

For every actual endpoint `u`, prove the curve

```text
a |-> kernelCoordinate actualKernelSlope (u + a)
```

has derivative `actualCoordinateQ` at `a=0`. Extend this componentwise to the
ordered endpoint triple, then connect differentiation of the maintained
`coordinateLambda`, `coordinateDelta`, and `coordinatePsi` objects to their
named simultaneous-translation formulas.

## No-cheating gates

- Include the derivative of the vector-field coefficient `Q(p)`; do not treat
  the transformed translation field as constant.
- Work only at actual coordinate points; no global surjectivity premise.
- No symbolic-CAS equality may substitute for the Lean chain rule.
- No bounded or sampled domain and no RH consequence.

## Exit condition

PO-0025 is closed only when the literal actual-endpoint curve and the paper's
named translation objects are joined by kernel-checked derivative theorems
with no uninstantiated analytic premise.
