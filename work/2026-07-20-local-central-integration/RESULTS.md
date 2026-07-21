# Results

## Closed-gap derivatives

`closedGapLeft_hasDerivAt_densityDifference` proves that the left closed gap
has rate

```text
leftMuDensity - leftNuDensity.
```

`closedGapRight_hasDerivAt_negDensity` proves that the right tail has rate

```text
-rightNuDensity.
```

Both are literal derivatives of the independently defined closed forms.

## Branch meeting

`closedGap_match_on_Icc` derives equality of the two branch values at `z` from
their local integral representations and the two exact normalized mass
identities. The equality is not assumed for integration by parts.

## Direct integration by parts

`coordinateGap_integral_eq_densityDifference` splits the compact integral at
`z` and applies integration by parts separately on `[p,z]` and `[z,w]`.

- The `p` and `w` terms vanish by the exact closed-gap endpoint formulas.
- The two `z` terms cancel using `closedGap_match_on_Icc`.
- The remaining integrals are exactly

```text
nuLeft + nuRight - mu.
```

This step uses no measure, expectation, CDF, probability, or complement-mass
object.

## Endpoint primitive reduction

`integral_decreasing_linear_mul_deriv_on_Icc` and
`integral_increasing_linear_mul_deriv_on_Icc` are compact-interval versions of
the two elementary FTC reductions for the maintained primitives `H` and `J`.

`expandedTransportK_eq_densityDifference_on_Icc` applies those reductions to
the three direct density integrals. Their internal `H z` terms cancel, and the
existing purely algebraic endpoint theorem identifies the result with
`expandedTransportK`.

## Central identity

`expandedTransportK_eq_coordinateTransportIntegral_on_Icc` composes the two
halves and proves the exact P000120 residual equality:

```text
expandedTransportK
  = transportIntegral coordinateGap Q curvature derivedC4.
```

Its assumptions are all compact-interval object data:

- the derivative tower `Q' = Q1` through `Q3' = Q4` on `Icc p w`;
- continuity of `Q4` there;
- positivity of `Q` and coordinate curvature there;
- ordered endpoints `p < z < w`.

There is no determinant-sign premise because the central identity is an
equality. Determinant positivity enters only after this equality, in the
strict-transport theorem from P000120.

## Verification

The candidate compiles with the pinned Lean 4.32.0 project in one targeted
invocation. It contains no `sorry`, `admit`, custom axiom declaration,
measure-wrapper assumption, central-identity premise, or global extension.

