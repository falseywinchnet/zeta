# Results

## Local strict closed gap

`coordinateGap_pos_of_normalized_on_Icc` reconstructs the maintained
one-crossing proof with only

```text
ContinuousOn (curvature Q2) (Icc p w).
```

It retains both cases of the proof:

- before the unique left-density crossing, the prefix integral is strictly
  positive;
- after the crossing, exact total-mass cancellation leaves a nonnegative
  reverse left tail plus a strictly positive right tail.

No probability variable, symbolic positive endpoint mass, or desired gap sign
is introduced. `coordinateGap_pos_on_Icc` derives the normalizers and their
mass identities from the local jet, so its conclusion has no detached
normalization premise.

## Local continuity

`coordinateGap_continuousOn_of_normalized` proves the two closed branches meet
at `z` using their exact integral forms and mass cancellation. It combines the
locally continuous branches with `ContinuousOn.if`; values of `Q`, `Q1`, or
`Q2` outside `Icc p w` are never inspected.

`coordinateGap_continuousOn_Icc` derives the two mass identities from the
local curvature jet and removes the normalization premises.

## Actual coordinate specialization

`actualCoordinateGap_properties` proves both continuity and strict interior
positivity for the coordinate interval obtained from original points
`x < m < r`. It constructs:

- containment of the coordinate interval in the genuine range;
- the `Q`, `Q1`, and `Q2` coordinate derivatives there;
- positive coordinate curvature from the actual `F2` sign;
- local curvature continuity from the constructed `Q2` derivative.

It requires the original derivative tower only through `q2' = q3`, together
with `q > 0` and `F2 > 0`.

## One-boundary terminal theorem

`coordinatePartialXiPsi_neg_on_Icc_of_centralIdentity` reconstructs the strict
terminal derivative proof after deriving both gap properties internally. Its
only unresolved object premise is

```text
expandedTransportK = transportIntegral coordinateGap Q curvature derivedC4.
```

This is an equality of independently defined objects, not a sign, positive
scalar, monotonicity statement, or restatement of the conclusion. All other
calculus, determinant, normalizer, continuity, and strict transport inputs are
derived on the compact interval.

## Verification

The P000118 dependency and `LocalGapClosure.lean` compile through serialized,
targeted Lean invocations. The new source contains no `sorry`, `admit`, custom
axiom declaration, global-range assumption, or project-wide build step.

