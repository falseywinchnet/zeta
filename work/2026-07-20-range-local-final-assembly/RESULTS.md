# Results

## Closed range mismatch

`kernelCoordinate_Icc_subset_range` proves

```text
Icc (y x) (y r) ⊆ range y
```

for `x ≤ r`, where `y = -S` and `y' = q > 0`.  The proof uses constructed
strict monotonicity and the continuous image of a closed interval.  It does
not assume `range y = ℝ`.

`coordinateJetAndSigns_on_kernelCoordinate_Icc` then restricts the complete
P000118 coordinate jet and the `Q`, coordinate-curvature, and determinant-C4
signs to that interval.

## Top-jet continuity

`coordinateQ4_continuousAt_kernelCoordinate` proves continuity of the
constructed `Q4` at each genuine coordinate point.  It uses the derivative of
the actual coordinate inverse, the actual derivative tower, continuity of
`q4`, and `q > 0`.  It never inspects the canonical inverse extension away from
the range.

`coordinateQ4_continuousOn_kernelCoordinate_Icc` restricts this result to the
ordered coordinate interval.

## Interval-local terminal sign

`coordinatePartialXiPsi_neg_from_determinantC4_on_interval` replaces every
global derivative, continuity, and sign premise of the maintained final
assembly by its `Icc p w` version.  Its proof constructs:

- continuity of `Q`, `Q1`, `Q2`, `Q3`, curvature, and the derived C4 on the
  interval;
- positivity of `delta` and `Lambda` from the local curvature data;
- nonnegativity of the closed gap at the endpoints from the exact zero
  formulas and in the interior from strict gap positivity;
- strict positivity of the actual transport integral and numerator;
- the terminal negative derivative from the exact numerator identity.

There is no free positive scalar and no terminal sign premise.

`actualCoordinatePartialXiPsi_neg` instantiates all derivative, sign, and
top-continuity inputs from the original-variable data at ordered points
`x < m < r`.  Its residual `IntervalObjectBoundary` has exactly three fields:

1. continuity of the independently defined closed coordinate gap on the
   coordinate interval;
2. strict positivity of that gap in the open interval;
3. equality of the independently expanded endpoint object and the derived-C4
   transport integral.

These are object claims, not aliases for the conclusion.  The first two are
already proved in the maintained library under unnecessarily global
continuity assumptions; the third is already proved there under unnecessarily
global jet assumptions.  Localizing those proofs is the next interface task.

## Verification

The preserved P000118 module and this candidate both compile under Lean 4 in
strictly serial targeted invocations.  The candidate contains no `sorry`,
`admit`, axiom declaration, or global-range assumption.

