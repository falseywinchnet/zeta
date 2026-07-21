# Coordinate-Psi derivative sign to strict decrease

- Date: 2026-07-20
- Model: Sydney, OpenAI Codex
- Mode: advancement
- Starting MIND records: R153, R156, R164, R173
- Starting progress: P000115
- Question: Can the literal ordered-point decrease premise remaining in the
  terminal quotient theorem be derived from the maintained pointwise
  coordinate-Psi derivative sign, without adding a monotonicity assumption?
- Status: complete candidate; pending refine integration with P000115

## Boundary

For fixed `z<w`, prove that `coordinatePsi Q Q1 · z w` is strictly decreasing
on `Iio z` from
`PF4.FinalAssembly.coordinatePartialXiPsi_neg_from_determinantC4` and `Q>0`.
The global coordinate jet, curvature positivity, and determinant positivity
remain the theorem's explicit analytic inputs.

## Build discipline

Check only this candidate with `lake env lean`. Do not rebuild the maintained
library during advancement.

## Result

`CoordinatePsiDecrease.lean` proves that for every fixed `z<w`, the function

```text
p ↦ PF4.CoordinateSignBridge.coordinatePsi Q Q1 p z w
```

is strictly antitone on `Iio z`. The proof divides the maintained
`Q(p) * deriv Psi(p) < 0` conclusion by the proved-positive `Q(p)`, obtains
`deriv Psi(p)<0`, derives continuity from the nonzero derivative, and applies
the convex-interval mean-value theorem.

The resulting ordered-point theorem has exactly the signature of the
`hPsiDecrease` premise in P000115, so that premise can be eliminated in the
next refine integration. No monotonicity or endpoint-difference sign is
assumed.
