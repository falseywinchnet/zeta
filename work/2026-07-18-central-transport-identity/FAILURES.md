# Replay notes and rejected shortcuts

## Failed elaboration paths

1. Automatic continuity did not discharge quotients containing curvature.
   The proof now supplies nonzero denominators from strict curvature positivity.
2. Interval integral congruence exposes membership in the unordered interval.
   The proof converts it explicitly to `Icc p w` using `p < z < w`.
3. Rewriting `C4` did not penetrate the opaque `curvatureWeight` definition.
   The adapter unfolds only that definition and then applies exact pointwise
   equality.

## Rejected proof shapes

- No conclusion is obtained from an inequality that restates an assumption.
- No endpoint or sign claim substitutes for the central equality.
- No tolerance, residual bound, `sorry`, `admit`, or vacuous implication is
  present.
- The independent `C4` is not silently redefined to make the result true; its
  exact identification is visible as the remaining interface.
