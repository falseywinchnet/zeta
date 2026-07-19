# Replay notes and rejected shortcuts

## Failed elaboration paths

1. Mathlib has explicit determinant formulas through size three, not size four.
   The proof expands the first row and uses the checked size-three formula for
   each minor.
2. The first simplification left `Fin.succAbove` index expressions opaque.
   Unfolding those finite-index maps exposed the actual matrix entries before
   ring normalization.
3. Function-level negation and multiplication elaborate through different
   module instances than pointwise lambdas. Explicit eventual equalities bridge
   those representations without adding a mathematical premise.
4. The derivative expressions retained pointwise `Pi` applications. Expanding
   only those applications allowed ring normalization to verify the coordinate
   recurrence.

## Rejected proof shapes

- Defining `C4` to be the desired curvature numerator.
- Assuming the thirteen-term polynomial rather than deriving it from the
  determinant.
- Using certified positivity of `C4` to infer an equality.
- Testing the identity numerically at samples.
- Hiding a denominator behind an unrestricted field simplification.
- Any `sorry`, `admit`, vacuous implication, tolerance, or residual bound.
