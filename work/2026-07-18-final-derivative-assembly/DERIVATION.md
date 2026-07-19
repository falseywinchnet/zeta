# Final derivative assembly

## Independent object chain

The final theorem composes three previously checked boundaries:

1. P000100 differentiates the independently defined
   `Psi = Lambda + T Lambda / Lambda` and proves the exact orientation

   `partialXiPsi = -Q(p) N / Lambda²`.

2. P000101 proves the exact equality between the expanded endpoint transport
   object and the deterministic coordinate-gap integral.
3. P000102 starts from the central-moment Hankel determinant and proves that
   its `C4` is exactly the curvature numerator used in that integral.

The present theorem proves the two separately named derived-`C4` functions are
definitionally the same after unfolding, transfers determinant positivity to
the transport weight, derives its continuity, and supplies P000101 to the sole
remaining P000100 premise.

## Final statement

Under the explicit derivative, regularity, ordering, and certified determinant
sign inputs,

`Q(p) * deriv (fun x => coordinatePsi Q Q1 x z w) p < 0`.

The left side is the actual derivative of the independently defined function.
It is not a fresh scalar named `partialXiPsi`.

## Non-vacuity

- The desired derivative inequality is not an assumption.
- Positivity is assumed only for the primary determinant `C4`, the upstream
  certified sign object—not for `N`, the transport integral, or the derivative.
- The central identity is invoked as a theorem, not passed as a premise.
- Curvature continuity is derived from the `Q₂` derivative tower.
- Every connection is equality; there is no tolerance or bounded residual.
