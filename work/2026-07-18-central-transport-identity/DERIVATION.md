# Exact central transport derivation

## Meaning of `gap`

`cdfGap` and `coordinateGap` denote the same signed function:

`F_μ(t) - F_ν(t)`.

The word records subtraction between two CDFs. It does not grant an interval of
acceptable values and does not bound an unresolved discrepancy. The theorem
`cdfGap_eq_coordinateGap` is pointwise equality on the entire integration
interval.

## Equality chain

For `p < z < w`, positive `Q`, positive continuous curvature, and the displayed
derivative tower, the Lean candidate proves:

1. the expanded algebraic transport term equals the concrete expectation
   difference;
2. the expectation difference equals the integral of the measure-backed CDF
   difference against the curvature weight;
3. the measure-backed CDF difference equals `coordinateGap` pointwise;
4. the derivative of `paperPrimitive` equals `primitiveRate`;
5. with `derivedC4 = Q^6 κ^2 primitiveRate`, the curvature weight equals that
   derivative exactly.

Composition yields

`expandedTransportK = ∫ coordinateGap(t) * curvatureWeight(t) dt`.

No sign hypothesis about the CDF difference is used to establish this identity.
No numerical computation, approximation theorem, or admitted proposition occurs
in the candidate.

## Independent `C4` interface

The final adapter accepts an independently defined `C4` only through

`C4(t) = derivedC4(t)` for every `t ∈ [p,w]`.

This isolates the remaining PO-0028-style formula identification. A later round
must prove that exact equality from the independent determinant/cumulant
definition. Replacing it with closeness, a one-sided bound, or positivity would
not close that boundary.
