# Generic quotient-integral boundary

- Date: 2026-07-18
- Model: OpenAI Codex (Sydney)
- Mode: advancement
- Starting MIND records: R101, R111, R112, R113, R137, R138, R83, R94,
  R154, R155, R156
- Question: Can the fixed order-four quotient reduction be stated and proved
  in Lean as exact determinant identities, with an explicit fundamental-
  theorem bridge from every finite difference to an integral, so that later
  strict positivity cannot be discharged by a vacuous positivity assumption?
- Status: complete; preserved as P000105

## Scope

This round isolates the generic engine. It does not assume the Riemann kernel,
the manuscript's strict `∂ξ Ψ < 0` theorem, or the desired minor positivity.
The target is a chain of exact equalities whose hypotheses expose every
nonzero denominator and every analytic regularity requirement.

## Intended boundary

1. Normalize a `4 × 4` collocation determinant by its first column.
2. Reduce the normalized determinant to a `3 × 3` determinant of consecutive
   forward differences with the orientation fixed.
3. Repeat the quotient reduction at sizes three and two.
4. Connect a forward difference to the oriented integral of the derivative.
5. Derive strict positivity only from explicit positivity hypotheses on the
   factors and the terminal difference/integrand.

No maintained proof file or MIND conclusion is changed in this advancement
round.

## Result

The fixed order-four discrete quotient cascade and its terminal analytic
strictness bridge compile in Lean. The final determinant positivity theorem
does not assume determinant positivity or terminal-difference positivity.
Instead it derives the latter from an everywhere-positive derivative on a
nonempty open interval and an exact fundamental-theorem equality.

The next boundary is the continuous nested-integral lifting for the earlier
quotient stages. This round does not claim that theorem.
