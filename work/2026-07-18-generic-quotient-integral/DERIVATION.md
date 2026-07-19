# Derivation ledger

The proof is intentionally split into algebra and analysis.

## Algebraic layer

For rows `(1,aᵢ,bᵢ,cᵢ)`, subtracting row `i` from row `i+1` and expanding
along the first column leaves the `3 × 3` matrix of consecutive differences.
This fixes the sign: increasing point order corresponds to forward differences.

Before that row operation, dividing row `i` by its first entry contributes the
product of all first entries. The same normalization-and-difference operation
is then repeated on the `3 × 3` and `2 × 2` determinants.

## Analytic layer

For `x < y`, the fundamental theorem gives

`f(y) - f(x) = ∫ t in x..y, f'(t)`.

Thus the terminal forward difference is not introduced as a positive symbol:
it is connected by equality to an integral. Strict positivity must subsequently
come from positivity of the integrand on a nondegenerate interval (or another
non-vacuous theorem implying that integral is positive).

## Lean result

`GenericQuotientIntegral.lean` proves:

- exact `4 × 4 → 3 × 3` forward-difference reduction;
- exact row-factor extraction at sizes four and three;
- the exact terminal size-two identity;
- a single composed identity
  `det₄ = (∏rᵢ)(∏vᵢ)(∏wᵢ)(q₁-q₀)` in cumulative quotient coordinates;
- the fundamental-theorem equality for `q(y)-q(x)`;
- strict positivity of that difference from `x<y` and `q'>0` on `(x,y)`;
- strict positivity of the original determinant without assuming its sign.

All theorem hypotheses are computationally and logically used. In particular,
the interval-length hypothesis is consumed by Mathlib's strict integral
positivity theorem; replacing `x<y` by `x≤y` would not prove strictness.

## Remaining boundary

The cumulative quotient theorem is a discrete divided-difference engine. The
paper's continuous proof additionally needs a fixed-order nested-integral
theorem that turns the first- and second-stage quotient factors into integrals
over their ordered boxes. That lifting is not claimed here. It is the next
generic boundary before the Riemann-specific `∂ξ Ψ < 0` result can feed the
collocation minor theorem directly.
