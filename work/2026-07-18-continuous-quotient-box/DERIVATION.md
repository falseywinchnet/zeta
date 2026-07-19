# Derivation ledger

The triple-integral identity can be proved without an abstract Fubini or
determinant-continuity API. Define the explicit alternating trilinear row
determinant `rowDet3`. Integrate one row at a time:

1. integrating the derivative in row three replaces that row by the endpoint
   difference across `[t₂,t₃]`;
2. integrating row two replaces it by the endpoint difference across
   `[t₁,t₂]`;
3. integrating row one replaces it by the endpoint difference across
   `[t₀,t₁]`.

The result is exactly the forward-difference determinant produced by the
normalized four-row algebra of P000105. This route keeps all orientation signs
visible and gives a reusable one-row integration lemma.

## Completed chain

`ContinuousQuotientBox.lean` proves row-slot derivative and integration lemmas
for explicit `3 × 3` and `2 × 2` determinants. It composes them into:

- `normalizedDet4_eq_tripleIntegral`;
- `normalizedDet3_eq_doubleIntegral`;
- strict positivity transfers for both identities;
- `rowDet3_factored` and `rowDet2_factored`;
- `normalizedDet4_pos_of_full_quotient_chain`;
- `rawFactoredDet4_pos_of_full_quotient_chain`.

In the final theorem, the quotient-coordinate relations are exact equalities:

- `B' = A' V`;
- `C' = A' W`;
- `W' = V' q`.

The positive inputs are precisely `A'`, `V'`, and `q'`, corresponding to the
three successive quotient stages. Each strict node separation is used by an
interval strict-positivity theorem. Thus a zero-length box cannot satisfy the
proof by simplification.

## Orientation

All integrals run from the lower node to the upper node. The terminal factor is
`q(r₁)-q(r₀)` for `r₀<r₁`; it is positive when `q'>0`. When instantiated with
the paper's `q = w₄/w₃`, the maintained `∂ξ Ψ<0` result must be translated with
the established `p₄<p₃` orientation before applying this theorem.
