# Exact determinant-to-curvature derivation

## Independent starting object

The proof begins with cumulants `c₂,…,c₆`, constructs central moments

`m₀=1, m₁=0, m₂,…,m₆`,

and defines `C4` as the determinant of the resulting `4 × 4` Hankel matrix.
Neither the thirteen-term polynomial nor the curvature expression is used as
the definition of that determinant.

## Equality chain

1. Laplace expansion of the actual matrix determinant, followed by ring
   normalization, gives the thirteen-term cumulant polynomial exactly.
2. Starting from `c₂=-Q`, the derivative tower proves that repeated application
   of `Q d/dy` gives the displayed coordinate cumulants `c₃,…,c₆`.
3. Substitution of those five cumulants into the determinant polynomial gives

   `Q⁶(2-Q₂)² primitiveRate`.

4. Since `κ=2-Q₂`, this is precisely the `derivedC4` used by the P000101
   transport identity.
5. Function extensionality yields pointwise equality everywhere, hence on
   every interval. Rewriting by that function equality gives literal equality
   of the determinant-weighted and primitive-weighted transport integrals.

Strict curvature is used only to establish `2-Q₂ ≠ 0` while clearing the
logarithmic-derivative denominator. It is not used to infer the polynomial
identity from a sign.

## Non-vacuity

The conclusion compares independently defined objects. No theorem assumes
their equality and returns it. No residual is bounded, and no approximation is
introduced. The transport-integral join follows by replacing one weight with a
globally equal function.
