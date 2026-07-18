# PO-0038 derivation boundary

The paper supplies four independently defined objects:

\[
A_0(y)=3(y-Q'(y))-Q(y)\frac{\kappa'(y)}{\kappa(y)},
\]

\[
\mathcal H(y)=3y^2-3Q(y)-3yQ'(y)+Q'(y)^2+Q(y)Q''(y),
\]

\[
\mathcal J(y)=y^3-3yQ(y)+Q(y)Q'(y),
\]

and the endpoint expansion

\[
K_{\rm end}=\Lambda+Q'(p)-Q[p,z]
+\frac{U(p,z)-U(z,w)}{\Lambda}
+\frac{U(p,z)-Q(p)(2-Q''(p))}{L\delta}.
\]

The formal proof must establish, in this order:

1. `HasDerivAt J H` from the first two jets of `Q`.
2. `HasDerivAt H (κ * A₀)` from three jets of `Q`,
   `κ = 2-Q″`, and `κ′=-Q‴`.
3. The three weighted integral formulas for `(z-y)`, `(y-p)`, and
   `(w-y)`, retaining their endpoint terms.
4. The actual Bochner expectations against `muMeasure` and `nuMeasure` equal
   the paper's expectation endpoint expression.
5. After the independent triangular endpoint identities for `δ` and `Λ`,
   clearing nonzero denominators makes that endpoint expression equal
   `K_end`.

No definition in this chain may mention the equality it is meant to prove.

