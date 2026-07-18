# Exact derivation

Write

\[
\Lambda=\operatorname{coordinateLambda}(Q;p,z,w),\qquad
\delta=\operatorname{coordinateDelta}(Q,Q';p,z).
\]

The simultaneous-translation endpoint objects are defined independently by

\[
T\Lambda=U(z,w)-U(p,z),
\]

\[
T\delta=
\frac{U(p,z)-(Q(z)-Q(p))\delta-Q(p)(2-Q''(p))}{z-p},
\]

where `U` is `PF4.TransportObject.chordMoment`. Then

\[
\mathcal N=delta\Lambda^2+Q'(p)\delta\Lambda
 +\Lambda T\delta-\delta T\Lambda
\]

is a definition, not an assumed positive scalar, and

\[
\Psi=\Lambda+\frac{T\Lambda}{\Lambda}
\]

is defined separately.

Direct differentiation of `U(p,z)` from the endpoint formula proves

\[
\partial_p U(p,z)=Q'(p)\delta+T\delta.
\]

Therefore

\[
\partial_p(T\Lambda)=-(Q'(p)\delta+T\delta),
\qquad
\partial_p\Lambda=-\delta,
\]

and the quotient rule gives

\[
\partial_p\Psi=-\frac{\mathcal N}{\Lambda^2}.
\]

Since `partial_xi = Q(p) partial_p`, Lean obtains

\[
\partial_\xi\Psi=-\frac{Q(p)\mathcal N}{\Lambda^2}.
\]

Separately, cleared endpoint algebra proves

\[
\mathcal N=\delta\Lambda\,
  \operatorname{expandedTransportK}.
\]

Thus the only remaining PO-0041 assembly edge is the exact central identity

\[
\operatorname{expandedTransportK}
=\int_p^w\operatorname{coordinateGap}(t)
  \frac{C_4(t)}{Q(t)^6\kappa(t)^2}\,dt.
\]

The final conditional theorem names precisely this equality and derives the
strict sign using the already checked deterministic transport positivity. It
does not assume the sign, positivity of the numerator, or positivity of the
integral.

