# Exact transport-kernel identity

Let `p<z<w`, `L=z-p`, `R=w-z`, and retain the curvature-coordinate notation

\[
 \rho=1-Q'',\qquad \kappa=2-Q''=1+\rho>0,
 \qquad a=Q(\log\kappa)'.
\]

The local order-four density is

\[
 D(y):=3\rho(y)-a'(y)
      =\frac{C_4(y)}{Q(y)^6\kappa(y)^2}.                 \tag{1}
\]

For the Riemann kernel, R152 gives `C4>0` globally, hence `D>0`.

## The two triangular probability measures

Write

\[
 \delta=\frac1{L^2}\int_p^z(z-y)\kappa(y)\,dy,
\]

\[
 \lambda_L=\frac1L\int_p^z(y-p)\kappa(y)\,dy,
 \qquad
 \lambda_R=\frac1R\int_z^w(w-y)\kappa(y)\,dy,
 \qquad \Lambda=\lambda_L+\lambda_R.
\]

Define probability measures on `[p,w]` by

\[
 d\mu(y)=\frac{(z-y)\kappa(y)}{L^2\delta}\,1_{[p,z]}(y)\,dy,       \tag{2}
\]

\[
 d\nu(y)=
 \frac{(y-p)\kappa(y)}{L\Lambda}\,1_{[p,z]}(y)\,dy
 +\frac{(w-y)\kappa(y)}{R\Lambda}\,1_{[z,w]}(y)\,dy.             \tag{3}
\]

These are exactly the normalized triangular measures already present in
`delta` and `Lambda`.

For an interval `[c,d]`, put

\[
 V_{cd}(y)=Q(c)+(y-c)Q[c,d],\qquad E_{cd}(y)=V_{cd}(y)-Q(y).
\]

The normalized endpoint flow transports an interior point with velocity
`V_cd`.  Therefore differentiation under the integrals gives

\[
 \mathcal T\log\delta=\mathbb E_\mu[V_{pz}(\log\kappa)'],          \tag{4}
\]

\[
 \mathcal T\log\Lambda=
 \mathbb E_\nu[M+V(\log\kappa)'],                                \tag{5}
\]

where `(M,V)=(Q[p,z],V_pz)` on the left component of `nu` and
`(M,V)=(Q[z,w],V_zw)` on the right component.

## Exact cancellation lemma

Set

\[
 b(y)=y-Q'(y),\qquad A(y)=3b(y)-a(y).
\]

Then `A'=D`.  Direct integration by parts in (2)--(5), using

\[
 E_{cd}(c)=E_{cd}(d)=0,\quad
 E_{cd}'=Q[c,d]-Q',\quad
 \kappa'= -Q''',\quad \rho=b',                                  \tag{6}
\]

gives the transport identity

\[
 \boxed{
 \Lambda+Q'(p)+\mathcal T\log\delta-\mathcal T\log\Lambda
 =\mathbb E_\nu[A]-\mathbb E_\mu[A].}                            \tag{7}
\]

The cancellation can be displayed before the final integration.  Since
`V=Q+E`, equations (4)--(5) first give

\[
 K=B_0+\mathbb E_\mu[a]-\mathbb E_\nu[a]
   +\mathbb E_\mu[E(\log\kappa)']
   -\mathbb E_\nu[E(\log\kappa)'],
\]

where

\[
 B_0=\Lambda+Q'(p)-\mathbb E_\nu[M].
\]

The apparent remainder vanishes by (6):

\[
 \boxed{
 B_0+\mathbb E_\mu[E(\log\kappa)']
       -\mathbb E_\nu[E(\log\kappa)']
 =3\{\mathbb E_\nu[b]-\mathbb E_\mu[b]\}.}                     \tag{8}
\]

Here is an explicit integration-by-parts audit of that cancellation.  The
weighted density of `A` has the elementary primitive

\[
 \kappa A=3(2-Q'')(y-Q')+Q Q'''=H',                         \tag{9}
\]

\[
 H(y)=3y^2-3Q(y)-3yQ'(y)+Q'(y)^2+Q(y)Q''(y).
\]

Put `I_L=integral_p^z H` and `I_R=integral_z^w H`.  Integrating the linear
weights in (2)--(3) once gives

\[
 \mathbb E_\nu[A]-\mathbb E_\mu[A]
 =\frac{-I_L/L+I_R/R}{\Lambda}
  +\frac{L H(p)-I_L}{L^2\delta}.                              \tag{10}
\]

Using `Q''=2-kappa` in `H` and the definition of the chord moment `U`, the
right side of (10) is exactly

\[
 \Lambda+Q'(p)-Q[p,z]
 +\frac{U(p,z)-U(z,w)}\Lambda
 +\frac{U(p,z)-Q(p)\kappa(p)}{L\delta}.                       \tag{11}
\]

Equation (11) is `N/(delta Lambda)` obtained directly by dividing equation
(8) of P000057 by `delta Lambda`.  This proves (7) and (8) for arbitrary
smooth `Q`; no polynomial assumption and no bound is used.

Substitution of (8) is exactly (7).  No bound is used in this cancellation.
The companion script checks (7)--(8) identically for a generic degree-five
polynomial `Q` with symbolic interval lengths `L,R`, and independently for a
non-polynomial analytic `Q` at 30 decimal digits.

## The crossing kernel is nonnegative

Let `F_mu,F_nu` be the CDFs of (2)--(3) and define

\[
 W(t)=F_\mu(t)-F_\nu(t).                                        \tag{12}
\]

On `[z,w]`, `F_mu=1`, so `W=1-F_nu>=0`.  On `[p,z]` the two densities have
ratio

\[
 \frac{d\mu/dy}{d\nu/dy}
 =\frac{\Lambda(z-y)}{L\delta(y-p)},                             \tag{13}
\]

which decreases strictly from infinity to zero.  Consequently `W'` changes
sign exactly once, from positive to negative.  But

\[
 W(p)=0,\qquad W(z)=\nu([z,w])>0.
\]

It follows that `W(t)>0` for every `p<t<w`, with `W(p)=W(w)=0`.  Thus `mu`
is stochastically to the left of `nu`.

Integrating (7) against the CDFs now yields the closed formula

\[
 \boxed{
 K:=\Lambda+Q'(p)+\mathcal T\log\delta-\mathcal T\log\Lambda
 =\int_p^w W(t)D(t)\,dt.}                                      \tag{14}
\]

Since the P000057 numerator satisfies

\[
 \mathcal N=\delta\Lambda K,
\]

we obtain

\[
 \boxed{
 \mathcal N=\delta\Lambda\int_p^w
 W(t)\frac{C_4(t)}{Q(t)^6\kappa(t)^2}\,dt.}                    \tag{15}
\]

Every factor in (15) is strictly positive away from the harmless endpoint
zeros of `W`.

## Positive double-integral form

For the independent product coupling, (14) is

\[
 K=\iint\left(\int_u^vD(t)\,dt\right)d\mu(u)d\nu(v).           \tag{16}
\]

The fiber in (16) is sign-indefinite when `u>v`; this occurs only in the
left-left component.  It is the exact apparent sign-indefinite kernel.  It
does not survive integration.

Indeed, stochastic dominance supplies the monotone quantile coupling

\[
 U(s)=F_\mu^{-1}(s),\qquad V(s)=F_\nu^{-1}(s),\qquad U(s)\le V(s).
\]

Under this coupling the same quantity is the genuinely positive double
integral

\[
 \boxed{
 K=\int_0^1\int_{U(s)}^{V(s)}D(t)\,dt\,ds>0.}                  \tag{17}
\]

Thus the local transport inequality integrates globally.  There is no
remaining outer band, seam, anchor chart, or compact box domain in this
reduction.

## Consequence pending audit

Equations (1), (15), R152, and the PF4 equivalence R156 together imply strict
global PF4 for the Riemann kernel.  This implication is an advancement-round
result.  It must be independently audited against the sign conventions and
normalizations in CERT3 and CERT5 before it is established in MIND.
