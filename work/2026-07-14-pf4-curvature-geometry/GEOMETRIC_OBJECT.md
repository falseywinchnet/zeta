# The score-transport object and its two-point lift

Everything in this note is advancement-round mathematics.  Exact algebraic
identities are separated from conjectural implications.

## 1. One-point score geometry

Write the positive even kernel as `Phi=exp(-V)` and put

\[
s=(\log\Phi)',\qquad y=-s=V',\qquad q=y'=V'',
\qquad Q(y(t))=q(t).
\]

The established strict log-concavity makes `t -> y` a global increasing
coordinate.  In this coordinate CERT9 uses

\[
 \kappa=2-Q'',
 \qquad
 A(y)=3\{y-Q'(y)\}-Q(y)(\log\kappa)'(y),
\]

and the exact identity

\[
 \boxed{A'(y)=D(y)=\frac{C_4(y)}{Q(y)^6\kappa(y)^2}>0.}
\tag{1}
\]

Evenness makes `y(t)` odd, `Q,kappa,D` even, and `A` odd.  Thus exact PF4
does more than provide a sign: it produces a second global increasing
coordinate

\[
 \boxed{a(t)=A(y(t)),\qquad a'(t)=Q(y(t))D(y(t))>0.}
\tag{2}
\]

Every CERT9 transport margin is an average of the positive measure

\[
 dA=D(y)\,dy.
\]

This is the geometric object behind the order-four proof.  PF4 sees positivity
of this measure.  Any additional invariant must see its shape, its interaction
with convolution/correlation, or arithmetic data that PF4 discards.

## 2. An exact PF4-adapted basis

Fix `R>0` and define

\[
 \zeta_R(t)=\frac{a(t)}{a(R)}:[-R,R]\longrightarrow[-1,1].
\]

If `(h_n)` is any orthonormal basis of `L2(-1,1)`, then

\[
 \boxed{
 \psi_{n,R}(t)=
 \sqrt{\frac{a'(t)}{a(R)}}\,
 h_n\!\left(\frac{a(t)}{a(R)}\right)
 }
\tag{3}
\]

is orthonormal in `L2(-R,R)`.  Indeed `d zeta_R=a'(t)dt/a(R)`, so (3) is
just the unitary pullback by the transport coordinate.  Choosing Dirichlet
sines for `h_n` gives a conforming endpoint-vanishing basis; choosing Legendre
modes gives a polynomial transport basis.

Equation (3) is exact.  Whether it improves a localized-Weil complement bound
is untested: that application requires an explicit derivation connecting the
kernel coordinate `t` to Suzuki's operator coordinate, not merely a numerical
basis substitution.

## 3. The exact Fourier correlation has its own score coordinate

Dimitrov and Xu's second correlation of `Phi` is

\[
 \nu_2(T)=\int_{\mathbb R}(T-2u)^2\Phi(T-u)\Phi(u)\,du.
\tag{4}
\]

Put `T=2x` and `u=x+r`.  Then

\[
 \boxed{
 \nu_2(2x)=4\int_{\mathbb R}r^2 P_x(r)\,dr,
 \qquad P_x(r)=\Phi(x-r)\Phi(x+r).
 }
\tag{5}
\]

The negative logarithmic derivative of the pair density is

\[
 \eta_x(r)=s(x-r)-s(x+r),
\]

and it satisfies the exact global monotonicity law

\[
 \boxed{\eta_x'(r)=q(x-r)+q(x+r)>0.}
\tag{6}
\]

Thus every correlation fiber has a global score coordinate.  If `R_x` is the
inverse of `eta_x` and

\[
 Q_x(\eta)=q(x-R_x(\eta))+q(x+R_x(\eta)),
\]

then (5) becomes

\[
 \boxed{
 \nu_2(2x)=4\int_{\mathbb R}
 \frac{R_x(\eta)^2
 \Phi(x-R_x(\eta))\Phi(x+R_x(\eta))}{Q_x(\eta)}\,d\eta.
 }
\tag{7}
\]

This is the first direct bridge found in this round: the correlation object
whose translate density characterizes Fourier real-rootedness is itself a
family of curvature-coordinate geometries.

## 4. Wronskian identity and the exact RH edge

For

\[
 F(z)=\int_{\mathbb R}\Phi(t)e^{-izt}\,dt,
\]

symmetrizing the product integrals gives

\[
 \boxed{
 F(z)F''(z)-F'(z)^2=-\frac12\widehat{\nu_2}(z).
 }
\tag{8}
\]

Multiplication of (4) by `cosh(T beta)` gives

\[
 \mathcal F[\cosh(\beta\,\cdot)\nu_2](z)
 =\frac12\{\widehat{\nu_2}(z+i\beta)
            +\widehat{\nu_2}(z-i\beta)\}.
\tag{9}
\]

Dimitrov--Xu prove, under the hypotheses satisfied by the Riemann kernel, that
RH is equivalent to density in `L1(R)` of the translates of

\[
 K_\beta(T)=\cosh(\beta T)\nu_2(T)
\]

for every `0<|beta|<1/2`.  By Wiener's theorem this is equivalent to the
right side of (9) having no real zeros.  Equations (5)--(7) place that exact
edge inside a pair-score geometry rather than the PF hierarchy.

## 5. Outward score-convexity and closure under pairing

The Riemann kernel has the additional established inequality

\[
 Q''\ge0.
\]

Since

\[
 Q''(y(t))=\frac{(\log q)''(t)}{q(t)},
\]

this says that the curvature `q` is log-convex in the original coordinate.
It is independent of `D>0`.

There is a useful exact closure lemma.  If `q` is positive and log-convex,
then for every fixed `x`

\[
 q_x(r)=q(x-r)+q(x+r)
\]

is log-convex, because sums of positive log-convex functions are log-convex.
By (6), `q_x` is precisely the curvature of the pair-score coordinate.
Therefore outward score-convexity propagates from the one-point kernel to
every Dimitrov--Xu correlation fiber.

This does not prove the Wiener nonvanishing in (9): the second-moment mixture
over `r` in (5) can lose information.  It does, however, identify a concrete
place for the next theorem.  A successful bridge would show that

\[
 \text{PF4 transport }(D>0)
 +\text{ pairwise outward score-convexity}
 +\text{ one explicit mixing inequality}
\]

forces the nonvanishing in (9).

## 6. Candidate additional property

The least circular candidate exposed by this round is **correlation-coherent
score convexity**:

1. `D=A'>0` (exact PF4 transport);
2. `Q''>=0`, equivalently `log q` convex;
3. the pair-score family (6) obeys a uniform mixing inequality strong enough
   to prevent real zeros of every tilted transform (9).

The third clause is deliberately not named as a theorem.  Replacing it by the
bare nonvanishing of (9) would merely restate RH.  The next mathematical task
is to find a checkable inequality on the pair family in (7)—for example a
variation-diminishing or coercive estimate—that implies Wiener nondegeneracy.

