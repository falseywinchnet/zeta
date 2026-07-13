# A nested Peano hierarchy for the PF4 criterion

## 1. Full division-free numerator

Use `x<m<r` and

\[
B=A(x,m),\quad C=A(m,r),\quad
M_L=M(x,m),\quad M_R=M(m,r),
\]

with analogous `N_L,N_R`.  Put

\[
\lambda=B+C+M_L-M_R,
\]

\[
T\lambda=q(r)-q(x)+(N_L-M_L^2)-(N_R-M_R^2).
\]

For `f=q'/q`, define

\[
D=B+f(x)-M_L>0,
\qquad
TD=B M_L+f'(x)-N_L+M_L^2.
\]

P000030 gives

\[
H=\partial_b\lambda=\frac{q(x)D}{B}>0,
\qquad
G=H\lambda^2+\lambda TH-H T\lambda.
\]

All occurrences of `D` in the denominator cancel if

\[
\boxed{
J=D\lambda^2
+\lambda\{D[f(x)-M_L]+TD\}
-D\,T\lambda .}
\]

Exact algebra gives

\[
G=\frac{q(x)}B J.
\]

Since `q(x)/B>0`, the original PF4 sign is equivalent to `J>=0`.
After replacing `M,N` by endpoint quotients, `J` has denominator
`B C q(x)` and a 42-term polynomial numerator.  This is substantially
smaller than expanding the original rational derivative.

## 2. Generic two-gap collision

Set

\[
x=m-\beta\varepsilon,\qquad r=m+\alpha\varepsilon,
\qquad \alpha,\beta>0.
\]

The exact generic-jet expansion is

\[
\boxed{
J=
\frac{\beta(\alpha+\beta)^2}{12q(m)^3}
C_4(m)\,\varepsilon^3+O(\varepsilon^4).}
\]

Thus every interior collision direction, not merely a nested limit, has a
strictly positive leading coefficient from the existing `C4>0` certificate.
Combining this with `G=q(x)J/B` and
`lambda=(alpha+beta)C3 epsilon/(2q^2)+O(epsilon^2)` recovers

\[
\partial_b\Psi\longrightarrow \frac{qC_4}{3C_3^2}>0.
\]

The fourth-order coefficient has also been derived exactly.  It is linear in
`alpha` and `beta` after the forced factor `beta(alpha+beta)^2` is removed and
uses the jet through `q^(5)`.  This identifies the derivative order required
for a uniform small-gap remainder bound.

## 3. One-sided edge remainder

At `x=m`, define

\[
P=q(m)-\frac12f'(m)=\frac{C_3(m)}{2q(m)^2}>0,
\]

\[
L=A(m,r)+f(m)-M(m,r)>0.
\]

The edge target is

\[
\partial_x\Psi=-\frac{E}{L^2},
\]

where the denominator-free remainder is

\[
\boxed{E=P L^2+P'L-P\,TL.}
\]

It begins at

\[
E(m,m+a)=\frac{C_4(m)}{12q(m)^3}a^2+O(a^3).
\]

## 4. First edge factorization

Differentiate with respect to `r`.  Put

\[
Q=A(m,r)+M(m,r)-f(r).
\]

The same weighted-mean calculation used in P000030 gives

\[
Q=\frac1A\int_m^r
\{A(z,r)q(z)+A(m,z)h(z)\}\,dz>0,
\]

and hence

\[
R:=L_r=\frac{q(r)Q}{A}>0.
\]

Exact differentiation factors the remainder:

\[
\boxed{
E_r=P R S,
\qquad
S=2L+T\log P-T\log R.}
\]

At collision, `S(m,m)=0`, and

\[
\boxed{
S(m,m+a)=
\frac{2q(m)C_4(m)}{3C_3(m)^2}a+O(a^2).}
\]

Consequently, the single two-point inequality

\[
S_r(m,r)\ge0\qquad(m<r)
\]

would prove the entire one-sided edge: first `S>=0`, then `E_r>=0`, then
`E>=0`.  With endpoint quotients substituted, `S_r` has denominator

\[
A^2q(r)^2Q^2>0
\]

and a 24-term numerator involving the jets through `q'''` at the endpoints.
This is the best current analytic target for the edge.  Direct convexity
`E_{rr}>=0` is stronger and produces a less structured 41-term numerator.

## 5. Reopening the left gap

Because `J=BG/q(x)` and `G` tends to `E` as `b=m-x` tends to zero,

\[
J(0)=0,\qquad J_b(0)=E.
\]

Exact endpoint differentiation gives a rational `J_b` with a 74-term
numerator.  Therefore the second sufficient inequality

\[
J_b(x,m,r)\ge0
\]

would extend the proved edge into the full three-point domain:

\[
J(b)=\int_0^bJ_b(u)\,du\ge0.
\]

This is a stronger monotonicity statement than the original target and is not
yet proved.  It is retained because it creates a nested Peano proof with exact
positive collision data.

## 6. Sufficient Peano theorem

For the Riemann curvature, the following two inequalities are sufficient for
global PF4:

\[
S_r(m,r)\ge0\quad(m<r),
\qquad
J_b(x,m,r)\ge0\quad(x<m<r).
\]

Indeed:

1. `S(m,m)=0` and `S_r>=0` imply `S>=0`.
2. `E(m,m)=0` and `E_r=PRS` with `P,R>0` imply `E>=0`.
3. `J(0)=0`, `J_b(0)=E`, and `J_b>=0` imply `J>=0`.
4. `G=q(x)J/B>=0`, hence `partial_b Psi>=0` and
   `partial_x Psi<=0`.

The theorem is a reduction, not a proof that the two displayed densities are
positive.

## 7. Exact exponential model at every level

For `q(t)=c exp(k t)`:

\[
M=k,\quad N=k^2,\quad h=q,
\]

and all new densities collapse to manifestly positive expressions:

\[
E=q(m)A(m,r)^2,
\quad S=2A(m,r),
\quad S_r=2q(r),
\]

\[
J=B(B+C)^2,
\quad
J_b=q(x)(B+C)(3B+C).
\]

These identities are checked symbolically.  They give nonzero margins for an
analytic same-tail perturbation, except when gaps coalesce; the collision
expansions above cover that degeneracy.

