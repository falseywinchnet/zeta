# Analytic structure of the three-point inequality

## 1. Coordinates and the positive densities already available

Let

\[
s=(\log\Phi)',\qquad q=-s'>0,\qquad f=\frac{q'}q,
\]

and, for `u<v`,

\[
A(u,v)=\int_u^v q,\qquad
M(u,v)=\frac{q(v)-q(u)}{A(u,v)}.
\]

Thus `M(u,v)` is the `q`-weighted mean of `f` on `[u,v]`.  Put

\[
h=q-f'=q-\frac{qq''-(q')^2}{q^2}=\frac{F_2}{q^2}.
\]

The established PF3 certificate gives `q>0` and `F2>0`, hence `h>0`, on the
whole line.

Write

\[
x=\xi,\quad B=A(x,m),\quad C=A(m,r),\quad
\lambda=\Lambda(x;m,r)=A(x,r)+M(x,m)-M(m,r).
\]

Use gap coordinates `x=m-b`, `r=m+a`.  The translation generator `T` moves
all three points and commutes with `partial_b`.

## 2. Peano representation of Lambda

Since `M` is a weighted mean,

\[
M(x,m)-M(m,r)
=-\frac1{BC}\int_x^m\int_m^r q(u)q(v)
  \int_u^v f'(z)\,dz\,dv\,du.
\]

Changing integration order gives the exact one-dimensional formula

\[
\lambda=
\int_x^m\left[q(z)-\frac{A(x,z)}Bf'(z)\right]dz
+\int_m^r\left[q(z)-\frac{A(z,r)}Cf'(z)\right]dz.
\]

Each bracket is a convex combination of `q` and `h=q-f'`:

\[
q-wf'=(1-w)q+wh,\qquad 0\le w\le1.
\]

This recovers `lambda>0` without a scan and exposes the natural positive
densities for a higher-order Peano argument.

## 3. Endpoint derivative and the residual rate inequality

Define

\[
D=B+f(x)-M(x,m).
\]

Another change of integration order gives

\[
D=\frac1B\int_x^m
\big[A(x,z)q(z)+A(z,m)h(z)\big],dz>0.
\]

Direct differentiation now factors the left-gap derivative:

\[
H:=\partial_b\lambda=-\partial_x\lambda
=\frac{q(x)D}{B}>0.
\]

For `Psi=lambda+T log lambda`, commutation of `T` and `partial_b` gives

\[
\partial_b\Psi
=H+T\left(\frac H\lambda\right)
=\frac H\lambda K,
\]

where

\[
K:=\lambda+T\log H-T\log\lambda.
\]

Therefore the certified PF4 target has the exactly equivalent form

\[
\partial_x\Psi\le0\quad\Longleftrightarrow\quad K\ge0.
\]

All prefactors have already been proved positive.  A denominator-free target
for an integral representation is

\[
G:=H\lambda^2+\lambda,TH-H,T\lambda
=\lambda^2\partial_b\Psi.
\]

This is the useful new boundary: the problem is no longer to control the sign
of a cancellation-prone rational expression, but to prove positivity of the
single determinant-like quantity

\[
G=H\lambda^2+
\det\begin{pmatrix}\lambda&T\lambda\\H&TH\end{pmatrix}.
\]

The most promising route is to insert the positive Peano formulas for
`lambda` and `H` into `G` and seek a symmetrized multiple-integral density in
`q`, `h`, and one genuinely order-four local remainder.

## 4. One-sided and full collision boundaries

Let `x` approach `m` while `r` stays fixed.  Set

\[
P=q-\frac12f'=\frac{q+h}{2}
=\frac{2q^3-qq''+(q')^2}{2q^2}
=\frac{C_3}{2q^2}>0
\]

at `m`, and

\[
L=A(m,r)+f(m)-M(m,r).
\]

The same Peano calculation gives

\[
L=\frac1{A(m,r)}\int_m^r
\big[A(m,z)q(z)+A(z,r)h(z)\big],dz>0.
\]

The boundary target is exactly

\[
\lim_{x\uparrow m}\partial_x\Psi
=-\frac PL\left(L+\frac{P'}P-\frac{TL}{L}\right).
\]

Thus the first nontrivial boundary is a two-point rate comparison.  If the
remaining point also approaches `m`, generic Taylor algebra yields

\[
\boxed{
\lim_{x,m,r\to t}\partial_x\Psi
=-\frac{q(t)C_4(t)}{3C_3(t)^2}.}
\]

The approach here is the nested collision `x -> m` followed by `r -> m`; the
smooth Wronskian limit fixes the same value for the confluent boundary.  The
identity is checked exactly in `derive_reductions.py`.  Existing certificates
give `q>0`, `C3>0`, and `C4>0`, so the fully confluent target is strictly
negative for every real `t`.  This is proof support, not evidence from the old
scan.

## 5. Exact tail model

For the one-mode curvature model

\[
q(t)=c e^{kt},\qquad s(t)=-q(t)/k,
\]

every interval has `M=k`, `N=k^2`.  Consequently

\[
\lambda=A(x,r),\qquad T\lambda=k\lambda,qquad
\Psi=\lambda+k,qquad \partial_x\Psi=-q(x)<0.
\]

The reflected exponential gives the negative tail.  The Riemann curvature has
`q=4x+O(x^{-1})`, `q'=8x+O(x^{-1})`, and `q''=16x+O(x^{-1})` in the positive
tail, so this model identifies the correct dominant term and margin.  A valid
tail proof must perturb the division-free `G`, not the original rational
formula, because direct denominator estimates are nonuniform when gaps
coalesce.

## 6. Prioritized analytic routes

### Route A: positive Peano density for G

Expand `G` using the integral formulas for `lambda`, `H`, and their translated
derivatives.  Symmetrize before estimating.  The desired endpoint density is
forced by the collision identity to reduce to `q C4`; lower-order pieces
should reduce to products of `q`, `h`, and `C3`.  A same-sign representation
would prove the theorem globally and is the highest-value route.

### Route B: prove the two-point edge, then a nonlocal comparison

First prove

\[
L+P'/P-TL/L\ge0
\]

for every `m<r`, using the positive integral for `L`.  This closes the
one-sided collision boundary analytically.  Extending from that boundary must
use a comparison for `G`; simple monotonicity in the remaining gap is not
assumed, because the order-five failure warns that the quotient ladder cannot
remain sign-preserving indefinitely.

### Route C: analytic escape lemmas around the exponential model

Use the existing theta-tail enclosures in the division-free expression `G`.
Split by gap size only to handle removable collision singularities:

1. small gaps: Taylor-expand `G`; the leading term is controlled by `C4`;
2. resolved gaps in one tail: perturb the exact exponential identity;
3. one or both endpoints escaping with the middle point bounded: use dominance
   of the endpoint curvature and reflection.

This is a finite family of analytic estimates, not a sweep of point samples.

### Route D: theta-mode same-sign decomposition on the compact core

Csordas--Varga successfully isolate the first theta mode and dominate the
remaining modes to prove a stronger radial concavity property of `Phi`.
Attempt the same at the level of the division-free `G`.  The target is a
finite collection of explicit mode-pair or mode-triple inequalities.  Directed
arithmetic is appropriate only after such a decomposition reduces the proof
to bounded one-dimensional remainders; a three-dimensional cell census would
not explain the sign.

## 7. What is not a proof route

- The old 8.4-million-point sweep supplies no part of these deductions.
- `C4(t)>0` alone is only the fully confluent boundary, not the global
  three-point inequality.
- The Csordas--Varga concavity theorem controls a lower-order radial mean of
  `q`; it does not by itself control `K` or `G`.
- Direct evaluation of the rational `partial_x Psi` is the wrong object for
  tail perturbations and collision limits.  Use `G`.

