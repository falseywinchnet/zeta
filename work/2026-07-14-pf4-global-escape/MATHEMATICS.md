# Global PF4 escape compactification

## 1. The missing global Peano comparison

Use the notation of P000031 and P000049:

\[
B=A(x,m),\quad D=B+f(x)-M_L,\quad
D={I\over B},
\]

\[
I=\int_x^m\{A(x,z)q(z)+A(z,m)h(z)\}\,dz,
\qquad h=q-f'.
\]

The global bounds from P000033 and P000049 are

\[
q\ge18,\qquad |f|<2,\qquad 0<f'<8.
\]

Therefore

\[
{5\over9}q\le q-8<h\le q.                               \tag{1}
\]

Both Peano integrals can now be evaluated in the curvature coordinate:

\[
\int_x^m A(x,z)q(z)\,dz={B^2\over2},\qquad
\int_x^m A(z,m)q(z)\,dz={B^2\over2}.
\]

Consequently the collision-regular quotient has the global, gap-independent
bound

\[
\boxed{{7\over9}\le\delta:={D\over B}={I\over B^2}\le1.} \tag{2}
\]

This is much stronger than the compact constants in P000049 and does not
require either endpoint of `[x,m]` to be bounded.

## 2. A global translated-rate bound

To differentiate the second Peano density safely, bound the logarithmic rate
of `h`.  On `[-1,1]`, P000049 gives `q<100` and `|h'|<200`; hence

\[
|f''|=|q'-h'|<2q+200<400.
\]

On either tail put `X=pi exp(2|u|)`.  R143 gives

\[
q\ge3X,\qquad |q'|\le9X,\qquad |q''|\le20X.
\]

For the first theta term, exact differentiation gives

\[
0<q_1'''<64X\qquad(X\ge23).
\]

P000033's checked theta-ratio inventory gives
`|q'''-q_1'''|<2^{-12}/X`, so `|q'''|<65X`.  The identity

\[
f''={q'''\over q}-{3q'q''\over q^2}
       +2\left({q'\over q}\right)^3
\]

then yields

\[
|f''|<{65\over3}+60+54={407\over3}<136
\]

on the tails.  Thus `|f''|<400` globally.  From (1),

\[
{|h'|\over h}
\le {2q+400\over q-8}
\le {436\over10}<44.                                    \tag{3}
\]

Under simultaneous translation, the two positive pieces of `I` have relative
rates at most

\[
2|f|\le4,qquad |f|+{|h'|\over h}\le46.
\]

Hence

\[
{|TI|\over I}\le46.
\]

Since `H=q(x)I/B^2` and `M_L` is a weighted mean of `f`,

\[
|T\log H|le |f(x)|+{|TI|\over I}+2|M_L|\le52.           \tag{4}
\]

For

\[
\eta={D(f(x)-M_L)+TD\over B}=\delta T\log H,
\]

(2)--(4) give `|eta|<=52` everywhere.

## 3. Uniform right escape without bounded anchors

The exact numerator identity is

\[
{J\over B}=\delta\lambda^2+\lambda\eta-\delta T\lambda.
\]

The variance identity and the global `f'` bound give

\[
T\lambda=q(r)-q(x)+V_L-V_R\le q(r)+12.
\]

Therefore

\[
{J\over B}\ge {7\over9}\lambda^2-52\lambda-q(r)-12.    \tag{5}
\]

Assume `x<1` and put `X=pi exp(2r)>=64`.  Integrating R143 from `1` to `r`
gives

\[
A(x,r)\ge A(1,r)>2X-49,
\]

so

\[
\lambda=A(x,r)+M_L-M_R>2X-53,qquad q(r)<4X+1.
\]

The quadratic part of (5) is increasing once `lambda>234/7`; at `X=64` the
lower bound for `lambda` is `75`.  Thus

\[
{J\over B}\ge
P_R(X)={28\over9}X^2-{2456\over9}X+{44350\over9}.
\]

The exact shift

\[
P_R(64+z)={28\over9}z^2+{376\over3}z+206
\]

is strictly positive for `z>=0`.  Hence

\[
\boxed{J>0\quad\text{if }x<1\text{ and }\pi e^{2r}\ge64.} \tag{6}
\]

If `x>=1`, R162 already proves the target.  Therefore (6) and R162 together
close the right escape for every ordered triple, regardless of where `m`
lies.

## 4. Left escape that closes the mixed-sign atlas

Let

\[
R_{64}={1\over2}\log(64/\pi)=1.507076598\ldots
\]

and assume

\[
-1\le r\le R_{64},\qquad Y=\pi e^{-2x}\ge64.
\]

Now `[x,r]` contains `[x,-1]`.  Evenness and the negative-tail integral give

\[
A(x,r)>2Y-49,qquad \lambda>2Y-53.
\]

Also `q(r)<257`: use the compact `q<100` bound on `[-1,1]` and R143 on
`[1,R_64]`.  Equation (5) becomes

\[
{J\over B}\ge
P_L(Y)={28\over9}Y^2-{2420\over9}Y+{42046\over9},
\]

and

\[
P_L(64+z)={28\over9}z^2+{388\over3}z+206>0.             \tag{7}
\]

Thus the left escape is uniform in `m` throughout the entire central and
mixed-sign range `r>=-1`.

Combining (6)--(7), every triple with `r>=-1` is either proved or lies in the
single compact ordered chart

\[
\boxed{-R_{64}<x<m<r<R_{64}.}                            \tag{8}
\]

Indeed, `r>=R_64` is the right escape; for `-1<=r<R_64`, `x<=-R_64` is the
left escape.  The only unbounded region not compactified by this theorem is
the all-negative tail `x<m<r<-1`.

## 5. Exact reflection orientation

For the reflected triple

\[
(x,m,r)^*=(-r,-m,-x),
\]

evenness gives

\[
\lambda^*=\lambda,\qquad (T\lambda)^*=-T\lambda.
\]

Define the right Peano factor in the original orientation by

\[
D_R=C-f(r)+M_R,
\]

\[
TD_R=C M_R-f'(r)+N_R-M_R^2.
\]

Exact simultaneous substitution in `prove_global_compactification.py` gives

\[
\boxed{
J(x^*;m^*,r^*)=
D_R\lambda^2
+\lambda\{D_R[-f(r)+M_R]-TD_R\}
+D_R T\lambda.}                                         \tag{9}
\]

Thus `J` is not reflection invariant.  If

\[
\Psi_+=\lambda+T\log\lambda,
\qquad
\Psi_-=\lambda-T\log\lambda,
\]

then

\[
\Psi_+(x^*,m^*,r^*)=\Psi_-(x,m,r),
\]

and the reflected left-end criterion is

\[
\partial_{x^*}\Psi_+(x^*,m^*,r^*)
=-\partial_r\Psi_-(x,m,r).
\]

Consequently the positive-tail certificate reflects to a right-end
monotonicity statement for `Psi_-`; it does not by itself prove the required
left-end monotonicity of `Psi_+` on the all-negative tail.  This names the
remaining mirror lemma exactly rather than hiding it behind parity.

## Status

The central and both mixed-sign escape directions are now analytically
compactified to (8).  Global PF4 is not yet proved.  The remaining unbounded
piece is the all-negative mirror chart, and the compact chart still requires
collision-divided certification plus an origin cone.
