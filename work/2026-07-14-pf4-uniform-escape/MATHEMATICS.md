# Uniform endpoint escape for the PF4 Peano numerator

This note proves two explicit escape lemmas for the exact numerator `J` from
P000031.  It does not infer a sign from a numerical scan.  The only directed
partition is the one-dimensional compact certification of four curvature
constants on `[0,1]`; both unbounded variables are handled by rational
inequalities.

## 1. Common bounds

Write

\[
q=-(\log\Phi)'',\qquad f=q'/q,\qquad h=q-f',
\]

and use `B=A(x,m)`, `C=A(m,r)`, with `M_L,M_R,N_L,N_R` as in P000031.
P000033's compact-plus-tail proof gives `F_1>0` globally.  Therefore
`f'=F_1/q^2>0`.  Since `q` is even, `f` is odd; the tail asymptotics in R143
give `f(u)->2` as `u->+infinity`.  Hence

\[
|f|<2.                                                     \tag{1}
\]

The directed centered-Taylor calculation in `prove_uniform_escape.py`
certifies on `[-1,1]`

\[
18<q<100,\qquad 0<f'<8,\qquad |h'|<200.                   \tag{2}
\]

It follows there that

\[
10<h=q-f'<100.                                            \tag{3}
\]

The same `f'<8` bound is global.  Outside the compact interval, P000033 has
`|F_1-F_{1,1}|<1` and R143 has `q>4X-1` for `X>=23`.  Exact coefficient
shifting proves `F_{1,1}<600`; consequently `f'<601/91^2<1` in either tail.

For every interval, the weighted variance term

\[
V=N-M^2=\operatorname{Var}_q(f)+\mathbb E_q(f')
\]

therefore satisfies

\[
0\le V\le 2^2+8=12.                                      \tag{4}
\]

## 2. Collision-regular right-escape estimate

Assume

\[
-1\le x<m\le1,\qquad X=\pi e^{2r}\ge 2^{15}.
\]

The positive Peano formula for

\[
D=B+f(x)-M_L
\]

is

\[
D={I\over B},\qquad
I=\int_x^m\{A(x,z)q(z)+A(z,m)h(z)\}\,dz.
\]

Put `delta=D/B=I/B^2`.  Equations (2)--(3), integrated before division by
`B^2`, give the gap-independent enclosure

\[
{63\over2500}\le\delta\le {2500\over81}.                 \tag{5}
\]

This is the key collision division: neither bound degenerates as `m-x` tends
to zero.

Under simultaneous translation of `x,z,m`, the two positive integrands obey

\[
|T(A(x,z)q(z))|\le 2\|f\|_\infty A(x,z)q(z),
\]

\[
|T(A(z,m)h(z))|
\le\left(\|f\|_\infty+{\|h'\|_\infty\over h_{\min}}\right)
 A(z,m)h(z).
\]

Thus `|TI|/I<=22`.  Since

\[
H={q(x)I\over B^2},\qquad
T\log H=f(x)+{TI\over I}-2M_L,
\]

we obtain `|T log H|<=28`.  If

\[
\eta={D(f(x)-M_L)+TD\over B},
\]

then exact algebra gives `eta=delta T log H`, and hence

\[
|\eta|\le {70000\over81}.                                \tag{6}
\]

The exact PF4 numerator becomes

\[
{J\over B}=\delta\lambda^2+\lambda\eta-\delta T\lambda. \tag{7}
\]

The tail bound in R143 integrates, using
`23<pi e^2<24`, to

\[
2X-49\le A(x,r)\le2X+201.
\]

Since `|M_L-M_R|<=4`,

\[
2X-53\le\lambda\le2X+205.                                \tag{8}
\]

Also, by (4),

\[
T\lambda=q(r)-q(x)+V_L-V_R\le4X+13.                      \tag{9}
\]

Substitution of (5)--(9) in (7) yields

\[
{J\over B}\ge P_R(X),
\]

\[
P_R(X)={63\over625}X^2-{31340153\over16875}X
       -{35941915673\over202500}.
\]

After `X=2^15+z`, every coefficient is positive:

\[
P_R(2^{15}+z)=
{63\over625}z^2+{80136583\over16875}z
+{9557826593767\over202500}>0.
\]

Therefore `J>0`, equivalently `partial_x Psi<0`, uniformly on this entire
right-escape branch, including the collision `m-x -> 0`.

## 3. Direct parity-correct left-escape estimate

Assume instead

\[
x<m<r,\qquad -1\le m<r\le1,\qquad Y=\pi e^{-2x}\ge2^{15}.
\]

No invariance of `J` under reflection is asserted.  Evenness is used only to
integrate the negative tail.  It gives

\[
2Y-49\le B\le2Y+201,
\]

while `0<C<=200`.  Consequently

\[
\lambda\ge2Y-53,\quad D\ge2Y-53,
\]

\[
\lambda\le2Y+405,\quad D\le2Y+205.                       \tag{10}
\]

For the middle term of `J`, (1) and (4) give

\[
|D(f(x)-M_L)+TD|
\le4(B+4)+(2B+24)=6B+40.                                 \tag{11}
\]

Similarly

\[
|T\lambda|\le q(x)+q(r)+V_L+V_R\le4Y+125.               \tag{12}
\]

Using (10)--(12) directly in

\[
J=D\lambda^2+\lambda\{D(f(x)-M_L)+TD\}-D T\lambda
\]

gives

\[
J\ge P_L(Y)=8Y^3-668Y^2+8432Y-679132.
\]

Again the threshold is proved in one coefficient shift:

\[
P_L(2^{15}+z)=8z^3+785764z^2+25726034160z
+280757992792868>0.
\]

Thus `partial_x Psi<0` on the left-escape branch as well.  In ordinary
coordinates the common threshold is

\[
R_*={1\over2}\log(2^{15}/\pi)=4.626238911\ldots:
\]

the right lemma applies for `r>=R_*`, and the left lemma for `x<=-R_*`, with
the indicated two anchors in `[-1,1]`.

## 4. Scope

These lemmas close the two bounded-anchor escape obligations at the canonical
compact seam `[-1,1]`.  They do not yet prove the two mixed charts when the
non-escaping anchors themselves range through a tail, nor do they certify the
remaining compact boxes.  Those are separate sign patterns and must retain
their orientation.
