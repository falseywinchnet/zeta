# A finite PF1 reduction for the reciprocal-xi kernel

## Object

Let

\[
 A(t)=\frac{1}{\xi(1/2+t)},\qquad
 L(x)=\frac{1}{2\pi}\int_{\mathbb R}A(t)e^{-itx}\,dt.
\]

The function `A` is positive and even on the real axis and decays faster than
exponentially.  Thus `L` is real and even.  The PF1 assertion is exactly
`L(x)>=0`.

This note reduces strict PF1 to six deliberately coarse enclosures and a
standard finite zero statement.  The algebraic glue is exact.  The enclosures
are now certified by `CERT13` and `CERT14`, and `CERT15` seals the global
compact/tail implication; the resulting strict PF1 theorem is recorded as
`R177`.

## Compact interval

For `j=0,1,2,3`, put

\[
 M_{2j}=\frac1\pi\int_0^\infty \frac{t^{2j}}{\xi(1/2+t)}\,dt.
\]

The global Taylor inequality

\[
 \cos y\ge 1-\frac{y^2}{2!}+\frac{y^4}{4!}-\frac{y^6}{6!}
 \qquad (y\in\mathbb R)
\]

follows by the usual alternating pair induction: the even truncation is an
upper bound, its negative second derivative proves that the following odd
truncation is a lower bound, and conversely.  Integration against `A(t)>0`
therefore gives

\[
 L(x)\ge M_0-\frac{M_2x^2}{2!}
       +\frac{M_4x^4}{4!}-\frac{M_6x^6}{6!}.
\]

It is enough to certify

\[
 M_0>\frac{19}{5},\qquad M_2<91,\qquad
 M_4>6700,\qquad M_6<900000.                 \tag{C}
\]

Set `u=(10x/3)^2`.  On `0<=x<=3/10`, the resulting lower polynomial has
power coefficients

\[
 \frac{19}{5},\quad-\frac{819}{200},\quad
 \frac{1809}{800},\quad-\frac{729}{800},
\]

and degree-three Bernstein coefficients on `0<=u<=1`

\[
 \frac{19}{5},\quad\frac{487}{200},\quad
 \frac{1459}{800},\quad\frac{211}{200}.
\]

All are positive.  Hence (C) proves `L(x)>0` for `|x|<=3/10`.

The exploratory moment values are

\[
 M_0=3.820844218\ldots,\quad M_2=90.39147140\ldots,
\]
\[
 M_4=6761.173653\ldots,\quad M_6=884160.3019\ldots.
\]

## One-residue tail

Write `Xi(z)=xi(1/2+iz)`.  Let `gamma_1` be its first positive zero and

\[
 c_1=-\frac1{\Xi'(\gamma_1)},\qquad
 I_{16}=\frac1{2\pi}\int_{\mathbb R}
       \left|\frac1{\xi(1/2+u-16i)}\right|\,du.
\]

Assume the strip between imaginary heights `0` and `-16` contains only the
simple pole `-i gamma_1`.  Moving the Fourier contour down to height `-16`
gives, for `x>0`,

\[
 L(x)=c_1e^{-\gamma_1x}+R_{16}(x),\qquad
 |R_{16}(x)|\le I_{16}e^{-16x}.               \tag{T}
\]

It is enough to certify

\[
 \gamma_1<14.14,\qquad c_1>700,
 \qquad I_{16}<1200.                          \tag{R}
\]

For `x>=3/10`, (T) and (R) imply

\[
 L(x)>e^{-\gamma_1x}
 \left(700-1200e^{-(16-\gamma_1)x}\right).
\]

Now `(16-gamma_1)x > (16-14.14)(3/10)=279/500`, and

\[
 e^{279/500}>
 1+\frac{279}{500}+\frac1{2!}\left(\frac{279}{500}\right)^2
 +\frac1{3!}\left(\frac{279}{500}\right)^3
 =\frac{435659713}{250000000}>\frac{12}{7}.
\]

Thus the bracket is positive and `L(x)>0` for `x>=3/10`.  Evenness supplies
the negative half-line.

The exploratory values are

\[
 \gamma_1=14.13472514\ldots,\qquad
 c_1=723.2126958\ldots,\qquad
 I_{16}=1159.866364\ldots.
\]

## Certificate boundary

The following components are independently certified:

1. the four moment bounds (C);
2. the first-zero location, simplicity, and absence of another zero below
   height `16`;
3. the residue lower bound and contour-norm upper bound (R).

The Platt--Trudgian source is vastly stronger than the finite zero-count
requirement.  The new numerical work consists of four positive real integrals,
one derivative enclosure at the first zero, and one absolute contour integral.
No FLINT machinery, multidimensional sweep, or high-zero residue table is used.
