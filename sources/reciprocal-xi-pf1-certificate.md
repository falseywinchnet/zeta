# Strict PF1 certificate for the reciprocal-xi kernel

## Statement

Put

\[
A(t)=\frac1{\xi(1/2+t)},\qquad
L(x)=\frac1{2\pi}\int_{\mathbb R}A(t)e^{-itx}\,dt.
\]

Then `L(x)>0` for every real `x`.  Consequently the reciprocal-xi
Schoenberg kernel is strictly PF1.

## Compact interval

For

\[
M_{2j}=\frac1\pi\int_0^\infty\frac{t^{2j}}{\xi(1/2+t)}\,dt,
\]

`scripts/verify_reciprocal_xi_moments.py` proves

\[
M_0>3.80725,quad M_2<90.80074,quad
M_4>6738.27009,quad M_6<887149.65951.
\]

The verifier uses integer-grid outward rounding, Machin's formula, rational
atanh and exponential series, Robbins' gamma bounds, finite Dirichlet bounds

\[
\sum_{n=1}^Nn^{-s}<\zeta(s)
<\sum_{n=1}^Nn^{-s}+\frac{N^{1-s}}{s-1},
\]

and a composite Riemann sum corrected by an independently enclosed total
variation.  The tail follows from the exact two-step gamma recurrence.  No
floating-point or special-function evaluation occurs in this certificate.

Since

\[
\cos y\ge 1-\frac{y^2}{2!}+\frac{y^4}{4!}-\frac{y^6}{6!},
\]

these bounds give, with `u=(10x/3)^2`, a lower polynomial whose Bernstein
coefficients on `0<=u<=1` are

\[
\frac{19}{5},\quad\frac{487}{200},\quad
\frac{1459}{800},\quad\frac{211}{200}.
\]

Thus `L(x)>0` for `|x|<=3/10`.

## First residue

Write `Xi(z)=xi(1/2+iz)`.  The directed verifier
`scripts/verify_reciprocal_xi_complex.py` proves

\[
\Xi(14.1347)>0,\qquad \Xi(14.1348)<0,
\]

and, throughout that rational interval,

\[
-0.001395<\Xi'(t)<-0.001370.
\]

Hence the enclosed zero is simple and

\[
c_1=-\frac1{\Xi'(\gamma_1)}>700,qquad \gamma_1<14.14.
\]

Platt and Trudgian's rigorous verification through height `3e12` shows that
this is the first positive ordinate and that shifting to height `-16` crosses
no other nontrivial zero.

The complex verifier is no-FLINT directed interval arithmetic.  It evaluates
zeta and its derivative by Euler--Maclaurin.  After `K` corrections, it uses

\[
|B_{2K}(\{x\})|<\frac{4(2K)!}{(2\pi)^{2K}}
\]

to enclose the remainder and differentiates the same remainder integral for
the derivative.  Complex Gamma is evaluated by `mpmath.iv`.  Digamma is
shifted by `48` and evaluated by its Stirling series; throughout the domain
`|tan(arg w)|<1/6`, so the complex remainder factor satisfies

\[
\sec(\arg w)^{24}<\left(\frac{37}{36}\right)^{12}<2.
\]

## Contour norm

Let

\[
I_{16}=\frac1{2\pi}\int_{\mathbb R}
\left|\frac1{\xi(1/2+u-16i)}\right|\,du.
\]

The same directed verifier proves

\[
I_{16}<1164.008<1170.
\]

Here is the monotonicity used by its left Riemann sum.  Pair the zeros of
`F(z)=xi(1/2+z)` under conjugation and `z -> -z`.  A critical-line pair gives

\[
\left|1+\frac{(u-16i)^2}{\gamma^2}\right|^2,
\]

whose derivative with respect to `u^2` is
`2(gamma^2+16^2+u^2)/gamma^4>0`.  A noncritical quartet
`+-a+-i gamma` gives the even factor

\[
P(z)=z^4+2(\gamma^2-a^2)z^2+(a^2+\gamma^2)^2.
\]

For `X=u^2`, every coefficient of
`d|P(u-16i)|^2/dX` is positive when `|a|<1/2` and
`gamma>=3e12`; the constant coefficient is bounded below by

\[
4\{(\gamma^2+16^2)(\gamma^2-16^2)^2
-a^6-a^4(\gamma^2+16^2)-10a^2\gamma^2 16^2\}>0.
\]

Platt--Trudgian places every lower zero on the critical line.  The symmetric
Hadamard product therefore proves that
`u -> |xi(1/2+u-16i)|` is increasing for `u>=0`.  The verifier uses a rational
step `1/50` through `u=60`.  Beyond `60`, the exact gamma recurrence and Euler
product bounds give a two-unit ratio below `1/8`, so the omitted integral is a
geometric tail.

## Tail positivity

Moving the Fourier contour to height `-16` gives, for `x>0`,

\[
L(x)=c_1e^{-\gamma_1x}+R_{16}(x),\qquad
|R_{16}(x)|\le I_{16}e^{-16x}.
\]

For `x>=3/10`, the certified bounds reduce positivity to

\[
e^{(16-14.14)3/10}>\frac{1200}{700}=\frac{12}{7}.
\]

The cubic Taylor lower bound at `279/500` proves this exactly, with margin
`49617991/1750000000`.  Evenness completes the real line.
