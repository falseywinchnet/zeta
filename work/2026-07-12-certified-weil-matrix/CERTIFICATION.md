# Certification argument

Status: advancement work. This document certifies the implemented finite
projected matrices subject to the stated software and mathematical checks. It
does not certify the full localized-Weil operator.

## 1. Arithmetic backend

`python-flint==0.9.0` supplies Arb real balls, Acb complex balls, validated Acb
integration, and ball-matrix eigenvalue isolation. All decimal inputs are parsed
as containing balls. The working precision, origin cutoff, and requested
integration tolerance are printed with every run.

The computation uses no floating-point quadrature result. Python floats occur
only after an Arb floor has produced an exact small integer for prime-power
enumeration. The code rejects enumeration beyond the exact binary64 integer
range and rejects an `a` ball whose `exp(2a)` straddles an integer.

## 2. Exact one-dimensional reduction

For the orthonormal Dirichlet modes

\[
\phi_n(x)=\sin\frac{n\pi(x+1)}2,
\qquad k_n=\frac{n\pi}{2},
\]

the scaled form matrix is

\[
M_{ij}(a)=\frac1a\int_0^2 g(at)
\left(C_{ij}(t)+C_{ji}(t)\right)dt,
\]

where

\[
C_{ij}(t)=\int_{-1}^{1-t}\phi_i'(y+t)\phi_j'(y)\,dy.
\]

Product-to-sum gives the analytic expression implemented in
`derivative_correlation`. When `i=j`, the difference frequency is exactly zero
and is handled symbolically. Subtracting two independently rounded copies of
`k_i` would only produce a ball containing zero and cannot justify division.

Mode `n` is even about zero for odd `n` and odd for even `n`. Since `g(x-y)` is
even, cross-parity matrix entries vanish exactly. The implementation inserts
exact zeros for these entries rather than attempting to certify cancellation.

## 3. Prime-power pieces

Every `n <= exp(2a)` that is an integer prime power is found by exact integer
factorization. On a piece beginning at `t=log(n)/a`, its ramp

\[
\frac{\Lambda(n)}{\sqrt n}(at-\log n)
\]

is added to the fixed analytic callback. It vanishes at the new endpoint. No
callback contains a conditional prime-power test.

## 4. Origin enclosure

The Lerch representation is never integrated through zero. On `[0,epsilon]`,
use

\[
\frac{g(at)}a=rac12t\log(at)+At+\frac{r(at)}a,
\qquad r(0)=r'(0)=0.
\]

For `0<u<=1`, write

\[
r''(u)=-2\cosh(u/2)+F(u),\qquad
F(u)=\frac{e^{u/2}}{2\sinh u}-\frac1{2u}.
\]

The numerator form

\[
2F(u)=\frac{u e^{u/2}-\sinh u}{u\sinh u}
\]

and the elementary bounds

\[
e^{u/2}-1\le\frac u2e^{1/2},\quad
\sinh u-u\le\frac{u^3}{6}\cosh 1,\quad
\sinh u\ge u
\]

give

\[
|F(u)|\le\frac{e^{1/2}}4+rac{u\cosh1}{12}<0.55.
\]

Consequently `|r''(u)|<3` and `|r(u)|<=3u^2/2`. Cauchy--Schwarz gives

\[
|C_{ij}(t)+C_{ji}(t)|\le2k_i k_j.
\]

For `a epsilon < min(1,log 2)`, the omitted entry integral therefore has radius

\[
2k_i k_j\left[
\frac{\epsilon^2}{4}\left(-\log(a\epsilon)+\frac12\right)
+\frac{A\epsilon^2}{2}+\frac{a\epsilon^3}{2}
\right].
\]

Every operation in this expression is evaluated as an Arb ball and the upper
endpoint becomes a symmetric error ball.

Arb may request a coarse nonanalytic range evaluation on a ball touching zero
even when the integration interval does not. For that request only, the callback
returns the same local magnitude enclosure. Analytic callbacks crossing zero
remain rejected. A dyadic mesh from `epsilon` to `1/8` keeps the analytic
neighborhoods in the right half-plane.

## 5. Validated integration

Away from zero and prime breakpoints, the original Hurwitz--Lerch expression is
analytic for the requested neighborhoods. `acb.integral` encloses each piece.
The real parts are summed, the imaginary balls must contain zero, and the origin
ball is added last.

The reported `max_integration_radius` is the largest radius after summing the
validated pieces for one entry. `max_origin_radius` is reported separately. In
the production runs the origin bound dominates by more than thirty orders of
magnitude.

## 6. Eigenvalue enclosure

Let the interval matrix be represented as midpoint `M_0` plus symmetric
uncertainty `E`, with `|E_ij|<=r_ij`. Arb isolates the eigenvalues of `M_0`.
For every represented real symmetric matrix,

\[
\|E\|_2\le\sqrt{\|E\|_1\|E\|_\infty}
=\|E\|_\infty
\le\max_i\sum_j r_{ij}=:\rho,
\]

because the radius matrix is symmetric. Weyl's inequality then widens every
midpoint eigenvalue ball by `rho`. This is the printed
`entry_perturbation_norm`.

## 7. Meaning of a positive result

A positive lower endpoint certifies positivity of the displayed finite Ritz
matrix. Since its trial space is conforming, its smallest eigenvalue is still an
upper bound for the full `lambda_a`. The infinite-dimensional complement is not
controlled here. No positive finite result proves `lambda_a>=0` or RH.
