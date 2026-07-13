# Mathematical reduction

For the even Riemann kernel

\[
\Phi(u)=\sum_{n\ge1}
\left(4\pi^2n^4e^{9|u|/2}-6\pi n^2e^{5|u|/2}\right)
e^{-\pi n^2e^{2|u|}},
\]

global PF3 is exactly the nonnegativity of

\[
\det[\Phi(x_i-y_j)]_{i,j=1}^3
\]

for every pair of strictly increasing triples. Global PF4 requires the analogous
condition through order four.

Khare's Theorem E reduces the check, under the kernel's decay, to the largest
minor at each order: lower minors need not be added separately. It does not
reduce the continuous configuration space to Toeplitz minors.

## PF3 slope criterion

Write `ell=log Phi`, `s=ell'`, and `q=-ell''>0`. Fix `a,b>0`, divide the three
columns belonging to `y_1<y_2<y_3` by the middle translate, and put

\[
A(t)=\frac{\Phi(t+a)}{\Phi(t)},\qquad
B(t)=\frac{\Phi(t-b)}{\Phi(t)}.
\]

Log-concavity makes `A` decreasing and `B` increasing. Every three-row
determinant is nonnegative exactly when the slope `B'/(-A')` is nondecreasing.
Direct differentiation reduces this to

\[
L(t,a,b)=s(t-b)-s(t+a)
+\frac{q(t)-q(t-b)}{s(t-b)-s(t)}
-\frac{q(t+a)-q(t)}{s(t)-s(t+a)}\ge0.
\]

Thus global PF3 is a three-variable scalar inequality. This is the useful
content of the order-three characterization route: it removes both row triples
and both absolute translations without restricting to equal spacing. The
denominators are positive by strict PF2.

Translation invariance leaves `2k-1` variables. Set `x_1=0`; encode the other
coordinates by positive gaps and retain one relative offset between the tuples.
The numerical search divides rows and columns by positive maxima. This preserves
the determinant sign and prevents the super-exponential tail from hiding the
interior geometry.

Numerical positivity is not a classification. A negative candidate can be
promoted only after directed interval evaluation of the kernel entries and the
determinant. A positive classification requires a global reduction covering
interior configurations and every collision or escape boundary.

## Sufficiency of the curvature pair

Set `f=q'/q`, `F1=q*q''-(q')^2`, `F2=q^3-F1`. For `alpha<beta` define

\[
M(\alpha,\beta)
=\frac{q(\beta)-q(\alpha)}{s(\alpha)-s(\beta)}
=\frac{\int_\alpha^\beta q'}{\int_\alpha^\beta q},
\]

a `q`-weighted mean of `f` on `[\alpha,\beta]`, hence between the minimum and
maximum of `f` there. Since `s'=-q`, the slope criterion is exactly

\[
L(t,a,b)=\int_{t-b}^{t+a} q\;+\;M(t-b,t)\;-\;M(t,t+a).
\]

Let `m\in[t-b,t]` attain the minimum of `f` on the left interval and
`p\in[t,t+a]` its maximum on the right. Then `m\le p` and

\[
M(t,t+a)-M(t-b,t)\le f(p)-f(m)=\int_m^p f'
\le\int_{t-b}^{t+a}\max\!\big(f',0\big)
=\int_{t-b}^{t+a}\frac{\max(F_1,0)}{q^2},
\]

using `f'=F_1/q^2`. Therefore

\[
L(t,a,b)\ \ge\ \int_{t-b}^{t+a}\frac{q^3-\max(F_1,0)}{q^2}
=\int_{t-b}^{t+a}\frac{\min(q^3,F_2)}{q^2}.
\]

**Lemma.** If `q>0` on all of `R` and `F2>=0` on all of `R`, then
`L(t,a,b)>=0` for every `t` and all `a,b>0`, hence every order-three minor is
nonnegative. If additionally `F1>=0`, the bound sharpens to
`L >= \int F_2/q^2`. Orders one and two hold independently: every theta term is
positive because `2\pi n^2e^{2|u|}\ge2\pi>3`, so `\Phi>0`; and `q>0` is strict
log-concavity, which is exactly order two. So `q>0` and `F2>=0` on `R` give
global PF3.

Evenness of `\Phi` makes `q` and `F2` even (`q'` is odd, `q''` even), so
certification on `[0,U]` covers `[-U,U]`; the escape boundary is `u>=U`.

## Tail bounds for u >= 1

Put `x=\pi e^{2u}`, so `u\ge1` means `x\ge x_0=\pi e^2>23.14`. Then
`\Phi=e^{5u/2}g(x)` with

\[
g(x)=\sum_{n\ge1}2\pi n^2(2n^2x-3)e^{-n^2x}
=4\pi x\,e^{-x}\,(1+\rho(x)),\qquad
\rho=-\frac{3}{2x}+\sigma,
\]

where `\sigma=\sum_{n\ge2}\big(n^4-\tfrac{3n^2}{2x}\big)e^{-(n^2-1)x}` obeys
`|\sigma^{(k)}|\le10^6e^{-3x}\le10^{-24}` for `k\le4`, `x\ge x_0`; it is
absorbed into the padding of every constant below. With `v=1+\rho\ge0.9351`
(so `1/v\le1.0694`) and `w=\log(1+\rho)`:

\[
|w'|\le\frac{1.61}{x^2},\quad
|w''|\le\frac{3.33}{x^3},\quad
|w'''|\le\frac{10.4}{x^4},\quad
|w''''|\le\frac{42.8}{x^5},
\]

from `w'=\rho'/v`, `w''=\rho''/v-(\rho')^2/v^2`,
`w'''=\rho'''/v-3\rho'\rho''/v^2+2(\rho')^3/v^3`,
`w''''=\rho''''/v-(4\rho'''\rho'+3(\rho'')^2)/v^2
+12\rho''(\rho')^2/v^3-6(\rho')^4/v^4`,
with `\rho'=3/(2x^2)`, `\rho''=-3/x^3`, `\rho'''=9/x^4`, `\rho''''=-36/x^5`,
each padded to absorb `\sigma` (e.g. `|\rho'|\le1.501/x^2`).

Since `\ell=\tfrac52u+\psi(x)` with `\psi=\log(4\pi)+\log x-x+w` and
`dx/du=2x`, direct differentiation gives, with all polynomial constants
cancelling exactly,

\[
q=4x-4xw'-4x^2w'',\qquad
\dot q=8x-8xw'-24x^2w''-8x^3w''',
\]
\[
\ddot q=16x-16xw'-112x^2w''-96x^3w'''-16x^4w'''',
\]

(dots are `d/du`), hence for `x\ge x_0`

\[
|q-4x|\le\frac{19.8}{x},\qquad
|\dot q-8x|\le\frac{176}{x},\qquad
|\ddot q-16x|\le\frac{2082}{x}.
\]

Writing `q=4x+\alpha`, `\dot q=8x+\beta`, `\ddot q=16x+\gamma`, the leading
`64x^2` terms of `q\ddot q` and `\dot q^2` cancel exactly:
`F_1=4x\gamma+16x\alpha+\alpha\gamma-16x\beta-\beta^2`, so for `x\ge x_0`

\[
q\ge4x-0.86>0,\qquad
|F_1|\le4\cdot2082+16\cdot19.8+16\cdot176+\frac{19.8\cdot2082+176^2}{x^2}
\le11596,
\]
\[
F_2\ge(4x-0.86)^3-11596\ge(4x_0-0.86)^3-11596>7.5\cdot10^5>0.
\]

So `q>0` and `F2>0` hold on `|u|\ge1` with enormous margin; no delicate
cancellation is needed because `F2` compares `F1=O(1)` against `q^3=O(x^3)`.
(The true asymptotics, confirmed numerically in `tail-bounds-check.txt`, are
`q=4x+6/x+O(x^{-2})` and `F_1\to384`.)

## Conclusion at order three

The directed interval certificate (`certify_pf3_curvature.py`, output
`pf3-curvature-certificate.txt`) proves `q>0`, `F1>0`, `F2>0` on `[0,1]`
(7731 adaptive cells, second-order Taylor enclosures, certified lower bounds
`q\ge18.726`, `F_1\ge0.181`, `F_2\ge3889.2`); evenness extends this to
`[-1,1]`; the tail bounds cover `|u|\ge1`. By the sufficiency lemma the
Riemann kernel is globally PF3. Combined with the certified negative Toeplitz
5x5 minor (kernel not PF5, R14/R16), the exact global Polya-frequency order of
the Riemann kernel is either 3 or 4, and only global PF4 remains open.

The order-four analogue of the slope reduction replaces the planar curve
`(B,1,A)` by a curve in three ratios; convexity of a planar curve becomes
positivity of a third-order Wronskian-type condition, and the two-sided mean
argument above has no direct analogue. The order-four question stays open with
Sobol evidence only (`sobol-order-4.json`: 2^20 configurations, no negative
minor).
