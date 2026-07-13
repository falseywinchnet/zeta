# Pre-prime ground-state flow

## Fixed-interval form

For `w(t)=v(at)` on `(-1,1)`, the localized Weil form is

`q_a(w)=L(w)-[log a+(2A+1)]||w||_2^2-P_a(w)-<R_a w,w>`,

where

`R_a(x,y)=a r''(a|x-y|)`.

If `0<a<(log 2)/2`, then `P_a=0`. Hence all these forms have the common
logarithmic form domain and differ by bounded operators.

## Comparison lemma

Let `a0<=a<=b<(log 2)/2`, and define

`H(x)=r''(x)+x r'''(x)`.

Write `H(0)=-7/4` and `J(x)=H(x)-H(0)`. If `|J(x)|<=M_1` for
`0<=x<=2b`, then

`lambda_b >= lambda_a-log(b/a)-4M_1(b-a)`.               (1)

Indeed,

`partial_a [a r''(a|u|)]=H(a|u|)`.

The constant part of the flow contributes

`H(0)|integral w|^2<=0`

to the remainder-operator derivative and may be discarded in an upper bound.
The centered kernel difference has Schur norm at most

`integral_{-2}^2 M_1(b-a) du=4M_1(b-a)`.

The scalar shift contributes `-log(b/a)`. The bounded form comparison extends
from the smooth core to the common closed form domain, and taking Rayleigh
infima gives (1).

## Uniform bound for the remainder flow

For `x>0`,

`r''(x)=-2 cosh(x/2)+e^(x/2)/(2 sinh x)-1/(2x)`.

The Bernoulli-polynomial generating function gives, for `|x|<pi`,

`e^(x/2)/(2 sinh x)-1/(2x)`

`=sum_{n>=1} B_n(3/4) 2^(n-1) x^(n-1)/n!`.

Thus

`H(x)=-2 cosh(x/2)-x sinh(x/2)`

`+sum_{n>=1} n B_n(3/4) 2^(n-1)x^(n-1)/n!`.            (2)

For `n>=2` and `0<=y<=1`, the Fourier series of Bernoulli polynomials gives

`|B_n(y)| <= 2 n! zeta(n)/(2 pi)^n`.

Writing `X=log 2` and `q=X/pi`, subtracting `H(0)` in (2) yields

`|J(x)| <= 2[cosh(X/2)-1]+X sinh(X/2)`

`+(2/pi)[(1-q)^(-2)-1] < 13/16`                        (3)

for `0<=x<=X`. The endpoint at zero is understood through the convergent
series. Consequently `4M_1<13/4` throughout the full pre-prime region.

Combining (1) and (3),

`lambda_b >= lambda_a-log(b/a)-(13/4)(b-a)`.            (4)

## Propagation from `a=0.3`

The secured anchor is

`lambda_0.3 >= 0.003702862589668072165872279687848`.

Take `b=0.30056`. Since

`log(b/0.3)<=(b-0.3)/0.3=7/3750`

and `b-0.3=7/12500`, (4) gives

`lambda_0.30056 >= 0.00001619592300140549920561302118133333333`.

Monotonicity then gives the same positive endpoint lower bound for every
`a in [0.3,0.30056]`.

This is an analytic full-operator extension of the certified anchor. No Ritz
matrix, tail compression, or spectral-cluster closure enters the propagation.
