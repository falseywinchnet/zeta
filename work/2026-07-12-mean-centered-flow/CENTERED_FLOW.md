# Centered smooth-flow bound

## Exact split

Below the first prime threshold,

`partial_a q_a(w)=-a^(-1)||w||_2^2-<H_a w,w>`,

where `H_a(x,y)=H(a|x-y|)` and

`H(x)=r''(x)+x r'''(x)`.

The Bernoulli series gives `H(0)=-7/4`. Set

`J(x)=H(x)-H(0)`.

Then

`-<H_a w,w>=(7/4)|integral w|^2-<J_a w,w>`.            (1)

The first term is positive. It is kept visible and may be discarded when a
state-independent lower bound is wanted.

## Linear pointwise majorant

For `X=log 2`, the series from P000018 gives

`J(x)=-2[cosh(x/2)-1]-x sinh(x/2)`

`+sum_{n>=2} n B_n(3/4)2^(n-1)x^(n-1)/n!`.

For `0<=x<=X`, use

`2[cosh(x/2)-1]/x <= sinh(X/2)`,

`sinh(x/2)<=sinh(X/2)`,

and the Bernoulli-polynomial Fourier bound. With `q=X/pi`,

`|J(x)|/x <= 2sinh(X/2)`

`+(2/pi^2)(2-q)/(1-q)^2 < 4/3`.                        (2)

## Hilbert--Schmidt flow

On `(-1,1)`, (2) gives

`||J_a|| <= ||J_a||_HS`

`<= (4/3)a [integral integral |x-y|^2 dxdy]^(1/2)`

`=(4/3)a sqrt(8/3)`.                                   (3)

For `a<=0.301`, the right side is below `2/3`. Combining (1)--(3),

`partial_a q_a(w) >=-[a^(-1)+2/3]||w||_2^2`

as a quadratic-form inequality. Integration yields

`lambda_b>=lambda_a-log(b/a)-(2/3)(b-a)`               (4)

for `0.3<=a<=b<=0.301`.

## Extended positive interval

Take `b=0.30092`, so `b-a=23/25000`. Then

`log(b/a)<= (b-a)/a=23/7500`

and

`(2/3)(b-a)=46/75000`.

Using the secured anchor,

`lambda_0.30092`

`>=0.003702862589668072165872279687848-0.00368`

`=0.000022862589668072165872279687848`.                 (5)

Monotonicity gives the same lower endpoint throughout `[0.3,0.30092]`.

Equation (1) contains additional positive flow proportional to the squared
mean. Bound (5) does not use it.
