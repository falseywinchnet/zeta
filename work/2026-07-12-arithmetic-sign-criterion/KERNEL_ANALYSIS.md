# Kernel analysis

For `0<omega<1/2`, write `G=G_omega` and `g=g_omega`.

## Endpoint signs

Suzuki's source asymptotic is

`g(x)~-D_omega x^(omega-1)` as `x->0+`,

`D_omega=4^omega pi^(omega-1/2)Gamma(3/2-omega)>0`.

Using

`G(x)=x^(-1/2)integral_x^1 y^(-1/2)g(y)dy`

gives

`G(x)~-D_omega/(1/2-omega) x^(omega-1)<0`.              (5)

At the other endpoint,

`g(x)~(2pi)^omega/Gamma(omega)(1-x)^(omega-1)`,

so

`G(x)~(2pi)^omega/Gamma(omega+1)(1-x)^omega>0`.         (6)

Therefore `G` has at least one zero in `(0,1)`.

## Differential identity

Differentiating the defining integral gives

`2xG'(x)+G(x)=-2g(x)`.                                 (7)

Equations (5)--(7), together with the incomplete-beta formula, reduce the
one-zero gate to a sign-variation problem for `g`. A proof that `g` changes sign
in the required order and that (7) permits only one crossing would establish
the one-negative-region/one-positive-region structure used by the pairing
strategy.

## Numerical location only

For `omega=0.1,0.25,0.4`, direct evaluation finds the predicted negative and
positive regions. The arithmetic sums through `x=100000` remain positive and
`sqrt(x)H_omega(x)` remains near one. These values locate the proposed theorem;
they do not support its eventual or uniform conclusion.
