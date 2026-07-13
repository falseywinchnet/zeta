# Prime-threshold flow

## Endpoint-overlap lemma

Let the zero extension of `w` be supported in `[-1,1]`, and define its
autocorrelation

`C_w(s)=integral_{-1}^{1-s} w(t+s) conjugate(w(t)) dt`, `0<s<2`.

Put `ell=2-s`. The two factors in this integral lie in the opposite endpoint
strips of width `ell`. Suzuki's positive reference form contains the boundary
term

`-(1/2) integral |w(x)|^2 log(1-x^2) dx`.

On either endpoint strip, `1-x^2<=2 ell`. Therefore, when `0<ell<1/2`,

`integral_endpoint |w|^2 <= 2L(w)/log(1/(2ell))`.

Cauchy--Schwarz on the two endpoint strips gives

`|C_w(2-ell)| <= 2L(w)/log(1/(2ell))`.                 (5)

## Entry of a prime-power ramp

For a prime power `n`, set

`a_n=(log n)/2`, `c_n=Lambda(n)/sqrt(n)`.

Just above `a_n`, its scaled translation has

`s_n(a)=log(n)/a`,

`ell_n(a)=2-s_n(a)=2(a-a_n)/a`.

Its full quadratic contribution is `2c_n Re C_w(s_n(a))`. From (5),

`|P_{n,a}(w)| <= epsilon_n(a)L(w)`,

`epsilon_n(a)=4c_n/log(1/(2ell_n(a))) -> 0`

as `a` decreases to `a_n` from above. Thus every new arithmetic ramp enters
continuously in the `L`-form topology even though translation is not continuous
in operator norm on `L2`.

This identifies the correct threshold coordinate: endpoint overlap measured by
the logarithmic boundary energy. An `L2` norm estimate erases precisely the
small factor that makes threshold continuation possible.

## Motion of existing translations

For shifts `s` and `t`, Fourier inversion of the zero-extended autocorrelation
gives, for every `R>1`,

`|C_w(s)-C_w(t)|`

`<= R|s-t| ||w||_2^2 + [2/log R] E_log(w)`,             (6)

where

`E_log(w)=(2pi)^(-1) integral log^+|xi| |what(xi)|^2 dxi`.

Equation (6) follows by splitting frequencies at `R`, using
`|exp(i xi s)-exp(i xi t)|<=|xi||s-t|` below `R` and `<=2` above it.

## Source-normalized logarithmic bridge

Suzuki's exact Fourier identity is

`L(w)=(2pi)^(-1) integral [log|xi|+gamma]|what(xi)|^2 dxi`.

On `|xi|<1`, support in `[-1,1]` gives

`|what(xi)|<=||w||_1<=sqrt(2)||w||_2`.

Since `integral_{-1}^1 -log|xi| dxi=2`, splitting the Fourier identity at one
gives the explicit bound

`E_log(w)<=L(w)+(2/pi-gamma)||w||_2^2`.                 (7)

Combining (6) and (7),

`|C_w(s)-C_w(t)| <= [2/log R]L(w)`

`+[R|s-t|+2(2/pi-gamma)/log R]||w||_2^2`.              (8)

Equation (8) is the quantitative modulus for every active prime translation;
(5) handles the instant at which a new one appears. Taking, for example,
`R=|s-t|^(-1/2)` makes both coefficients tend to zero, with the expected
logarithmic rate in the form term.

## Piecewise form comparison

On an interval carrying a fixed finite set `N` of active prime powers, put

`S=sum_{n in N} Lambda(n)/sqrt(n)`.

Applying (8) termwise gives

`|P_b(w)-P_a(w)| <= eta L(w)+kappa||w||_2^2`,

`eta=4S/log R`,

`kappa=2R sum_n [Lambda(n)/sqrt(n)]|s_n(b)-s_n(a)|`

`+4(2/pi-gamma)S/log R`.                               (9)

The scalar and smooth remainder terms have ordinary Lipschitz bounds. Since on
every compact `a`-interval the remaining part of `q_a-L` is bounded on `L2`,
there is an explicit `D_a` with

`L(w)<=q_a(w)+D_a||w||_2^2`.

Consequently (9) produces

`q_b(w)>=(1-eta)q_a(w)-K(a,b,R)||w||_2^2`,             (10)

More explicitly, if `C_I` bounds the positive norm of the smooth-kernel flow
on the chosen compact interval and

`D_a=max(0,log a+2A+1)+2S+||R_a||`,

then one may take

`K=log(b/a)+C_I(b-a)+kappa+eta D_a`.                    (11)

Thus

`lambda_b >= (1-eta)lambda_a-K`.                       (12)

This is the desired analytic comparison architecture.
Every coefficient tends to its identity value as `b->a`, including at a new
prime threshold by (5).
