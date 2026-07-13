# Exact arithmetic reduction

## Jordan-totient Dirichlet series

Absolute rearrangement in its convergence half-plane gives

`sum_{n>=1} c_omega(n)n^(-s)=zeta(s-omega)/zeta(s+omega)`. (2)

Thus the arithmetic part is a generalized Jordan-totient sequence. The
denominator is exactly where the zero-free problem enters.

## Vanishing continuous main term

The kernel has the exact moment cancellation

`integral_0^1 y^omega G_omega(y)dy=0`.                  (3)

To see it, first interchange the two integrals defining `G_omega`:

`integral_0^1 x^omega G_omega(x)dx`

`=(omega+1/2)^(-1) integral_0^1 y^omega g_omega(y)dy`.

In the explicit formula for `g_omega`, the first term integrates to
`(1/2)B(3/2,omega)`. Reversing the incomplete-beta integral in the second term
gives the same quantity. Their difference is zero.

Let

`C_omega(t)=sum_{n<=t}c_omega(n)`,

`A_omega=1/[(1+omega)zeta(1+2omega)]`,

`E_omega(t)=C_omega(t)-A_omega t^(1+omega)`.

The main term has differential

`d[A_omega t^(1+omega)]=t^omega dt/zeta(1+2omega)`.

By (3), its complete contribution to (1) vanishes. Therefore

`x H_omega(x)`

`=integral_(0,x] G_omega(t/x) dE_omega(t)`.             (4)

Equation (4) is exact. The RH-sensitive object is a signed transform of the
Jordan-totient discrepancy, not the positive average order of `c_omega`.

## Meaning of the square-root asymptotic

The Mellin transform of `H_omega` is `Theta_omega(z)/(-iz)`. The pole at
`z=0`, with `Theta_omega(0)=1`, produces the term `x^(-1/2)`. Poles arising
from zeros of `xi(1/2+omega-iz)` obstruct shifting the Mellin contour.

Hence

`sqrt(x)H_omega(x)->1`

is not an elementary average-order statement. It encodes the required
zero-free half-plane. The eventual-sign condition is the weaker target worth
attacking directly.
