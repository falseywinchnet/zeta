# Source normalization

Suzuki defines

`Theta_omega(z)=xi(1/2-omega-iz)/xi(1/2+omega-iz)`.

RH is equivalent to `Theta_omega` being meromorphic inner in the upper
half-plane for every `omega>0`.

For `omega>0`, set

`c_omega(n)=n^omega product_{p|n}(1-p^(-2omega))`.

Every coefficient is strictly positive. The continuous kernel `g_omega` is
given explicitly by incomplete beta integrals, and

`G_omega(x)=g_omega^{<1>}(x)`

`=integral_x^1 sqrt(y/x) g_omega(y) dy/y`, `0<x<1`.

The arithmetic summatory kernel is

`H_omega(x)=h_omega^{<1>}(x)`

`=x^(-1) sum_{n<=x} c_omega(n)G_omega(n/x)`, `x>1`.     (1)

Suzuki's Theorem A.1 gives either of the following sufficient conditions for
innerness:

1. `H_omega(x)` has one sign for all sufficiently large `x`;
2. `sqrt(x)H_omega(x)` has a finite limit.

Consequently, proving eventual one-sidedness of (1) for every
`0<omega<1/2` is a deterministic route to RH.
