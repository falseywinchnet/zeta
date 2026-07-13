# Results

The selected forward target is:

`H_omega(x)>=0` eventually for every `0<omega<1/2`,

where

`H_omega(x)=x^(-1)sum_{n<=x}c_omega(n)G_omega(n/x)`

and every `c_omega(n)>0`. Suzuki's theorem makes this sufficient for RH.

The continuous average term cancels exactly:

`integral_0^1 y^omega G_omega(y)dy=0`.

Consequently

`xH_omega(x)=integral G_omega(t/x)dE_omega(t)`,

with `E_omega` the generalized Jordan-totient discrepancy. This identifies the
full arithmetic object that must be controlled.

The kernel is provably negative near zero and positive near one. Numerical
reconnaissance indicates a single crossing and gives positive arithmetic sums
through `x=100000` for `omega=0.1,0.25,0.4`; no eventual conclusion is taken
from those samples.

The next theorem-sized step is a proof of the kernel's one-crossing structure,
followed by a deterministic allocation or one-sided discrepancy inequality
showing that its positive index region dominates its negative region.
