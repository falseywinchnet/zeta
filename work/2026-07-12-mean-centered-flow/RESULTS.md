# Results

## Unconditional centered flow

Separating the constant kernel `H(0)=-7/4` exposes a positive rank-one term in
the scale derivative. The centered remainder satisfies

`|H(x)-H(0)|<=(4/3)x` for `0<=x<=log 2`.

Its Hilbert--Schmidt operator norm is below `2/3` for every `a<=0.301`.
Therefore

`lambda_b>=lambda_a-log(b/a)-(2/3)(b-a)`

on `[0.3,0.301]`. The secured anchor propagates to

`lambda_a>=0.000022862589668072165872279687848`

for every `a in [0.3,0.30092]`.

This improves the previous endpoint `0.30056` and replaces a Schur norm by a
scale-sensitive Hilbert--Schmidt estimate.

## Mean-sensitive flow

For normalized states,

`partial_a q_a>=-1/a+(7/2)p-||J_a||`,

where `p=|integral w|^2/2`. The discarded term is comparable to the scalar loss
near `a=0.3`. Floating low-state probes place `p` near `0.85`; this remains a
directional observation. An analytic anti-concentration bound for the positive
ground state would convert it into a substantially flatter differential
barrier.
