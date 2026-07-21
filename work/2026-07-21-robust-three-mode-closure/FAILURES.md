# Failures and rejected closures

## Constant outer box is insufficient for the sign theorem

After dividing coordinate `j` by `x^j`, the exact two-mode cleared values tend
to zero polynomially (numerically their leading behavior is of order `1/x`).
The generated `outerE` box is a valid universal tail bound, but its induced
polynomial perturbation budget is constant.  Therefore no fixed positive
margin can compare the two all the way to infinity.

This is not a counterexample and not a leak in the analytic tail theorem.  It
is loss of essential exponential information in the chosen abstraction.  The
rejected route would have produced a theorem with an unprovable uniform-margin
premise.  The next route keeps `exp (-8*x)` visible.
