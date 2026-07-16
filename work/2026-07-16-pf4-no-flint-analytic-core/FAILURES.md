# Failed and redirected approaches

## Global convexity alone

Sampling found `q`, `F2`, and `C4` increasing on the compact interval, with
positive sampled second derivatives. This does not extend to absolute
monotonicity: prior work already found sign changes in higher derivatives of
`q`. A proof based only on an unspecified convexity pattern was rejected.

## One theta mode at the origin

The first mode has excellent closed forms after `x>=5`, but at `u=0` it
captures only about 10.8 percent of `F2` and gives the wrong sign for the
second derivative of `F2`. Uniform first-mode perturbation at the origin is
therefore structurally poor.

## Independent two-mode rectangle on the whole half-line

Treating `y=e^{-3x}` as independent of `x` creates false negative Bernstein
coefficients for `q` and `C4`. The repair was not subdivision: negative
odd-power corrections were divided by the positive base and proved to decrease
along the exact exponential relation.

## A single origin rectangle for the F2 margin

Allowing `y=0` near the origin destroys the quantitative `F2>1000` margin,
because the second mode supplies most of that margin. The exact bound
`e^{-10}<y<e^{-9.42}` on the short origin band restores a positive Bernstein
certificate.

## Overly crude derivative envelopes

Coefficient-sum bounds for `P_j` inflated the sixth-derivative tail bound from
about 17 to nearly one million. Shifting the exact signed polynomials at
`t=27` produced the sharp elementary envelope
`0<(-1)^j P_j(t)<=2^(j+1)t^(j+1)` and closed the perturbation estimate.
