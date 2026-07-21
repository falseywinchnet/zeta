# Next boundary: discharge the bounded-interval estimate

The formal theta-series mechanism now reduces the analytic boundary to one
non-circular inequality.  For each `B > 0`, construct
`ThetaJetControl (Set.Ioo (-1) B)` with

\[
 r=\pi e^{-2},\qquad
 M_j(n)=K_j(B)n^{2j+6}e^{-rn},\qquad 0\le j<6,
\]

and prove, for `-1 < t < B`,

\[
 |\operatorname{mode}_{j+1}(n,t)|\le M_j(n).
\]

This is enough because `ThetaSeriesJet.lean` already proves every `M_j` summable
and turns those estimates into the ordinary derivative tower through level six.

## Proposed coefficient route

Let

\[
 A_j=\sum_{m\in\operatorname{support}(P_j)}|[X^m]P_j|,
 \quad c_+=\pi e^{2B}.
\]

For `n >= 1`, `X = pi n^2 exp(2t)`, and `-1 < t < B`, prove

\[
 |P_{j+1}(X)|
 \le A_{j+1}\max(1,c_+)^{j+2}n^{2j+4}.
\]

Combine it with

\[
 e^{5t/2}\le e^{5B/2},\qquad
 e^{-X}\le e^{-\pi e^{-2}n^2}\le e^{-\pi e^{-2}n}.
\]

Thus one valid closed coefficient is

\[
 K_j(B)=2\pi e^{5B/2}A_{j+1}\max(1,c_+)^{j+2}.
\]

Do not expand six separate derivatives.  Prove one finite-support polynomial
evaluation bound, instantiate it with the recursive `certPoly`, and build the
control with `ThetaJetControl.of_exponentialBound`.

## Boundary after that

Once these controls exist for every `B > 0`, specialize the derivative tower at
each `t >= 0`, prove the literal series agrees with the maintained kernel, and
feed the resulting raw jet into the cleared certificate bridge.  The modular
theta identity/even continuation and the three strict cleared signs remain
separate obligations; neither is claimed here.
