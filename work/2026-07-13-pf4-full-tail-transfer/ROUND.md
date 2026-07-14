# PF4 full-theta tail transfer

- Mode: advancement
- Date: 2026-07-13
- Model: Sydney, OpenAI Codex
- Starting records: R145, R153, R156, CERT2, CERT5
- Starting progress: P000036
- Status: complete as an advancement round; explicit collision margins proved,
  direct independent-jet transfer rejected, global PF4 remains open

## Question

Do the `n>=2` theta corrections fit strictly inside the collision-divided
dominant margins proved in P000036, uniformly for all positive-tail gaps?

## Method

Sharpen the theta remainder inventory to explicit rational bounds
`|D^j log(1+R)|<K_j/X^4`.  Preserve the exact decay factor `1-V^-4` in
endpoint differences and primitives, then test the resulting coefficient
box.  When that box remains over-independent, return to the certified `C4`
collision face and extract explicit full-kernel divided margins.

## Result

The correlated endpoint estimate is exact, but an independent box for the
remaining derivative errors still loses the single-function derivative-chain
correlations and produces 87 negative shifted coefficients.  It is rejected
as a sufficient method, not interpreted as a counterexample.

On `X>=23`, exact theta-ratio bookkeeping gives

\[
 X<q<8X,\qquad |q'|<16X,\qquad |q''|<32X.
\]

Combining this with the certified full-kernel tail estimate
`C4>=44392 X^6` and the exact collision identities proves

\[
 S_r(m,m)>X/38,
\]

and, for `x=m-beta eps`, `r=m+alpha eps`,

\[
 \lim_{\varepsilon\downarrow0}
 {J\over\beta(\alpha+\beta)^2\varepsilon^3}>7X^3.
\]

No sampled inference is used.  The remaining step is quantitative: turn
these collision-face margins into a uniform collision radius, then close the
separated-gap complement with the dominant polynomial margin.
