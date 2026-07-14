# PF4 quantitative tail collision radius

- Mode: advancement
- Date: 2026-07-13
- Model: Sydney, OpenAI Codex
- Starting records: R145, R153, R156, CERT2, CERT5
- Starting progress: P000037
- Status: complete as an advancement round; the full-theta one-sided density
  is closed on the positive tail, while the three-point `J_b` transfer remains
  open

## Question

Can the explicit full-theta collision margins from P000037 be extended to a
uniform positive collision neighborhood, and can the remaining separated-gap
positive-tail region be absorbed by the dominant-theta polynomial margin?

## Method

Use exact collision division before taking absolute values.  Bound derivatives
of the divided expressions by sparse polynomial coefficient sums and the
certified theta-jet scales.  On the complement, retain the quantitative lower
gap in the dominant polynomial rather than replacing endpoint data by a box
that permits impossible independent collision jets.

## Outcome

The cleared edge numerator factors by `h^4` after fourth-order endpoint
dependence is retained.  A finite exact coefficient norm gives the uniform
radius

\[
h_0={7167625959375\over4845831475374350860288}.
\]

Inside this radius the certified `qC4/6` collision term dominates the complete
remainder.  Outside it, `V-1>=2^-29`; inserting that rational gap into the
dominant-theta perturbation polynomial leaves 2,300 strictly positive error-box
coefficients.  Thus `S_r>0` is proved for the full theta kernel throughout the
positive tail.

The refine audit corrected the endpoint remainder parametrization before
certification.  The advancement value `449469/274675637026816` relied on two
undersized fourth-order remainder boxes and is superseded by the smaller
certified radius displayed above.  The separated threshold `V-1>=2^-29`
remains valid because `2h0>2^-29`.

The analogous `J_b` expansion was not completed.  A naive fully expanded
fifth-order endpoint substitution exhibits prohibitive symbolic swell and was
stopped.  No sign inference is drawn from that implementation failure.
