# PF4 sparse J_b collision series

- Mode: advancement
- Date: 2026-07-13
- Model: Sydney, OpenAI Codex
- Starting records: R158, R160, R161, CERT6, CERT7
- Starting progress: P000039
- Status: complete as an advancement round; dense obstruction removed, exact
  first two divided coefficients obtained, rigorous all-order radius remains
  open

## Question

Can the three-point `J_b` collision expansion be evaluated after forced-factor
division without the dense symbolic swell recorded in P000038?

## Method

Evaluate the 74-term cleared numerator in a sparse univariate epsilon-series
ring.  Retain symbolic geometry and theta jets in the coefficients, but never
expand the full substituted multivariate expression.

## Outcome

The sparse evaluator completes in seconds.  It proves exact vanishing through
order four and exact divisibility of both the fifth and sixth coefficients by
the forced angular factor `alpha*beta^2`.  The fifth coefficient is the
positive `C4` collision margin.  The sixth divided coefficient has only 56
terms and an explicit normalized coefficient norm.

This does not yet prove a collision radius: the displayed
`FIRST_CORRECTION_RADIUS` controls the fifth-plus-sixth truncation only.  The
next proof must parameterize the complete endpoint remainder before taking its
coefficient norm.
