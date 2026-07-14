# Failed three-point implementation

The proposed simultaneous-collision proof for `J_b` substituted fifth-order
left and right Taylor jets into its 74-term cleared numerator and attempted a
full multivariate expansion before collision division.  The expression swell
did not complete after sustained exact computation and the attempt was
stopped.

This is an implementation failure, not a failed inequality.  The collision
leading term remains analytically positive:

\[
{J_b\over\rho^2}\longrightarrow
{(1+2\theta)C_4\over12q^3}>7(1+2\theta)X^3.
\]

The repair is to use a sparse epsilon-series algebra: preserve the exact
coefficient through order five, factor the forced angular term
`alpha*beta^2`, and majorize only coefficients of order six and higher.
