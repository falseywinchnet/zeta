# Sparse collision division for J_b

Let

\[
x=m-\beta\varepsilon,\qquad r=m+\alpha\varepsilon.
\]

Substitute the central Taylor jets into the 74-term cleared numerator `N_b` of
`J_b`, but carry only a sparse univariate epsilon series.  Exact evaluation
gives

\[
[\varepsilon^k]N_b=0\qquad(0\le k\le4),
\]

and

\[
[\varepsilon^5]N_b=
{\alpha\beta^2(\alpha+\beta)(\alpha+3\beta)q^2C_4\over12}.
\]

Thus the forced denominator geometry `alpha*beta^2` is present before any
absolute estimate.  This is the cleared-numerator form of

\[
{J_b\over\rho^2}\longrightarrow
{(1+2\theta)C_4\over12q^3}.
\]

The sixth coefficient also divides exactly by `alpha*beta^2`; its quotient has
56 monomials.  On `alpha,beta<=1` and
`|q^(j)|<=2^(j+3)X`, exact coefficient summation gives

\[
\left|{[\varepsilon^6]N_b\over\alpha\beta^2}\right|
\le {8273788928\over3}X^8.
\]

Using the collision margin `q^2C4/12>=44392X^8/12`, the fifth-plus-sixth
truncation stays positive for

\[
\varepsilon\le {5549\over8273788928}.
\]

This last number is not yet a collision radius for the complete function; the
order-seven-and-higher remainder remains to be bounded.
