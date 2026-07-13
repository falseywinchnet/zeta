# Tail log-convexity lemma required by `D_b`

For the `n=1` theta term, put `X=pi exp(2u)` and `D=2X d/dX`.  Linear terms
in `log Phi_1` disappear after two derivatives, and exact algebra gives

\[
q_1=\frac{4X(4X^2-12X+15)}{(2X-3)^2},
\]

\[
F_{1,1}=q_1D^2q_1-(Dq_1)^2
=\frac{1536X^3(16X^3-36X^2+45)}{(2X-3)^6}>0
\quad(X\ge23).
\]

The full theta kernel is `Phi=Phi_1(1+rho)`, where

\[
\rho=\sum_{n\ge2}
n^2\frac{2n^2X-3}{2X-3}e^{-(n^2-1)X}.
\]

For `X>=23`, write the rational prefactor as

\[
n^4+\frac{3n^2(n^2-1)}{2X-3}.
\]

Applying `D` at most four times, Leibniz's rule and
`|D^j(2X-3)^{-1}|<2048(2X-3)^{-1}` give the deliberately loose bound

\[
|D^j\rho|
<2^{22}\sum_{n\ge2}n^4 z_n^4e^{-z_n},
\qquad z_n=(n^2-1)X,quad 0\le j\le4.
\]

Here `z_2>=69`.  The exact elementary inequality `exp(7/10)>2` gives
`exp(-69)<2^-98`.  Moreover consecutive summands have ratio below

\[
2^8e^{-115}<2^{-156},
\]

because the algebraic ratio is at most `2^8`.  Consequently the sum is less
than twice its `n=2` term.  Including one additional factor `X`, which is
needed when perturbing `q_1,q_1',q_1''`, still gives the following bound
because `X^5 exp(-(n^2-1)X)` is decreasing once `(n^2-1)X>=69>5`:

\[
X|D^j\rho|<2^{-35}\qquad(0\le j\le4).
\]

The derivatives through order four of `log(1+rho)` are finite polynomials in
`D^j rho` divided by powers of `1+rho>1`; the sum of their integer
coefficients is below `2^8`.  Exact rational comparison also gives
`q_1<5X`, `Dq_1<10X`, and `D^2q_1<20X` on this range.  Hence the perturbation
of `F1=q q''-(q')^2` is less than one.  On the other hand the displayed exact
factor gives, using `(2X-3)^6<(2X)^6`,

\[
F_{1,1}>24(16-36/X)>300.
\]

Thus `F1>299>0` for `u>=1`; evenness gives the negative tail.  Together with
the existing directed compact certificate R142, this supplies the previously
unstated global tail sign needed for the `D_b` argument.

The constants are intentionally coarse.  `prove_theta_remainder_bound.py`
checks the derivative and logarithmic coefficient inventories with exact
rational arithmetic.  The lemma remains advancement work until an independent
refine round audits the argument and its verifier.
