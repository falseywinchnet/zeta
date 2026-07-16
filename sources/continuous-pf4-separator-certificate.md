# Continuous strict-PF4 Fourier separator certificate

Status: refine-round audit of P000066.

## Kernel

Let

\[
B(w)=\sum_{k=-3}^{3}b_kw^k,qquad
(b_{-3},\ldots,b_3)=(2,10,23,30,23,10,2),qquad c=1/64,
\]

and define

\[
f(x)=e^{-cx^2}B(e^{2cx})
=\sum_{k=-3}^{3}b_ke^{ck^2}e^{-c(x-k)^2}.
\]

The second expression proves positivity and Schwartz decay.  Palindromy of
the coefficients proves evenness.  The function is entire in `x`.

## Strict PF3

Give `K in {-3,...,3}` the tilted law proportional to
`b_k exp(2ckx)`, and let `kappa_j` be its cumulants.  Direct differentiation
of the finite log-partition function gives

\[
q=2c-(2c)^2\kappa_2,qquad q'=-(2c)^3\kappa_3,qquad
q''=-(2c)^4\kappa_4.
\]

Since the support interval has length six, Popoviciu's inequality gives
`0<=kappa_2<=9`.  Thus

\[
q\ge2c(1-18c)=2c(23/32)>0.
\]

Moreover

\[
F_2=q^3-(qq''-(q')^2)
=q^3+q(2c)^4\kappa_4+(2c)^6\kappa_3^2.
\]

The central-moment identity
`kappa_4=mu_4-3 kappa_2^2` gives `kappa_4>=-243`.  Consequently

\[
F_2\ge q(q^2-3888c^4)
\ge q c^2(529/256-243/256)>0.
\]

The generic slope theorem R141, paired with the exact CERT12 sign boundary,
therefore proves strict PF3.

## Exact order-four invariant

Put `epsilon=1/32`, `t=exp(epsilon x)`, and

\[
P(t)=t^3B(t)=2+10t+23t^2+30t^3+23t^4+10t^5+2t^6.
\]

For `E=t d/dt`, define

\[
N_1=tP',\qquad N_{j+1}=t(N_j'P-jN_jP').
\]

The quotient rule proves `E^j log P=N_j/P^j`.  Hence, with
`ell_j=(log f)^(j)`,

\[
\ell_2={-\epsilon P^2+\epsilon^2N_2\over P^2},qquad
\ell_j={\epsilon^jN_j\over P^j}\quad(3\le j\le6).
\]

The verifier independently reconstructs `C4` as the `4x4` central-moment
Hankel determinant from these five cumulants.  It does not import the
thirteen-term advancement formula.  Every resulting monomial has derivative
weight twelve, so

\[
C_4(x)={H(t)\over P(t)^{12}}.
\]

Exact arithmetic over the rationals proves that `H` is palindromic of degree
72, has no coefficient gaps, and all 73 coefficients are positive.  Its
smallest coefficient is `3/65536`.  Therefore `C4(x)>0` globally.

CERT9 proves for any positive smooth strictly log-concave kernel satisfying
the PF3 bridge that

\[
-\partial_\xi\Psi={Q(p)\delta\over\Lambda}
\int_p^wW(t){C_4(t)\over Q(t)^6\kappa(t)^2}\,dt,qquad
\kappa={q^3+F_2\over q^3}.
\]

All factors are strictly positive here.  CERT5's quotient-Wronskian
equivalence, included transitively in CERT9, therefore proves strict PF4.

## Nonreal Fourier zeros

Gaussian translation gives

\[
\widehat f(z)=\sqrt{\pi/c}\,e^{-z^2/(4c)}
\sum_{k=-3}^{3}b_ke^{ck^2}e^{-ikz}.
\]

For `w=e^{-iz}` and `u=w+w^{-1}`, the Laurent factor reduces exactly to

\[
R_c(u)=2e^{9c}u^3+10e^{4c}u^2+(23e^c-6e^{9c})u+30-20e^{4c}.
\]

At `c=1/64`, put `r=e^(1/64)`, `x=r^2`, and `y=x-1`. Exact expansion gives

\[
\operatorname{disc}(R_c)=4r^{10}G(x).
\]

The constant and first two terms of `G(1+y)` are `-1-10y-12y^2`; all
remaining coefficients are positive. The binomial theorem gives
`0<y<1/30`, while the sum of all positive terms at `y=1/30` is

\[
\frac{1621193195302591}{36905625000000000}<1.
\]

Thus the discriminant is exactly negative. The real cubic therefore has a
nonreal conjugate pair. If `|w|=1`, then
`w+w^{-1}` is real, so each nonreal `u` root lifts to a `w` root off the unit
circle and hence to a Fourier zero with nonzero imaginary part.

Thus `f` is positive, even, Schwartz, and strict PF4, but its entire Fourier
transform is not real-rooted.  Continuous PF3 and PF4 membership alone are
insufficient for Fourier real-rootedness.

## Replay boundary

`scripts/verify_continuous_pf4_separator.py` checks the exact PF3 algebra and
margin, independently reconstructs the central determinant and all 73
positive numerator coefficients, verifies exact rational spot values, checks
the Laurent-to-cubic reduction, and proves the negative discriminant by exact
rational polynomial inequalities. The certificate depends on CERT12 and
CERT9 for the PF3 and PF4 implication theorems.
