# Escape derivative, sixth-jet invariant, and exact dominant tail

## 1. The right-escape coefficient

Let `B=A(x,m)`, `f=q'/q`, and `M=(q(m)-q(x))/B`.  Exact differentiation at
fixed `m` gives

\[
D_b=q(x)-f'(x)-\frac{q'(x)}B+\frac{M q(x)}B.
\]

With

\[
F_1=qq''-(q')^2,\qquad F_2=q^3-F_1,
\]

`prove_db_structure.py` verifies

\[
\boxed{D_b=\frac{F_2(x)}{q(x)^2}+\frac{q(x)}B(M-f(x)).}
\]

The established PF3 certificate gives `F2>0` globally and `F1>0` on
`[-1,1]`.  The tail argument below supplies `F1>0` for `|x|>=1`.  Hence
`f'=F1/q^2>0` globally.  Since `M` is the `q`-weighted mean of `f` on
`[x,m]`, strict monotonicity gives `M>f(x)` and therefore

\[
\boxed{D_b>0\quad(x<m).}
\]

This closes the necessary right-escape condition found in P000032:
`J_b=4D_b X_r^2+O(X_r)>0` as `r` escapes to the positive tail.

## 2. Missing tail log-convexity

For the first theta term, `X=pi exp(2u)` and `D=2X d/dX`, exact algebra gives

\[
q_1=\frac{4X(4X^2-12X+15)}{(2X-3)^2},
\]

\[
F_{1,1}=\frac{1536X^3(16X^3-36X^2+45)}{(2X-3)^6}>300
\qquad(X\ge23).
\]

Write `Phi=Phi_1(1+rho)`.  The exact ratio is

\[
\rho=\sum_{n\ge2}n^2\frac{2n^2X-3}{2X-3}e^{-(n^2-1)X}.
\]

`prove_theta_remainder_bound.py` checks the derivative inventories through
order eight.  The first exponent is at least 69, and exact rational
bookkeeping gives

\[
X|D^j\rho|<2^{-29}\quad(0\le j\le8),
\]

\[
X|D^j\log(1+\rho)|<2^{-12}\quad(1\le j\le8).
\]

The perturbation of `F1` is therefore less than one, so `F1>299` on `u>=1`.
Evenness supplies `u<=-1`.  Details and the deliberately coarse estimates are
in `F1_TAIL_LEMMA.md`.

## 3. The new sixth-jet invariant

For the generic collision `x=m-beta eps`, `r=m+alpha eps`, write the fifth
coefficient as

\[
[\varepsilon^5]J=
\frac{\beta(\alpha+\beta)^2}{240q^5}
\{\alpha^2P_{20}+\alpha\beta P_{11}+\beta^2P_{02}\}.
\]

Define the 33-term sixth-jet invariant

\[
\boxed{N_6:=P_{20}.}
\]

Let

\[
A_6=q^2C_4'',\quad B_6=qq'C_4',\quad
C_6=qq''C_4,\quad D_6=(q')^2C_4.
\]

Exact polynomial reduction in `isolate_sixth_jet_invariant.py` proves

\[
P_{11}=-\frac{10}{3}A_6+\frac{95}{6}B_6+\frac{40}{9}C_6
-\frac{65}{3}D_6+\frac43N_6,
\]

\[
P_{02}=\frac53A_6-\frac{35}{3}B_6-\frac{80}{9}C_6
+\frac{85}{3}D_6+\frac43N_6.
\]

It also proves that `N6` is outside the span of the four old generators.
Thus exactly one new invariant is necessary and sufficient at fifth order.
For `q=c exp(kt)`,

\[
C_4=12q^6,\qquad N_6=140k^2q^8.
\]

## 4. Tail positivity of `N6`

For the exact first theta term,

\[
N_{6,1}=\frac{5242880X^8P_8(X)}{(2X-3)^8},
\]

where

\[
\begin{aligned}
P_8={}&1792X^8-21504X^7+129792X^6-491520X^5\\
&+1257120X^4-2278080X^3+3095280X^2-3024000X+1488375.
\end{aligned}
\]

Every coefficient of `P8(23+y)` is positive.  The verifier proves the stronger
bound `N6_1>2^24 X^8`.  On the box
`|q^(j)|<=2^(j+3)X`, its exact multivariate sensitivity to perturbations
`|Delta q^(j)|<=2^-9/X` is less than `2^25 X^6`.  The theta remainder bound is
stronger than the required perturbation hypothesis.  Consequently

\[
\boxed{N_6>0\quad(|u|\ge1).}
\]

## 5. Exact Peano positivity for the dominant theta kernel

The first theta term has rational logarithmic slope

\[
s_1(X)=\frac52+\frac{4X}{2X-3}-2X.
\]

Therefore its primitives are exact rational differences
`A_1(u,v)=s_1(X_u)-s_1(X_v)`.  Substituting these primitives and the exact
jets into the cleared Peano numerators gives a purely rational problem.

`prove_one_term_tail_density.py` substitutes

\[
X=23+y,\qquad U=1+a,\qquad V=1+c,
\qquad y,a,c\ge0.
\]

After clearing positive denominators:

- the `J_b` numerator has 1,863 coefficients and none is negative;
- the `S_r` numerator has 308 coefficients and none is negative.

Both polynomials are nonzero for positive gaps.  Hence the exact dominant
theta kernel satisfies

\[
\boxed{S_r^{(1)}>0,\qquad J_b^{(1)}>0}
\]

for every `X>=23` and every `U,V>1`, with no resolved-gap restriction.

## 6. Boundary of the full-tail result

The same statement for the full theta kernel is not yet proved.  Its
`n>=2` correction is exponentially tiny, but the dominant numerator margins
vanish at collisions.  A uniform absolute perturbation cannot be compared to
a vanishing margin.  The transfer must split into:

1. a noncollision region, using the positive-coefficient dominant polynomial;
2. a collision region, using `C4`, the reduced fourth coefficient, and `N6`.

`test_one_large_gap_box.py` confirms this analytically: independent endpoint
error boxes have negative lower coefficients when either gap is allowed to
collapse.  This is failure of an over-independent enclosure, not a negative
density value.

