# Universal outer perturbation theorem

## 1. Objects

Fix `x >= 5` and `0 <= j <= 6`.  Let `P_j` be the derivative polynomials

\[
P_0(s)=2s-3,\qquad
P_{j+1}(s)=(5/2-2s)P_j(s)+2sP_j'(s).
\]

Write the normalized full jet as `a+e`, where

\[
a_j=\frac{P_j(x)+4e^{-3x}P_j(4x)}{2x-3}
\]

contains the first two theta modes and

\[
e_j=\sum_{n\ge3}
\frac{n^2e^{-(n^2-1)x}P_j(n^2x)}{2x-3}
\]

is the literal infinite remainder.

Put `C_j=2^(j+1)`.  Exact shifted coefficients prove the elementary envelope

\[
|P_j(s)|\le C_js^{j+1}\qquad(s\ge5).
\tag{1}
\]

This lower threshold is important: the historical verifier checked a related
signed envelope only from `s=27`, then used the stronger absolute statement
from `s=5` without explicitly checking it.  The new audit checks both
polynomials `C_j s^(j+1) +/- P_j(s)` after `s=5+z`; every coefficient is
nonnegative for all seven values of `j`.

## 2. Two-mode outer bound

For `y=e^(-3x)`, the exact exponential estimate at `x=5` gives
`0<y<1/3,000,000`.  Since `j<=6`,

\[
4^{j+2}y\le4^8y<1.
\]

Using (1), `x<=2x-3`, and positivity of the denominator,

\[
|a_j|
\le \frac{C_jx^{j+1}(1+4^{j+2}y)}{2x-3}
<2C_jx^j.
\tag{2}
\]

Thus no outer Bernstein table is needed for the coordinate bound.

## 3. Complete infinite tail

For `n>=3`, (1) gives

\[
|e_{j,n}|\le
C_jn^{2j+4}x^je^{-(n^2-1)x}.
\]

Let `p=2j+4<=16`.  Consecutive majorants satisfy

\[
\frac{M_{n+1}}{M_n}
\le\left(\frac43\right)^{16}e^{-35}<\frac12
\qquad(n\ge3,x\ge5).
\]

The final inequality follows from the exact Taylor lower bound
`exp(35)>2(4/3)^16`.  Summing the entire geometric majorant—not a finite
truncation—yields

\[
|e_j|<2C_j3^{2j+4}x^je^{-8x}.
\tag{3}
\]

## 4. Weighted perturbation lemma

Let `N` be any of the three cleared raw-jet polynomials.  Each monomial has a
single derivative weight

\[
w=\sum_{j=0}^6j m_j:
\qquad w_q=2,\quad w_{F_2}=6,\quad w_{C_4}=12.
\]

For coordinate bounds `A_j` and `E_j`, the product telescoping inequality
gives, monomial by monomial,

\[
\left|\prod_j(a_j+e_j)^{m_j}-\prod_ja_j^{m_j}\right|
\le\prod_j(A_j+E_j)^{m_j}-\prod_jA_j^{m_j}.
\tag{4}
\]

Set

\[
\alpha_j=2C_j,\qquad
\beta_j=2C_j3^{2j+4},\qquad r=e^{-8x}.
\]

Equations (2)--(3) allow `A_j=alpha_j x^j` and
`E_j=beta_j x^j r`.  Weighted homogeneity factors every right side in (4)
as

\[
x^w\left(\prod_j(\alpha_j+\beta_jr)^{m_j}
-\prod_j\alpha_j^{m_j}\right).
\]

After summing coefficient absolute values, the bracket is a polynomial

\[
B_N(r)=\sum_{k\ge1}d_{N,k}r^k,\qquad d_{N,k}\ge0.
\tag{5}
\]

Every summand in `x^w B_N(e^(-8x))` is strictly decreasing on `[5,infinity)`:

\[
\frac d{dx}\left(x^we^{-8kx}\right)
=x^{w-1}e^{-8kx}(w-8kx)<0,
\]

because `w<=12`, `k>=1`, and `x>=5`.  Therefore the whole perturbation is
bounded by its endpoint value.  Using the exact inequality
`exp(-40)<1/(2*10^17)` gives

\[
\begin{array}{c|c|c}
N&|N(a+e)-N(a)|\text{ upper bound}&\text{required margin}\\ \hline
N_q&6.480000000000004\cdot10^{-11}&10\\
N_{F_2}&0.029494886400000975&1000\\
N_{C_4}&418286.5920007575&50000000.
\end{array}
\tag{6}
\]

The audit stores and compares the exact rational values, not these decimal
renderings.

## 5. Uniform two-mode margins

The two-mode cleared numerators themselves satisfy, for every `x>=5`,

\[
N_q(a)>10,\qquad N_{F_2}(a)>1000,\qquad
N_{C_4}(a)>50,000,000.
\tag{7}
\]

For `F2`, the shifted half-strip Bernstein coefficients are nonnegative for
`x=5+z`, `0<=3,000,000y<=1`, with a strictly positive constant floor.

For `q` and `C4`, write the exact numerator as

\[
B(x)+\sum_{k\ge1}S_k(x)y^k.
\]

The base `B` has positive coefficients after `x=10/3+z`.  Positive `S_k`
may be discarded.  For each negative piece `S_k=-M_k`, exact shifted
coefficients prove

\[
3kM_kB-M_k'B+M_kB'>0.
\]

Consequently `M_k(x)e^(-3kx)/B(x)` is strictly decreasing.  At `x=10/3`,
the sums of the rational upper endpoint ratios are respectively

\[
\frac{4499}{50550}<1,
\qquad
\frac{513927052752896}{602857191796875}<1.
\]

These are direct certificates for the cleared numerators, so no implicit
change from logarithmic invariants to cleared polynomials remains.

## 6. Universal conclusion

For each cleared polynomial, (6)--(7) give

\[
N(a+e)\ge N(a)-|N(a+e)-N(a)|>0
\qquad(x\ge5).
\]

This covers every point of the unbounded half-line and every mode in the
theta tail.  It does not rely on a terminal range check, a limiting premise,
or a relative error with an unproved nonzero reference.

Together with P000137's literal compact theorem on `x<=5`, this is the correct
mathematical architecture for the desired all-`t>=0` Lean theorem.
