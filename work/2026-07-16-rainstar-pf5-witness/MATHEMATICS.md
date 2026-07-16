# Direct order-five obstruction at the origin

## Statement

Let

\[
 \Phi(u)=\sum_{n\ge1}e^{-\pi n^2e^{2u}}
 \left(4\pi^2n^4e^{9u/2}-6\pi n^2e^{5u/2}\right)
\]

on the positive half-line, with its analytic even continuation to the real
line. Define

\[
 H_k(0)=\det[\Phi^{(i+j)}(0)]_{i,j=0}^{k-1}.
\]

The retained certificate proves

\[
 H_4(0)>0,\qquad H_5(0)<0.
\]

The second sign alone implies that `Phi` is not PF5. Together with the paper's
independent strict global PF4 theorem, it gives exact Polya-frequency order
four without CITE4 or the decimal witness in CITE2.

## Derivative series

Put `x=pi*n^2*exp(2u)`. The `n`th summand is

\[
 e^{u/2-x}P_0(x),\qquad P_0(x)=2x(2x-3).
\]

If its `j`th derivative is `e^{u/2-x}P_j(x)`, direct differentiation gives

\[
 P_{j+1}(x)=2xP_j'(x)+(1/2-2x)P_j(x).
\]

Consequently

\[
 \Phi^{(j)}(0)=\sum_{n\ge1}e^{-\pi n^2}P_j(\pi n^2).
\]

The verifier generates `P_0,...,P_8` from this recurrence using exact
rational coefficients.

## Elementary enclosures

Only three modes are evaluated. The certificate encloses `pi` from Machin's
identity

\[
 \pi=16\arctan(1/5)-4\arctan(1/239)
\]

using alternating rational sums through indices 24 and 6. For a positive
rational `r`, write `r=m y` with integer `m=ceil(r)` and `0<=y<=1`.
Alternating Taylor sums through degrees 29 and 30 enclose `exp(-y)`; raising
the positive endpoints to the `m`th power encloses `exp(-r)`.

All endpoints are then rounded outward to the grid `10^-36 Z`. Every addition,
subtraction, multiplication, integer power, and rational scaling rounds
outward on that same grid. Thus the fixed precision limits the size of the
integers but does not turn the computation into floating-point arithmetic.

For the tail, let `S_j` be the sum of the absolute coefficients of `P_j`.
Since `deg P_j=j+2`, `pi<22/7`, and `pi>3`, for `n>=4`

\[
 |P_j(\pi n^2)|e^{-\pi n^2}
 \le S_j(22/7)^{j+2}n^{2j+4}20^{-n^2}.
\]

Here `e^3>sum_{k=0}^8 3^k/k!>20`. For every needed order `j<=8`, the ratio of
successive majorants is at most

\[
 r_*=(5/4)^{20}20^{-9}<1.
\]

The entire omitted tail is therefore bounded by its `n=4` majorant divided
by `1-r_*`. This single deliberately coarse estimate suffices for all five
derivatives.

## Parity factorization

Write `s_j=Phi^(j)(0)`. Evenness makes every odd `s_j` zero. Simultaneously
permuting the rows and columns of the derivative Hankel matrices by parity
does not change their determinants. Hence

\[
 H_4(0)=AB,\qquad H_5(0)=CB,
\]

where

\[
 A=s_0s_4-s_2^2,\qquad B=s_2s_6-s_4^2,
\]

and

\[
 C=\det\begin{pmatrix}
 s_0&s_2&s_4\\ s_2&s_4&s_6\\ s_4&s_6&s_8
 \end{pmatrix}.
\]

The exact-rational output gives the simpler integer consequences

\[
 445<A<446,\qquad 189223<B<189228,
\]

\[
 -674000000<C<-614000000.
\]

Thus `H_4(0)=AB>0` and `H_5(0)=CB<0`.

## From confluence to distinct nodes

For `f` of class `C^(2k-2)` near `z`, fixed strictly increasing tuples
`a_0<...<a_(k-1)` and `b_0<...<b_(k-1)`, and positive `h`, repeated row and
column divided differences give

\[
 \lim_{h\downarrow0}
 \frac{\det[f(z+h(a_i-b_j))]_{i,j=0}^{k-1}}
 {h^{k(k-1)}V(a)V(b)}
 =\frac{(-1)^{k(k-1)/2}}
 {\prod_{r=0}^{k-1}(r!)^2}
 \det[f^{(i+j)}(z)]_{i,j=0}^{k-1}.
\]

The two Vandermonde factors are positive. For `k=5` the sign factor is
`(-1)^10=1`. Take `z=0` and `a_i=b_i=i`. Since the limit is `H_5(0)` divided
by a positive constant and is strictly negative, the determinant

\[
 \det[\Phi((i-j)h)]_{i,j=0}^{4}
\]

is negative for every sufficiently small positive `h`. Both node tuples are
strictly increasing. This is a genuine translation minor, so `Phi` is not
PF5. No numerical coordinates or explicit threshold for `h` are required.
