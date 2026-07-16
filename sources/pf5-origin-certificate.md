# Riemann-kernel origin PF5 certificate

Status: refine-round audit of the advancement result in
`work/2026-07-16-rainstar-pf5-witness/`.

## Claim

For the analytic even Riemann kernel `Phi`, put

\[
 H_k(0)=\det[\Phi^{(i+j)}(0)]_{i,j=0}^{k-1}.
\]

The certificate proves

\[
 H_4(0)>0,\qquad H_5(0)<0.
\]

The negative order-five sign transfers by confluent divided differences to
genuine equally spaced translation minors at every sufficiently small
positive step. Hence the Riemann kernel is not PF5. The result uses neither an
external PF5 paper nor the decimal coordinates in CITE2.

## Derivative series

For `x=pi*n^2*exp(2u)`, the `n`th summand of the positive-side kernel series is

\[
 e^{u/2-x}P_0(x),\qquad P_0(x)=2x(2x-3).
\]

If the `j`th derivative is `e^(u/2-x) P_j(x)`, direct differentiation gives

\[
 P_{j+1}(x)=2xP_j'(x)+(1/2-2x)P_j(x).
\]

Thus

\[
 \Phi^{(j)}(0)=\sum_{n\ge1}e^{-\pi n^2}P_j(\pi n^2).
\]

The verifier generates the polynomials through order eight over the exact
rationals.

## Directed rational enclosure

The proof arithmetic uses only Python integers and rational constants. Every
interval endpoint lies on `10^-36 Z`; addition, subtraction, multiplication,
integer powers, and rational scaling round outward after each operation.

Machin's identity

\[
 \pi=16\arctan(1/5)-4\arctan(1/239)
\]

is enclosed by alternating rational series through indices 24 and 6. For a
positive rational `r`, write `r=m y`, where `m=ceil(r)` and `0<=y<=1`.
The degree-29 and degree-30 alternating Taylor sums enclose `exp(-y)`; raising
their positive endpoints to the `m`th power encloses `exp(-r)`.

Only the modes `n=1,2,3` are evaluated. Let `S_j` be the sum of the absolute
coefficients of `P_j`. Since `deg P_j=j+2`, `3<pi<22/7`, and

\[
 e^3>\sum_{r=0}^8\frac{3^r}{r!}>20,
\]

for `n>=4` and every required `j<=8`,

\[
 |P_j(\pi n^2)|e^{-\pi n^2}
 \le S_j(22/7)^{j+2}n^{2j+4}20^{-n^2}.
\]

The ratio of successive majorants is at most

\[
 r_*=(5/4)^{20}20^{-9}<1.
\]

Therefore the complete omitted tail is bounded by the `n=4` majorant divided
by `1-r_*`. This deliberately coarse bound already leaves large sign margins.

## Parity blocks

Write `s_j=Phi^(j)(0)`. Evenness gives `s_j=0` for odd `j`. Applying the same
parity permutation to the rows and columns preserves each determinant and
gives

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
 s_0&s_2&s_4\\s_2&s_4&s_6\\s_4&s_6&s_8
 \end{pmatrix}.
\]

The replay gives the exact-rational consequences

\[
 445<A<446,\qquad 189223<B<189228,
\]

\[
 -674000000<C<-614000000.
\]

Consequently `H_4(0)=AB>0` and `H_5(0)=CB<0`.

## Distinct-node implication

For `f` of class `C^(2k-2)` near `z`, and fixed strictly increasing tuples
`a` and `b`, repeated row and column divided differences give

\[
 \lim_{h\downarrow0}
 \frac{\det[f(z+h(a_i-b_j))]_{i,j=0}^{k-1}}
 {h^{k(k-1)}V(a)V(b)}
 =\frac{(-1)^{k(k-1)/2}}
 {\prod_{r=0}^{k-1}(r!)^2}
 \det[f^{(i+j)}(z)]_{i,j=0}^{k-1}.
\]

Take `k=5`, `z=0`, and `a_i=b_i=i`. The sign factor is `(-1)^10=1`, both
Vandermonde factors are positive, and the right side is strictly negative.
Hence

\[
 \det[\Phi((i-j)h)]_{i,j=0}^{4}<0
\]

for every sufficiently small positive `h`. These are translation minors at
strictly increasing nodes. No explicit coordinate threshold is required.

## Replay boundary

`scripts/verify_pf5_origin.py` runs the exact advancement verifier. The MIND
certificate hashes the launcher, the complete verifier, its preserved output,
and this proof record. The replay uses the Python standard library only and
takes about 0.05 seconds on the development machine.
