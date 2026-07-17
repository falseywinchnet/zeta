# Mathematics

## Conventions and scaling

Let `Phi` denote the doubled kernel used in the current paper and let `phi_M`
denote the normalization and coordinate in Michałowski's paper. Directly from
the two displayed theta series,

\[
 \Phi(t)=2\phi_M(t/2).
\]

For the equal-step Toeplitz determinant

\[
 D_r(u,h)=\det[\Phi(u+(i-j)h)]_{i,j=0}^{r-1},
\]

this gives

\[
 D_r^{\rm ours}(u,h)=2^rD_r^M(u/2,h/2).
\]

Writing `m=r(r-1)` for the confluent exponent,

\[
 C_r^M(u)=2^{m-r}C_r^{\rm ours}(2u).
\]

At order five the confluent scale factor is `2^15=32768`, while a finite
determinant has scale factor `2^5=32`. Raw values cannot be ranked until this
conversion is made.

For consecutive nodes,

\[
 V(0,\ldots,r-1)=\prod_{j=1}^{r-1}j!,
\]

so the Vandermonde and factorial factors in the two-sided confluent formula
cancel exactly:

\[
 C_r(u)=(-1)^{r(r-1)/2}\det[\Phi^{(i+j)}(u)]_{i,j=0}^{r-1}.
\]

Thus `C5=H5` in the paper's convention.

## Confluent threshold

High-precision theta summation gives the first positive zero

\[
 u_c=0.0622795266356228914879435511139761806023\ldots.
\]

In Michałowski's coordinate this is

\[
 u_c/2=0.0311397633178114457439717755569880903012\ldots.
\]

The sign is negative below this zero and positive immediately above it. A wide
scan finds no later zero. The global uniqueness statement is not yet a
certificate in this advancement round.

Put

\[
 x=\pi e^{2u},\qquad y=e^{-3x},\qquad z=e^{-8x}.
\]

After removing the common positive first-mode amplitude, the first three theta
modes have derivative jet

\[
 a_j=P_j(x)+4yP_j(4x)+9zP_j(9x),
\]

where

\[
 P_0(x)=2x-3,\qquad
 P_{j+1}=\left(\frac52-2x\right)P_j+2xP_j'.
\]

The exact determinant `det[a_(i+j)]_(i,j=0)^4` factors as a positive monomial
times a polynomial of degree 23 in `x`, degree 5 in each of `y,z`, and only 231
nonzero monomials. Its path derivative is obtained from

\[
 \frac{d}{du}=2x(\partial_x-3y\partial_y-8z\partial_z).
\]

The three-mode zero is

\[
 u_{c,3}=0.0622795266365508082000861167786219362464\ldots,
\]

only `9.279167...e-13` above the full-series candidate. This gives a short
formal route: prove the 231-term polynomial has one crossing, then absorb
`n>=4` with the same geometric derivative-tail technique used at the origin.

## Finite-spacing outer intercept

The outer boundary of the negative component connected to `h=0` is not the
confluent point. Numerically it is a tangency solving

\[
 D_5(u,h)=0,\qquad \partial_hD_5(u,h)=0.
\]

The candidate is

\[
 \begin{aligned}
 u_f&=0.0638435718036738292563841696516556800858\ldots,\\
 h_f&=0.0463846589476232612946983689306631150192\ldots.
 \end{aligned}
\]

Here `partial_u D5>0` and `partial_h^2 D5>0`, so this is locally the first
finite-spacing intercept encountered while moving from large center toward
the origin. In Michałowski's coordinate both numbers are divided by two.

A log-scaled scan over `0<=u<=1.5`, `0.01<=h<=1.5`, augmented by the alignment
rays `h=u/k`, found no farther negative component. This is reconnaissance, not
a global exclusion proof.

## Depth versus intercept

If "largest witness" means outermost center, the candidate is the tangency
`(u_f,h_f)` and the boundary value itself is zero; witnesses occur immediately
inside it. If it means greatest negative magnitude, it is a different point.
The equal-step Toeplitz search gives

\[
 u=0,\qquad h=0.10553396\ldots,qquad
 D_5=-1.067974810074\ldots\times10^{-7}.
\]

In the common half-amplitude normalization this is approximately
`-3.33742128148e-9`, about 1.81 times the magnitude of the published
`-1.84723607344e-9` configuration. The published configuration itself becomes
`-5.91115543502e-8` under the paper's doubled normalization, exactly by the
factor `2^5`.

