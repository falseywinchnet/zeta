# Full-theta collision margins

Write `Phi=Phi1(1+R)` and `w=log(1+R)`.  Exact theta-series majorization gives

\[
 |D^j w|<{K_j\over X^4},\qquad 1\le j\le6,
\]

with the rational constants printed by `prove_positive_tail_transfer.py`.
Since `q=q1-w''`, exact positive-coefficient comparisons for the rational
first-theta jets imply, for `X>=23`,

\[
 X<q<8X,\qquad 0<q'<16X,\qquad 0<q''<32X.
\]

Consequently

\[
 |F_1|=|qq''-(q')^2|<512X^2.
\]

Using `C3=2q^3-F1`, its certified positivity, and `X>=23`,

\[
 0<C_3<(1024+512/23)X^3<1047X^3.
\]

The certified tail certificate supplies `C4>=44392X^6`.  The exact one-sided
collision identity therefore gives

\[
 S_r(m,m)={2qC_4\over3C_3^2}
 >{88784\over3288627}X>{X\over38}.
\]

For the generic collision `x=m-beta eps`, `r=m+alpha eps`, the exact divided
limit is

\[
 \lim_{\varepsilon\downarrow0}
 {J\over\beta(\alpha+\beta)^2\varepsilon^3}
 ={C_4\over12q^3}
 >{5549\over768}X^3>7X^3.
\]

These are full-theta margins on the collision faces.  They do not yet give a
collision radius; that requires a uniform bound for the next divided
coefficient and its remainder.
