# Findings

## Definitions

Put

\[
A(t)=\frac1{\xi(1/2+t)},\qquad
L(x)=\frac1{2\pi}\int_{\mathbb R}A(t)e^{-ixt}\,dt.
\]

The functional equation makes `A` positive and even on the real axis. Hence
`L` is real, even, and positive-definite. This does not imply `L>=0`.

PF1 is `L>=0`. If `L>0`, PF2 is equivalent to

\[
N_2(x)=L'(x)^2-L(x)L''(x)\geq0.
\]

## A positive spectral density for the PF2 numerator

Differentiating under the Fourier integral and symmetrizing gives

\[
N_2(x)=\frac1{8\pi^2}\iint_{\mathbb R^2}
(t-u)^2A(t)A(u)e^{-ix(t+u)}\,dt\,du.
\]

Thus

\[
N_2(x)=\frac1{2\pi}\int_{\mathbb R}B(v)e^{-ixv}\,dv,
\]

where

\[
B(v)=\frac1{4\pi}\int_{\mathbb R}(2t-v)^2A(t)A(v-t)\,dt>0.
\]

This proves that the PF2 numerator is positive-definite, but pointwise
positivity of its Fourier transform remains to be shown.

## Shifted contour

For `x>0` and a downward shift `0<a<gamma_1`, Cauchy's theorem gives

\[
L(x)=\frac{e^{-ax}}{\pi}\operatorname{Re}
\int_0^\infty\frac{e^{-ixu}}{\xi(1/2+u-ia)}\,du.
\]

This removes the catastrophic cancellation in direct real-axis quadrature.
The probes at shifts 4, 8, and 12 agree through their reliable ranges.

## Residue tail

Let `Xi(z)=xi(1/2+iz)`. Crossing a simple critical-line zero `gamma_n`
contributes

\[
c_ne^{-\gamma_nx},\qquad c_n=-\frac1{\Xi'(\gamma_n)}.
\]

For the first two zeros the computed values are

\[
\begin{aligned}
\gamma_1&=14.13472514173469\ldots,&c_1&=723.21269576658\ldots>0,\\
\gamma_2&=21.02203963877155\ldots,&c_2&=-56338.7384970265\ldots<0.
\end{aligned}
\]

Consequently

\[
L(x)=c_1e^{-\gamma_1x}+c_2e^{-\gamma_2x}+\text{remainder}
\]

has positive leading term, while

\[
N_2(x)=-c_1c_2(\gamma_2-\gamma_1)^2
e^{-(\gamma_1+\gamma_2)x}+\text{remainder}
\]

also has positive leading term. The leading PF2 coefficient is approximately
`1.932738016e9`. The two-residue prediction agrees with the shifted-contour
probe already at `x=2`, and to the displayed precision by `x=3`.

Selected shifted-contour values are:

| `x` | `L(x)` | `-(log L)''` |
|---:|---:|---:|
| 0 | 3.820844218071254 | 23.6574605606679 |
| 1 | 4.93155516228037e-4 | 2.22661944830909 |
| 2 | 3.81913228366899e-10 | 3.80394020787053e-3 |
| 3 | 2.77566218454069e-16 | 3.92804329400161e-6 |
| 4 | 2.01712825257063e-22 | 4.00719126195581e-9 |

These are observations, not interval enclosures.

## Candidate proof split

1. Prove `L>0` and `N_2>0` on a compact interval, plausibly `0<=x<=4`,
   using the real-axis integral for the large-margin part and the shift `a=12`
   for the cancellation-sensitive part.
2. Shift past the first two zeros for `x>=4`. Use their exact residue signs
   and bound the shifted-contour remainder and its first two derivatives.
3. Use an existing rigorous zero count below the chosen contour height to
   ensure that the crossed poles are exactly the listed simple critical-line
   zeros. This is finite zero information, not RH.

The architecture is one-dimensional and finite. PF1 appears distinctly easier.
PF2 is also plausible because the first two residue signs force the correct
tail sign, but its compact lower margin decays rapidly and requires scaled
enclosures. No global certificate has yet been proved.

## Local source

`platt-trudgian-rh-height.pdf` is the locally preserved arXiv source for the
rigorous verification of RH through height `3e12`. Its SHA-256 is
`3362f66af9fa9373977eee70e2282ec33989d5d8b97e0852df9e32cc25b52885`.
