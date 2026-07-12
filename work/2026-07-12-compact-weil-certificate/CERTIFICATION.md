# Certification argument

Status: directed full-operator certificate at `a=0.3`. This does not address
larger scales and does not prove RH.

## 1. Fourier lower split

For functions supported in `(-a,a)`, Suzuki's Fourier formula gives

\[
Q_W^a(v)=\frac1{2\pi}\int_{\mathbb R}m_a(z)|\widehat v(z)|^2\,dz.
\]

At `a=0.3`, `exp(2a)<2`, so the prime-power sum is empty. Set `mu=1` and

\[
V(z)=(1-m_a(z))_+.
\]

Pointwise, `m_a >= 1-V`. If `K` is the positive convolution operator on
`L2(-a,a)` with Fourier multiplier `V`, then

\[
Q_W^a(v)\ge \|v\|_2^2-\langle Kv,v\rangle,
\qquad
\lambda_a\ge1-\|K\|.
\]

## 2. Compact frequency support

The code uses the exact signed symbol

\[
m_a(z)=\Re\psi(1/4+iz/2)-\log\pi
-\widehat{r_0''\mathbf1_{(-2a,2a)}}(z).
\]

For positive `z`, the series for the digamma function shows that
`Re psi(1/4+iz/2)` is increasing: differentiating its real-part series gives a
sum of positive terms. The raw remainder transform satisfies

\[
|\widehat{r_0''\mathbf1}(z)|
\le4\frac{\tfrac12\sinh a+z\cosh a}{z^2+1/4},
\]

whose right side decreases for `z>=22`. Arb gives the lower enclosure

```text
m_0.3(z) >= 1.061858142532649...  for z >= 22.
```

Therefore `V` is identically zero outside `[-22,22]`.

## 3. Directed range sums

On every frequency cell the implementation evaluates the symbol at its midpoint
with Arb and widens it by a global derivative bound. The bound is

\[
|m_a'(z)|\le\tfrac12\psi_1(1/4)
+\int_{-2a}^{2a}|t r_0''(t)|\,dt
\le 9.334945759739.
\]

This converts the midpoint into a range enclosure over the whole cell. Taking
the positive part interval then encloses `V` without locating its nonsmooth
zeros. Every integral is an interval Riemann sum of complete cell ranges.

No binary floating-point value is used in a bound. A float conversion is used
only to recover the already enclosed integer cell count.

## 4. Legendre compression and exact complement trace

Let `phi_n` be the normalized Legendre basis of `L2(-a,a)`. Its Fourier
transform is

\[
T_n(z)=\sqrt{2a(2n+1)}\,i^n j_n(az).
\]

The implementation evaluates `j_n` through its `0F1` representation. The cell
range is widened using

\[
|T_n'(z)|\le\|x\|_2\|\phi_n\|_2
=\sqrt{2a^3/3}.
\]

Let `P` project onto the first eight Legendre modes. Parseval applied to
`exp(izx)` gives the exact identity

\[
\sum_{n=0}^{\infty}|T_n(z)|^2=2a.
\]

Consequently the unresolved positive trace is

\[
\tau=\operatorname{tr}((I-P)K(I-P))
=\frac1\pi\int_0^{22}V(z)
\left(2a-\sum_{n=0}^7|T_n(z)|^2\right)dz.
\]

The same cell ranges enclose `tau` directly. Since `K` is positive, for every
unit vector split as `p+q`, Cauchy--Schwarz in the `K` form gives

\[
\langle K(p+q),p+q\rangle
\le\left(\sqrt{\lambda_{\max}(PKP)}\|p\|
+\sqrt\tau\|q\|\right)^2
\le\lambda_{\max}(PKP)+\tau.
\]

This controls the complete infinite-dimensional complement.

## 5. Finite eigenvalue enclosure

The interval Legendre matrix is replaced by its exact midpoint ball matrix. Arb
isolates the midpoint eigenvalues. Weyl's inequality widens the largest one by
the maximum row sum of entry radii. Adding the directed tail trace produces an
upper bound for `||K||`.

The main run yields

```text
||K|| <= 0.9962971374103319278341277203122
lambda_0.3 >= 0.003702862589668072165872279687848
```

The coarser independent run also remains positive:

```text
lambda_0.3 >= 0.0008337821885253995277789034834233
```

Thus the sign is stable under a fourfold change in cell width and increased
precision.

