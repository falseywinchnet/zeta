# Mathematical development

Status: raw advancement mathematics.

## 1. Exact Fourier multiplier

For (v) supported in ((-a,a)), Suzuki's equations (2.5)--(2.7) give

\[
Q_W^a(v)=\frac1{2\pi}\int_{\mathbb R}m_a(z)|\widehat v(z)|^2\,dz,
\]

with

\[
m_a(z)=\Re\psi\!\left(\frac14+\frac{iz}{2}\right)-\log\pi
-2\sum_{n\le e^{2a}}\frac{\Lambda(n)}{\sqrt n}\cos(z\log n)
-\widehat{r''_{0}\mathbf1_{(-2a,2a)}}(z).
\]

Here (r_0(t)=-4(e^{t/2}+e^{-t/2}-2)), so

\[
\widehat{r''_{0}\mathbf1_{(-2a,2a)}}(z)
=-4\frac{\tfrac12\sinh(a)\cos(2az)
+z\cosh(a)\sin(2az)}{z^2+1/4}.
\]

The last sign matters. Equation (2.5) contains
(-\langle r''*v,v\rangle). The digamma term already absorbs the signed
(r_1'') contribution, leaving minus the raw truncated (r_0'') transform.
Using the opposite sign produces a spurious large negative eigenvalue. With the
displayed sign, Fourier integration reproduces all three P000011 (N=8)
certified centers.

For the fixed-interval scaling (v(x)=w(x/a)), the Rayleigh form is

\[
q_a(w)=\frac1{2\pi}\int_{\mathbb R}m_a(\omega/a)
|\widehat w(\omega)|^2\,d\omega.
\]

This representation removes the weak spatial singularity and exposes the prime
translations as a finite trigonometric symbol.

## 2. Pointwise symbol geometry

The symbol is not pointwise nonnegative. At (a=1), the probe finds 41 negative
bands on the positive half-line through (z=1500), with a sampled minimum about
(-2.385). A further band occurs near (1549.9); none was found between there
and (5000) at mesh (0.05).

Since

\[
S_a=2\sum_{n\le e^{2a}}\frac{\Lambda(n)}{\sqrt n}
\]

is finite and the truncated (r_0'') transform is (O_a(|z|^{-1})), the
digamma asymptotic implies

\[
m_a(z)\ge \log\frac{|z|}{2\pi}-S_a-O_a(|z|^{-1}+|z|^{-2}).
\]

Thus all negative bands lie in a finite frequency interval for fixed (a). For
(a=1), (S_a\approx5.85247), giving the crude leading threshold
(2\pi e^{S_a}\approx2187). A directed digamma remainder would turn this into
an explicit pointwise-positive tail.

Pointwise positivity cannot prove the form positive, because the negative bands
are real. Compact support supplies the required uncertainty constraint.

## 3. Constant-baseline compact split

For (mu>0), write

\[
m_a\ge \mu-(\mu-m_a)_+.
\]

The correction has compact frequency support and defines a positive compact
convolution operator on ((-a,a)). The sufficient condition
(|K_{(\mu-m_a)_+}|\le\mu) would prove positivity.

This bound is viable at the first two tested scales. The estimated margins
`mu-||K||` are positive at `a=0.3` for `mu=1,2`, approximately `4.81e-3` and
`6.92e-3`. At `a=0.5, mu=2`, the margin is approximately `4.53e-7`. The other
tested thresholds at `a=0.5` fail.

At `a=1`, every tested `mu=0.1,0.5,1,2` fails; the best displayed deficit is
about `-0.6045`. The sufficient inequality loses too much positive surplus
there. Thus the compact negative-part route is a realistic certificate for
`a=0.3` and possibly `a=0.5`, but not the current `a=1` architecture.

## 4. Relative-compact formulation

Let

\[
h(\omega)=\log(e+|\omega|),\qquad
w_a(\omega)=h(\omega)-m_a(\omega/a).
\]

On the fixed interval, write (q_a=H-W_a). Formally set

\[
K_a=H^{-1/2}W_aH^{-1/2}.
\]

Then (q_a\ge0) is equivalent to the largest spectral value of (K_a) being at
most one.

This is the correct compact object. Indeed, (w_a/h\to0) as
(|\omega|\to\infty). Split frequency at (R). On ([-R,R]), restriction to
functions supported in ((-1,1)) factors through a band-limited integral
operator and is compact. Above (R), the relative form norm is bounded by

\[
\sup_{|\omega|>R}\frac{|w_a(\omega)|}{h(\omega)}\to0.
\]

Therefore (K_a) is compact. This replaces the nondecaying absolute prime-shift
norm by a relatively compact perturbation of logarithmic coercivity.

The crude displayed tail converges only like (1/\log R), so it is not yet a
usable (10^{-12})-scale certificate. Oscillation and exact matrix-element
bounds must be retained rather than collapsed into the supremum.

## 5. Quantitative logarithmic tail

Chen--Véron's individual eigenvalue estimate for the one-dimensional logarithmic
Laplacian implies, on ((-1,1)),

\[
\lambda_k\!\left(\tfrac12L_\Delta\right)
\ge \log\frac{k\pi}{2e}.
\]

Suzuki's positive reference form (L) adds Euler's constant, hence its
(k)-th eigenvalue obeys the candidate bound

\[
\lambda_k(L)\ge \log\frac{k\pi}{2e}+\gamma.
\]

This agrees with the observed logarithmic scale and supplies an explicit tail
edge once the normalization and hypotheses are checked in refinement. It does
not by itself control the arithmetic perturbation.

## 6. Domain-aligned trial spaces

The closed logarithmic form admits constants and other nonzero endpoint values.
Every finite Dirichlet sine trial vanishes at both endpoints. Although the sine
union is form-dense, boundary mismatch can make convergence slow.

Yoshida's restricted periodic space suggests the orthonormal fixed-interval
basis

\[
2^{-1/2},\quad \cos(n\pi x),\quad \sin(n\pi x).
\]

A conditional 300-zero comparison shows that this basis lowers and stabilizes
the (a=0.3) Ritz sequence faster: dimension 24 gives (0.007327) versus
(0.008616) for Dirichlet modes. At (a=1), both bases expose a cascade of very
small eigenvalues; the periodic basis reaches it sooner. This suggests genuine
near-null geometry rather than a Dirichlet-only artifact.
