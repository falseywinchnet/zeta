# Results

## Closed candidate boundary

`PoissonParityBridge.lean` uses the maintained literal real definitions and
proves the following without an `abs`-based or piecewise kernel definition.

1. `riemannTheta_modular` specializes
   `Real.tsum_exp_neg_mul_int_sq` to

   \[
   \vartheta(x)=x^{-1/2}\vartheta(1/x),\qquad x>0.
   \]

   Mathlib proves the imported theorem by Gaussian Fourier transform and
   Poisson summation. The positivity premise and normalization conversion are
   explicit in the local wrapper.

2. `riemannH_neg` and `riemannH_even` prove the exact paper parity

   \[
   H(-t)=H(t).
   \]

3. `riemannTheta_eq_evenKernel` and
   `riemannTheta_eq_re_jacobiTheta` identify the literal real sum with
   mathlib's Jacobi-theta realization on the positive axis.

4. `analyticAt_riemannH`, `contDiff_riemannH`,
   `analyticAt_globalRiemannKernel`, and `contDiff_globalRiemannKernel` prove
   global real analyticity and smoothness of the maintained `H` and kernel.
   The definitions remain real; complex analysis is proof infrastructure for
   regularity.

5. `globalRiemannKernel_even` proves kernel parity, and
   `globalRiemannKernel_eq_thetaSeries_abs` combines it with the previously
   checked nonnegative-axis termwise-differentiation theorem to obtain

   \[
   \Phi(t)=\operatorname{thetaSeries}(|t|)\qquad(t\in\mathbb R).
   \]

## Why this is an analytic foundation

The chain is exact and theorem-backed:

```text
literal real convergent sum
  -> Gaussian Poisson theorem
  -> theta modular identity
  -> parity
  -> Jacobi-theta holomorphy
  -> real analyticity and C-infinity regularity
  -> justified differential operator
  -> locally uniform termwise differentiation
  -> global reflected kernel series.
```

No numerical approximation establishes an identity or derivative. The later
rational certificates are needed only for strict signs of derived expressions.

## Evidence boundary

This round does not prove that `thetaSeries t` itself equals the kernel for
negative `t`; it proves the reflected positive-side form `thetaSeries |t|`,
which is sufficient for parity-based transport of half-line sign
certificates. It also does not identify the exact raw series jet with all
global iterated derivatives at the origin, nor import the CERT12 propositions
for `q`, `F2`, or `C4`.

## Replay

From `proof/formal/`, run serially:

```sh
lake env lean ../../work/2026-07-21-poisson-parity-bridge/PoissonParityBridge.lean
```
