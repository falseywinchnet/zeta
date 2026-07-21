# Results

## Closed boundary

`ThetaModularContinuation.lean` formalizes a non-circular global form of the
Riemann kernel.

1. `riemannTheta` is fixed to mathlib's zero-characteristic real Hurwitz
   kernel.
2. `hasSum_int_riemannTheta` proves that, for `x > 0`, it is exactly

   \[
   \sum_{n\in\mathbb Z} e^{-\pi n^2x}.
   \]

3. `riemannTheta_modular` proves the paper's exact transformation

   \[
   \vartheta(x)=x^{-1/2}\vartheta(1/x).
   \]

   The imported mathlib theorem is proved from Poisson summation; the
   zero-characteristic specialization and normalization identification are
   explicit here.
4. `riemannH_neg` and `riemannH_even` prove

   \[
   H(t)=e^{t/2}\vartheta(e^{2t}),\qquad H(-t)=H(t).
   \]

5. `riemannHComplex` gives a local holomorphic realization near every real
   point. `analyticAt_riemannH` and `contDiff_riemannH` prove that the global
   real `H` is smooth to all orders independently of evenness.
6. `globalRiemannKernel` is defined directly by

   \[
   \Phi(t)=\frac12\left(H''(t)-\frac14H(t)\right),
   \]

   with `globalRiemannKernel_eq_paper_form` checking the displayed ordinary
   derivative form. `continuous_globalRiemannKernel` and
   `globalRiemannKernel_even` prove continuity and evenness.

## Why this form is legal

No definition contains `|t|`, a sign branch, a stored derivative jet, or a
smoothness premise. The theta modular equation proves evenness of the already
global object. The global kernel is obtained by applying a differential
operator to a globally smooth function.

Consequently, equality with the positive-side `thetaSeries` from P000128 is a
later representation theorem. It cannot be circularly used to manufacture
smoothness at zero, because smoothness is already proved from holomorphy.

## Evidence boundary

This round proves no CERT12 strict sign and no PF4 minor. It closes the modular
identity, global continuation, smoothness, and even-kernel construction only.
The three exact sign certificates remain independent inputs.

## Replay

From `proof/formal/`, run one Lean process:

```sh
lake env lean ../../work/2026-07-21-theta-modular-continuation/ThetaModularContinuation.lean
```

The file contains no `sorry`, `admit`, custom `axiom`, or unsafe bridge.
