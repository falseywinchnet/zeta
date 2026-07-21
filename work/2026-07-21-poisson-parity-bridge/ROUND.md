# Poisson parity bridge

- Date: 2026-07-21
- Mode: advancement
- Model: Sydney, OpenAI Codex
- Starting progress: P000131
- Starting references: R181--R184
- Starting certificates: CERT19--CERT20
- Status: complete advancement candidate

## Question

Can mathlib's real Gaussian Poisson-summation theorem be normalized directly
to the maintained literal `PF4.riemannTheta`, then used to prove evenness of
`PF4.riemannH` and `PF4.globalRiemannKernel` without changing any definition?

## Evidence boundary

The imported theorem must remain named and its exact positivity hypothesis and
normalization conversion must be visible. This round does not claim the
CERT12 signs, strict PF4, or an all-real termwise series representation.

## Result

The candidate compiles. It proves the exact real theta transformation,
global analyticity and smoothness of `riemannH` and `globalRiemannKernel`,
evenness of both, and the global reflected representation

```text
globalRiemannKernel t = thetaSeries |t|.
```

