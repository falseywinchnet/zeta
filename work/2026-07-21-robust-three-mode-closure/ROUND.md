# Robust three-mode closure

- Mode: advancement
- Date: 2026-07-21
- Model: OpenAI Codex
- Starting MIND records: P000136, P000135, P000134, R171--R173,
  R189--R194, CERT12, CERT21
- Question: prove the literal normalized `clearedQ`, `clearedF2`, and
  `clearedC4` inequalities with no remaining tail, range, or sign premise.
- Status: complete as a strict advancement round; the compact continuum and
  outer coordinate/tail bounds are closed, while the final outer sign transfer
  remains the next theorem and is not claimed here.

## Acceptance theorem

The round succeeds only if Lean proves all three strict inequalities for the
literal normalized theta-series jet at every `t>=0`, then the existing parity
bridge transports them to every real kernel input.  A bounded box is useful
only when its theorem quantifies over every point and the actual infinite tail
is proved to lie in it; both directions must be connected in Lean.

## Starting reduction

P000136 proves that every normalized jet coordinate equals its first two
modes plus its exact third mode multiplied by `1+delta_j`, with
`0<=delta_j<1/1000`.  This round connected that statement to the literal
series, proved a decreasing exact third-mode profile, certified the full
compact continuum through `x=5`, and established scaled base/tail bounds on
the entire outer half-line.

The acceptance theorem is not yet met.  The remaining edge is explicit: the
old constant outer perturbation budget cannot be compared to a scaled
two-mode margin which tends polynomially to zero.  The actual perturbation
decays exponentially, so the next theorem must retain that `x` dependence.
