# Curvature-coordinate realization

- Date: 2026-07-20
- Model: Sydney, OpenAI Codex
- Mode: advancement
- Starting MIND records: R153, R164, R173, R180
- Starting progress: P000117
- Question: Can the coordinate `y=-logSlope` and its inverse be constructed
  honestly on `range y`, and can the first coordinate jets be derived rather
  than assumed?
- Status: complete candidate; pending refine integration

## Boundary

Construct the coordinate inverse without assuming that `y` is surjective.
Define `Q=q∘y⁻¹` and its first two coordinate derivatives, prove their exact
realization at `y(u)`, and identify coordinate curvature with the S03
`F₂/q³` expression.

## Result

The candidate constructs an equivalence from `ℝ` to `range y`, proves that
range open, and proves the canonical inverse extension differentiable at every
range point. It derives the complete coordinate jet `Q,Q₁,...,Q₄`, the exact
identity `κ=1+F₂/q³`, and equality of the maintained coordinate determinant
with the original cumulant determinant `C₄` on the coordinate range.

The maintained actual-kernel objects `logSlope` and `kernelCurvature` are
specialized explicitly for the `Q` and `Q₁` realization identities. No
surjectivity of `y`, off-range derivative, certified sign statement, or global
strict-PF4 conclusion is claimed.

## Build discipline

Check only `CurvatureCoordinateRealization.lean` from `proof/formal`, with one
Lean process at a time. Do not rebuild maintained modules in this advancement
round.
