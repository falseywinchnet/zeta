# PF4: six analytical proof obligations

- Mode: advancement
- Date: 2026-07-13
- Model: Sydney, OpenAI Codex
- Starting MIND records: R101, R111, R112, R113, R137, R138, R153,
  R156, R83, R94
- Starting progress: P000031
- Status: complete as an advancement round; resolved-tail boxes proved,
  collision compression obstruction preserved, global PF4 still open

## Question

Can the two sufficient Peano densities from P000031 be proved nonnegative for
the Riemann translation curvature, thereby proving that the translation
kernel is PF4 entire?  If either stronger density is false, preserve the
obstruction and return to the exact original numerator `J`; do not infer PF4
failure from failure of a sufficient condition.

## Six obligations

1. Produce compact common-subexpression forms for the 24-term numerator of
   `S_r` and the 74-term numerator of `J_b`, retaining exact positive
   denominators.
2. Substitute the normalized positive-tail variables `X,U,V` and isolate the
   exact exponential positive parts.
3. Prove a resolved-gap positive-tail regime from the existing `E2`--`E5`
   error boxes.
4. Bound the fourth- and fifth-order collision remainders using `C4`, its first
   two derivatives, and the order-eight theta jet.
5. Transfer the positive-tail result by reflection and prove dominance when
   one endpoint escapes while the other two remain bounded.
6. Determine whether either sufficient monotonicity density changes sign by
   analytic reduction and isolated premise tests only.  No broad numerical
   sweep is admissible evidence.

## Evidence discipline

Every symbolic identity is checked by exact algebra.  Numerical evaluations,
if used, are named diagnostics and cannot establish a sign on a continuum.
All conclusions, including failed routes and counterexamples, remain in this
directory for later refinement.
