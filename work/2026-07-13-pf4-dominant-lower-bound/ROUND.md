# PF4 dominant-theta collision-divided lower bound

- Mode: advancement
- Date: 2026-07-13
- Model: Sydney, OpenAI Codex
- Starting records: R145, R153, R156, CERT2, CERT5
- Starting progress: P000035
- Status: complete advancement artifact; explicit positive-tail bounds proved

## Question

Extract explicit lower bounds from the positive-coefficient one-theta-term
polynomials for `J_b` and `S_r`, after removing their forced collision factors.

## Evidence discipline

Every lower bound must follow from exact rational identities and coefficient
signs.  Floating evaluations may diagnose a candidate comparison but cannot
establish it.

## Outcome

Exact shifted-coefficient comparison gives uniform rational lower bounds for
both dominant-theta densities.  Monotonicity of the dominant curvature then
converts the `J_b` comparison into a collision-divided lower bound for `J`
itself, uniform in both gap sizes and their ratio.
