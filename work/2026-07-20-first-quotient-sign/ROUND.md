# First translation-quotient sign

- Date: 2026-07-20
- Model: Sydney, OpenAI Codex
- Mode: advancement
- Starting MIND records: R4, R154, R155, R156, R164, R171
- Starting progress: P000110
- Question: Can the first open sign premise of the maintained translation
  quotient tower be derived from an exact closed kernel-curvature formula,
  rather than assumed or renamed?
- Status: complete at the stated advancement boundary. The exact closed
  factorization and strict sign transfer are kernel-checked. This does not
  construct the Riemann kernel or formalize its certified global `q>0` input.

## Boundary

For positive `Φ` with jets `Φ1, Φ2`, define the actual logarithmic slope and
curvature directly from those same functions:

```text
S = Φ1 / Φ
q = (Φ1^2 - Φ*Φ2) / Φ^2.
```

Prove `S'=-q`, use `q>0` to prove that `S` is strictly decreasing, factor the
maintained `firstQuotD` exactly, and conclude its global strict positivity for
ordered columns.

## Evidence discipline

This round may take `q>0` as the literal upstream analytic sign boundary, but
may not assume `firstQuotD>0`, strict monotonicity of `S`, or any minor,
Wronskian, finite-difference, or integral sign.

## Result

`FirstQuotientSign.lean` proves:

1. the exact closed derivative identity `S'=-q`;
2. strict antitonicity of `S` from the literal pointwise sign `q>0`;
3. the exact factorization of the maintained `firstQuotD`;
4. global `firstQuotD>0` for every ordered pair of columns.

The final theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`. The next advancement boundary is the second quotient sign; it
must expose the exact `Λ` factor rather than assume positivity of
`secondQuotD` or an equivalent renamed Wronskian.
