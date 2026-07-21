# Infinite-tail theorem refactor

- Mode: advancement
- Date: 2026-07-21
- Model: OpenAI Codex
- Starting MIND records: P000135, P000134, P000128, R171--R173,
  R189--R194, CERT12, CERT21
- Question: can the modes-three-and-higher seam be stated and proved as one
  global analytic theorem, rather than seven unrelated interval constants?
- Status: completed; the literal infinite tail is eliminated from the
  theorem-facing boundary by a closed Lean theorem

## Acceptance criterion

The exported conclusion must exclude a counterexample at every real input.
No sampled range is evidence for this theorem.  Intermediate compact
certificates are acceptable only when their semantics quantify over every
real point of the compact set and a universal theorem covers its complement.

## Refactor direction

Write `x = pi * exp (2*t)`.  Scale the `j`th normalized jet coordinate by
`x^j`.  The three cleared polynomials are weighted homogeneous of weights
`2`, `6`, and `12`, while their first-two-mode margins have natural degrees
`1`, `3`, and `6`.  The intended replacement for seven constant tail bounds
is one theorem of the form

```text
forall j <= 6,
  abs (normalizedTailJet j t) <= x^j * D j * exp (-8*x).
```

Together with global weighted bounds on the two-mode jet, a scalar
Lipschitz perturbation theorem can compare the tail directly with margins
proportional to `x`, `x^3`, and `x^6`.  Since
`x^(1,3,6) * exp(-8*x)` decreases for `x >= 3`, the comparison has one
analytic endpoint and no artificial `x=5` split.

## Final refactor

The coarse weighted envelope was still unnecessarily wasteful in jet six.
The successful statement peels off the exact `n=3` mode and proves that the
literal `n>=4` `tsum`:

1. has the same alternating sign as `n=3` through order six;
2. is strictly less than `10^-3` of the exact `n=3` coordinate.

Consequently, for every `t>=0` and `j<=6`, Lean proves

```text
normalizedSeriesJet j t
  = normalizedModeJet j 0 t
  + normalizedModeJet j 1 t
  + normalizedModeJet j 2 t * (1 + delta)
```

for some `0 <= delta < 1/1000`.  This is an exact theorem about the literal
infinite series.  No tail assumption remains.
