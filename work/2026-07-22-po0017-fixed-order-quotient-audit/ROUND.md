# PO-0017 fixed-order quotient/Wronskian audit

- Mode: advancement
- Date: 2026-07-22
- Model: OpenAI Codex
- Starting MIND IDs: R154, R156, CERT5, CERT18
- Question: does the maintained Lean tree contain every exact fixed
  order-four quotient/Wronskian identity printed in S05, with the correct
  endpoint orientation?
- Status: complete

## Audit finding

The discrete determinant cascade, literal quotient derivative tower,
translation-minor identity, and separated-minor assembly are maintained.
The paper's two explicitly displayed confluent identities
`W3=u1^3 W(v2,v3)` and
`W4=u1^4 v2^3 w3^2 (w4/w3)'` were not exported as named Lean theorems.

## Gates

- add only fixed sizes three and four;
- use the literal maintained quotient derivatives;
- prove the reversed `p4<p3<p2<p1` orientation from increasing columns;
- no sign premise and no target determinant premise in algebra identities;
- arbitrary-order quotient generalization is optional and out of scope.

## Result

`PF4.FixedOrderQuotientWronskian` exports the exact fixed-order `W3` identity,
the three successive `W4` extractions, their assembled terminal product, and
the reversed endpoint orientation. The focused module build and axiom audit
pass. `CERT29` replays the audit. PO-0017 is closed at 38/41 active formal
obligations; arbitrary-order generalization remains optional and outside the
active denominator.
