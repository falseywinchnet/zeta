# Terminal quotient and coordinate-Psi bridge

- Date: 2026-07-20
- Model: Sydney, OpenAI Codex
- Mode: advancement
- Starting MIND records: R4, R141, R153, R154, R155, R156, R164
- Starting progress: P000114
- Question: Can the maintained terminal quotient derivative be identified
  exactly with the difference of the already maintained
  `PF4.CoordinateSignBridge.coordinatePsi` endpoint values, so that its sign
  follows from the literal coordinate-Psi decrease premise rather than from a
  renamed terminal sign?
- Status: complete candidate; pending refine integration

## Boundary

For ordered columns `a<c<b<d`, derive the third quotient sign from the first
and second conversion layers. The result may retain the actual-kernel
coordinate realization and strict coordinate-Psi decrease as explicit
premises. It may not assume `terminalQuotD > 0`, a Wronskian or minor sign, or
an unidentified rate difference.

## Build discipline

Work only in this directory. Check the candidate directly with
`lake env lean`; do not rebuild the maintained library unless a later refine
round chooses to integrate it.

## Result

`TerminalQuotientPsi.lean` proves:

1. exact equality of the S05 lower `Lambda`, its simultaneous derivative,
   and its `Psi` with the already maintained coordinate objects under the
   explicit curvature-coordinate realization;
2. the exact rate
   `secondQuotD2 = secondQuotD * (coordinatePsi - commonChord)` by
   differentiating the checked second-level factorization and using
   derivative uniqueness;
3. cancellation of the common chord in the terminal quotient;
4. the exact terminal identity
   `terminalQuotD = terminalQuot * (coordinatePsi(p_d)-coordinatePsi(p_b))`;
5. strict positivity from `a<c<b<d`, the existing first/second conversion
   hypotheses, the explicit coordinate realization, and literal strict
   decrease of the maintained `coordinatePsi` on ordered triples.

No terminal derivative, Wronskian, finite-difference, integral, or minor sign
is assumed. Actual-kernel `q>0`, lower-`Lambda>0`, coordinate realization, and
coordinate-Psi decrease remain named inputs for later instance integration.
