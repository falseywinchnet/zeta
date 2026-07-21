# Outer perturbation proof analysis

- Mode: advancement
- Date: 2026-07-21
- Model: OpenAI Codex
- Starting MIND records: P000137, P000136, P000135, R171--R173,
  R189--R194, CERT12, CERT21
- Question: find a universal outer-half-line proof of the literal cleared
  `q`, `F2`, and `C4` signs, without a constant-box leak at infinity.
- Status: complete; a universal unscaled proof architecture was found and
  exact-audited.  Lean formalization is deliberately deferred to the next
  round.

## Rule for this round

Lean advancement is paused.  The round audits and redesigns the mathematical
outer argument.  No finite sample is evidence for the target theorem.  A
successful design must quantify over every `x >= 5`, retain the complete
infinite theta tail, and provide strict margins for all three cleared
polynomials.

## Starting observation

The constant scaled tail box from P000137 is a true bound but the wrong final
abstraction: the correspondingly scaled two-mode cleared values tend to zero.
The paper's original unscaled route instead uses weighted homogeneity.  This
round checks whether that route is complete and whether it admits a smaller,
more transparent proof.
