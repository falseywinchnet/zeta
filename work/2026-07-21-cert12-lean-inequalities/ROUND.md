# CERT12 Lean inequalities

- Mode: advancement
- Date: 2026-07-21
- Model: OpenAI Codex
- Starting MIND records: P000072, P000124, P000134, R171--R173,
  R189--R194, CERT12, CERT21
- Question: reconstruct the three first-mode-normalized strict inequalities
  for `clearedQ`, `clearedF2`, and `clearedC4` as Lean-checkable analytic
  statements, without treating the external verifier result as a proof term.
- Status: completed as an advancement round; the global Lean sign theorem is
  not yet closed

## Initial decomposition

The proof has three layers:

1. finite rational Bernstein positivity for the exact two-mode margins;
2. analytic bounds for the normalized modes-three-and-higher derivative tail;
3. deterministic perturbation transfer from the two-mode margins to the full
   three cleared polynomials.

This round first constructs reusable Lean certificate semantics for layers 1
and 3, then connects as much of the literal theta-series layer as can be
checked without introducing an opaque oracle.

## Acceptance criterion

The target is a theorem universally quantified over every real kernel input.
A finite point mesh, regardless of density, cannot discharge it.  A compact
Bernstein certificate is admissible only because its basis theorem proves the
inequality at every real point in the box; it must be paired with a universal
proof on the complementary half-line.  This round does not claim the target:
the actual infinite theta-tail estimates have not yet been replayed in Lean.

## Compression discovered

`verify_compact_two_mode.py` replaces the exploratory 361-coefficient
two-dimensional two-mode certificate by the following exact structure.

- `q-10`: one harmful exponential term and one decreasing-ratio proof on the
  whole half-line from `157/50`.
- `F2-1000`: two degree-11 one-variable Bernstein checks (24 coefficients)
  on `[157/50,10/3]`, followed by shifted coefficient positivity and one sign
  split on the half-line.
- `C4-50000000`: one degree-13 one-variable Bernstein check (14 coefficients)
  on `[157/50,16/5]`, followed by decreasing ratios for the only two harmful
  exponential terms.

The script uses exact rational polynomial algebra only and has no sampled
sign decisions.  It is a design certificate for the next Lean implementation,
not a substitute for that implementation.
