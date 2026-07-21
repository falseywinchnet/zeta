# Theta-series jet advancement round

- Date: 2026-07-21
- Mode: advancement
- Model: OpenAI Codex
- Starting boundary: P000124; R171; R181; CERT12; CERT19
- Question: Can the literal positive-side Riemann theta kernel be connected to the
  ordinary six-derivative jet required by the cleared certificate bridge, without
  assuming the derivatives or hiding convergence behind an unevaluated `tsum`?
- Status: completed; the literal mode jet, central convergence base, and
  termwise-differentiation mechanism are proved.  The remaining interval
  coefficient estimate is isolated in `NEXT.md`.

## Intended boundary

1. Define the literal `n >= 1` theta summand.
2. Generate all derivatives from the CERT12 polynomial recurrence.
3. Prove in Lean that each recursive mode is the derivative of the preceding mode.
4. Separate pointwise summability, locally uniform derivative control, termwise
   differentiation, and the eventual even extension as distinct obligations.
5. Admit no `sorry`, custom axiom, or vacuous implication whose hypotheses merely
   restate the desired derivative jet.

## Outcome

See `RESULTS.md`.  The Lean artifact compiled successfully as a single process.
The formal result does not claim that a `tsum` differentiates merely because its
terms do: level-zero convergence is proved at `t = 0`, and every later level is
forced by an explicit summable majorant.

## Safety and scope

Lean is run one process at a time.  This advancement round writes only below this
directory; it does not promote claims into MIND or alter the maintained proof.
