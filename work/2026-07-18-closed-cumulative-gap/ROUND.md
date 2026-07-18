# Closed cumulative gap

- Date: 2026-07-18
- Mode: advancement
- Model: OpenAI Codex (Sydney)
- Starting MIND references: R101, R111, R112, R113, R137, R138, R153, R83, R94
- Starting progress: P000095
- Target obligations: PO-0037 and the deterministic interface preceding PO-0039
- Status: complete advancement candidate; awaiting refine-round audit

## Question

Can the cumulative triangular weights and their gap be expressed directly in
endpoint values of `Q` and `Q1`, so that probability-measure language is only
an optional semantic bridge rather than the proof's primary object?

## Boundary

This is advancement work. No submitted-paper file is changed and no MIND
claim is established in this round. The candidate must compile without
`sorry`, `admit`, or detached positive symbols.

## Result

`ClosedCumulativeGap.lean` compiles and replaces cumulative-integral notation
by endpoint formulas. On `[p,z]` the gap is

\[
\frac{-(z-y)^2-(z-y)Q_1(y)-Q(y)+(z-p)^2+(z-p)Q_1(p)+Q(p)}
     {(z-p)^2\delta}
-\frac{(y-p)^2-(y-p)Q_1(y)+Q(y)-Q(p)}{(z-p)\Lambda}.
\]

On `[z,w]` it is the single right-tail expression

\[
\frac{(w-y)^2+(w-y)Q_1(y)+Q(y)-Q(w)}{(w-z)\Lambda}.
\]

The Lean candidate defines these deterministic functions before mentioning
measures, proves the endpoint formulas from explicit antiderivatives, and
identifies them with the normalized density integrals. Both endpoint zeros are
definition-level theorems. The probability/CDF vocabulary is therefore an
optional interface, not the source of the formulas.

## Clean-build finding

Clearing the generated Lean cache exposed that the P000095 curvature FTC
lemmas had compiled earlier only in a richer stale import environment. The
source omitted the FTC integrability premise and direct imports for derivative
powers and inverses. `PF4/Curvature.lean` was repaired so continuity supplies
the integrability hypotheses explicitly. A clean dependency-cache restoration
and full `lake build PF4` now succeed.

## Next refine edge

Promote the deterministic closed forms into a module preceding `PF4.CDF`, add
thin equality bridges from the existing measure-backed cumulative functions,
and rename the proof-facing objects away from probability terminology while
retaining the measure implementation as a validation interface.
