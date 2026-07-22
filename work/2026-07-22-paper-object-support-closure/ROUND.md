# Paper-object support closure

- Mode: advancement
- Date: 2026-07-22
- Model: OpenAI Codex
- Starting MIND IDs: R181, R202–R205, CERT19, CERT22–CERT25
- Question: can PO-0009, PO-0010, PO-0022, and PO-0029 be closed by
  literal actual-kernel statements without an off-range inverse assumption or
  a symbolic denominator convention?
- Status: closed; focused compilation, axiom audit, full build, and CERT26
  replay complete

## Exact targets

1. Define the maintained actual objects `ell`, `s`, and `q`; prove `exp ell =
   Phi`, `ell' = s`, `s' = -q`, and `q > 0` globally.
2. Define the maintained actual `A` and `M`; for every `a < b`, prove the
   denominator `A(a,b)` is strictly positive and prove its integral
   provenance `A(a,b) = integral_a^b q`.
3. Define coordinate `rho` and `kappa`; prove `rho = F2/q^3 > 0` and `kappa =
   1 + rho > 1` on the complete actual coordinate range.
4. Define the paper primitive rate `D`; prove `D > 0` on the complete actual
   coordinate range from the exact pointwise determinant factorization.

## No-cheating gates

- no sampled or bounded domain;
- no positivity, nonzero-denominator, or determinant premise in the final
  actual-kernel statements;
- no assertion that the coordinate map is onto all real numbers;
- no use of the arbitrary inverse extension outside its actual range;
- no RH consequence and no reopening of T1–T3.

## Result

- `actualLogSlopeCurvature_globally_wellDefined` closes PO-0009.
- `actualAM_wellDefined_on_ordered` closes PO-0010 and includes the exact
  fundamental-theorem-of-calculus identity `A=integral q`.
- `actualCoordinateRhoKappa_pos_on_range` closes PO-0022 on the complete
  actual coordinate range.
- `actualCoordinateD_pos_on_range` closes PO-0029 through the new pointwise
  determinant-to-rate transfer.
- All four public theorems use exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- The complete Lean build passes 3734 jobs.
- CERT26 replays the exact four-theorem public audit.
