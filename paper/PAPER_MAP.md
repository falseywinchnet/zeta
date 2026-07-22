# PF4 paper map

## Thesis

For the Riemann/de Bruijn--Newman kernel `Phi`, every translation minor of
order at most four is strictly positive at strictly ordered nodes. At spacing
`211/2000`, an exact rational enclosure gives a negative order-five
translation minor. The exact global Polya-frequency order is therefore four.

The positive half follows the dependency chain

`q,F2 > 0` -> `PF3 and Lambda > 0` -> `quotient reduction` ->
`C4 curvature identity` -> `positive closed gap` ->
`partial_xi Psi < 0` -> `strict PF4`.

## Included sections

| ID | File | Proof burden |
|---|---|---|
| `S00` | `sections/S00-abstract.tex` | Exact-order claim and proof mechanism |
| `S01` | `sections/S01-introduction.tex` | Main theorem and dependency outline |
| `S01a` | `sections/S01a-related-work.tex` | Finite-order and Riemann-kernel context |
| `S02` | `sections/S02-kernel.tex` | Theta definition, Poisson bridge, analytic parity, global jet |
| `S03` | `sections/S03-certified-inputs.tex` | Global `q>0`, `F2>0`, `C4>0` |
| `S04` | `sections/S04-pf3.tex` | `Lambda>0` and strict PF3 |
| `S05` | `sections/S05-quotient-reduction.tex` | Fixed-order quotient cascade and determinant integrals |
| `S06` | `sections/S06-curvature-coordinate.tex` | Curvature coordinate and sign bridge |
| `S07` | `sections/S07-confluent-invariant.tex` | `C4=Q^6 kappa^2 D` |
| `S08` | `sections/S08-transport-identity.tex` | Endpoint transport identity |
| `S09` | `sections/S09-crossing-kernel.tex` | Positive closed gap and central integral |
| `S10` | `sections/S10-completion.tex` | Strict PF4 assembly and direct negative PF5 witness |
| `S11` | `sections/S11-reproducibility.tex` | Objective verification criteria and finite replay |
| `S11a` | `sections/S11a-availability.tex` | Declarations and archival identities |
| `S12` | `sections/S12-references.tex` | References |
| `A1` | `appendices/A1-algebra.tex` | Cumulant and curvature factorization |
| `A2` | `appendices/A2-tail.tex` | Two-mode margins and analytic tail transfer |
| `A3` | `appendices/A3-endpoints.tex` | Endpoint substitutions |

## Verification boundary

The final theorem is
`PF4.globalRiemannKernel_pfOrderExactly_four`. Its positive and negative
inputs are `PF4.globalRiemannKernel_strictPFUpTo_four` and
`PF4.globalRiemannKernel_orderFive_translationMinor_neg`. Section `S11`
defines the pinned build, kernel check, axiom-closure audit, exact-arithmetic
criterion, and universal quantifier coverage.

## Editorial rules

1. The mathematical sections contain the proof, not implementation or
   provenance narration.
2. Formal-system and replay details occur only in the verification section.
3. The theorem path contains only claims needed for the exact-order result.
4. PF4 is never presented as an RH proof.
