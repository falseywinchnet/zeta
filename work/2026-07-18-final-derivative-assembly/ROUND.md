# Final derivative assembly

- Date: 2026-07-18
- Mode: advancement
- Model: OpenAI Codex (Sydney)
- Starting MIND references: R101, R111, R112, R113, R137, R138, R153, R156, R164, R83, R94
- Starting progress: P000102
- Target: remove the final central-identity premise from the PO-0041 derivative sign assembly
- Status: complete candidate; preserved through P000103

## Question

Do P000100, P000101, and P000102 compose into strict negativity of the
independently differentiated coordinate `Psi`, using only the actual
determinant `C4` positivity input and upstream regularity?

## Required joins

1. Identify P000101 `derivedC4` with P000102 `primitiveDerivedC4` exactly.
2. Transfer positivity from the determinant-defined `C4` to the transport
   weight without redefining either object.
3. Derive continuity of the curvature numerator from the derivative tower.
4. Supply P000101's central identity to P000100's exact PO-0027 sign bridge.

## Result

`coordinatePartialXiPsi_neg_from_determinantC4` proves strict negativity of
the derivative of the independently defined coordinate `Psi`. Its statement
contains no central transport identity, detached positive numerator, CDF-gap
sign, or curvature-numerator formula as a hypothesis.

The remaining analytic inputs are explicit:

- `p < z < w`;
- a global derivative tower `Q,Q₁,Q₂,Q₃,Q₄`, with `Q₄` continuous;
- global positivity of `Q` and curvature;
- global positivity of the primary central-moment determinant `C4`.

Curvature continuity, lower-jet continuity, the determinant-to-derived-`C4`
transfer, the central transport equality, numerator positivity, and the exact
negative derivative orientation are all derived inside the theorem.

## Boundary

PO-0041 is closed as an advancement candidate relative to its named upstream
analytic and certified sign inputs. The next formal assembly boundary is the
quotient/Wronskian transfer from strict `partialXiPsi < 0` to strict order-four
minors (PO-0017, PO-0018, PO-0020, and PO-0042), or a refine round can first
promote P000100--P000103 into the maintained Lean tree.

## Preservation

- Progress: P000103
- Commit: delegated to `MIND PROGRESS COMMIT`
