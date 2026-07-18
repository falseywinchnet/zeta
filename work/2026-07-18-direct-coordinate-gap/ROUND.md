# Direct coordinate-gap positivity

- Date: 2026-07-18
- Mode: advancement
- Model: OpenAI Codex (Sydney)
- Starting MIND references: R101, R111, R112, R113, R137, R138, R153, R83, R94
- Starting progress: P000097
- Target obligation: PO-0037
- Status: integrated at P000099

## Question

Can strict positivity of the proof-facing closed `coordinateGap` be proved
without measures, probability CDFs, or complement identities?

## Boundary

The permitted inputs are the actual closed endpoint object, positive continuous
curvature, the explicit unique density crossing, exact integral normalization,
and positive interval lengths. No gap value or tail mass may be assumed
positive.

## Result

`DirectCoordinateGap.lean` compiles four linked statements:

1. `coordinateGap_pos_of_normalized` proves strict interior positivity from
   the closed branches, the explicit density crossing, and exact normalization.
2. `coordinateGap_continuous_of_normalized` proves that the left and right
   closed branches meet at `z` by exact mass cancellation, hence the piecewise
   coordinate gap is continuous.
3. `coordinateGap_pos` specializes the first theorem to the actual coordinate
   definitions of `delta` and `Lambda`, deriving both normalization identities.
4. `coordinateTransportNumerator_pos_closed` derives continuity of the
   displayed curvature-weighted integrand and proves the actual transport
   numerator strictly positive.

No measure is constructed. No probability object, CDF, complement identity,
assumed-positive gap, assumed-positive tail mass, `sorry`, or `admit` occurs.

## Proof mechanism

On the left of `z`, split at the explicit unique density crossing. Before the
crossing, the cumulative gap is an integral of a strictly positive density
difference. After the crossing, exact total-mass cancellation rewrites it as a
strictly positive right-tail density integral plus a nonnegative reverse-density
integral. On the right of `z`, the gap is directly the positive right-tail
integral. The normalized left and right formulas agree at `z`, so the closed
piecewise gap is continuous and may be integrated against the positive
curvature weight.

## Next boundary

P000099 audited and integrated the direct PO-0037 and PO-0040 candidates into
`PF4.Cumulative` and `PF4.Transport`, updated the obligation ledger to 8/46,
and retained the older measure/CDF route as an independent validation
interface. The next advancement boundary is the exact object-level identity
connecting this deterministic transport numerator to the displayed partial-xi
expression; its sign implication already exists.
