# Next boundary: localize the three object statements

The arbitrary off-range extension mismatch is closed.  The final adapter now
needs only `IntervalObjectBoundary`, whose fields are structural and local.

The next advancement should remove those fields in this order:

1. localize `coordinateGap_pos_of_normalized` and
   `coordinateGap_continuous_of_normalized` from global continuity of
   `curvature Q2`, `Q`, and `Q1` to `ContinuousOn` the relevant compact
   intervals;
2. use the already constructed local jet to discharge the localized closed-gap
   continuity and strictness theorems;
3. localize the FTC and integration-by-parts lemmas used by
   `expandedTransportK_eq_coordinateTransportIntegral`, passing derivatives
   and continuity only on `Icc p w` and its two subintervals;
4. discharge the local central identity with the same coordinate jet and top
   continuity package;
5. only after those three fields disappear, integrate P000118 and this round
   into maintained Lean in a refine round.

Do not replace any field by a terminal sign, positive free numerator, arbitrary
smooth extension, or `range y = ℝ`.  The actual kernel derivative tower and
the certified `q`, `F2`, and determinant-C4 signs remain explicit
certificate-to-Lean inputs until their maintained constructions are present.

