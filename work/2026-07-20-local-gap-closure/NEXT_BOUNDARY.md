# Next boundary: range-local central identity

Only the central object equality remains. The next advancement should prove it
directly on `Icc p w`, avoiding the globally continuous measure wrappers.

A shorter local route than rebuilding the full measure interface is available:

1. prove local derivative formulas for `closedGapLeft` and
   `closedGapRight`; their rates are respectively
   `leftMuDensity - leftNuDensity` and `-rightNuDensity`;
2. split the transport integral at `z` and integrate `gap * A'` by parts on
   `[p,z]` and `[z,w]`; endpoint terms at `p` and `w` vanish, while the two
   values at `z` cancel by the local continuity theorem from this round;
3. obtain the direct density-integral difference
   `nuLeft + nuRight - mu` without introducing measures;
4. localize the two elementary primitive FTC calculations for `transportH`
   and `transportJ`, reducing those three density integrals to the maintained
   endpoint expression;
5. apply the existing purely algebraic
   `expectationEndpoint_eq_expandedTransportK` cancellation;
6. instantiate the resulting local central identity with the P000118 jet and
   remove the last premise of
   `coordinatePartialXiPsi_neg_on_Icc_of_centralIdentity`.

This route uses only compact-interval derivatives and integrability. Do not
construct global extensions, introduce measure/probability assumptions, or
take the terminal sign as input.

