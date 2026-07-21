# Results

The advancement candidate closes the algebraic and differential layer between
CERT12's raw derivative interface and the maintained terminal cascade.

Principal checked theorems:

1. `normalizedJet_hasDerivAt` — the single normalized-moment recurrence.
2. `curvatureDerivativeTower_of_rawJet` — reconstruction of `q1` through
   `q4` from `Phi0` through `Phi6`.
3. `clearedQ_identity`, `clearedF2_identity`, and `clearedC4_identity` — exact
   positive-denominator identities.
4. `clearedC4_eq_rawHankel4_det` — equality of the expanded polynomial and the
   literal raw derivative Hankel determinant.
5. `kernelSigns_of_clearedSigns` — transfer of the three raw strict signs to
   the maintained kernel objects.
6. `actualCoordinatePartialXiPsi_neg_of_clearedJetSigns` — direct entry to the
   maintained actual-coordinate proof.
7. `terminalQuotD_pos_of_clearedJetSigns` — end-to-end terminal cascade from
   the raw jet and cleared signs.

The final theorem's analytic premises are:

```text
Phi0' = Phi1, ..., Phi5' = Phi6,
Continuous Phi6,
Phi0 > 0,
clearedQ > 0,
clearedF2 > 0,
clearedC4 > 0,
a < c < b < d.
```

The desired terminal sign and every intermediate curvature, coordinate, and
lower-cascade sign are conclusions.  All printed axiom sets contain only
`propext`, `Classical.choice`, and `Quot.sound`.
