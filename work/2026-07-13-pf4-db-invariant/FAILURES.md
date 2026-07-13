# Preserved enclosure failures

## Independent one-large-gap boxes

The P000032 relative endpoint boxes prove `J_b>0` when both adjacent tail
ratios are at least two.  Repeating the coefficient argument with only one
ratio at least two produces negative lower coefficients in both orientations.
The calculation is exact and stored in `test_one_large_gap_box.py`.

This does not exhibit a negative `J_b`.  Near a collision, endpoint errors and
primitive errors are derivatives and integrals of the same theta remainder;
treating them as independent destroys the cancellations forced by `C4` and
`N6`.

## Initial rational reduction

The first version of `prove_one_term_tail_density.py` requested global SymPy
factorization before coefficient extraction and did not finish within seven
minutes.  Replacing that unnecessary factorization by exact denominator
collection completed and produced the 1,863-term positive polynomial.  No
mathematical conclusion was drawn from the interrupted run.
