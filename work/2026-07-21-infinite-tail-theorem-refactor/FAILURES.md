# Failed and superseded formulations

## Single coarse weighted envelope

The initial refactor attempted one bound
`abs tail_j <= D_j*x^j*exp(-8*x)`.  It is globally valid in principle, but the
uniform degree-six polynomial envelope loses too much at the left endpoint;
an absolute perturbation estimate then obscures the available `C4` margin.

## Seven unrelated coordinate constants

The previous core/outer split can be formalized, but it hides the fact that
all tail modes have one alternating sign and that `n=3` overwhelmingly
dominates.  It is superseded by the exact relative-tail theorem.

## Monotone invariant hope

Adding the tail is not uniformly beneficial to all three cleared invariants:
the actual tail decreases `clearedQ` and `clearedC4` near the origin while it
increases `clearedF2`.  Sign structure alone therefore does not close the
invariants; the proved relative magnitude is essential.
