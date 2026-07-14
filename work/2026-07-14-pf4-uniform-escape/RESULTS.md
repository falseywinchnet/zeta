# Results

- Proved a collision-regular right-escape lower bound for the exact full-kernel
  PF4 numerator when `-1<=x<m<=1` and `pi exp(2r)>=32768`.
- Proved a direct, parity-correct left-escape lower bound when
  `-1<=m<r<=1` and `pi exp(-2x)>=32768`.
- The common coordinate radius is `R_*=log(32768/pi)/2`, approximately
  `4.626238912`.
- The proof uses a 2,048-cell directed one-dimensional certificate only for
  compact curvature constants.  The escape variables are handled by exact
  positive-coefficient polynomial shifts; no sweep supplies a sign.
- The right bound preserves the `m-x=0` face through the Peano quotient
  `delta=I/B^2`.  The left bound is proved in the original orientation and
  does not assume that `J` is reflection invariant.

Status: advancement proof support.  Independent refine-round audit and MIND
integration remain required.
