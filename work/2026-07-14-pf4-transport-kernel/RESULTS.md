# Results

- Normalized the `delta` and `Lambda` triangular weights as probability
  measures `mu` and `nu`.
- Proved the exact cancellation identity
  `N/(delta Lambda) = E_nu[A]-E_mu[A]`, where
  `A'=C4/(Q^6 kappa^2)`.
- Converted the difference of expectations to
  `integral W C4/(Q^6 kappa^2)`, with `W=F_mu-F_nu`.
- Proved `W>=0` without numerical bounds: the left density ratio is strictly
  decreasing and the right component makes the terminal left CDF gap
  positive.
- Identified the only sign-indefinite representation: the oriented fiber
  integral under the independent product coupling when its two left samples
  arrive in reverse order.
- Removed that artifact by the monotone quantile coupling, obtaining an
  explicitly positive double integral.
- Checked the cancellation exactly for generic degree-five polynomial `Q`
  with symbolic interval lengths, and numerically for an unrelated analytic
  non-polynomial `Q`.

This is a candidate completion of the global PF4 inequality from the already
certified global confluent `C4>0` statement R152.  It is not established in
MIND during this advancement round.
