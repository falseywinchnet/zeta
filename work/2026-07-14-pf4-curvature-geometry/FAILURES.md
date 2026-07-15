# Failures and exclusions

## NumPy integration alias

The first plot-data run used the removed `numpy.trapz` alias and stopped before
writing any generated artifact.  Replacing it by `numpy.trapezoid` repaired the
mechanical failure.  No mathematical output from the failed run was retained.

## Tail geometry alone

Asymptotic resemblance to the Riemann score cone cannot be accepted without a
separator test.  The known Gaussian-smoothed PF4 separator has asymptotically
constant score curvature and therefore fails the Riemann condition `Q''>=0`
somewhere unless it is exactly Gaussian.  This distinguishes that realization,
but does not prove that outward score-convexity forces Fourier real-rootedness.

## PF4 alone

Positivity of `D=A'` is exactly the already established PF4 axis.  Rebranding
`D>0` as a new geometric condition would add no information and cannot imply
RH in view of the PF4 separator.

## Double-precision complex zero scan

The first adversarial-family scan reported apparent nonreal roots near the
edge of its search box.  A 70-digit direct integral and nonlinear solve sent
the strongest candidate at `30.3219+1.02746 i` to the real zero
`31.4077242599548`.  The apparent complex root was cancellation noise in a
Fourier transform many orders of magnitude below its value at zero.  The scan
now requires a separate high-precision integral confirmation and reports no
unconfirmed root as evidence.
