# Initial results

Status: raw numerical observations. None is a MIND fact or an RH result.

## 1. Independent form comparison

Trial space: first eight Dirichlet sine modes on `(-1,1)`.

| `a` | direct midpoint, grid 400 | decomposed form, GL 220 | parity of computed ground state |
|---:|---:|---:|:---|
| 0.1 | 0.482480907114 | 0.482395763323 | even |
| 0.3 | 0.0101518476068 | 0.0101031974612 | even |
| 0.5 | 0.0000536693521 | -0.0000208459550 | even |
| 1.0 | 0.0000369655527 | -0.000577058434 | even |

The disagreement is negligible on the scale of the form before the first prime
threshold. It becomes sign-changing when the true cancellation scale falls below
the quadrature error. The negative decomposed values are not negative trial
quotients: the numerical integral error is larger than the reported value.

## 2. Quadrature convergence near cancellation

Decomposed representation, `N=8`:

| GL order | `a=0.5` | `a=1.0` |
|---:|---:|---:|
| 80 | -2.28889073e-4 | -4.54208635e-3 |
| 120 | -7.81398443e-5 | -1.97794739e-3 |
| 180 | -3.28100788e-5 | -8.67578426e-4 |
| 260 | -1.39671415e-5 | -4.10550513e-4 |
| 400 | -3.95295208e-6 | -1.68953806e-4 |
| 600 | 1.19075711e-7 | -7.12714535e-5 |

Direct midpoint representation, `N=8`:

| grid | `a=0.5` | `a=1.0` |
|---:|---:|---:|
| 100 | 6.14301066e-4 | 4.25834710e-4 |
| 200 | 1.80422340e-4 | 1.33508649e-4 |
| 400 | 5.36693521e-5 | 3.69655527e-5 |
| 800 | 1.71980021e-5 | 1.01368433e-5 |

Both elementary quadratures converge too slowly to resolve `a=1`. Their opposite
sign tendencies are nevertheless a useful implementation diagnostic.

## 3. Conditional zero-sum cross-check

Equation (3.1), evaluated only at the first 200 numerical critical-line zero
pairs, gives the following positive partial matrices for `N=8`:

| `a` | smallest eigenvalue of 200-pair partial matrix |
|---:|---:|
| 0.3 | 1.01093260626e-2 |
| 0.5 | 3.37381357067e-6 |
| 1.0 | 1.41439373993e-12 |

The piecewise-adaptive one-dimensional kernel reduction subsequently produced:

| `a` | adaptive kernel Ritz value | maximum reported scalar quadrature error |
|---:|---:|---:|
| 0.3 | 1.01117508912e-2 | 6.77e-12 |
| 0.5 | 3.37951556796e-6 | 8.05e-12 |
| 1.0 | 1.41653696018e-12 | 5.50e-12 |

This reduction splits at every prime-power kink and uses an analytic
derivative-correlation function, so it avoids tensor singular quadrature. The
`a=1` value is smaller than the reported entrywise quadrature error and its sign
is not certified, despite agreement with the zero-sum diagnostic.

At `a=0.3`, this agrees with both continuous-kernel representations. At `a=0.5`,
it falls between their convergence sequences. At `a=1`, it demonstrates the
severity of cancellation but does not approximate the full lowest Ritz value
without a zero-tail matrix bound.

Increasing the number of zero pairs from 25 to 200 increased each partial
matrix in Loewner order, as expected. This monotonicity is conditional on using
real critical-line zeros and applies only to the sampled partial sum.

## 4. Trial dimension warning

For the same 200-pair partial sum, the smallest eigenvalue decays rapidly with
trial dimension:

| `a` | `N=2` | `N=4` | `N=8` | `N=12` |
|---:|---:|---:|---:|---:|
| 0.3 | 1.1801e-2 | 1.1328e-2 | 1.0109e-2 | 9.4456e-3 |
| 0.5 | 3.2227e-3 | 9.7094e-5 | 3.3738e-6 | 1.2881e-6 |
| 0.75 | 6.6312e-4 | 2.5358e-6 | 1.2931e-9 | 4.5890e-12 |
| 1.0 | 1.2531e-4 | 2.1722e-8 | 1.4144e-12 | 1.9595e-15 |

A finite zero sum has finite rank and will eventually acquire an exact nullspace.
The decay therefore cannot be interpreted as decay of the true operator ground
state. For a fixed finite trial space, a usable spectral calibration requires an
explicit tail bound for the omitted zeros.

## 5. Structural checks

- `Lambda(n)` is nonzero exactly at the expected prime powers through 10.
- `g(0)=0` and the implementation is even.
- Finite differences of the pointwise remainder agree with the analytic `r''`
  formula at `u=0.1,0.5,1.2` within `8e-7`.
- The analytic sine-basis Fourier transform agrees with adaptive quadrature to
  twelve decimal places on the tested points.
- The two form representations agree before the first prime threshold within
  the deliberately loose quadrature-regression tolerance `2.5e-3`.

## 6. Small-interval asymptotic

Suzuki's Theorem 1.4 gives

\[
\mu_1=\lambda_a-\log(1/a)+\log(2\pi)+\gamma+O(a).
\]

The adaptive kernel computation gives:

| modes | `a` | Ritz `lambda` | inferred finite-`a` `mu_1` |
|---:|---:|---:|---:|
| 12 | 0.005 | 3.15998833386 | 0.276764... |
| 12 | 0.010 | 2.48324738240 | 0.293170... |
| 16 | 0.005 | 3.15366914950 | 0.270445... |
| 16 | 0.010 | 2.47704904961 | 0.286972... |
| 20 | 0.005 | 3.14979467154 | 0.266570... |
| 20 | 0.010 | 2.47324758759 | 0.283171... |

A linear two-point extrapolation in `a` at `N=20` is approximately `0.2500`.
The value decreases with trial dimension, as a Ritz upper approximation should.
The computed ground state is even and separated from the second eigenvalue by
about `1.19` in the `N=20`, `a=0.005` run. This reproduces positivity,
simplicity, parity, and the asserted logarithmic scale numerically. Neither the
extrapolation error nor the infinite-dimensional trial-space error is certified.

## 7. What the computations do and do not say

They do say:

1. The equation normalizations are mutually consistent after correcting the
   prime-scaling error recorded in `ROUND.md`.
2. The translation-invariant two-dimensional kernel matrix reduces exactly to
   piecewise one-dimensional integrals.
3. The small-interval asymptotic is numerically consistent with a positive
   limiting `mu_1` near `0.25`.
4. Prime terms cause extreme, structured cancellation at modest interval size.
5. A certification strategy must control quadrature and spectral tails at the
   matrix level.

They do not say:

1. that any displayed negative value is a true negative Rayleigh quotient;
2. that any displayed positive value lower-bounds `lambda_a`;
3. that the finite critical-line zero sum is an unconditional form identity;
4. that the large-`a` endpoint is numerically resolved.
