# Results

Status: exploratory unless explicitly identified as an algebraic derivation.

## Exact-symbol cross-check

Truncated Fourier integration with eight Dirichlet modes gives:

| `a` | Fourier-symbol center | P000011 certified center |
|---:|---:|---:|
| 0.3 | `0.0101117500483` | `0.0101117508912` |
| 0.5 | `3.37950707869e-6` | `3.37951556782e-6` |
| 1.0 | `1.41670300928e-12` | `1.4167316571e-12` |

The remaining differences have the sign and scale expected from the omitted
positive logarithmic Fourier tail. This independent representation found and
fixed the raw-(r_0'')-transform sign.

## Relative spectrum

Using (h=\log(e+|\omega|)), the largest generalized value of (W u=\kappa H u)
for eight Dirichlet modes is approximately:

| `a` | `kappa_1` | `1-kappa_1` |
|---:|---:|---:|
| 0.3 | `0.9924353501` | `7.56e-3` |
| 0.5 | `0.9999976172` | `2.38e-6` |
| 1.0 | `0.9999999999991` | `9.13e-13` |

At (a=1), double precision saturates at larger dimensions. Several generalized
eigenvalues approach one, so a cluster certificate is required; a scalar
ground-vector residual is insufficient.

## Compact negative-part margins

For `V_mu=(mu-m_a)_+`, the estimated sufficient margin is:

| `a` | `mu` | `||K_V||` | `mu-||K_V||` |
|---:|---:|---:|---:|
| 0.3 | 1 | `0.9951891282` | `4.81087e-3` |
| 0.3 | 2 | `1.9930823604` | `6.91764e-3` |
| 0.5 | 2 | `1.9999995469` | `4.53091e-7` |
| 1.0 | 1 | `1.6045267916` | `-0.604527` |
| 1.0 | 2 | `3.1652210619` | `-1.16522` |

These are floating Nyström estimates, not interval bounds. The positive margins
at 0.3 and 0.5 are the strongest certificate candidates from this round.

## Trial-space comparison

Conditional 300-zero minima:

| `a` | basis | dim 8 | dim 16 | dim 24 |
|---:|---|---:|---:|---:|
| 0.3 | Dirichlet | `0.0101107` | `0.00905513` | `0.00861637` |
| 0.3 | periodic | `0.00786127` | `0.00739472` | `0.00732714` |
| 0.5 | Dirichlet | `3.37714e-6` | `1.09779e-6` | `1.07833e-6` |
| 0.5 | periodic | `1.43912e-6` | `1.19507e-6` | `1.01993e-6` |
| 1.0 | Dirichlet | `1.41577e-12` | numerical zero | numerical zero |
| 1.0 | periodic | `2.31269e-13` | numerical zero | numerical zero |

These values are conditional finite-zero diagnostics. The collapse at (a=1)
is a precision warning, not a certified zero eigenvalue.

## Preserved failures

1. The first Fourier-symbol implementation used the wrong sign for the raw
   truncated (r_0'') transform and produced a spurious negative Ritz value.
2. The constant-baseline negative-part operator fails at `a=1` and at several
   smaller thresholds, although it succeeds numerically at selected thresholds
   for `a=0.3` and `a=0.5`.
3. Absolute block coupling remains nondecaying.
4. The elementary relative high-frequency bound decays only as (1/\log R).
5. Double precision cannot resolve the clustered (a=1) generalized spectrum
   beyond the initial eight-mode scale.
