# Failure ledger

## Raw truncated-remainder sign

The first `symbol_probe.py` version added the raw Fourier transform of
`r0'' 1_{(-2a,2a)}`. Equation (2.5) requires subtracting it. That version
produced the stale diagnostic files `relative-a0.3.txt`, `relative-a0.5.txt`,
and `relative-a1.txt`; they are retained as the failure trace and must not be
used as results.

The corrected relative outputs contain `-corrected` in their names. The compact
and ordinary `symbol-a*.txt` outputs were regenerated after the correction.

## Absolute one-block complement

The prior P000011 failure remains: absolute coupling norms do not decay. The
new Fourier residual calculation confirms that full block norms remain large
even when individual low-eigenvector residuals are small.

## Constant-baseline limit

The compact negative-part sufficient bound works numerically at selected
thresholds for `a=0.3` and `a=0.5`, but fails for all tested thresholds at
`a=1`. It is not a universal replacement for the relative formulation.

