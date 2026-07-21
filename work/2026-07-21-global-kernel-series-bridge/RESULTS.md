# Results

## Closed boundary

`GlobalKernelSeriesBridge.lean` proves the exact nonnegative-axis
representation theorem

```lean
theorem globalRiemannKernel_eq_thetaSeries_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    globalRiemannKernel t = thetaSeries t
```

The proof is independent of any `abs` or piecewise kernel definition.

1. `hasSum_nat_gaussian` extracts the paired positive Gaussian modes from
   mathlib's Jacobi theta series.
2. `riemannH_eq_base_add_hSeries` identifies the global `H` value with its
   constant mode plus the positive series.
3. `hCertPoly`, `hModeJet`, and `HIntervalControl` give a polynomial-geometric
   majorant on every interval `(-1,B)` and justify two termwise derivatives.
4. `secondOrder_hMode_eq_thetaMode` checks the exact summand identity.
5. `secondOrder_hSeries_eq_thetaSeries` passes the operator through the sum.
6. The constant mode is differentiated separately and annihilated by
   `D² - 1/4`, giving the final global-kernel equality for `t ≥ 0`.

In displayed form, the checked conclusion is

\[
\frac{H''(t)-H(t)/4}{2}
=\sum_{n\ge 1}
\left(4\pi^2n^4e^{9t/2}-6\pi n^2e^{5t/2}\right)
e^{-\pi n^2e^{2t}},\qquad t\ge0.
\]

## Evidence boundary

This closes the representation bridge only. It does not prove a PF4 minor or
any CERT12 strict sign. The six-derivative positive-side jet from P000128 and
the global smooth/even continuation from P000129 remain separate inputs for
the next transport theorem.

## Replay

From `proof/formal/`, run one Lean process:

```sh
lake env lean ../../work/2026-07-21-global-kernel-series-bridge/GlobalKernelSeriesBridge.lean
```

The command exits successfully. The file contains no `sorry`, `admit`, or
custom `axiom`.
