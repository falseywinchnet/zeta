# R113 complement probe

Status: exploratory and uncertified. The projected-matrix certification in
`CERTIFICATION.md` does not extend to the calculations in this file.

## Setup

On the fixed interval write

\[
q_a=L+B_a,
\]

where `L` is Suzuki's positive logarithmic form and `B_a` contains the scalar
shift, finite prime translations, and smooth remainder kernel. The probe forms
large sine-basis matrices, solves the generalized eigenproblem for `L`, and
expresses `B_a` in that approximate `L` eigenbasis.

For a cutoff `N`, it records:

- `alpha`: smallest eigenvalue of the retained `q_a` block;
- `beta`: smallest eigenvalue of the finite tail block;
- `c`: spectral norm of the retained-to-tail coupling;
- the two-block lower estimate

\[
\frac{\alpha+\beta-sqrt{(\beta-\alpha)^2+4c^2}}2.
\]

This estimate is valid for the displayed finite matrix if its blocks are exact.
Here they are not: the singular product quadrature is floating point and creates
small negative eigenvalue artifacts. The experiment is used only to measure
whether coupling visibly decays.

## 64-mode observations

Quadrature order was 1000.

### `a=0.5`

| cutoff | coupling | tail `L` edge | tail `B` norm | block estimate |
|---:|---:|---:|---:|---:|
| 8 | 0.3029 | 3.1729 | 2.2121 | -0.0761 |
| 16 | 0.2782 | 3.8359 | 2.2121 | -0.0425 |
| 24 | 0.3212 | 4.2308 | 2.2121 | -0.0463 |
| 32 | 0.3216 | 4.5129 | 2.2121 | -0.0423 |
| 48 | 0.3215 | 4.9123 | 2.2113 | -0.0367 |

### `a=1`

| cutoff | coupling | tail `L` edge | tail `B` norm | block estimate |
|---:|---:|---:|---:|---:|
| 8 | 0.6323 | 3.1729 | 4.0611 | -0.6324 |
| 16 | 0.7546 | 3.8359 | 4.0502 | -0.7110 |
| 24 | 0.7567 | 4.2308 | 4.0260 | -0.5052 |
| 32 | 0.7813 | 4.5129 | 4.0197 | -0.5040 |
| 48 | 0.8165 | 4.9123 | 3.8111 | -0.4010 |

The coupling does not decay over the tested range. A low-`L` spectral projection
combined with a single coupling norm therefore does not approach the tiny
ground-state scale. At `a=1`, the coupling is roughly twelve orders of magnitude
larger than the certified eight-mode Ritz minimum.

## Crude analytic norm obstruction

Termwise contraction gives

\[
\|B_a\|\le |\log a+2A+1|
+2\sum_{n\le e^{2a}}\frac{\Lambda(n)}{\sqrt n}
+2a\sup_{0\le u\le2a}|r''(u)|.
\]

For `a<=1`, the same elementary argument used at the origin, enlarged to
`u<=2`, gives the safe coarse bound `|r''(u)|<4.5`. At `a=1`, this makes the
right side larger than 17. Such a bound discards precisely the cancellation that
produces the small positive projected eigenvalues. Since `L` has logarithmic
spectral growth, a proof based on this global norm would require an enormous
cutoff even if a sharp complement eigenvalue bound were available.

## Consequence for the next design

The simplest interpretation of R113 is not viable:

> low `L` modes + one global off-diagonal norm + one global tail norm.

The next design must preserve more structure. Candidates are:

1. a multiblock Schur scheme aligned with prime-translation scales;
2. a basis approximately invariant under the *combined* perturbation, with a
   validated residual rather than separate termwise norms;
3. a parity-separated enclosure plus certified lower bounds for higher states;
4. a renormalized comparison between consecutive prime-power thresholds.

The finite matrices show a useful spectral gap: at `a=1,N=8`, the first two
certified projected eigenvalues are approximately `1.42e-12` and `1.38e-10`.
Exploiting that gap would still require a full-space lower bound for the next
state or a validated invariant-subspace theorem. It cannot be inferred from the
finite block alone.
