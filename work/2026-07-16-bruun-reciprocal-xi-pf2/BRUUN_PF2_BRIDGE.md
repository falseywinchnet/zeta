# Normalized Bruun factorization as a PF2 certificate engine

## Source map

The relevant objects in `../bfft`, read at commit
`60c68a671a6d8f27bb778facece201afcb291ed9`, are:

- `experiments/scratch_bruun.py`: real factorization of `z^N-1` and the
  polynomial-remainder interpretation of each Fourier bin.
- `experiments/scratch_normbruun.py`: readable normalized power-of-two
  reference and the exact Bruun leaf permutation.
- `src/detail/bruun_dif_kernel.hpp`: production normalized DIF factor tree and
  stable half-angle recurrence.
- `src/detail/bruun_dit_kernel.hpp`: normalized DIT merge and its exact inverse.
- `src/detail/bruun_dif_dit_kernel_audit.md`: the unit-frame interpretation
  `F=sqrt(N) Q`, with `Q` orthogonal.
- `experiments/cone_fft_gauged.py`: positive two-sheet lift and mass-potential
  gauge.
- historical `notes/genbruun_port_handoff.md` at commit `8e18f8c`: the
  condition-one cascade identity for arbitrary composite sizes.

## The local cell

For `c^2+s^2=1`, the normalized Bruun cell sends

```text
(A0,B0,A1,B1) ->
(A0+cB0-sB1, A1+sB0+cB1, A0-cB0+sB1, -A1+sB0+cB1).
```

If `M(c,s)` is this real matrix, direct multiplication gives

```text
M(c,s)^T M(c,s) = 2 I.
```

The binomial cell `(a,b)->(a+b,a-b)` has the same identity. Consequently every
normalized stage is a uniform dilation times an orthogonal map. The full real
Fourier transform, in the paired residue coordinates used by BFFT, is
`sqrt(N)` times an orthogonal map. Its inverse is the reverse cell schedule
with the transpose and the known factors of `1/2`.

This matters for certification: perturbations have an exact Euclidean gain,
with no small-angle `1/sin(theta)` loss and no anisotropic interval growth.

## Positive two-sheet lift

For a real matrix `M`, write `M=M_+-M_-` entrywise and lift it to

```text
L(M) = [[M_+, M_-], [M_-, M_+]].
```

If a signed state is represented by nonnegative rails `(p,n)` with `x=p-n`,
then projection intertwines the lift and the original cell:

```text
pi L(M) = M pi,  pi(p,n)=p-n.
```

The backward potential in `cone_fft_gauged.py` rescales every wire so that the
lifted cells are column-stochastic. Total rail mass is then conserved by
transport and decreases only at explicit local annihilations. This produces an
exact error and cancellation ledger made entirely of nonnegative quantities.

The lift does not make an arbitrary Fourier coefficient positive. It replaces
hidden complex cancellation by the explicit comparison `p_out>n_out`, which is
considerably easier to enclose and audit.

## Application to reciprocal-xi PF2

Put

```text
A(t) = 1/xi(1/2+t),
L(x) = (2 pi)^(-1) integral A(t) exp(-ixt) dt.
```

For positive `L`, PF2 is equivalent to positivity of

```text
N2(x) = L'(x)^2 - L(x)L''(x).
```

The prior exact symmetrization gives a single Fourier transform

```text
N2(x) = (2 pi)^(-1) integral B(v) exp(-ixv) dv,
B(v) = (4 pi)^(-1) integral (2t-v)^2 A(t)A(v-t) dt > 0.
```

This is the natural Bruun input. It avoids subtracting separately computed
values of `L'^2` and `L L''`. On a symmetric dyadic `v` grid, one normalized
real Bruun transform evaluates every dyadic `x` node of the quadrature at once.
The two-sheet lift keeps the positive density and all later cancellation in
nonnegative rails. The unit-frame identity converts input enclosure error
`e` into the sharp transform bound

```text
||F_N e||_2 = sqrt(N) ||e||_2,
```

before the quadrature normalization. The gauged lift additionally supplies an
exact `l1` mass ledger when that is sharper.

For intervals between Fourier nodes, apply the same transform schedule to
`v^j B(v)` for several small `j`. These are the derivatives of `N2`; a local
Taylor enclosure then avoids a global first-derivative bound. All derivative
channels share the same twiddles and error geometry.

## Honest boundary

This factorization simplifies the compact certificate, not the theorem by
itself. A complete PF2 proof still needs:

1. rational or directed enclosures for the sampled convolution density `B`;
2. truncation and quadrature remainders for `B` and the weighted densities
   `v^j B`;
3. a finite Taylor cover on the compact `x` interval;
4. a separately scaled residue/contour argument where `N2` becomes extremely
   small.

The existing first-residue height-16 certificate is sufficient for PF1, but
PF2 tail dominance naturally requires the first two residues and a contour
above the second zero. Bruun does not remove that analytic tail step.

## Recommended next experiment

Build a slow exact reference, not a production FFT binding:

1. choose a modest power-of-two symmetric grid for `B(v)`;
2. enclose `B`, `vB`, ..., `v^mB` at every input cell;
3. replay the readable normalized cells with interval endpoints and the
   positive two-sheet gauge;
4. compare its certified node margins and propagated error against direct
   interval cosine quadrature;
5. accept the pathway only if it reduces both runtime and certificate size.

The likely useful split is a Bruun/Taylor compact proof followed by a
two-residue contour proof. No claim about the sign of `N2` is made here.
