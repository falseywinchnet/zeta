# Results

## Clear line at `a=0.5`

For `V=(2-m_{1/2})_+`, the positive half-line splits into 13 active bands before
`z=118.411`. The analytic cutoff bound gives `m_{1/2}(z)>2.0146` for `z>=130`.
The remaining classified boundary slivers have full trace below `1.04e-13`.

The directed analytic-band integration completed all entries of the 72-mode
Legendre compression; `a05-matrix.tsv` preserves them. Floating reconnaissance
places the compact-operator margin near `4.53e-7`. The useful observation is its
scale: the compact mechanism persists past the first prime term, but only in a
thin numerical corridor.

## `a=1` cluster

The 160-mode floating diagnostic consistently sees:

- 11 generalized eigenvalues above `1-1e-3`;
- 9 above `1-1e-6`;
- 7 or 8 above `1-1e-9`;
- a leading margin below the resolution of double precision at cuts 32--128.

For an eight-vector retained cluster, the finite outer coupling decreases from
`2.22e-5` at cut 32 to `1.19e-6` at cut 128. The corresponding proxy Schur cost
`c^2/delta` decreases from `1.90e-3` to `8.49e-5`, while the next finite margin
is about `1.68e-8`. This is still vastly larger than the near-ground-state
margin. Merely enlarging the Fourier cutoff is therefore not a viable closure.

The cluster is the signal. It is stable enough to name, but its coupling does
not decay on the ground-state scale. Cutoff growth is therefore set aside.

## Direction

The compact and relative calculations agree on the strategic boundary:
finite compression is descriptive at larger `a`; it is not the continuation
mechanism. The continuation mechanism must govern the operator as `a` moves or
replace spectral closure by an exact arithmetic mapping statement.
