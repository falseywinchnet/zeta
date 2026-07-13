# Exact PF4 separator certificate

Let `a=(1,3,4,2)`, extended by zero outside indices `0,1,2,3`, and let
`T(i,j)=a[j-i]`.

For a connected nonzero minor of order `k`, translate the row indices so the
least is zero. The support condition `0 <= j-i <= 3` makes the associated
bipartite graph disconnect across any row gap greater than three. Thus the
largest row index is at most `3(k-1)`. A column outside `0,...,3k` is zero or
disconnected. Every other minor is zero or factors into connected minors.
Consequently the exact enumeration in `scripts/verify_pf4_separator.py`
exhausts all Toeplitz minors through order four. It returns no negative
determinants among `4`, `63`, `1800`, and `60060` candidates respectively.
Hence `a` is PF4.

Write

`A(w)=1+3w+4w^2+2w^3=(1+w)(1+2w+2w^2)`.

The last factor has roots `(-1+i)/2` and `(-1-i)/2`, both of modulus
`1/sqrt(2)`. Symmetrize the discrete PF4 measure associated with `a` by
convolving it with its reflection, then convolve with a Gaussian. Composition
of totally positive kernels preserves PF4. The resulting kernel is positive,
even, entire, Schwartz, and PF4. Its Fourier transform is, up to a nonzero
Gaussian factor,

`A(exp(-iz)) A(exp(iz))`,

which has nonreal zeros because the two displayed roots do not lie on the unit
circle. Therefore PF4, and hence PF3, does not imply real-rootedness of the
Fourier transform, even with positivity, evenness, and Schwartz decay.

This separates PF3/PF4 membership from a real-zero conclusion. It does not
determine whether the Riemann kernel itself is globally PF3 or PF4, and it does
not exclude a separately defined kernel-specific transition invariant.
