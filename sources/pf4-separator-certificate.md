# Exact discrete PF4-sequence certificate

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
Hence `a` is a discrete PF4 sequence.

Write

`A(w)=1+3w+4w^2+2w^3=(1+w)(1+2w+2w^2)`.

The last factor has roots `(-1+i)/2` and `(-1-i)/2`, both of modulus
`1/sqrt(2)`. Autocorrelation gives the symmetric lattice weights
`(2,10,23,30,23,10,2)` on shifts `-3,...,3`. Gaussian smoothing therefore
produces a positive even Schwartz function whose Fourier transform is, up to
a nonzero Gaussian factor,

`A(exp(-iz)) A(exp(iz))`,

which has nonreal zeros because the two displayed roots do not lie on the unit
circle.

The missing implication is continuous PF4. The discrete Toeplitz certificate
does not make the lattice measure a continuous PF4 translation kernel, so the
usual continuous composition theorem cannot be invoked without an additional
mixed-domain argument. No Gaussian variance is specified or checked here.
Consequently this certificate does **not** establish a positive even Schwartz
PF4 separator, and it does not prove that continuous PF3 or PF4 membership is
insufficient for Fourier real-rootedness. A valid continuous separator, or a
theorem proving PF4 for one explicitly parameterized smoothing, remains open.
