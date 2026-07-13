# Mathematics

## Compact operator line

Let `m_a(z)` be the corrected localized-Weil symbol and put

`V(z)=(2-m_{1/2}(z))_+`.

For functions supported in `[-a,a]`, positivity follows from

`2 I-K_V >= (2-||K_V||) I`,

where `K_V` is the positive time-frequency concentration operator with
quadratic form `integral V(z)|F(z)|^2 dz/pi`.

The normalized Legendre basis has transform amplitudes

`A_n(z)=sqrt(2a(2n+1)) j_n(az)`

up to unit phases. Completeness gives the exact diagonal identity

`sum_{n>=0}|A_n(z)|^2=2a`.

For the first `N` modes, let `M_N` be the compression of `K_V`. Positivity and
the trace bound on the omitted compression give

`||K_V|| <= lambda_max(M_N)+tau_N`,

`tau_N=integral V(z)(2a-sum_{n<N}|A_n(z)|^2) dz/pi`.

The implementation computes `tau_N` as the directed total weighted mass minus
the directed diagonal sum. Root-boundary slivers can be paid by their full
trace.

The symbol is classified by a global derivative bound. Beyond `z=130`, the
real digamma term is bounded from below at the endpoint, while the prime cosine
and compact-remainder terms are bounded by absolute amplitudes. This gives a
lower bound above `2.0146`, so `V` vanishes there.

## Cluster Schur condition at `a=1`

For the relative operator `K=H^{-1/2}WH^{-1/2}`, set `A=I-K`. Given an
orthogonal decomposition into a retained cluster and its complement,

`A = [[A_00, C*], [C, A_11]]`.

If `A_00 >= alpha I`, `A_11 >= delta I`, and `||C||<=c`, then the elementary
Schur condition

`alpha delta >= c^2`

implies `A>=0`. Equivalently, the complement costs at most `c^2/delta` from the
cluster margin. This is the quantity reported by `cluster_a1.py` in a larger,
but still finite, Fourier space.

The formula identifies the analytic demand: control the whole cluster projector,
the complementary gap, and their coupling in one norm. The finite probe is used
only to locate those scales.
