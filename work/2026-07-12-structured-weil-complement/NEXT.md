# Certification handoff

The next certificate should use the exact Fourier symbol and a domain-aligned
trial space. Do not return to one global translation norm.

## Finite block

1. Implement (m_a(z)) in Arb, including the signed truncated (r_0'')
   transform and exact prime-power list.
2. Use periodic/Yoshida modes or a mixed constant-plus-sine basis.
3. Integrate finite-frequency panels with directed Acb quadrature.
4. Bound the Fourier tail analytically using exact basis transforms, the digamma
   asymptotic with remainder, and oscillatory prime integrals.
5. Isolate the near-one generalized eigenvalue cluster with ball arithmetic.

## Complement

Use (K_a=H^{-1/2}W_aH^{-1/2}), not (B_a) in absolute norm.

- certify a finite-rank approximation to the low-frequency relative operator;
- bound its residual in the (H)-dual norm;
- retain the whole near-one cluster in the Schur block;
- exploit oscillatory matrix-element decay for prime translations;
- use the explicit logarithmic-Laplacian eigenvalue bound for the remaining
  reference tail;
- prove a directed pointwise-positive frequency threshold.

The decisive inequality is a cluster Schur bound for (I-K_a). At (a=1), the
available margin is about (10^{-12}) already at eight modes, so every discarded
tail and rounding term must be substantially smaller.

## First target

Certify `a=0.3` first with the simpler compact negative-part formulation, using
`mu=1` and `mu=2` as independent checks. Their observed margins are about
`4.8e-3` and `6.9e-3`. Then attempt `a=0.5, mu=2`, whose observed margin is only
`4.5e-7`.

The negative-part test fails at `a=1`. Use the relative formulation and a
near-one cluster there; do not spend interval effort trying to rescue the tested
constant baselines.
