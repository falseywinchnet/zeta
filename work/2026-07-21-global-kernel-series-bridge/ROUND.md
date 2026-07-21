# Global-kernel positive-series bridge

- Date: 2026-07-21
- Mode: advancement
- Model: OpenAI Codex
- Starting progress: P000129
- Starting boundary: `work/2026-07-21-theta-modular-continuation/NEXT.md`
- Status: complete

## Question

Can the globally smooth even kernel

\[
\Phi=\frac12(H''-H/4)
\]

be proved equal on the nonnegative axis to the literal positive-side
`thetaSeries` from P000128?

## Route

First identify `H` with its constant mode plus paired positive Gaussian modes.
Then pass the second-order operator through the positive series using a
two-derivative polynomial-geometric majorant. Prove the constant mode is
annihilated and each positive mode produces the exact `thetaMode` summand.

## Safety

Lean checks are serialized. The P000129 definitions needed by the bridge are
copied into this round and extended; the committed P000129 artifact is
unchanged. The bridge file does not duplicate the earlier holomorphic
smoothness proof, which remains a separate established boundary.
