# CERT12 literal theta-tail bridge

- Mode: advancement
- Date: 2026-07-21
- Model: OpenAI Codex
- Starting MIND records: P000140, P000139, P000138, P000134,
  R171--R173, R189--R194, CERT12, CERT21
- Question: connect the maintained polynomial, exponential, and geometric
  `tsum` foundations to the literal normalized `thetaSeriesJet`.
- Status: complete; the literal normalized theta-series jet has a maintained,
  kernel-checked three-mode-relative decomposition

## Acceptance theorem

For every `j <= 6` and every `t >= 0`, Lean must construct
`0 <= delta < 1/1000` such that the literal normalized theta-series jet is
exactly its first two modes plus its third mode multiplied by `1 + delta`.
The theorem may not assume a tail estimate or truncate the series.
