# Compact localized-Weil certificate

- Mode: advancement
- Date: 2026-07-12
- Model: Sydney, OpenAI Codex
- Status: complete; awaiting later refine integration
- Starting epoch: P000014 (`2518011a219096730a6ecc8e35cc313cfbdc166b`)
- Starting targets: R101, R111, R113

## Question

Can the compact negative-part formulation from P000014 rigorously certify the
full localized-Weil form as positive at `a=0.3`, including its
infinite-dimensional complement?

## Boundary

Everything here is raw advancement evidence until a separate refinement round
audits it. The target is one finite scale, not RH.

## Outcome

The compact negative-part operator is certified to have norm below one. The main
directed run proves

\[
\lambda_{0.3}>0.0037028625896680721.
\]

The complete infinite-dimensional Legendre complement is controlled by a
directed trace bound. A coarser independent run also retains a positive lower
endpoint. No result is claimed at larger `a`, and R113 remains open globally.
