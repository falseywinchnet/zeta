# PF4 paper revision history

## Submitted release: pf4-paper-v1.0.0

- Immutable tag: `pf4-paper-v1.0.0`
- Commit: `4a14988093d7afaf05f453f8daf5441c09ba58b3`
- MIND epoch: `P000074`
- Status: frozen historical submission; preserved without rewriting

## Revised release: PF4-paper-v2.0.0

- MIND epoch: `P000163`
- Revision date: 2026-07-22
- Status: maintained post-submission proof backport
- The theorem and scope are unchanged: the exact global PF order is four and
  the result remains RH-neutral.
- Material changes: the exact-order theorem now organizes the paper; the
  maintained real/analytic Lean foundation is explicit; fixed-order Wronskian
  identities replace generic proof debt; the deterministic actual-range
  coordinate gap replaces the measure/CDF crossing chain on the critical
  path; and the direct `211/2000` witness replaces confluence as the PF5 input.
- Evidence boundary: `proof/formal`, `CERT20` through `CERT29`, and the
  independent exact replay listed in `paper/RELEASE_MANIFEST.md`.

The v1 source remains reachable through its immutable tag. The v2 source is
the content-addressed P000163 progress commit; the two versions are distinct
repository releases rather than an in-place rewrite of the submission.
