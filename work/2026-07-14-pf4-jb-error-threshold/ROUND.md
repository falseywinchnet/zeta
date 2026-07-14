# Manual J_b error-scale threshold diagnostic

- Mode: advancement
- Date: 2026-07-14
- Provenance: manual terminal execution; full output in `run.log`
- Starting progress: P000042-P000043 and the floor-18 run

Cached exact floor-18 residual forms were retested after uniformly shrinking
the tail-error box.  The left chart first passed at scale `1/32`; the strip
first passed at `1/64`; both passed at `1/100`, which contains the recorded
floor-20 error ratios.  This is strong containment evidence for a floor-20
separated theorem, but the actual floor-20 rebuild and its collision join were
not completed.

Status: raw progress, not promoted.  It is unnecessary for the fixed floor-23
global completion atlas.
