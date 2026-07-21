# Replay

The candidate imports the preserved P000118 advancement module without moving
it into the maintained proof tree.  Compile the two modules serially from
`proof/formal`; never launch overlapping Lean processes.

```sh
lake env lean \
  --root=/Users/quentinkuttenkuler/zeta/work/2026-07-20-curvature-coordinate-realization \
  -o /tmp/CurvatureCoordinateRealization.olean \
  /Users/quentinkuttenkuler/zeta/work/2026-07-20-curvature-coordinate-realization/CurvatureCoordinateRealization.lean

LEAN_PATH=/tmp lake env lean \
  --root=/Users/quentinkuttenkuler/zeta/work/2026-07-20-range-local-final-assembly \
  /Users/quentinkuttenkuler/zeta/work/2026-07-20-range-local-final-assembly/RangeLocalFinalAssembly.lean
```

Observed replay: both commands succeeded serially.  The first took about 25
seconds; the second took about 28 seconds.  No project-wide rebuild was run.

