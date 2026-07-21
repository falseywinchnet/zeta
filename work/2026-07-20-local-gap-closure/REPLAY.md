# Replay

Run from `proof/formal`. The generated dependency cache belongs to the replay
environment and is not committed as evidence.

```sh
mkdir -p ../../work/2026-07-20-local-gap-closure/.lean-deps

lake env lean \
  --root=/Users/quentinkuttenkuler/zeta/work/2026-07-20-curvature-coordinate-realization \
  --o=/Users/quentinkuttenkuler/zeta/work/2026-07-20-local-gap-closure/.lean-deps/CurvatureCoordinateRealization.olean \
  /Users/quentinkuttenkuler/zeta/work/2026-07-20-curvature-coordinate-realization/CurvatureCoordinateRealization.lean

LEAN_PATH=/Users/quentinkuttenkuler/zeta/work/2026-07-20-local-gap-closure/.lean-deps \
  lake env lean \
  --root=/Users/quentinkuttenkuler/zeta/work/2026-07-20-local-gap-closure \
  /Users/quentinkuttenkuler/zeta/work/2026-07-20-local-gap-closure/LocalGapClosure.lean
```

Run the two Lean invocations serially. No full build and no thread-count
override are required.

