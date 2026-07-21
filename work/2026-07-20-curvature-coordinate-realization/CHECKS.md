# Checks

The candidate was checked directly from `proof/formal`:

```text
lake env lean ../../work/2026-07-20-curvature-coordinate-realization/CurvatureCoordinateRealization.lean
```

Only one Lean process was active at a time. No maintained module or full
library build was run.

The final targeted check passed without warnings. Every printed target depends
exactly on:

```text
[propext, Classical.choice, Quot.sound]
```

The candidate contains no `sorry`, `admit`, custom `axiom`, `unsafe`, or
`native_decide` bridge.
