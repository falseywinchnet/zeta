# Replay

From `proof/formal/` run:

```sh
lake env lean ../../work/2026-07-18-po0038-transport-object/TransportObject.lean
```

Expected result: exit status zero. The final five lines report only the
standard Lean/mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`.
