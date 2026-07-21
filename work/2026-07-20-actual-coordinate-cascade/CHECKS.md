# Checks

One Lean compilation was run at a time.

From `proof/formal/`:

```sh
lake env lean ../../work/2026-07-20-actual-coordinate-cascade/ActualCoordinateCascade.lean
```

Final result: exit code 0.

The printed axiom dependencies for all four public theorems are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

A repository text audit found no `sorry`, `admit`, or user-declared `axiom` in
the candidate.  No broad rebuild or concurrent Lean process was used.
