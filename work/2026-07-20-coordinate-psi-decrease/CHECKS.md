# Checks

The candidate is checked directly from `proof/formal`:

```text
lake env lean ../../work/2026-07-20-coordinate-psi-decrease/CoordinatePsiDecrease.lean
```

No maintained source is changed and no full build is required.

The final direct run passed without warnings. Both printed theorem audits
depend exactly on:

```text
[propext, Classical.choice, Quot.sound]
```
