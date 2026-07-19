# Replay notes and rejected shortcuts

## Failed replay paths

1. The first non-interactive replay could not locate the Lean launcher. The
   script now resolves the pinned Elan installation explicitly and accepts a
   `LAKE_BIN` override.
2. Namespace-alias syntax was not accepted by the pinned Lean version. The
   final candidate uses full public namespace paths, making each imported
   boundary visible.
3. A first direct debug invocation used one too many parent-directory steps.
   The checked replay script resolves all paths from its own repository root.

## Rejected proof shapes

- Retaining P000100's `hcentral` premise in the exported final theorem.
- Assuming positivity of `coordinateNumerator`, `transportIntegral`, or the
  derivative itself.
- Replacing determinant `C4` by the desired numerator definition.
- Assuming curvature continuity when it follows from the derivative tower.
- Numerical checking, approximation, tolerance, `sorry`, or `admit`.
