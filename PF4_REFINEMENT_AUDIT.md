# PF4 refinement audit — 2026-07-14

## Integrated

`P000041`–`P000043` jointly prove the complete positive-tail `J_b` statement:

- all-order collision cone with exact radius;
- left separated box with correlated full-theta errors;
- right near-face strip with a shared-jet mean-value model and exact first
  Peano cancellation;
- both angular faces and an exact exhaustive join.

`CERT8` is the replay boundary.  Its proof artifact contains 38,103 left-box
and 53,001 strip residual integers.  Every residual is strictly positive.
Routine replay checks all residuals, their source hashes, the symbolic
cancellation, a fresh all-order collision derivation, and the join.  The deep
generator reconstructs the artifact from the 74-term symbolic numerator.

The collision script formerly asked a general rational-cancellation engine to
divide forty coefficients by the already known monomial `alpha*beta^2`.
Termwise exact exponent checks reduce that replay from more than nine minutes
without completion to about 2 minutes 17 seconds.  Coefficientwise collapse of
error blocks reduces each separated residual transform from roughly 10–15
minutes to about 12 seconds after block generation.

MIND integration:

- `R161`: established positive-tail `J_b>=0`;
- `R162`: established `partial_xi Psi<=0` whenever `pi exp(2xi)>=23`;
- `R153`: remains the global criterion TODO.

## Preserved as raw progress

The supplied 3,094-line ChatGPT/manual-work transcript is retained losslessly
at `sources/chatgpt-global-pf3-pf4-verification-2026-07-14.txt` with SHA-256
`b116d197c1cf216162bc0446e2e3cb09bcc8e6ee7b39cf3ddf89134bcb5aefcc`.

- Floor 6: all three sufficient coefficient boxes failed.
- Floor 18: `S_r` passed; both `J_b` boxes failed.
- Error-scale diagnostic: cached `J_b` residuals pass for a `1/100` shrink,
  containing the recorded floor-20 error ratios.
- Floor 20: no actual rebuild completed; its output file was empty.
- Stable-tail `S_r` at floor 18 is promising but lacks a standalone retained
  generator, so it is not established.

None of these diagnostics is used by `CERT8`.  Large `.pkl` caches remain local
and ignored; exact conclusions and failures are retained in the committed logs.

## Planning correction

The old completion map encouraged repeated lowering of the one-term tail seam.
That is retired.  `PF4_PATHWAY.md` fixes the certified seam at 23 and gives the
finite remaining atlas: uniform escape, positive compact core, two mixed-sign
charts, origin collision cone, then mirror and exhaustive join.
