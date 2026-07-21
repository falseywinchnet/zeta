# Next boundary: integrate the range-local chain

P000118 constructs the genuine curvature-coordinate inverse, jet, and signs.
P000120 constructs the local closed-gap continuity and strictness and reduces
the terminal derivative sign to the central equality. This round proves that
central equality from the same local jet.

The next round should be refine mode:

1. integrate the range-local inverse/jet module from P000118;
2. integrate the compact closed-gap theorems from P000120;
3. integrate the direct central integration-by-parts theorems from this round;
4. replace the global implementation path in `PF4.FinalAssembly` with the
   composed local theorem;
5. extend `PF4.Audit` with axiom checks for every new maintained boundary;
6. run only the affected targeted Lean checks first, then the repository's
   required validation gate through `MIND PROGRESS COMMIT`.

The actual kernel derivative tower and the CERT12 `q`, `F2`, and determinant
`C4` signs remain explicit certificate-to-Lean inputs until their maintained
analytic constructions are added. Do not report those certificate inputs as
Lean-derived facts.

