# Next analytical obligations

1. Starting from equations (1)--(8) in `CURVATURE_COORDINATE.md`, expand the
   numerator as a positive-measure comparison of the left triangular measure
   `delta` and the two-sided triangular measure `Lambda`.
2. Put `a=Q(log kappa)'`.  Integrate differences `a(v)-a(u)` using the exact
   local inequality `a'<3(kappa-1)` supplied by `C4>0`; retain the chord error
   `V-Q` exactly rather than bounding it independently.
3. Determine whether the resulting remainder is a positive double integral.
   If not, name its kernel and seek an exact sign or a symbolic counterexample.
4. Exploit `Q''=F1/q^3`, `0<Q''<4/9`, `Q>=18`, and `|Q'|<2` only after the
   integrations are complete.  Do not return to three-dimensional tiling.
5. Investigate the curvature-shape invariant
   `kappa'=(3q'F1-qF1')/q^5`; a proved one-dimensional monotonicity or
   log-shape theorem may sign the surviving covariance term.
6. If the local transport inequality is insufficient, search for an exact
   analytic counterexample within low-degree positive `Q` satisfying the PF3
   and local-C4 constraints.  A counterexample to the proposed master lemma is
   useful and must not be hidden by refinement.
