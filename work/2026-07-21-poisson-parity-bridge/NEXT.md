# Next boundary

Refine this candidate into the maintained analytic modules. The imported
Poisson and Jacobi-theta dependencies are now intentional and must be named in
`proof/IMPORTS.md`; do not preserve the previous claim that the maintained
analytic foundation has no such imports.

After integration, construct the exact global derivative package consumed by
the certificate bridge:

1. identify the positive-side `thetaSeriesJet 0,...,thetaSeriesJet 6` with
   `iteratedDeriv 0,...,6 globalRiemannKernel` on `t>0`;
2. use global smoothness and evenness to transport the jet across zero and to
   negative points with the correct factor `(-1)^j`;
3. define the actual logarithmic tower `ell,s,q,q1,...,q4` from the global
   kernel and prove the maintained derivative equalities;
4. state and connect the exact CERT12 propositions for `q>0`, `F2>0`, and
   determinant `C4>0`;
5. feed that package to the maintained actual-range coordinate and terminal
   quotient theorem.

Do not bundle any target sign, coordinate gap, or terminal conclusion into the
analytic package.

