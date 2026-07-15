# Next PF4 obligations

1. Implement a third-order multivariate Taylor model for the regular Hermite
   columns `g[x]`, `g[x,x]`, `g[x,x,m]`, `g[x,x,m,r]`; do not divide by
   `theta`, `1-theta`, or a small gap.
2. Cross-check its determinant against `Jhat` on interior cells and against
   the exact two-point boundary modules on `theta=0,1`.
3. Cover the exact compact complement printed by `audit_compact_complement.py`
   adaptively.  Store accepted boxes, precision, truncation order, and bounds.
4. Resolve undecided boxes only by subdivision, increased Taylor order, or a
   named analytic lemma.  Counts or midpoint values are not evidence.
5. Replay the manifest from a clean process and require zero unresolved boxes.
6. In a later refine round, audit the cone proof and any complete complement
   manifest before adding CERT/MIND support.
