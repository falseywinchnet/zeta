# Next proof obligations

1. Add a multi-center separated evaluator: local Taylor models for `g(x)`,
   `g(m)`, `g(r)`, and `g'(x)`, combined by recursive divided differences only
   where the relevant gap has a certified positive lower bound.
2. Join it to the one-center Hermite evaluator on an explicit radial overlap.
3. Treat near-`theta=0` and near-`theta=1` strips by expansions about the exact
   two-point face formulas, so no arbitrarily small angular denominator enters.
4. Extend the manifest from the origin slab to the exact compact complement,
   preserving separate face, overlap, tail, and escape records.
5. Require zero globally unresolved boxes before any PF4 claim.  Keep
   `global_pf4_claim=false` otherwise.
6. In a later refine round, audit and register a certificate only for the
   exact domain actually replayed.
