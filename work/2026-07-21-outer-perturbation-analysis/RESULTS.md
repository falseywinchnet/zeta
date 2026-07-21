# Results

The outer proof works in an unscaled form.

The constant scaled box rejected in P000137 was not the paper's essential
argument.  Keeping the raw cleared numerators unscaled exposes their weighted
homogeneity.  Every tail perturbation becomes a positive sum of terms
`x^w exp(-8*k*x)`, all strictly decreasing on `x>=5`.  Exact evaluation at the
single boundary point is therefore a theorem about the entire half-line, not
a range check.

The audit also repaired two proof-presentation omissions:

1. it explicitly proves the absolute derivative-polynomial envelope from
   `s=5`, which the historical verifier used but did not check;
2. it checks the outer `q` and `C4` margins directly for the cleared raw-jet
   polynomials, avoiding an implicit transfer from logarithmic invariants.

`audit_outer_mechanism.py` replays every finite algebraic premise with exact
rational/SymPy arithmetic.  `MATHEMATICS.md` gives the quantified analytic
argument, including the complete geometric tail and monotonicity to infinity.

Status: successful mathematical design, not yet a Lean theorem.
