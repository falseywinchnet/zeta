# Results

`RobustThreeModeClosureCombined.lean` is an all-in-one Lean replay of the
relevant previous advancement artifacts and this round.  It proves:

- the norm of every literal infinite tail coordinate through order six is
  below the exact compact perturbation budget for every `t >= 0`;
- the literal normalized series is definitionally connected to the exact
  two-mode jet plus the complete infinite tail;
- `clearedQ`, `clearedF2`, and `clearedC4` are strictly positive for every
  `t >= 0` satisfying `certX t <= 5`;
- the formerly missing `C4` continuum on `10/3 < x <= 5` is covered by four
  exact rational Bernstein certificates and proved exponential bounds;
- on the entire half-line `certX t >= 5`, every two-mode coordinate divided
  by `x^j` lies in `outerB`, and every complete infinite-tail coordinate
  divided by `x^j` lies strictly in `outerE`.

All range certificates quantify over continua.  The tail proofs quantify over
all natural mode indices.  There is no sampled-grid or finite-truncation claim.

The total PF4 programme is not closed by this round: the three outer sign
inequalities and their final global parity/kernel transport remain.
