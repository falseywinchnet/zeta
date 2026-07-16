# Confluent order-four certificate for the Riemann kernel

For the even Riemann kernel `Phi` with `q = -(log Phi)''`, define the fully
doubly-confluent order-four minor: the limit of
`det[Phi(x_i-y_j)]_{4x4}` as all `x_i -> t` and all `y_j -> 0`, divided by the
two positive Vandermonde factors. Up to the positive factor `Phi(t)^4` this is

`C_4(t) = det[m_{i+j-2}(t)]_{i,j=1..4}`,

the central-moment Hankel determinant in the cumulants
`kappa_j = (log Phi)^(j)`, `j = 2..6` (sign `(-1)^{k(k-1)/2}` from the
`y`-derivatives; scaling `det/(eps^12 C4 Phi^4) -> 1` verified numerically for
node pattern `(0,1,2,3)`).

The claim certified here: `C_4(t) > 0` for every real `t`. Consequently no
order-four minor of the Riemann kernel can go negative through full collision
of its nodes. CERT11 now closes the adjacent origin boundary directly: exact
rational enclosure gives `H_4(0)>0` while `H_5(0)<0`, and the latter sign
transfers to distinct order-five minors by the confluent limit.

## Structure

- Order three ties to PF3: `C_3/Phi^3 = 2q^3 - F_1 = q^3 + F_2`, so the
  certified PF3 curvature data (R142-R144) already give strict positivity of
  every fully confluent order-three minor.
- `C_4` is weight-12 homogeneous in cumulants, thirteen terms, and decomposes
  exactly in the audited PF3 invariants:
  `C_4 = 3(2q^3-F_1)(2q^3-3F_1) + 2(q^2F_1''-6qq'F_1'+9q'^2F_1) - det H_3[q]`,
  where `H_3[q]` is the 3x3 Hankel of `q`-derivatives and
  `2q^3-F_1 = q^3+F_2 > 0` globally.

## Chain

1. Compact core: `certify_c4.py` proves `C_4 >= 2.817e7` on `[0,1]` by
   directed interval arithmetic (second-order Taylor cells over sympy-generated
   division-free CSE forms of `C_4, C_4', C_4''` in `kappa_2..kappa_8`; 8050
   adaptive cells; startup self-checks tie the cumulant recursion to the
   audited hardcoded `ell_2..ell_6` and the decomposition to the direct form).
   Evenness of `C_4` extends this to `[-1,1]`.

   This theorem-producing base cover uses python-flint/Arb at 192-bit
   precision with seven retained theta terms. It is distinct from the quick
   `scripts/verify_c4_confluent.py` wrapper, which uses exact SymPy algebra and
   50--120 digit mpmath diagnostics. `scripts/replay_paper.py --full` executes
   and hash-checks both layers.
2. Tail: with `x = pi e^{2u}`, the Stirling identity
   `D^j psi = 2^j sum_k S(j,k) x^k psi^(k)` for `D = 2x d/dx` gives
   `kappa_j = -2^j x + eps_j`, `|eps_j| <= E_j/x`, with
   `E = {19.8, 176, 2082, 30770, 545900}` from the `w`-derivative enclosures
   (`|w^(5)| <= 222/x^6`, `|w^(6)| <= 1376/x^7` extend the audited P000024
   constants). At `eps = 0` the Hankel collapses to `49152 x^6` exactly; every
   perturbation monomial has `x`-degree at most 4, so for all `x >= pi e^2`
   `C_4/x^6 >= 49152 - sum_d B_d x_0^{d-6} > 44392`. Hence `C_4 > 0` on
   `|u| >= 1`.

## Audit

`scripts/verify_c4_confluent.py` (this refine round, 45 checks) verifies
independently: the central-moment formulas from the cumulant generating
function; Hankel shift invariance; that `f^(j)/f` are the raw moments of the
log-derivative cumulants; the confluent scaling and sign for orders three and
four against genuine epsilon-spaced minors; the C3 identity, thirteen-term C4
expansion, and structural decomposition; the moment-cumulant recursion through
order eight; the Stirling operator identity through order six; the exact
`E_j` sums (E_2..E_4 reproduce the audited P000024 tail constants); the
`w^(5)`, `w^(6)` constants at sampled `x` (tight within 0.5% at the boundary);
the generated `c4_jet` value and derivatives against independent mpmath
evaluation (relative error ~1e-61); and the tail margin by an independent
Laurent expansion (44392.81).

## Epistemic status

The interval computations are machine-certified with directed rounding. The
reduction, decomposition, Stirling/cumulant algebra, and tail enclosures are
repository-local derivations, not published literature. This certificate
proves the fully confluent inequality `C_4>0`; it does not alone prove global
PF4. The formerly open nonconfluent step is now closed independently by the
positive transport-kernel identity in `CERT9`, and the complete strict global
PF4 conclusion is `R164`.
