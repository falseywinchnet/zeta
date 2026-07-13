# Riemann-kernel PF4: the Wronskian (ECT) route

Mode: advancement

Date: 2026-07-13

Model: Claude Fable 5, Anthropic

Question: execute R153 — reduce global PF4 to translate-Wronskian positivity
and push it as far toward certification as the reduction allows.

Starting MIND: R4, R14, R140-R146, R147-R153, CITE24, CITE26.

`jet.py` is the audited order-eight jet copied from the P000025 round.

## Outcome

The route collapsed much further than R153 anticipated. Chain in
`MATHEMATICS.md`, every identity validated to ~50 digits
(`validate_reduction.py`):

1. Self-contained iterated-integral criterion: `q>0`, `L_3>0`, `L_4>0`
   pointwise imply strict global TP4 — no external Chebyshev-system theorem
   is needed, removing the citation gap R153 anticipated.
2. **W3 theorem.** `L_3 = A(p_3,p_2) Lambda / A(p_3,p_1)` with `Lambda` the
   audited R141 slope functional. The certified `q>0`, `F2>0` therefore
   already prove `W_3 > 0` globally: every order-three minor of the Riemann
   kernel, including all x-confluent ones, is strictly positive. Proved,
   pending refine audit; no new computation.
3. **Reduction theorem.** `L_4 = Psi(p_4) - Psi(p_3)` exactly, with
   `Psi(xi;m,r) = Lambda + T log Lambda`. Hence global PF4 is *equivalent* to
   the smooth three-parameter pointwise criterion `d/dxi Psi(xi;m,r) <= 0` on
   `xi < m < r`, rational in the jet `(s,q,q',q'')` at the three points. The
   self-similar ladder (`L_3 = Delta[A + T log A]`,
   `L_4 = Delta[Lambda + T log Lambda]`) must break at order five, where PF5
   fails.
4. Scans (`psi_scan.py`): 8.4 million Sobol configurations over four regimes
   including collision-targeted and extreme separations — zero violations,
   observed global maximum of `d/dxi Psi` about **-4.80** (at the collision
   boundary near t=0), so the criterion holds with a uniform margin on
   everything sampled. Escapes behave as `-q(xi) -> -infinity`.
5. Numerical-stability lesson recorded: theta-ratio jets in float64 are
   garbage beyond `|u| ~ 2.5` (spurious positives at `|u| ~ 18` refuted at
   140 digits); the scanner uses exact x-frame Stirling identities beyond
   `|u|=1`, branch-matched to 11 digits.

Not certified this round: the three-parameter criterion itself. The
certification plan (confluent 1D limit, compact 3D core, three escape lemmas
via the existing E-constants) is laid out in `MATHEMATICS.md`; the uniform
-4.8 margin and closed forms make it concrete. That certification would
complete global PF4 and, with R14, pin the exact Polya-frequency order of the
Riemann kernel at four.

Status: raw advancement research. The W3 theorem and the PF4 reduction are
derivations awaiting a refine audit; nothing here is an established MIND fact
until then.
