# PF4 paper map

## Thesis

For the Riemann/de Bruijn-Newman kernel `Phi`, every translation minor of
order at most four is strictly positive at strictly ordered nodes, while a
certified order-five minor is negative. Its exact global Polya-frequency order
is four. This classification is finite-order and RH-neutral.

The paper also constructs an explicit positive even Schwartz strict-PF4
kernel with nonreal Fourier zeros. This proves that continuous PF3 and PF4
membership alone do not force Fourier real-rootedness.

The paper proves the positive half by the dependency chain

`q,F2 > 0` -> `PF3 and Lambda > 0` -> `quotient reduction` ->
`partial_xi Psi < 0` -> `strict PF4`.

The last inequality is obtained from

`C4 > 0` -> `C4 = Q^6 kappa^2 D` -> `transport identity` ->
`positive CDF crossing kernel` -> `partial_xi Psi < 0`.

## Section shorthand

The shorthand is stable. Reorder the paper by changing only the `\input`
sequence in `manuscript/main.tex`; do not rename a section ID merely because
its displayed section number changes.

| ID | File | Object and burden | MIND / certificate anchors | Status |
|---|---|---|---|---|
| `S00` | `sections/S00-abstract.tex` | Claim, method, evidence boundary | `R145`, `R164`, `R170`, `CERT9`, `CERT10` | ready |
| `S01` | `sections/S01-introduction.tex` | Scope, exact-order and separator statements, RH boundary | `R81`, `R145`, `R164`, `R170` | ready |
| `S02` | `sections/S02-kernel.tex` | Analytic even kernel; smoothness at zero | `R4`, `CERT2` | ready |
| `S03` | `sections/S03-certified-inputs.tex` | Global `q>0`, `F2>0`, `C4>0` and what computation certifies | `R142`, `R143`, `R150`, `R151`, `CERT2`, `CERT3` | ready; replay-dependent |
| `S04` | `sections/S04-pf3.tex` | Full weighted-mean proof of `Lambda>0` and strict PF3 | `R140`-`R144`, `CERT2` | ready |
| `S05` | `sections/S05-quotient-reduction.tex` | Correct `T log(v3/v2)` derivation; fourth-order reduction; equivalence | `R154`-`R156`, `CERT5` | ready |
| `S06` | `sections/S06-curvature-coordinate.tex` | Increasing coordinate, triangular weights, sign bridge | `R153`, `CERT9` | ready |
| `S07` | `sections/S07-confluent-invariant.tex` | Central-moment determinant and `C4=Q^6 kappa^2 D` | `R147`-`R152`, `CERT3`, `CERT9` | ready |
| `S08` | `sections/S08-transport-identity.tex` | Exact expectation identity and endpoint cancellation | `R153`, `CERT9` | ready |
| `S09` | `sections/S09-crossing-kernel.tex` | Strict density-ratio monotonicity and positive integral | `R153`, `CERT9` | ready |
| `S10` | `sections/S10-completion.tex` | Strict minors, exact order four, no RH implication | `R14`, `R81`, `R145`, `R164` | ready |
| `S10a` | `sections/S10a-separator.tex` | Explicit positive even Schwartz strict-PF4 kernel with nonreal Fourier zeros | `R165`-`R170`, `CERT10` | ready; exact/direct replay |
| `S11` | `sections/S11-reproducibility.tex` | Human proof vs replay boundary and audit order | `CERT2`, `CERT3`, `CERT5`, `CERT9`, `CERT10` | ready |
| `A1` | `appendices/A1-algebra.tex` | Cumulant expansion and curvature factorization line by line | `R149`, `CERT3`, `CERT9` | ready |
| `A2` | `appendices/A2-tail.tex` | Tail constants, polynomial, normalized monotonicity | `R143`, `R151`, `CERT2`, `CERT3` | ready; replay-dependent |
| `A3` | `appendices/A3-endpoints.tex` | `(50)->(45)` endpoint algebra with all substitutions exposed | `R153`, `CERT9` | ready |
| `A4` | `appendices/A4-provenance.tex` | Claim-to-file replay table | `CERT2`, `CERT3`, `CERT5`, `CERT9`, `CERT10` | ready |
| `A5` | `appendices/A5-separator.tex` | Independent central-determinant reconstruction, coefficient positivity, Fourier discriminant | `R167`, `R168`, `CERT10` | ready |

## Review verdict ledger

`Closed` means the maintained manuscript now contains the missing derivation;
it does not mean a reviewer must trust code without replay. `Certificate`
means a numerical inequality remains intentionally computer-assisted and its
directed-rounding boundary is named.

| Review item | Resolution in maintained paper | Position |
|---|---|---|
| 1. Preliminary equation (17) | `S05` writes `T log A=M` from the stated definition, expands `T log(v_j/v_2)`, and applies the weighted-mean split. The counterexample in the verdict uses `T log A=-M`, the opposite sign convention. The fourth-order identity is derived from the same displayed factors, not asserted as an analogous cancellation. | closed |
| 2. Density-ratio monotonicity | `S09` differentiates `C(z-y)/(y-p)` and obtains `-C(z-p)/(y-p)^2<0`. | closed |
| 3. Confluent expansion | `S07` and `A1` give the moment matrix, its Schur complement, and the thirteen-term polynomial. | closed |
| 4. `C4=Q^6 kappa^2 D` | `A1` lists `c2,...,c6`, the factored determinant, and the expanded form of `D`. | closed |
| 5. Transport endpoint algebra | `S08` derives the primitives; `A3` substitutes `J,H,U,delta,Lambda` into one explicit rational identity. | closed |
| 6. Tail constants | `A2` derives `E_j=2^j sum S(j,k)C_k`, displays the `C_k` and `E_j` tables, and names the theta-tail padding. Directed enclosures remain a certificate input. | closed / certificate |
| 7. Monotonicity of `P(x)/x^6` | `A2` writes it as `49152-sum b_d x^{d-6}` and differentiates termwise. | closed |
| 8. Smoothness at zero | `S02` defines `H(t)=e^{t/2} theta(e^{2t})`, proves `H(-t)=H(t)`, and writes `Phi=(H''-H/4)/2`. | closed |
| 9. Order-three bound | `S04` gives the two weighted means, extrema argument, integral of `max(F1,0)/q^2`, and final lower bound. | closed |
| 10. PF4 equivalence | `S05` gives both directions: confluent row limits imply Wronskian sign and monotonicity; iterated integrals give the converse. Strict and weak cases are separated. | closed |

No critique position is currently unfilled. CERT10 and S10a additionally
close the continuous PF3/PF4 insufficiency position that remained open after
the original discrete smoothing proposal was rejected.

### Additional audit correction

The reviewed equation (30) prints `T delta` where differentiation of
`Psi` requires `Lambda T delta`. Its equation (32), the exact verifier, and
the maintained manuscript all use

`N = delta Lambda^2 + Lambda(Q'(p)delta + T delta) - delta T Lambda`.

This is a transcription/typesetting defect, not an unfilled research position.

## Retired material

The positive-tail atlas (`CERT6`-`CERT8`), collision cones, Hermite boxes,
escape charts, and regional joins are valid independent results but are not
dependencies of this paper. They remain in `work/` and must not be folded into
the main proof as if they were still necessary. This retirement is `R163`.

## Editorial rules

1. Every theorem-sized claim names an exact MIND or certificate boundary in
   this map before entering the paper.
2. The paper carries the human algebra. Scripts replay identities and directed
   inequalities; they are not prose substitutes.
3. Computational statements say exactly what interval, precision, cells,
   tail enclosure, and verifier establish them.
4. PF4 is never presented as an RH proof. The continuous PF4 Fourier separator
   is stated only through `R165`--`R170` and `CERT10`; `R81` names the resulting
   boundary and `R58` retains only the separate nowhere-density question.
