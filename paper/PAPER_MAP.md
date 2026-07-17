# PF4 paper map

## Thesis

For the Riemann/de Bruijn-Newman kernel `Phi`, every translation minor of
order at most four is strictly positive at strictly ordered nodes. At the
origin, exact rational enclosure gives `H4(0)>0` and `H5(0)<0`; the confluent
limit transfers the latter sign to distinct order-five translation minors.
Its exact global Polya-frequency order is four. This classification is
finite-order and RH-neutral.

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
| `S00` | `sections/S00-abstract.tex` | Claim, method, evidence boundary | `R145`, `R164`, `R170`, `CERT9`-`CERT12` | ready |
| `S01` | `sections/S01-introduction.tex` | Scope, exact-order and separator statements, RH boundary | `R14`, `R81`, `R145`, `R164`, `R170`, `CERT11` | ready |
| `S01a` | `sections/S01a-related-work.tex` | Bounded finite-order, Riemann-kernel, moment, and Wronskian context | `CITE5`, `CITE6`, `CITE25`, `CITE27` | ready |
| `S02` | `sections/S02-kernel.tex` | Analytic even kernel; smoothness at zero; positivity before `log Phi` | `R4`, `R171`, `CERT12` | ready |
| `S03` | `sections/S03-certified-inputs.tex` | Sweep-free global `q>0`, `F2>0`, `C4>0` | `R171`, `CERT12` | ready; exact replay |
| `S04` | `sections/S04-pf3.tex` | Full weighted-mean proof of `Lambda>0` and strict PF3 | `R140`, `R141`, `R172`, `CERT12` | ready |
| `S05` | `sections/S05-quotient-reduction.tex` | Correct `T log(v3/v2)` derivation; fourth-order reduction; equivalence | `R154`-`R156`, `CERT5` | ready |
| `S06` | `sections/S06-curvature-coordinate.tex` | Increasing coordinate on its image, triangular weights, sign bridge | `R153`, `CERT9` | ready |
| `S07` | `sections/S07-confluent-invariant.tex` | Central-moment determinant and `C4=Q^6 kappa^2 D` | `R147`, `R149`, `R171`, `R173`, `CERT9`, `CERT12` | ready |
| `S08` | `sections/S08-transport-identity.tex` | Exact expectation identity and endpoint cancellation | `R153`, `CERT9` | ready |
| `S09` | `sections/S09-crossing-kernel.tex` | Strict density-ratio monotonicity and positive integral | `R153`, `CERT9` | ready |
| `S10` | `sections/S10-completion.tex` | Strict minors, origin parity obstruction, unique order-five confluent threshold, finite rational witness, exact order four | `R14`, `R72`, `R145`, `R164`, `R178`, `R179`, `CERT11`, `CERT16`, `CERT17` | ready |
| `S10a` | `sections/S10a-separator.tex` | Explicit positive even Schwartz strict-PF4 kernel with nonreal Fourier zeros | `R165`-`R170`, `CERT10` | ready; exact/direct replay |
| `S11` | `sections/S11-reproducibility.tex` | Exact active replay, fixed artifacts, and software versions | `CERT5`, `CERT9`-`CERT12`, `CERT16`, `CERT17` | ready |
| `S11a` | `sections/S11a-availability.tex` | Public evidence anchor, availability, AI provenance, release gates | `P000069`, `P000070` | ready; release-gated |
| `A1` | `appendices/A1-algebra.tex` | Cumulant expansion and curvature factorization line by line | `R149`, `CERT9`, `CERT12` | ready |
| `A2` | `appendices/A2-tail.tex` | Two-mode margins and analytic all-mode perturbation | `R171`, `CERT12` | ready; exact replay |
| `A3` | `appendices/A3-endpoints.tex` | `(50)->(45)` endpoint algebra with all substitutions exposed | `R153`, `CERT9` | ready |
| `A4` | `appendices/A4-provenance.tex` | Claim-to-file replay table | `CERT5`, `CERT9`-`CERT12`, `CERT16`, `CERT17` | ready |
| `A5` | `appendices/A5-separator.tex` | Independent central determinant, reduced 13-coefficient certificate, exact Fourier discriminant | `R167`, `R168`, `CERT10` | ready |
| `A6` | `appendices/A6-pf5-threshold.tex` | Three-mode closed determinant, correlated Bernstein crossing, one-mode tail, finite witness | `R178`, `R179`, `CERT16`, `CERT17` | ready; exact replay |

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
| 5. Transport endpoint algebra | `S08` derives the primitives; `A3` substitutes `mathcal J, mathcal H, U, delta, Lambda` into one explicit rational identity. | closed |
| 6. Tail constants | `A2` replaces the old derivative paddings by a two-mode normalization and one analytic bound for every mode `n>=3`, including all derivatives through order six. | closed / exact certificate |
| 7. Tail monotonicity | `A2` proves the `n=3` derivative sign and the decreasing weighted-homogeneous outer perturbation explicitly. | closed |
| 8. Smoothness at zero | `S02` defines `H(t)=e^{t/2} theta(e^{2t})`, proves `H(-t)=H(t)`, and writes `Phi=(H''-H/4)/2`. | closed |
| 9. Order-three bound | `S04` gives the two weighted means, extrema argument, integral of `max(F1,0)/q^2`, and final lower bound. | closed |
| 10. PF4 equivalence | `S05` gives both directions: confluent row limits imply Wronskian sign and monotonicity; iterated integrals give the converse. Strict and weak cases are separated. | closed |
| 11. PF5 decimal and geometry audit | `S10` replaces the decimal witness entirely. `CERT11` uses no coordinates or floating determinant: exact rational enclosures give `H5(0)<0`, and the displayed confluent limit supplies equally spaced distinct nodes for every sufficiently small positive step. | closed / certificate |

No critique position is currently unfilled. CERT10 and S10a additionally
close the continuous PF3/PF4 insufficiency position that remained open after
the original discrete smoothing proposal was rejected.

The maintained paper now gives the unique confluent center threshold and a
robust finite rational witness. Determining the outermost center over all
finite spacings remains a separate two-variable extremal problem and is not
claimed by the paper.

### P000070 audit promotion through C2

The sibling audit is preserved under
`sources/pf4-paper-audit-2026-07-16/`; its advancement triage and replayable
candidate are retained in `work/2026-07-16-pf4-audit-through-c2/`.

| Audit item | Maintained resolution |
|---|---|
| V1 | Public repository and immutable `P000069` theorem-evidence commit are printed; `paper/RELEASE_MANIFEST.md` names the final tag/DOI and clean-platform replay as release gates. |
| V2 | `S11` identifies the sweep-free exact active replay; the 7731- and 8050-cell Arb covers are archived historical evidence and cannot run during routine replay. |
| V3 | `A5` prints the 13 independent coefficients of the reduced degree-24 numerator, while `A2` supplies the complete finite-domain table and analytic later-mode bounds. |
| V4 | `S01a` adds the supplied Khare, Dimitrov--Xu, and Csordas--Varga context; comprehensive priority search remains the explicitly deferred Q1 item. |
| V5 | `CERT11` and `S10` already replaced the external decimal PF5 witness. |
| V6 | `S00` and `A5` replace the directed separator discriminant by an exact rational inequality. |
| V7 | `S02` proves `Phi>0` before defining `log Phi`. |
| V8 | `S11`, the proof records, and certificate metadata distinguish base-cover and wrapper precision/dependencies. |
| V9 | `S10a` attributes positive `kappa` to the established `q>0,F2>0` inequalities. |
| V10 | Joshuah Rainstar, Airspy, Inc., contact, contribution, acknowledgments, competing-interests statement, keywords, MSC, PDF metadata, availability, and AI provenance are present; tagged-PDF compliance remains a toolchain gate. |
| C1 | `sharp` is removed from the title and Fourier-separator framing. |
| C2 | `S06` says the increasing coordinate is global on its image; unused surjectivity is not implied. |

### Additional audit correction

The reviewed equation (30) prints `T delta` where differentiation of
`Psi` requires `Lambda T delta`. Its equation (32), the exact verifier, and
the maintained manuscript all use

`N = delta Lambda^2 + Lambda(Q'(p)delta + T delta) - delta T Lambda`.

This is a transcription/typesetting defect, not an unfilled research position.

## Retired material

The positive-tail atlas (`CERT6`-`CERT8`), collision cones, Hermite boxes,
escape charts, and regional joins are valid independent results but are not
dependencies of this paper. The three certificate boundaries are archived:
routine replay skips them, while their records and explicit targeted replay are
preserved. They remain in `work/` and must not be folded into the main proof as
if they were still necessary. This retirement is `R163`.

## Editorial rules

1. Every theorem-sized claim names an exact MIND or certificate boundary in
   this map before entering the paper.
2. The paper carries the human algebra. Scripts replay identities and exact
   inequalities; they are not prose substitutes.
3. Computational statements distinguish exact theorem premises from diagnostic
   checks. The PF5 certificate separately names its rational grid, retained
   modes, Taylor degrees, and geometric tail.
4. PF4 is never presented as an RH proof. The continuous PF4 Fourier separator
   is stated only through `R165`--`R170` and `CERT10`; `R81` names the resulting
   boundary and `R58` retains only the separate nowhere-density question.
