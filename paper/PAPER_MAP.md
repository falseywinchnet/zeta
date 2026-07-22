# PF4 paper map

## Thesis

For the Riemann/de Bruijn-Newman kernel `Phi`, every translation minor of
order at most four is strictly positive at strictly ordered nodes. At the
exact spacing `211/2000`, a maintained rational certificate gives a negative
order-five translation minor. Its exact global Polya-frequency order is
therefore four. The origin and threshold calculations are optional structure,
not inputs to the classification. This result is finite-order and RH-neutral.

The paper also constructs an explicit positive even Schwartz strict-PF4
kernel with nonreal Fourier zeros. This proves that continuous PF3 and PF4
membership alone do not force Fourier real-rootedness.

The paper proves the positive half by the dependency chain

`q,F2 > 0` -> `PF3 and Lambda > 0` -> `quotient reduction` ->
`partial_xi Psi < 0` -> `strict PF4`.

The last inequality is obtained from

`C4 > 0` -> `C4 = Q^6 kappa^2 D` -> `endpoint transport identity` ->
`positive deterministic closed gap` -> `partial_xi Psi < 0`.

## Section shorthand

The shorthand is stable. Reorder the paper by changing only the `\input`
sequence in `manuscript/main.tex`; do not rename a section ID merely because
its displayed section number changes.

| ID | File | Object and burden | MIND / certificate anchors | Status |
|---|---|---|---|---|
| `S00` | `sections/S00-abstract.tex` | Exact-order claim, deterministic method, formal boundary | `R203`-`R205`, `CERT23`-`CERT24` | revised / Lean-backed |
| `S01` | `sections/S01-introduction.tex` | Organizing exact-order theorem and its T1/T2 inputs | `R203`-`R205`, `CERT23`-`CERT24` | revised / Lean-backed |
| `S01a` | `sections/S01a-related-work.tex` | Bounded finite-order, Riemann-kernel, moment, and Wronskian context | `CITE5`, `CITE6`, `CITE25`, `CITE27` | ready |
| `S02` | `sections/S02-kernel.tex` | Real theta definition, Poisson bridge, analytic parity, global jet | `R182`-`R188`, `R191`, `R195`-`R197`, `CERT20`-`CERT22` | revised / Lean-backed |
| `S03` | `sections/S03-certified-inputs.tex` | Universal global `q>0`, `F2>0`, `C4>0` | `R198`-`R202`, `CERT22` | revised / Lean-backed |
| `S04` | `sections/S04-pf3.tex` | Literal weighted-mean proof of `Lambda>0` and strict PF3 | `R203`, `CERT23`, `CERT28` | revised / Lean-backed |
| `S05` | `sections/S05-quotient-reduction.tex` | Fixed-order W3/W4 cascade and strict quotient integrals | `R206`-`R208`, `CERT23`, `CERT29` | revised / Lean-backed at active sizes |
| `S06` | `sections/S06-curvature-coordinate.tex` | Actual-range coordinate, simultaneous translation, sign bridge | `R181`, `CERT25`-`CERT27` | revised / Lean-backed |
| `S07` | `sections/S07-confluent-invariant.tex` | Central determinant and `C4=Q^6 kappa^2 D` | `R193`-`R194`, `CERT21`, `CERT25`-`CERT26` | revised / Lean-backed |
| `S08` | `sections/S08-transport-identity.tex` | Deterministic endpoint cancellation; measures optional | `R181`, `CERT19`, `CERT25` | revised / Lean-backed |
| `S09` | `sections/S09-crossing-kernel.tex` | Positive closed coordinate gap and direct integration by parts | `R181`, `CERT19`, `CERT25` | revised / Lean-backed |
| `S10` | `sections/S10-completion.tex` | Direct rational PF5 witness; optional origin/threshold structure | `R204`-`R205`, `CERT24`; optional `CERT16`-`CERT17` | revised / Lean-backed main path |
| `S10a` | `sections/S10a-separator.tex` | Explicit positive even Schwartz strict-PF4 kernel with nonreal Fourier zeros | `R165`-`R170`, `CERT10` | ready; exact/direct replay |
| `S11` | `sections/S11-reproducibility.tex` | Lean build/axiom audit plus independent exact replay | `CERT20`-`CERT29`; optional `CERT10`, `CERT16`-`CERT17` | revised |
| `S11a` | `sections/S11a-availability.tex` | Submitted/revised release identities and provenance | `P000074`, `P000158`-`P000163` | revised |
| `A1` | `appendices/A1-algebra.tex` | Cumulant expansion and curvature factorization line by line | `R149`, `CERT9`, `CERT12` | ready |
| `A2` | `appendices/A2-tail.tex` | Two-mode margins and analytic all-mode perturbation | `R171`, `CERT12` | ready; exact replay |
| `A3` | `appendices/A3-endpoints.tex` | `(50)->(45)` endpoint algebra with all substitutions exposed | `R153`, `CERT9` | ready |
| `A4` | `appendices/A4-provenance.tex` | Claim-to-Lean/certificate/standard-proof trace | `CERT20`-`CERT29` | revised |
| `A5` | `appendices/A5-separator.tex` | Independent central determinant, reduced 13-coefficient certificate, exact Fourier discriminant | `R167`, `R168`, `CERT10` | ready |
| `A6` | `appendices/A6-pf5-threshold.tex` | Direct finite witness and optional threshold certificate | `R204`, `CERT24`; optional `CERT16`-`CERT17` | revised |

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
| 11. PF5 decimal and geometry audit | `S10` uses the exact `211/2000` distinct-node witness directly. `CERT24` checks node order, signed orientation, primary-kernel boxes, and determinant negativity; confluence is optional. | closed / Lean certificate |

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
| V1 | `paper/REVISION_HISTORY.md` distinguishes submitted `pf4-paper-v1.0.0`/P000074 from revised `PF4-paper-v2.0.0`/P000163; the release manifest records the formal and exact replay gates. |
| V2 | `S11` identifies the sweep-free exact active replay; the 7731- and 8050-cell Arb covers are archived historical evidence and cannot run during routine replay. |
| V3 | `A5` prints the 13 independent coefficients of the reduced degree-24 numerator, while `A2` supplies the complete finite-domain table and analytic later-mode bounds. |
| V4 | `S01a` adds the supplied Khare, Dimitrov--Xu, and Csordas--Varga context; comprehensive priority search remains the explicitly deferred Q1 item. |
| V5 | `CERT24` and `S10` use the direct exact rational PF5 witness; the older confluent calculation is explicitly optional. |
| V6 | `S00` and `A5` replace the directed separator discriminant by an exact rational inequality. |
| V7 | `S02` proves `Phi>0` before defining `log Phi`. |
| V8 | `S11`, the proof records, and certificate metadata distinguish base-cover and wrapper precision/dependencies. |
| V9 | `S10a` attributes positive `kappa` to the established `q>0,F2>0` inequalities. |
| V10 | Joshuah Rainstar, contact, contribution, acknowledgments, competing-interests statement, keywords, MSC, PDF metadata, availability, and AI provenance are present; no institutional affiliation is claimed; tagged-PDF compliance remains a toolchain gate. |
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
