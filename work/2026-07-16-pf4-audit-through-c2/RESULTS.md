# Results

The sibling audit was re-evaluated against the post-`P000069` paper. Scope was
V1--V10 and C1--C2. C3 and all Q items were left untouched.

## Closed in the candidate

- **V2:** quick wrapper audits and full directed compact covers are now
  distinct. `replay_paper.py --full` actually regenerated both covers and
  matched the retained 7,731-cell and 8,050-cell hashes.
- **V3:** the categorical claim that every load-bearing reduction is printed
  is removed. The 37 independent coefficients of the palindromic degree-72
  separator numerator are printed exactly; a generated JSON certificate and
  hash are supplied. The theta paddings are described accurately as a directed
  certificate boundary.
- **V6:** the abstract separately discloses the directed 192-bit separator
  discriminant.
- **V7:** the paper proves `Phi>0` termwise on the positive half-line and uses
  evenness before defining `log Phi`.
- **V9:** positive `kappa` is attributed to the established `q>0,F2>0`
  inequalities, not strict PF3 alone.
- **C1:** `sharp` is removed from the title, section heading, introduction, and
  framing. No order-five Fourier sufficiency threshold is suggested.
- **C2:** the curvature variable is a global increasing coordinate on its
  image; unused surjectivity is not suggested.

## Already closed before this audit round

- **V5:** `CERT11` supplies the exact-rational origin PF5 obstruction, the
  confluent transfer is printed, and the removed citation is absent from the
  maintained and candidate papers.

## Materially improved but release-gated

- **V1:** the candidate names the public repository, `P000069`, and immutable
  theorem-evidence commit `97bd629c0188`. It adds a non-mutating quick/full
  replay and a release manifest. A final version tag or DOI and clean-platform
  result remain release actions.
- **V4:** a bounded related-work section now cites the supplied Khare,
  Dimitrov--Xu, and Csordas--Varga sources. The comprehensive priority search
  is Q1 and deliberately outside scope.
- **V8:** the candidate distinguishes the 192-bit base covers from the PF3
  256-bit wrapper cross-check and states that the C4 base cover requires Arb.
  `CERT2`/`CERT3` registry metadata must be corrected during promotion because
  advancement mode does not mutate MIND.
- **V10:** keywords, MSC, ordinary PDF metadata, availability, and AI
  provenance are added. Human identity/contact/funding/contribution/conflict
  fields cannot be inferred. Tectonic 0.16.9 cannot produce tagged PDF through
  the current LaTeX PDF-management interface.

## Verification

- Full non-mutating replay: passed in 38.03 seconds wall time.
- Directed compact outputs: exact SHA-256 matches for both retained covers.
- Paper-facing verifiers: `CERT2`, `CERT3`, `CERT5`, `CERT9`, `CERT10`, and
  `CERT11` all matched registered stdout and stderr hashes.
- Candidate PDF: 18 pages, no overfull/underfull boxes, undefined references,
  or undefined citations.
- Visual QA: all pages rendered; title/metadata, replay tables, coefficient
  table, provenance, and bibliography are unclipped and legible.
- Candidate PDF SHA-256:
  `ee9fe08429c82157c57a9d2eaed4cc81fa7a50e57c2d802d13dc261c21259ee1`.
