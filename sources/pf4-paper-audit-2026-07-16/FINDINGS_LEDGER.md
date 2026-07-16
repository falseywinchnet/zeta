# Findings ledger

This ledger distinguishes **verified defects**, **plausible concerns**, and **open questions**. The authoritative prioritization and revision recommendation are in `AUDIT_REPORT.md`.

## Verified defects

### V1. No externally resolvable reproducibility anchor

- Severity: major
- Confidence: high
- Location: Section 12; Appendix D; all repository-path references
- Problem: The PDF gives relative paths but no repository URL, archive DOI, release, commit, or locked environment.
- Why it matters: An independent reader cannot obtain the exact code or know which revision the claims refer to.
- Evidence: The publication PDF and source contain paths only; PDF metadata has no source locator.
- Required correction or test: Publish an immutable release and cite its DOI/URL plus commit and replay entry point in the paper.

### V2. Two named “directed” replay scripts do not replay the directed compact covers

- Severity: major
- Confidence: high
- Location: Section 12 table, lines 12-15 and 27-32; `verify_pf3_reduction.py`; `verify_c4_confluent.py`
- Problem: The named wrappers run symbolic and sampled checks, not the 7,731- and 8,050-cell Arb covers.
- Why it matters: The table overstates what a reader reproduces by running the cited command.
- Evidence: Static inspection of both scripts and their separate underlying compact artifacts.
- Required correction or test: Publish distinct full-replay commands and label the wrappers as audits/cross-checks.

### V3. The “all load-bearing algebra is displayed” claim is false

- Severity: major
- Confidence: high
- Location: Abstract lines 18-19; Section 11 lines 70-78; Appendix E lines 21-34; Appendix B lines 8-45
- Problem: The 73 separator coefficients are not displayed or reduced to a printed positive basis, and the global theta-tail paddings are asserted rather than fully derived.
- Why it matters: The article claims a human-readable proof boundary that it does not meet.
- Evidence: Appendix E reports properties of `H` but does not print `H`; Appendix B defers the tail inequalities to the verifier.
- Required correction or test: Display a compact independently checkable certificate (coefficient table/hash plus generator, and complete tail lemmas) or narrow the claim.

### V4. Literature support is materially incomplete

- Severity: major
- Confidence: high
- Location: Introduction lines 9-11 and 29-55; References
- Problem: The bibliography has only two entries, one slated for removal, and omits directly relevant supplied primary literature.
- Why it matters: Originality, relation to classical machinery, and contrary/adjacent work cannot be evaluated from the manuscript.
- Evidence: Supplied Khare and Dimitrov-Xu papers directly overlap finite-order PF characterization and Riemann-kernel/Fourier-Wronskian framing.
- Required correction or test: Add a related-work section and conduct a documented external priority search.

### V5. The replacement PF5 evidence boundary is not yet integrated

- Severity: major
- Confidence: high
- Location: Introduction lines 21-27; Section 10 lines 8-9; References; reproducibility and provenance tables
- Problem: The audited PDF still cites Michalowski, while the planned hardened replacement is not cited, versioned, or replay-linked.
- Why it matters: The exact-order headline remains conditional until the replacement order-five witness is an immutable evidence boundary.
- Evidence: The current bibliography and absence of the replacement from Sections 12 and Appendix D.
- Required correction or test: Integrate the hardened source; print the witness and directed determinant enclosure; add a public immutable locator and full replay command; remove all Michalowski references; verify the exact-order dependency map against the final PDF.

### V6. The abstract understates the computer-assisted boundary

- Severity: moderate
- Confidence: high
- Location: Abstract lines 6-8 versus Section 11.3 lines 102-108
- Problem: The abstract says the computer-assisted input is confined to `q,F2,C4` and “the remainder is exact,” but the separator uses a directed numerical discriminant enclosure.
- Why it matters: Readers receive an inaccurate evidence classification.
- Evidence: The discriminant interval is explicitly described as directed 192-bit arithmetic.
- Required correction or test: Scope the abstract sentence to the Riemann-kernel positive proof or list the separator discriminant separately.

### V7. Positivity of Phi is used before it is proved in the manuscript

- Severity: moderate
- Confidence: high
- Location: Section 2 lines 17-30; Section 3
- Problem: `ell=log Phi` is introduced without an explicit proof that `Phi>0`.
- Why it matters: Every logarithmic derivative and quotient denominator depends on positivity.
- Evidence: The proof exists implicitly: for `t>=0` every series term is positive because `2*pi*n^2*e^(2t)>3`, and evenness covers `t<0`; it is stated in the certificate note but omitted from the paper.
- Required correction or test: Add the two-line analytic proof before defining `ell`.

### V8. Certificate precision/dependency metadata are inconsistent with the base calculations

- Severity: moderate
- Confidence: high
- Location: Section 3 lines 28-35; CERT2/CERT3 metadata; retained compact outputs
- Problem: The base compact computations report 192 bits, while CERT2 summarizes 256 bits; CERT3's wrapper requirements omit python-flint/Arb used by the base compact certificate.
- Why it matters: A reproducer cannot infer the correct environment from the certificate header alone.
- Evidence: Direct comparison of metadata, wrappers, and retained outputs.
- Required correction or test: Separate base-certificate and audit-wrapper manifests with exact requirements and precision for each.

### V9. Strict PF3 is credited with a stronger implication than it provides

- Severity: moderate
- Confidence: high
- Location: Section 11 lines 80-86
- Problem: “Strict PF3 also gives kappa=...” attributes positive `kappa` to strict PF3. The displayed identity uses the specifically established relation `F2>0`; strict PF3 alone is not shown to imply it.
- Why it matters: The genericity of the separator bridge is overstated.
- Evidence: `kappa=1+F2/q^3` follows algebraically from the manuscript's definitions; the proof only establishes it through the stronger sufficient condition.
- Required correction or test: Replace the attribution with “The established inequalities `q>0` and `F2>0` give...”.

### V10. Submission and accessibility metadata are incomplete

- Severity: moderate
- Confidence: high
- Location: Title page and PDF metadata
- Problem: The author is a pseudonym with no affiliation/contact, contribution statement, acknowledgments, code/data availability statement, conflict statement, keywords, or MSC; the PDF is untagged.
- Why it matters: Many journals cannot process or publish the article in this state, and the PDF is not accessible.
- Evidence: Title page, source, and `pdfinfo`.
- Required correction or test: Add journal-required identity/provenance statements and produce a tagged accessible PDF.

## Plausible concerns

### C1. “Sharp” is undefined

- Severity: moderate
- Confidence: medium
- Location: Title and Introduction lines 29-36
- Problem: The separator proves PF4 insufficiency, not a finite-order threshold at which Fourier real-rootedness becomes sufficient.
- Why it matters: A hostile reviewer may read “sharp” as an optimality theorem not proved here.
- Evidence: No PF5-or-higher sufficiency theorem appears.
- Required correction or test: Define “sharp” as “matched to the proved order-four class” or remove the adjective.

### C2. “Global coordinate” may imply more than is proved

- Severity: minor
- Confidence: medium
- Location: Section 6 lines 3-8
- Problem: Strict monotonicity is shown, but surjectivity of `y=-s` onto all of `R` is not stated.
- Why it matters: The proof only needs an increasing coordinate on the image; terminology should not suggest an unused onto claim.
- Evidence: No endpoint-range argument is printed.
- Required correction or test: Say “global increasing coordinate on the image” or prove the range statement.

### C3. Independent implementation diversity is limited

- Severity: moderate
- Confidence: medium
- Location: Reproducibility section and certificate chain
- Problem: Several checks reuse SymPy/mpmath conventions and repository-derived formulas even when described as independent.
- Why it matters: Correlated implementation errors remain possible in a computer-assisted proof.
- Evidence: Common language/runtime and imported advancement modules in wrapper checks.
- Required correction or test: Add one genuinely independent implementation or a proof-assistant/formal algebra check for the central identities.

## Open questions

### Q1. External originality

- Severity: major if adverse prior art exists
- Confidence: low
- Location: Introduction and title
- Problem: No complete priority search was supplied.
- Why it matters: The paper's novelty cannot be certified from the local corpus.
- Evidence: The local corpus and two-entry manuscript bibliography are not a complete priority record.
- Required correction or test: Human search of MathSciNet, zbMATH, Crossref, citation graphs, and current preprints.

### Q2. Human verification of image-only literature

- Severity: moderate
- Confidence: low
- Location: Citation review
- Problem: The supplied Csordas-Varga PDF is image-based and yielded no searchable text.
- Why it matters: It may contain relevant moment inequalities or prior framing that should be discussed.
- Evidence: Local text extraction returned blank pages.
- Required correction or test: OCR or human reading of the paper before finalizing related work.

### Q3. Full independent certificate replay

- Severity: major if replay fails
- Confidence: low
- Location: CERT2 and CERT3 base computations
- Problem: The audit honored the instruction not to recompute already certified quantities.
- Why it matters: Static inspection cannot substitute for an independent fresh-platform replay.
- Evidence: Current MIND attestations and retained outputs were inspected, not regenerated.
- Required correction or test: Journal/reviewer replay from the immutable public release on a clean environment.
