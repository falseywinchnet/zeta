# Independent audit report

Manuscript audited: *Strict global PF4 for the Riemann kernel and a sharp Fourier separator*

Author shown in manuscript: falseywinchnet

Manuscript date: 16 July 2026

Audit date: 16 July 2026

Round mode: refine

Scope note: By author direction, the Michalowski citation will be removed. The exact-order conclusion is assumed to switch to a hardened version of *The Riemann Kernel is Not a Polya Frequency Function of Infinite Order*. That future hardened witness is treated as a mandatory pre-publication boundary, not as evidence already present in the audited PDF.

## 1. Executive assessment

The surviving mathematical core is promising. On the supplied record, the strict-global-PF4 proof has a coherent dependency chain:

`q,F2>0` -> strict PF3 and `Lambda>0` -> quotient-Wronskian reduction -> curvature transport identity -> positive one-crossing kernel -> `partial_xi Psi<0` -> strict PF4.

The explicit seven-Gaussian separator is also coherent: exact inequalities give `q,F2>0`, exact rational algebra gives a positive order-four density, and a directed discriminant enclosure gives nonreal Fourier zeros. I found no fatal sign error, invalid causal/statistical inference, or numerical contradiction in these two proof chains. The public and build PDFs are byte-identical and visually clean.

The paper is not publishable in its current form. Its most serious defects are at the evidence and editorial boundary. The PDF does not identify an immutable repository release; two scripts labeled as directed replay commands do not rerun the directed compact covers; the article claims that all load-bearing algebra is displayed when important certificate content is only summarized; and the literature review is too thin to establish originality or locate the work within finite-order total positivity and Riemann-kernel Wronskian research. The exact-order headline also remains conditional until the hardened replacement PF5 witness is integrated, publicly versioned, and replay-linked.

The correct disposition is major revision, not rejection, provided the authors can freeze and independently replay the full certificate chain and harden the replacement PF5 witness. Failure of either gate would escalate the recommendation to reject because the headline theorem would then lack an auditable evidence boundary.

## 2. Recommendation: major revision

**Recommendation: major revision.**

Reasons:

1. No fatal defect was found in the strict-PF4 transport proof or the continuous separator.
2. Crucial computer-assisted premises are locally certified, but the published PDF does not let an external reader obtain and fully replay the exact release.
3. The reproducibility table overstates what two named wrapper scripts execute.
4. Several evidence-boundary and logical-attribution statements are inaccurate.
5. The exact-order claim depends on a hardened replacement PF5 source that is not yet integrated.
6. The bibliography and related-work discussion are inadequate for priority, originality, and method attribution.
7. Submission identity, availability, and accessibility metadata are incomplete.

Acceptance should require an immutable release, a clean-room full replay, integration of the hardened order-five witness, corrected evidence language, and a substantially expanded literature review.

## 3. Ten highest-priority findings

### Finding 1: No externally resolvable reproducibility anchor

- **Status:** Verified defect
- **Severity:** major
- **Confidence:** high
- **Location:** Section 12; Appendix D; every repository-relative path in the PDF
- **Problem:** The PDF names files such as `scripts/verify_pf3_reduction.py` but supplies no repository URL, archive DOI, release tag, commit, environment lock, or source checksum.
- **Why it matters:** A reader cannot obtain the exact research object or determine whether a later repository state is the one that supports the theorem.
- **Evidence:** Inspection of the PDF, LaTeX source, metadata, and repository instructions. The local PDF is reproducible only because the auditor already has the repository.
- **Required correction or test:** Publish an immutable archive; cite its DOI/URL and commit in the PDF; give a one-command replay entry point and the final PDF hash.

### Finding 2: Two named “directed” replay scripts do not replay the directed compact covers

- **Status:** Verified defect
- **Severity:** major
- **Confidence:** high
- **Location:** Section 12, table lines 12-15 and prose lines 27-32; `scripts/verify_pf3_reduction.py`; `scripts/verify_c4_confluent.py`
- **Problem:** The PF3 wrapper performs symbolic identities, two imported jet comparisons, and sampled high-precision checks; it does not execute the 7,731-cell directed cover. The C4 wrapper reconstructs exact algebra and a tail margin but does not execute the 8,050-cell directed cover.
- **Why it matters:** “Directed and exact” is reasonably read as describing what happens when the named command is run. That is not what these two commands do.
- **Evidence:** Static inspection of the wrappers and the separate underlying scripts and retained outputs. The directed calculations exist, but under different files and without being the named wrapper action.
- **Required correction or test:** Publish separate commands for full directed replay and lightweight audit. Label each accurately and include expected output hashes, precision, run time, and dependencies.

### Finding 3: “All load-bearing algebraic reductions are displayed” is false

- **Status:** Verified defect
- **Severity:** major
- **Confidence:** high
- **Location:** Abstract lines 18-19; Section 11 lines 70-78; Appendix E lines 21-34; Appendix B lines 8-45
- **Problem:** The paper does not display the degree-72 separator numerator or its 73 coefficients, nor does it fully derive the global theta-tail padding inequalities. It reports that a verifier checked them.
- **Why it matters:** The distinction between a human-readable derivation and a code certificate is a central editorial claim of the paper. The present text crosses its own declared boundary.
- **Evidence:** Appendix E states degree, palindromy, and coefficient positivity without printing `H` or an equivalent positive decomposition. Appendix B says the verifier evaluates the tail inequalities with directed balls.
- **Required correction or test:** Either include a compact independently checkable certificate in the article/supplement or revise the claim to state exactly which steps are code-certified.

### Finding 4: Literature support is materially incomplete

- **Status:** Verified defect
- **Severity:** major
- **Confidence:** high
- **Location:** Introduction lines 9-11 and 29-55; References
- **Problem:** The bibliography contains only two entries, one slated for replacement. It omits supplied primary literature directly relevant to finite-order PF characterization and Riemann-kernel/Fourier-Wronskian methods.
- **Why it matters:** A reviewer cannot assess originality, method attribution, or relation to prior results. The sparse bibliography makes a substantial new theorem look isolated from its actual field.
- **Evidence:** Khare's supplied paper gives a finite-order TNp characterization; Dimitrov-Xu use the same Riemann-kernel normalization and study Fourier/Laplace Wronskians and real-zero criteria. Neither is cited.
- **Required correction or test:** Add a related-work section, cite the relevant primary literature, and complete a documented external priority search before making a precise originality claim.

### Finding 5: The replacement PF5 evidence boundary is not yet integrated

- **Status:** Verified current-artifact defect; planned correction acknowledged
- **Severity:** major
- **Confidence:** high
- **Location:** Introduction lines 21-27; Section 10 lines 8-9; References; Section 12; Appendix D
- **Problem:** The audited PDF still rests the exact-order corollary on Michalowski, while the planned hardened replacement is absent from the bibliography, provenance table, replay table, and MIND dependency statement printed in the paper.
- **Why it matters:** Strict PF4 proves only the positive half. The headline “exact order four” remains conditional until the negative order-five witness is an immutable, replayable premise for this exact kernel normalization.
- **Evidence:** Cross-file inspection of the current PDF and the stated replacement plan.
- **Required correction or test:** Integrate the hardened replacement; print the witness coordinates and directed determinant enclosure; add its full replay command and immutable locator; remove all Michalowski references; rerun a cross-document search for stale dependencies.

### Finding 6: The abstract understates the computer-assisted boundary

- **Status:** Verified defect
- **Severity:** moderate
- **Confidence:** high
- **Location:** Abstract lines 6-8 versus Section 11.3 lines 102-108
- **Problem:** The abstract says the computer-assisted input is confined to global positivity of `q,F2,C4` and that “the remainder is exact.” The separator's Fourier-zero proof uses a directed 192-bit discriminant enclosure.
- **Why it matters:** Readers are given an inaccurate classification of which conclusions depend on computation.
- **Evidence:** Section 11.3 explicitly reports the directed discriminant interval.
- **Required correction or test:** Scope the sentence to the Riemann-kernel positive proof or list the separator discriminant as a second computational boundary.

### Finding 7: Positivity of the Riemann kernel is used before it is proved

- **Status:** Verified defect
- **Severity:** moderate
- **Confidence:** high
- **Location:** Section 2 lines 17-30; all later definitions involving `ell=log Phi`
- **Problem:** The manuscript defines `log Phi` without explicitly proving `Phi>0`.
- **Why it matters:** Every logarithmic derivative, quotient, and probability normalization depends on strict positivity.
- **Evidence:** The missing proof is available from the manuscript itself: for `t>=0`, every term in the displayed series is positive because `2*pi*n^2*e^(2t)>3`; evenness covers `t<0`. The certificate note states this, but the article does not.
- **Required correction or test:** Add this analytic argument immediately before defining `ell`.

### Finding 8: Certificate precision and dependency metadata are inconsistent

- **Status:** Verified defect
- **Severity:** moderate
- **Confidence:** high
- **Location:** Section 3 lines 28-35; CERT2/CERT3 metadata; retained compact-certificate outputs
- **Problem:** The compact PF3 output and paper state 192-bit precision, while CERT2 summarizes 256 bits from the wrapper cross-check. CERT3's declared requirements omit python-flint/Arb even though its underlying compact cover uses them.
- **Why it matters:** A clean-room reproducer cannot infer which precision and packages belong to the theorem-producing calculation versus the audit wrapper.
- **Evidence:** Direct comparison of MIND metadata, wrapper source, base source, and retained outputs.
- **Required correction or test:** Give separate machine-readable manifests for base certificates and wrapper audits, with exact versions and precision for each.

### Finding 9: Strict PF3 is credited with an implication not established

- **Status:** Verified defect
- **Severity:** moderate
- **Confidence:** high
- **Location:** Section 11 lines 80-86
- **Problem:** “Strict PF3 also gives” the positive curvature quantity `kappa`. In the proof, `kappa=1+F2/q^3>0` comes from the stronger pointwise inequalities `q>0,F2>0`, not from strict PF3 as an abstract property.
- **Why it matters:** The sentence overstates the generic reach of the transport bridge and blurs necessity with a sufficient condition used for this example.
- **Evidence:** Algebra from the manuscript's definitions and the actual dependency chain.
- **Required correction or test:** Replace the attribution with “The established inequalities `q>0` and `F2>0` give...”.

### Finding 10: Submission provenance and accessibility metadata are incomplete

- **Status:** Verified defect
- **Severity:** moderate
- **Confidence:** high
- **Location:** Title page; PDF metadata; end matter
- **Problem:** The manuscript gives a pseudonym but no affiliation/contact convention, contribution statement, acknowledgments, conflicts, code/data availability statement, keywords, or MSC classification. The PDF is untagged.
- **Why it matters:** Many journals cannot process the submission in this state, and the PDF lacks accessibility structure.
- **Evidence:** LaTeX source and `pdfinfo` inspection.
- **Required correction or test:** Add journal-required provenance and availability statements, keywords/MSC, and produce a tagged accessible PDF.

## 4. Claim-by-claim audit

### 4.1 Strict global PF4

**Verdict:** Supported on the supplied local proof record; no fatal defect identified.

The weighted-mean proof of `Lambda>0` is valid under `q>0,F2>0`. The quotient identities have the correct sign orientation, and the iterated-integral argument is an appropriate route from successive quotient positivity to collocation minors. The converse coalescence argument correctly yields the monotonicity criterion under the already established strict lower-order positivity.

The curvature identity `C4=Q^6 kappa^2 D`, the endpoint cancellation, and the CDF integration-by-parts sign are mutually consistent. The density ratio decreases from infinity to zero, making the CDF difference positive in the open interval. Therefore the central transport numerator is positive and `partial_xi Psi<0` follows with the stated sign.

The main weaknesses are not an identified mathematical counterexample but the incomplete publication-level replay boundary and the omitted elementary positivity proof for `Phi`.

### 4.2 Exact global PF order four

**Verdict:** Conditional on the hardened replacement order-five witness.

Strict PF4 plus one certified negative fifth-order minor is sufficient. The final paper must make the replacement witness a first-class premise: exact coordinates, kernel normalization, directed enclosure, code, command, hash, and immutable source. Until then, the exact-order corollary is not independently auditable from the final publication plan.

### 4.3 Positive even Schwartz separator

**Verdict:** Supported locally.

The Gaussian-mixture form gives positivity and Schwartz decay; palindromy gives evenness. Popoviciu's bound and the fourth-cumulant inequality yield the printed strict margins. The exact rational recurrence and determinant reconstruction are logically sufficient if the reported 73 positive coefficients are reproduced from the immutable code release.

The selection of the coefficient vector does not introduce statistical selection bias into the existential theorem because the final object is verified exactly. It would matter only if the paper generalized from search frequency or success rate, which it does not.

### 4.4 Nonreal Fourier zeros of the separator

**Verdict:** Supported locally.

The Gaussian factor is zero-free. The palindromic Laurent factor reduces to the printed real cubic. A strictly negative discriminant gives a nonreal conjugate pair in `u`; such a value cannot equal `w+w^{-1}` with `|w|=1`, so a logarithmic lift gives a Fourier zero with nonzero imaginary part. The only non-exact step is the directed discriminant enclosure, which should be acknowledged in the abstract.

### 4.5 PF3/PF4 membership does not force Fourier real-rootedness

**Verdict:** Valid consequence of the separator.

Because strict PF4 includes PF4 and PF3 membership, one verified counterexample proves insufficiency of both finite-order conditions. The adjective “sharp” should be defined as “matched to the order-four class” rather than as a claim that PF5 or any finite higher order suffices.

## 5. Methodological and statistical audit

This is a computer-assisted proof, not an empirical study. Conventional sampling uncertainty, p-values, power, multiplicity, causal identification, and data leakage are not applicable to the theorem statements.

The relevant methodological risks are proof coverage, directed rounding, dependency completeness, implementation correlation, and selective presentation of computational checks.

- **Coverage:** The retained PF3 and C4 outputs report covers of `[0,1]`; evenness covers `[-1,1]`, and explicit tail lemmas start at `|t|>=1`. No domain gap was found.
- **Margins:** The printed compact lower bounds are conservative relative to retained outputs. The separator discriminant interval is far from zero at the reported precision.
- **Multiplicity:** Thousands of interval cells do not require statistical multiple-testing correction; each is a deterministic enclosure. They do require an exhaustive cover manifest or a trusted deterministic generator.
- **Selection bias:** The separator was evidently designed or searched, but exact verification of the final explicit kernel is sufficient for an existence theorem. Search provenance is not a validity premise.
- **Overfitting:** Not applicable in the statistical sense. A structurally analogous risk is verifying identities only at diagnostic points; the exact symbolic checks avoid that for the transport algebra, while the two compact inequalities still depend on their separate global directed covers.
- **Robustness:** The central theorem is stronger than a numerical scan because it uses exact transport identities. Robustness would improve materially with an independent implementation of the compact certificates and central symbolic identities.
- **Null results:** No null-hypothesis interpretation appears.

The main methodological correction is to distinguish full proof-producing computations from sampled or symbolic audit wrappers.

## 6. Citation and literature audit

The Belton et al. source supports the TP/TN definitions and Schoenberg background attached to it. The current Michalowski citation is slated for removal and is not assessed further.

The planned hardened replacement order-five paper must be cited as an immutable final object, not by a moving local filename. Its theorem must correspond exactly to the maintained kernel and must have a replay boundary in the main paper.

Verified gaps from the supplied library include:

1. Khare's finite-order TNp/PF characterization, directly relevant to how finite-order membership is certified.
2. Dimitrov-Xu on Riemann-kernel Fourier/Laplace Wronskians and real-zero criteria, directly relevant to both halves of the paper.
3. A primary source for the Riemann-kernel normalization and its Fourier relation to Xi.
4. A citation for Popoviciu's inequality.
5. Context for moment-inequality, Jensen-polynomial, and de Bruijn-Newman approaches so that the RH-neutral boundary is situated rather than merely asserted.
6. Literature on extended Chebyshev systems or quotient-Wronskian criteria if the iterated-integral machinery is classical; otherwise the paper should state precisely what part is new.

Originality remains an open external question. The local corpus is insufficient for a priority claim. A full human search of MathSciNet, zbMATH, Crossref, citation graphs, and current preprints is required.

## 7. Reproducibility audit

The local evidence architecture is stronger than the PDF communicates. MIND pins certificate scripts and artifacts by hash, and current attestations exist for CERT2, CERT3, CERT5, CERT9, and CERT10. The public and build PDFs are byte-identical.

The publication nevertheless fails an external reproducibility test because the reader is not told where to obtain that exact repository state. In addition, the two compact-certificate wrappers do not perform the full directed calculations named by the prose. The base calculations are separate artifacts.

A satisfactory release must provide:

1. An immutable archive DOI/URL and commit.
2. A machine-readable dependency lock or container.
3. Separate `full-replay` and `quick-audit` commands.
4. Expected hashes for all base outputs and the PDF.
5. Run-time, memory, precision, and platform information.
6. A theorem-to-command manifest including the hardened order-five witness.
7. One clean-room replay by a person or implementation not involved in producing the certificate.

The audit did not recompute already certified quantities, as instructed. This leaves clean-room replay as an explicit external verification item rather than a negative finding about the numerical results.

## 8. Internal contradictions and numerical discrepancies

### Verified contradictions or misstatements

1. Abstract “computer-assisted input is confined to `q,F2,C4`; remainder exact” versus the directed separator discriminant.
2. Section 12 labels two wrappers “directed and exact,” while they do not run the directed compact covers.
3. Abstract says all load-bearing algebra is displayed; the separator coefficient certificate and full tail padding proof are not displayed.
4. Section 11 attributes positive `kappa` to strict PF3 rather than to the stronger established `F2>0` condition.
5. The current bibliography points to the source that the author intends to remove, while the replacement evidence boundary is absent.

### Numerical checks with no discrepancy found

- `q>=18.7268` is below the retained certified lower endpoint.
- `F2>=3889.2` is below the retained certified lower endpoint.
- `C4>=2.817e7` is below the retained certified lower endpoint.
- Cell counts 7,731 and 8,050 match retained outputs.
- The tail `E4` example is arithmetically consistent.
- The separator's `143/128` margin is correct.
- Root and build PDFs have identical SHA-256 hashes.
- No unresolved LaTeX references, visible layout defects, or broken equations were found.

## 9. Missing analyses or evidence

1. Hardened and independently replayable order-five witness for the exact-order conclusion.
2. Immutable public source release tied to the PDF.
3. Full replay commands for the two compact interval covers.
4. Clean-room independent implementation or formal check of the most load-bearing identities.
5. Printable or supplementary exact certificate for the 73 separator coefficients.
6. Fully stated theta-tail lemmas with every constant and monotonicity condition.
7. Complete related-work and priority review.
8. Human/OCR inspection of the image-only Csordas-Varga source.
9. Author, contribution, availability, conflict, keyword, MSC, and accessibility metadata.
10. A post-revision consistency search across title, abstract, theorem statements, provenance table, references, and MIND anchors.

## 10. Strongest possible reviewer objections

1. **“I cannot reproduce the theorem from the paper.”** The PDF names local files but supplies no obtainable immutable release, and its named replay scripts do not all run the theorem-producing computations.
2. **“The paper overstates its human-readable proof boundary.”** The coefficient and tail certificates are summarized, not displayed, despite a categorical abstract claim.
3. **“The headline exact-order result depends on future evidence.”** The intended hardened replacement witness is not yet in the audited paper.
4. **“The novelty case is not made.”** One surviving background citation is not an adequate literature review for a theorem spanning finite total positivity, Riemann kernels, Wronskians, and Fourier zeros.
5. **“The computation has insufficient implementation diversity.”** Multiple checks use the same language ecosystem and repository-derived formulas; correlated mistakes are not excluded by spot checks.
6. **“The term ‘sharp’ overclaims.”** The separator proves order-four insufficiency but no finite-order sufficiency threshold.
7. **“The submission is editorially incomplete.”** Authorship/provenance, code availability, classifications, and accessibility are missing.

These objections support major revision. Objections 1 and 3 would support rejection if the authors cannot close them.

## 11. Concrete revision plan ordered by expected effect on validity

1. **Harden the replacement order-five witness.** Use exact printed coordinates, a directed determinant enclosure, explicit kernel normalization, an independent replay, and a content-addressed certificate.
2. **Freeze the complete evidence release.** Archive code, artifacts, sources, and the built PDF; cite the DOI/URL and commit in the manuscript.
3. **Create a truthful replay hierarchy.** Provide full directed replay commands and separate quick symbolic/audit commands; correct Section 12 and Appendix D.
4. **Correct the evidence-boundary claims.** Amend the abstract, disclose the separator discriminant, and stop claiming that every load-bearing reduction is printed unless it is.
5. **Close the elementary logical gaps.** Prove `Phi>0` before `log Phi`; attribute `kappa>0` to `q,F2>0`; qualify “global coordinate” and define or remove “sharp.”
6. **Expose compact certificate objects.** Add a supplement containing the separator coefficient certificate, complete tail constants, output hashes, and theorem-to-command manifest.
7. **Add independent verification.** Reimplement the compact inequalities or central symbolic identities using a second system or formal proof environment.
8. **Rewrite the introduction and related work.** Cite finite-order PF characterization, Riemann-kernel Wronskians, kernel normalization, and adjacent real-rootedness approaches; state the new contribution precisely.
9. **Complete submission metadata and accessibility.** Add author/provenance, availability, conflicts, keywords/MSC, acknowledgments, and a tagged PDF.
10. **Run final consistency and visual QA.** Search for stale citations and evidence anchors, rebuild, compare hashes, rerender all pages, and have an external reader follow the replay instructions from the PDF alone.

## 12. Findings requiring human or external-source verification

1. **Priority and originality:** comprehensive database and citation-graph search.
2. **Replacement PF5 evidence:** independent audit of the hardened final version, not the current local draft.
3. **Clean-room replay:** execution on a fresh system from the archived release.
4. **Image-only literature:** OCR or human reading of the supplied Csordas-Varga paper.
5. **Method attribution:** expert judgment on which quotient-Wronskian and stochastic-order steps are classical versus new.
6. **Journal compliance:** authorship identity, conflict, code-availability, accessibility, and computer-assisted-proof policies of the target journal.
7. **Long-term archive integrity:** confirmation that all cited papers, certificate outputs, and exact code artifacts are included with checksums.

---

**Bottom line:** The strict-PF4 and continuous-separator arguments merit serious consideration and survived this local adversarial audit without an identified fatal mathematical error. Publication should wait for a hardened order-five witness, an immutable cleanly replayable release, corrected evidence claims, and a real literature review.
