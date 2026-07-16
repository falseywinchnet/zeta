# Repository and manuscript inventory

## Authoritative publication

- Public PDF: `strict-global-pf4-riemann-kernel.pdf` (15 pages, letter size, 141,076 bytes).
- Maintained build PDF: `paper/build/strict-global-pf4-riemann-kernel.pdf`.
- SHA-256 of both PDFs: `736980434c4f754de0ac1cbe5e92102761827a1739f50a28aa20facd132209d5`.
- Result: the public and maintained PDFs are byte-identical.
- Visual result: all 15 pages rendered successfully. No clipped text, overlaps, broken glyphs, unresolved cross-references, or visibly broken tables were found.
- PDF metadata result: the file is untagged and has no accessibility structure.

## Maintained source

- Assembly: `paper/manuscript/main.tex`.
- Shared definitions: `paper/manuscript/preamble.tex`.
- Main sections: `paper/manuscript/sections/S00-abstract.tex` through `S12-references.tex`.
- Appendices: `paper/manuscript/appendices/A1-algebra.tex` through `A5-separator.tex`.
- Editorial dependency map: `paper/PAPER_MAP.md`.
- Build instructions: `paper/README.md` and `paper/Makefile`.

The source is modular and the public PDF is refreshed by the `publish` target. The build requires `tectonic`, but the PDF does not give readers a repository URL, release identifier, commit, DOI, or environment lock.

## Principal proof records

- `sources/pf3-global-certificate.md`
- `sources/c4-confluent-certificate.md`
- `sources/pf4-wronskian-reduction-certificate.md`
- `sources/pf4-transport-kernel-certificate.md`
- `sources/continuous-pf4-separator-certificate.md`

## Certificate-facing scripts

- `scripts/verify_pf3_reduction.py`
- `scripts/verify_c4_confluent.py`
- `scripts/verify_pf4_wronskian_reduction.py`
- `scripts/verify_pf4_transport_kernel.py`
- `scripts/verify_continuous_pf4_separator.py`

The MIND records identify these as `CERT2`, `CERT3`, `CERT5`, `CERT9`, and `CERT10`. Their attestations were current on 2026-07-16. The local copy is therefore treated as already certified; the audit inspected the verification boundary but did not recompute certified quantities.

## Underlying compact-certificate artifacts

- PF3 compact code/output:
  - `work/2026-07-12-riemann-kernel-pf34-classification/certify_pf3_curvature.py`
  - `work/2026-07-12-riemann-kernel-pf34-classification/pf3-curvature-certificate.txt`
- Confluent PF4 compact code/output:
  - `work/2026-07-13-riemann-kernel-pf4-verification/certify_c4.py`
  - `work/2026-07-13-riemann-kernel-pf4-verification/c4-certificate.txt`
- Analytic tail artifacts:
  - `work/2026-07-12-riemann-kernel-pf34-classification/verify_tail_bounds.py`
  - `work/2026-07-13-riemann-kernel-pf4-verification/tail-polynomial.txt`
  - `work/2026-07-13-riemann-kernel-pf4-verification/c4-tail-check.txt`

The retained outputs support the displayed lower bounds and report 192-bit precision, 7,731 PF3 cells, and 8,050 confluent-PF4 cells.

## Bibliography and supplied literature

The manuscript bibliography has two entries: Belton et al. and Michalowski. The latter citation is slated for deletion. The exact-order conclusion is expected to use a hardened replacement based on `papers/The Riemann Kernel is Not a Polya Frequency Function of Infinite Order.pdf`, which uses the same kernel normalization as the maintained manuscript. The replacement is not yet integrated into the audited PDF and is therefore a pre-publication evidence gate.

Supplied but uncited primary sources directly relevant to the surviving paper include:

- `papers/khare-multiply-positive.pdf` (finite-order TN/PF characterization).
- `papers/dimitrov-xu-wronskians.pdf` (Riemann kernel, Fourier/Laplace Wronskians, and the Fourier-real-zero setting).
- `papers/csordas-varga-moment-inequalities.pdf` (Riemann-kernel moment inequalities; the local PDF is image-based and needs human/OCR inspection for precise claim matching).
- `papers/jensen-polynomials-xi.pdf` (nearby real-rootedness literature, relevant mainly for contextual boundaries).
- `papers/rodgers-tao-debruijn-newman.pdf` (standard de Bruijn-Newman normalization and context).

## Data, figures, tables, and appendices

- No empirical dataset is used.
- No scientific figures are used.
- The paper has one reproducibility table and one provenance table.
- Quantitative evidence consists of directed interval calculations, exact symbolic/rational algebra, and high-precision diagnostic spot checks.
- Appendices A1-A5 contain algebraic expansions, tail constants, endpoint cancellation, provenance, and separator reconstruction summaries.
