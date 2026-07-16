# Candidate paper integration map

This is an advancement artifact. A later refine round must audit and integrate
it; the maintained manuscript is intentionally unchanged here.

1. Replace `paper/manuscript/sections/S10-completion.tex` with the audited form
   of `candidate-S10-completion.tex`.
2. In `S00-abstract.tex`, replace “Together with the certified negative
   order-five minor of Michalowski” by “A direct origin-confluent calculation
   gives a negative order-five minor.”
3. In `S01-introduction.tex`, replace the Michalowski paragraph by a forward
   reference to Theorem `thm:not-pf5`; retain the exact-order corollary.
4. Delete the `michalowski` bibliography item from `S12-references.tex`.
5. Remove CITE4/Michalowski dependencies from `PAPER_MAP.md`, the root paper
   map, theorem-support tables, and reproducibility prose. Replace them with
   the promoted certificate for `verify_origin_pf5.py`.
6. Replace `S11-reproducibility.tex` and `A4-provenance.tex` with audited forms
   of the candidate files in this round so the sixth replay boundary is named.
7. Copy the verifier and its preserved output into the maintained certificate
   surface, register its standard-library-only replay environment, and add the
   source checksum.
8. Compile and visually inspect the paper; search the assembled source and PDF
   text for “Michalowski” and the removed citation key.
