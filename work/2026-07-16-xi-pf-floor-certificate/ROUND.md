# Reciprocal-xi PF floor certificate

- Date: 2026-07-16
- Model: OpenAI Codex GPT-5
- Mode: advancement
- Starting MIND records: R5, R7, R17, R18, R61, R81, CITE30, P000075
- Question: What PF order can be proved as a global lower bound for the
  reciprocal-xi kernel, beginning with PF1?
- Status: promoted in the following refinement as `R177`, supported by
  `CERT13`--`CERT15` and `CITE32`

Write

\[
  A(t)=\frac{1}{\xi(1/2+t)},\qquad
  L(x)=\Lambda_\Xi(x)=\frac{1}{2\pi}\int_{\mathbb R}A(t)e^{-itx}\,dt.
\]

The primary target is a complete proof that `L(x)>0` on the real line.  PF2
will be tested against the same compact/tail decomposition, but it will not be
claimed unless its determinant numerator is separately certified.

All calculations, bounds, failures, and candidate lemmas from this round are
stored in this directory.  Nothing here is an established MIND theorem until a
later refinement audit.

The main result of the round is `FLOOR_REDUCTION.md`.  Strict PF1 follows from
four coarse real-moment bounds, the classical first-zero statement, one coarse
residue bound, and one absolute contour-norm bound.  The compact/tail splice is
the rational point `x=3/10`; the glue is verified using exact fractions by
`exact_floor_glue.py`.
