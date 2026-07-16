# Reciprocal-xi PF1/PF2 advancement

- Date: 2026-07-16
- Model: OpenAI Codex GPT-5
- Mode: advancement
- Starting MIND records: R5, R7, R17, R18, R61, R81, CITE30
- Question: Does the Schoenberg reciprocal-xi kernel admit a tractable PF1
  or PF2 certificate?
- Status: candidate finite certificate architecture found; no proof promoted

The kernel under study is

\[
  L(x)=\frac1{2\pi}\int_{\mathbb R}
  \frac{e^{-itx}}{\xi(1/2+t)}\,dt.
\]

PF1 is pointwise nonnegativity of `L`. For a positive smooth kernel, PF2 is
equivalent to log-concavity, or `L'(x)^2-L(x)L''(x) >= 0`.

See `NOTES.md` for the spectral identity, shifted-contour reduction, residue
tail, numerical observations, and the remaining proof burdens.

