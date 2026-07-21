# Certificate source mapping

The local evidence boundary is `CERT12`.

- `sources/riemann-signs-analytic-certificate.md` states the normalized
  two-mode derivative representation and the three cleared invariant signs.
- `scripts/verify_riemann_signs_core.py`, around its `RAW = a0:7` block,
  constructs:
  - `raw_q = a1^2 - a0*a2`;
  - `raw_f2` by clearing the denominator of the cumulant expression;
  - `raw_h4` as the determinant of the `4 x 4` raw derivative Hankel matrix.
- `ClearedJetCertificateBridge.lean` defines the same three expanded
  polynomials and proves their exact relation to the maintained curvature
  objects.

This round does not treat the Python execution as a Lean theorem.  Its final
Lean theorem has the three raw strict inequalities as explicit premises.  The
remaining certificate-to-Lean boundary is to construct the literal Riemann
theta derivative functions and prove those premises for them from a replayable
formal certificate representation.
