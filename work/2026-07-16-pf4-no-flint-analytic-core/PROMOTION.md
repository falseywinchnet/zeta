# Promotion checklist

## Candidate replacement scope

If independently audited, `verify_no_flint_compact.py` can replace the
FLINT/Arb compact and tail sign components of CERT2 and CERT3:

- R142 and R143 should be replaced by one global two-mode-plus-tail proof of
  `q>0` and `F2>0`;
- R150 and R151 should be replaced by the corresponding global proof of
  `C4>0`;
- R141, R147, R149, the PF3 slope lemma, and the PF4 transport theorem remain
  unchanged.

## Required independent audit

1. Re-derive the mode normalization (1) and tail normalization (2) without
   consulting the verifier implementation.
2. Reconstruct the raw `Nq`, `NF2`, and derivative-Hankel `NC4` identities in
   a separate symbolic route.
3. Audit the Bernstein power-to-basis conversion and every stated domain for
   `x` and `y=e^{-3x}`.
4. Audit the `P_j` sign/envelope and the exact monotonicity of the `n=3` term.
5. Audit the geometric bounds for `n>=4` and the weighted-homogeneity argument
   for `x>=5`.
6. Replay in an environment with SymPy installed and python-flint absent.
7. Compare high-precision values at the origin, both split points, and several
   tail points against the existing Arb certificates as a diagnostic only.

## Integration work after audit

- Add a new certificate instead of silently mutating CERT2/CERT3, then archive
  the superseded FLINT sign components only after dependency migration is
  complete.
- Rewrite the paper's certified-input and tail appendices around the two-mode
  formulas and exact coefficient lemma.
- Remove `python-flint` from `requirements-paper.txt` and the release manifest
  only when no remaining paper verifier imports it.
- Decide whether the 501 exact positivity coefficients belong in a generated
  appendix, a compact machine-readable artifact, or both.
- Optionally formalize the small rational kernel in Lean, Coq, or Isabelle;
  SymPy exact replay is not a proof-assistant trust boundary.
