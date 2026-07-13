# Riemann-kernel global PF4 verification

Mode: advancement

Date: 2026-07-13

Model: Claude Fable 5, Anthropic

Question: determine whether the Riemann/de Bruijn-Newman kernel is globally
PF4, completing the exact Polya-frequency classification left at "three or
four" by R145.

Starting MIND: R4, R14, R16, R27, R140-R146, CITE24, CITE25.

By R146 (Khare's Theorem E) only the order-four minors need checking: PF3 is
established (R144), and order-four nonnegativity plus measurability and decay
yields TN4.

Decision order:

1. Probe the collision boundary first, because that is where PF5 died (R14).
   The fully confluent order-four minor is one-dimensional: up to positive
   factors it is C4(t) = det of the 4x4 Hankel matrix of derivatives
   Phi^(i+j-2)(t), a polynomial in the cumulants ell_2..ell_6 of log Phi. A
   certified negative value converts to an explicit negative minor and closes
   PF4 (order exactly three). The order-three identity C3 = q^3 + F2 ties the
   confluent family to the certified PF3 quantities.
2. Probe the x-collision faces: the translate Wronskians W3(t; gaps) and
   W4(t; gaps) are limits of minors, so a negative value also refutes PF4.
3. Probe generic and clustered configurations (Sobol, partial collisions).
4. Whatever survives probing gets certified where the dimension allows:
   compact core by directed adaptive interval cells, escape regimes by
   analytic tail enclosures in x = pi e^{2u}, evenness for the negative axis.

`jet.py` is a copy of the audited P000023 certifier
(`certify_pf3_curvature.py`, CITE24) reused for its order-six derivative jet
and theta-tail machinery.

## Outcome

Every falsification probe came back positive for PF4:

1. Confluent Hankel scan (`confluent_hankel_scan.py`): C4(t) > 0 on the grid,
   minimum 1.32e8 at t=0; the C3 = q^3 + F2 identity held at every point.
2. Toeplitz anchor (`toeplitz_anchor.py`, `toeplitz-anchor.txt`): R14's
   order-five violation reproduced with directed intervals
   (det5 = -7.31e-13 certified negative at u0=0.01, h=0.05); the order-four
   determinant at the same configuration is certified positive (1.96e-8).
3. Wronskian faces (`wronskian_scan.py`): W3 and W4, 2^21 Sobol samples each,
   no negative; minima at the collision boundary, consistent with the
   positive confluent limits.
4. Clustered minors (`cluster_scan.py`): 2x2^21 samples near the PF5 failure
   regime and broadly, no negative.

Certified (raw, pending refine audit): C4(u) > 0 on all of R — every fully
doubly-confluent order-four minor of the Riemann kernel is strictly positive.
Chain in `MATHEMATICS.md`:

- moment-Hankel reduction C4/Phi^4 = det[m_{i+j-2}] in cumulants ell_2..ell_6,
  numerically validated against genuine epsilon-spaced minors
  (det/(eps^12 C4 Phi^4) -> 1);
- exact structural decomposition (sympy-verified):
  C4 = 3(2q^3-F1)(2q^3-3F1) + 2(q^2 F1'' - 6qq'F1' + 9q'^2 F1) - det H3[q],
  identifying the 2x2 cumulant minors with the audited PF3 invariants
  F1, F1', F1'' and exposing the certified factor 2q^3-F1 = q^3+F2 > 0;
- compact core on [0,1]: second-order Taylor cells over division-free CSE
  forms of C4, C4', C4'' in kappa_2..kappa_8 (`generate_c4_forms.py`,
  `c4_forms.py`, `certify_c4.py`), 8050 adaptive cells, certified
  C4 >= 2.817e7, seconds of runtime; startup self-checks tie the cumulant
  recursion to the audited hardcoded expansions and the decomposition to the
  direct form; evenness extends to [-1,1] (`c4-certificate.txt`);
- tail: kappa_j = -2^j x + O(E_j/x) via the Stirling identity
  D^j psi = 2^j sum_k S(j,k) x^k psi^(k); at exact kappa_j = -2^j x the
  Hankel collapses to 49152 x^6 identically (`tail_polynomial.py`), and the
  perturbation bound gives C4 >= 44392 x^6 for |u| >= 1, all delta-terms
  having x-degree <= 4; grid-verified with directed rounding
  (`verify_c4_tail.py`, `c4-tail-check.txt`).

Global PF4 itself remains open: the certified statement covers the full
collision boundary (where PF5 dies); the non-confluent surface has 10^7-scale
scan evidence and no counterexample. The natural continuation is the ECT
route: certify W3 > 0 and W4 > 0 over all translates (four parameters, three
escape regimes), which by the Wronskian criterion for extended complete
Chebyshev systems would imply every order-four minor is positive.

Status: raw advancement research, complete for the confluent boundary.
Nothing in this directory is an established MIND fact until a later
refinement audit.
