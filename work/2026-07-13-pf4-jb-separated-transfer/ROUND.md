# Advancement round: full-theta J_b separated transfer

Date: 2026-07-13
Model: Sydney, OpenAI Codex
Mode: advancement
Starting records: R101, R111, R112, R113, R137, R138, R157, R158,
R159, R160, R161; P000041

## Question

Can the exact collision radius from P000041 be joined to a full-theta
dominant-term transfer on its radial complement, without losing either angular
face?

## Status

In progress.

## w-frame restructuring (Claude Fable 5)

`prove_jb_clean_wframe.py` reformulates the clean n=1 obligation in
w = 2z-3 coordinates, where every one-term object is an exact Laurent
polynomial: s = 3/2 - w + 6/w, q = 2w+6+12/w+36/w^2, jets via the operator
2z d/dz = 2(w+3) d/dw, and the differences telescope:
B = d1(1+6/(w0 w1)), C = d2(1+6/(w1 w2)) with w1 = w0+d1, w2 = w0+d1+d2.
Verified symbolically, and the assembled comparison verified equal to
J_b - target at rational sample points against the original parametrization.

Findings:

- The cleared clean comparison is 746 terms, degrees (21,12,6), and FACTORS:
  4 * d2 * d1^2 * (w0+3)^3 * (d1+d2) * (d1+w0) * core, every prefactor
  manifestly positive on w0 >= 43, d1,d2 >= 0. The two angular faces are the
  explicit factors d1^2 * d2 * (d1+d2); no separate face modules are needed.
- The 312-term core (degrees (17,8,4)), shifted onto the exact separated
  boxes (d1 >= (w0+3)/2^34 resp. d2 >= (w0+d1+3)/2^34, both affine in the
  shifted variables), has 495 coefficients, all nonnegative, on both boxes.
  Runtime 42 seconds, ~100 MB, exact rational arithmetic.
- Still open to reach the full P000041 obligation: the theta-tail
  perturbation, previously threaded as ten error symbols through the whole
  pipeline. Proposed replacement: a single envelope lemma — every error
  coefficient carries a 2^-99 relative factor, so one positive-coefficient
  majorant polynomial in the same w-frame bounds the entire tail
  contribution below the certified core margin.

Support files: `validate_fast_shift.py` (integer synthetic-shift pipeline
validated sign-exact against coefficient_box_two_stage),
`prove_jb_separated_transfer_fast.py` and
`prove_jb_separated_transfer_flint.py` (earlier accelerations of the original
pipeline, superseded by the w-frame reformulation).



## Block decomposition results (Claude Fable 5, continued)

`prove_jb_blocks_wframe.py`: the full correlated-error comparison expands at
the abstract level into 531 exact epsilon-monomial blocks (3246 pieces,
1.9 s), each a small polynomial over the six-element factor base; the tiny
constants (ERROR ~ 2^-99, LAMBDA_J) stay outside the polynomial arithmetic.
Exact end-to-end validation at random rational points including random error
values. Certification runs on pure-Python integer kernels (validated
scale/shear/shift).

Results:
- LEFT separated box (d1 >= (w0+3) 2^-34, d2 >= 0 free): PASSES with zero
  negative residuals over 38103 geometry monomials, with the full correlated
  error model, both with and without the transfer target.
- RIGHT box: 1269 negative residuals, all on its d1=0 face, identically with
  and without the target. Diagnosis: every offending block contains eB. The
  independent eB relaxation breaks the first Peano cancellation
  c0*qbar + c1*qbar' + c2*qbar'' = 0: the true tail satisfies
  B_t = int q_t and (qm-qx)_t = int q_t' with the SAME q_t, so the true
  numerator vanishes to second order in d1 at the face while the
  independent-eB model only vanishes to first order. This is exactly the
  "integrated left/right differences" correlation named in the P000041
  transcript but not present in the coded error model.

Consequences:
- The left-box theorem plus the collision cone cover everything except the
  strip {0 < d1 < (w0+3) 2^-34, d2 >= (w1+3) 2^-34}.
- On the strip the sound model is the mean-value form
  B = B1 + d1 (16 E2/(w0+3)^4) ec0 + (d1^2/2) env eB,
  qm - qx = (clean) + d1 px_t(x0)/(2(w0+3)) tied to ec1 + (d1^2/2) env eL0,
  pm - px analogously via ec2, right differences unchanged; the independent
  endpoint errors are then second order in d1 and the face heals
  structurally. Envelope constants follow from the audited ERROR table with
  the d/dw = D/(2(w+3)) conversion. The bounded strip enters the polynomial
  certificate through the Moebius substitution d1 = (w0+3) 2^-34 tau/(1+tau).

Status: left box certified (raw); right box reduced to the mean-value strip
lemma above. The join (`join_positive_tail.py`) is verified: cone + left box
+ strip = the full positive-tail complement.
