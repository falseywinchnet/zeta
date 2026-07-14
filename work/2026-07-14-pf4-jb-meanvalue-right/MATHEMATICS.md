# The mean-value tail model and the strip certificate

## Two abstract identities (verified symbolically this round)

For the 74-term cleared J_b numerator `num` with left collision ideal
`I = (B, qm-qx, pm-px)`:

1. `num` has ideal degree exactly ONE in `I` (min total degree 1 after the
   substitution `qm = qx+dq, pm = px+dp`). Hence any error model that grants
   the three left coordinates independent first-order-in-`d1` errors can
   never certify the `d1=0` face: P000042's failure was necessary.
2. The first Peano cancellation: with `c0 = d num/dB`, `c1 = d num/d(dq)`,
   `c2 = d num/d(dp)` evaluated on the collision manifold,

   c0 qx + c1 px + c2 ux = 0     identically.

## The model

In `w = 2z-3`, `-ds/dw = q/(2(w+3))`, `dq/dw = px/(2(w+3))`,
`dpx/dw = ux/(2(w+3))` — consecutive D-jets over `2(w+3)`. Writing `tau_k`
for the theta-tail of the k-th D-jet with the audited pointwise envelope
`|tau_k(w)| <= 16 E_{k+2}/(w+3)^4` (w >= 43, CERT6/7 ERROR table):

- `B = int_{w0}^{w1} q_full/(2(w+3)) dw`, so with `g = tau0/(2(w+3))`,
  `g' = tau1/(4(w+3)^2) - tau0/(2(w+3)^2)`:

  B_tail = d1 tau0(w0)/(2(w0+3)) + R_B,
  |R_B| <= (d1^2/2)(4E3+8E2)/(w0+3)^6.

- `(qm-qx)_tail = d1 tau1(w0)/(2(w0+3)) + R_q`,
  `|R_q| <= (d1^2/2)(4E4+8E3)/(w0+3)^6`; `(pm-px)_tail` analogously via
  `tau2` and `(4E5+8E4)`.

- `tau_k(w0)` are the SAME quantities as the x-jet errors, so the `d1`-linear
  parts of `(B, qm-qx, pm-px)` are exactly
  `d1 (qx, px, ux)_model /(2(w0+3))` including the error parametrization
  (shared symbols ec0, ec1, ec2). By identity 2 the `d1`-linear part of the
  cleared numerator vanishes for EVERY error assignment: `d1^2` divides every
  block. Confirmed computationally: common face factors `d1^2 d2`.

- Right increments integrate to exactly the P000041 right-decay envelope:
  `int_{w1}^{w2} 16E/(2(w+3)^5) dw = 2 E rdec` (sympy cross-check in the
  prover), so the r-point and C pieces keep the audited form, with the qm/qr
  and pm/pr tail pieces shared identically.

## Certificate

Blocks (7171 pieces, 617 error-monomial blocks, exact end-to-end validation
against a direct sympy substitution of the same model). Error blocks are
collapsed into 423 lcd-class absolute envelopes before shifting (sound:
coefficientwise `|N C| <= |N| C` for positive cofactors, and all shift
weights are nonnegative; the 2^-99 error scale absorbs the conservatism).

Domain: `w0 = 43 + a`; `d2 >= (w0+3) 2^-34` by the integer shear (a weakening
of the true floor `(w1+3) 2^-34`, hence a superset); and the strip
`0 <= d1 < (w0+3) 2^-34` entered by the Moebius substitution
`d1 = (w0+3) 2^-34 t/(1+t)`, cleared by the single positive function
`2^{34 D}(1+t)^D` with the global degree `D = 35`.

Result: 53001 geometry monomials, zero negative residuals, face included.

The large-`d1` complement is not needed: the P000042 left box certificate
(`d1 >= (w0+3) 2^-34`, all `d2 >= 0`) covers it, seam closed on the left-box
side. The quadratic remainder of the mean-value model grows like `d1^2`, and
without the strip bound it genuinely overruns the clean part at the top
`d1`-degrees (the first strip-free attempt failed at `d1`-degree 35 exactly
as expected); the two models are complementary by design.

## Join: the positive-tail three-point obligation

With `a = U-1`, `c = V-1`, `rho = UV-1 = a+c+ac`:

- `rho <= 2 eps0`: collision cone, P000041.
- `a >= 2^-34`: left box, P000042.
- `a < 2^-34` and `c >= 2^-34`: this strip (`d1 = 2X a < (w0+3) 2^-34` when
  `a < 2^-34` since `2X = w0+3`; `d2 = 2UX c >= (w1+3) 2^-34`).
- Cover: `rho >= 2^-32 > 2 (2^-34) + 2^-68` forces `a >= 2^-34` or
  `c >= 2^-34`, and `2 eps0 > 2^-32` (P000042's join lemma).

Hence `J_b >= 0` on the whole positive tail (`X >= 23`): the R161 branch is
closed. With `S_r > 0` (R160), both densities of the one-sided Peano
reduction are settled on the positive tail.
