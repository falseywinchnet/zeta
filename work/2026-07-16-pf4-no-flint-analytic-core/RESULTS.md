# Results

## Main advance

A no-FLINT, sweep-free candidate proof now establishes the three global sign
inputs used by the PF4 paper:

- `q>0`;
- `F2=q^3-(q q''-(q')^2)>0`;
- `C4>0`.

The proof keeps two theta modes exactly and treats all `n>=3` modes as one
analytic perturbation. It covers the whole half-line `x=pi exp(2u)>=pi`; the
old split at `u=1` is unnecessary.

## Replay

`verify_no_flint_compact.py` reconstructs all formulas and checks:

- rational Machin and exponential bounds;
- the central-moment determinant identity for `C4`;
- raw-derivative/cumulant clearing identities;
- 361 exact Bernstein or decreasing-correction coefficients;
- 140 exact derivative-envelope coefficients;
- core and outer theta-tail perturbation bounds.

Measured replay time is about eight seconds on the development machine. It
imports SymPy but does not import or call python-flint/Arb.

## Proof status

This is a successful advancement candidate. It does not modify CERT2, CERT3,
MIND claims, or the maintained paper. A refine round must adversarially audit
the analytic majorants and coefficient transformations before promotion.
