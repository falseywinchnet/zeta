# Next boundary

The remaining analytic PF4 boundary is now exactly the following three Lean
propositions for every `t >= 0`:

```text
0 < clearedQ  (normalizedThetaSeriesJet 0 t) ...
0 < clearedF2 (normalizedThetaSeriesJet 0 t) ...
0 < clearedC4 (normalizedThetaSeriesJet 0 t) ...
```

These match CERT12's first-mode normalization. The checked common-scaling
theorems remove the positive first-mode factor exactly, and the checked parity
theorems transport the result globally.

## Required formal decoding

CERT12 currently verifies the following finite and analytic ingredients in
Python/SymPy:

1. the recurrence polynomials `P_0,...,P_6`;
2. exact rational bounds for pi and exponential tails;
3. 361 positive rational Bernstein coefficients for the two-mode margins;
4. shifted-coefficient positivity and geometric tail bounds for modes `n>=3`;
5. exact perturbation bounds below the `q`, `F2`, and `C4` margins.

A sound Lean continuation must either formalize those inequalities or define a
small, explicit certificate format whose rational polynomial and bound data
Lean checks. A successful process exit or the name `CERT12` is not itself a
proof term.

The preferable next theorem interface is a structure-free triple of the
literal normalized inequalities above. Feeding them to
`terminalQuotD_kernelJet_pos_of_nonneg_normalizedClearedSigns` then closes the
actual terminal cascade directly.
