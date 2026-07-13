# Forward path

## Kernel geometry

For tested `0<omega<1/2`, the explicit kernel `G_omega` has:

- a negative singular region near zero;
- one zero in `(0,1)`;
- one positive lobe;
- value zero at one;
- the exact weighted cancellation (3).

Because every `c_omega(n)` is positive, (1) asks whether the positive high-index
lobe always dominates the negative low-index region after arithmetic weighting.
This is a deterministic inequality.

## Candidate mechanism: arithmetic pairing

Let `rho_omega` be the zero of `G_omega`. Split

`xH_omega(x)=N_omega(x)+P_omega(x)`,

`N_omega=sum_{n<rho_omega x}c_omega(n)G_omega(n/x)<0`,

`P_omega=sum_{rho_omega x<n<=x}c_omega(n)G_omega(n/x)>0`.

The direct target is

`P_omega(x)>=-N_omega(x)`                               (5)

for all sufficiently large `x`, uniformly for `omega` on compact subsets of
`(0,1/2)`.

A valid proof of (5) may use:

1. an explicit injection or weighted allocation from low indices to high
   indices, using the multiplicative formula for `c_omega`;
2. one-sided bounds for `C_omega(t)` inserted into the exact discrepancy
   transform (4);
3. a positive factorization of the combined discrete kernel, not of its
   continuous main term.

## First analytic gates

1. Prove the one-zero/one-lobe structure of `G_omega` for
   `0<omega<1/2` from the incomplete-beta formula.
2. Derive upper and lower envelopes for `G_omega` on the two sign intervals.
3. Convert those envelopes into explicit finite-interval inequalities for
   `C_omega(t)` sufficient for (5).
4. Test whether known elementary bounds for generalized Jordan totients meet
   those inequalities. If not, identify the exact missing one-sided discrepancy
   estimate.

This path reaches the complete arithmetic sum. It succeeds only with a
deterministic sign theorem uniform in `x` and `omega`.
