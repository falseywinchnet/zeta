# Results

## Lean-checked foundations

The round produced compiling Lean files for:

1. universal Bernstein positivity on a closed box and on a half-strip;
2. exact rational Taylor bounds for the exponential constants used by CERT12;
3. exact first-two-mode numerator identities and the original finite margins;
4. deterministic polynomial perturbation bounds;
5. the literal decomposition of each normalized theta jet through order six
   into its first two modes plus the modes-three-and-higher `tsum`.

These files contain no `sorry`, `admit`, custom axiom, or sampled mesh.

## Smaller two-mode certificate

The exact exploratory checker `verify_compact_two_mode.py` proves that the
large two-dimensional Bernstein core is unnecessary.  Its output is:

```text
q   negative terms: 1; endpoint ratio 5181608243/60293850000 < 1
F2  one-dimensional Bernstein coefficients: 24
C4  one-dimensional Bernstein coefficients: 14;
    negative terms: 2;
    endpoint ratio
      966521566009613180835081589
      / 1881697649519115066406250000 < 1
```

The mechanism is exhaustive.  Bernstein coefficients establish all real
points of a closed interval; shifted nonnegative power coefficients establish
an entire half-line; decreasing exponential ratios prevent a later sign
reversal.  No finite collection of evaluation points is used.

## Exact remaining boundary

This round does **not** prove the three full theta-series inequalities in Lean.
`ThetaTailReduction.lean` identifies the exact infinite tail, and the generic
perturbation theorem says which coordinate bounds suffice, but the numerical
bounds on that `tsum` are not yet Lean theorems.  Consequently the global
counterexample-excluding theorem

```text
forall t : Real,
  clearedQ > 0 and clearedF2 > 0 and clearedC4 > 0
```

has not been obtained and must not be reported as proved.

## Architectural conclusion

The enormous generated algebra is not the conceptual core.  The compact proof
should consist of:

1. 38 one-variable Bernstein coefficients for the first two modes;
2. three decreasing-ratio arguments;
3. one uniform analytic majorant for the literal theta tail through jet six;
4. the already checked perturbation and global jet/parity bridges.

The third item is now the proof boundary.
