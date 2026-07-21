# Results

## Closed infinite-tail theorem

`RelativeTailRefactor.lean` compiles without `sorry`, `admit`, a custom axiom,
or a finite mode cutoff.  It proves, for every `t>=0` and `j<=6`:

- `modeX k t >= 27` for every original theta index `k>=2`;
- `(-1)^j * certPoly j s > 0` on the entire half-line `s>=27`;
- the complete `n>=4` `tsum` has the alternating weak sign;
- the complete `n>=3` tail has the alternating strict sign;
- consecutive `n>=4` polynomial-exponential majorants contract by less than
  `10^-9`;
- the actual `n>=4` tail norm is less than `1/1000` of the exact `n=3` mode;
- the literal normalized theta-series jet is exactly its first two modes plus
  its third mode multiplied by `1+delta`, where
  `0 <= delta < 1/1000`.

The last statement is
`normalizedSeriesJet_eq_first_three_relative`.  It consumes the maintained
literal `thetaSeriesJet` `tsum`; it does not restate a tail estimate as a
premise.

## Why this is exhaustive

The proof quantifies over every natural mode index and every real `t>=0`.
The infinite remainder is bounded by a proved geometric series.  The
polynomial sign and envelope lemmas quantify over complete real half-lines.
The two exponential constants are obtained from finite Taylor lower sums,
whose relationship to `Real.exp` is a mathlib theorem.  No point mesh or
maximum observed over a range occurs.

## Theorem refactor

The former boundary required seven unrelated absolute tail constants.  The
new boundary has no infinite series:

```text
for all x >= pi and all delta_0,...,delta_6 in [0,1/1000),
  let jet_j = mode1_j(x) + mode2_j(x) + mode3_j(x)*(1+delta_j)
  then clearedQ(jet)>0, clearedF2(jet)>0, clearedC4(jet)>0.
```

This finite robust theorem is sufficient because Lean now constructs the
required `delta_j` from the actual infinite theta series.

## Independent design replay

`verify_relative_tail_design.py` checks the same half-line polynomial
envelopes and exact rational constants independently with exact SymPy
algebra.  It is corroborating advancement evidence; the Lean theorem is the
formal result.
