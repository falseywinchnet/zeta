# Results

The failed monolithic replay has been replaced at its earliest dependency by
three maintained modules with a narrow import graph:

1. `PF4.CERT12TailPolynomial` proves exact alternating signs, polynomial
   envelopes, endpoint monotonicity, and the rational relative-tail
   coefficient inequality for every derivative order through six and every
   real point on the required half-lines.
2. `PF4.CERT12TailExponential` proves the exact exponential endpoint bound,
   continuous polynomial-times-exponential decay on `[3,∞)`, and a uniform
   contraction ratio below `10^-9` for every natural tail mode `n>=4`.
3. `PF4.CERT12GeometricTsum` converts pointwise geometric bounds over every
   natural index into a norm bound on the actual `tsum`, together with its
   strict relative form and the same-sign `tsum` lemma.

`lake build PF4.CERT12GeometricTsum` completed successfully.  Every exported
theorem's axiom print contains only mathlib's standard `propext`,
`Classical.choice`, and `Quot.sound`; none contains `sorryAx`.

The Taylor calculations are not sampled numerics.  Lean checks exact rational
finite sums, and `Real.sum_le_exp_of_nonneg` transports them to inequalities
about the exact real exponential.  The contraction and `tsum` theorems quantify
over all natural indices.

This epoch does not yet restore the previously claimed literal series theorem.
The next seam must identify the maintained theta-mode formula with these
majorants, prove summability, and compose the geometric result with the literal
`thetaSeriesJet`.
