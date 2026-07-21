# Rejected routes

- A constant scaled tail box loses exponential decay and cannot compare with
  scaled margins at infinity.
- Treating the exact second theta mode as part of the outer error gives overly
  coarse `F2` and `C4` budgets.  Keeping two modes exact is necessary for this
  proof architecture.
- Arbitrary constant boxes in `y=exp(-3*x)` fail on the unbounded `q` and
  `C4` numerator polynomials.  Their negative corrections must be controlled
  by the proved decreasing exponential ratios.
