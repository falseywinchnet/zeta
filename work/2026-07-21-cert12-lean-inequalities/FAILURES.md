# Failed or superseded approaches

## Large tensor-product core

`CERT12FiniteMargins.lean` compiles and gives universal, not sampled,
positivity on its stated boxes.  Nevertheless its 361 rational coefficients
obscure the proof and still require separate outer-range and theta-tail
arguments.  It is retained as raw evidence but superseded as the intended
architecture by `verify_compact_two_mode.py`.

## Premature global claim

The finite two-mode margins and generic perturbation budgets do not by
themselves exclude a counterexample in the full theta series.  Until the
literal `normalizedTailJet` bounds are Lean theorems, the three final sign
premises remain open.
