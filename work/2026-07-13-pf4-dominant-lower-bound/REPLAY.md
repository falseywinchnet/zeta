# Replay

```sh
$HOME/miniforge3/bin/python3 prove_explicit_lower_bounds.py
$HOME/miniforge3/bin/python3 -m py_compile *.py
```

Environment:

```text
Python 3.13.13
SymPy 1.14.0
```

The verifier reconstructs the generic rational densities from P000032 and the
exact dominant-theta formulas from P000033.  It computes the coefficientwise
optimal rational constants, checks them against the recorded values, and
requires every shifted coefficient to be nonnegative.
