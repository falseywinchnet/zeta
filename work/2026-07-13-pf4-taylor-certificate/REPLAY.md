# Replay

Use the repository Arb environment:

```sh
$HOME/miniforge3/bin/python3 certify_compact_jets.py
$HOME/miniforge3/bin/python3 certify_tm_cells.py
$HOME/miniforge3/bin/python3 verify_boundary_modules.py
$HOME/miniforge3/bin/python3 audit_compactification.py
$HOME/miniforge3/bin/python3 -m py_compile *.py
```

Expected terminal statuses are respectively `PASS`, four `PASS` cells, five
boundary `PASS` lines, and `COMPACTIFICATION_NOT_YET_PROVED`.  The final status
is an audited open premise, not a verifier failure.

Environment used:

```text
Python 3.13.13
python-flint 0.9.0
SymPy 1.14.0
```
