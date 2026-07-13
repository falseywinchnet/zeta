# Replay

The successful certificate fragments were replayed with:

```sh
$HOME/miniforge3/bin/python3 audit_supplied_witness.py
$HOME/miniforge3/bin/python3 verify_blowup_identity.py
$HOME/miniforge3/bin/python3 certify_jhat_cells.py
$HOME/miniforge3/bin/python3 -m py_compile *.py
```

The preserved negative experiments are replayed with:

```sh
$HOME/miniforge3/bin/python3 certify_jhat_rectangle.py
$HOME/miniforge3/bin/python3 certify_jhat_divided.py
```

Replay environment:

```text
Python 3.13.13
python-flint 0.9.0
SymPy 1.14.0
```

Inputs outside this directory:

```text
0472706dbbf3c74d4ac195e58786ea5683a21dccbbcafef572aa7bb6e1a304ca
  papers/The Riemann Kernel is Not a Polya Frequency Function of Infinite Order.pdf
dd05713c68334a888235e78be8dd5736615f7d41cd8b4a80c78f3a000d1a1050
  work/2026-07-13-riemann-kernel-pf4-verification/jet.py
```

`audit_supplied_witness.py` imports the established theta-jet and tail-bound
implementation from the second input.  A later refine round should package the
audit as a standalone CERT record before promoting its claim.
