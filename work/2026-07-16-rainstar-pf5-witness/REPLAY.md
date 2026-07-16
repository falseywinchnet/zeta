# Replay

Run from the repository root:

```sh
python3 work/2026-07-16-rainstar-pf5-witness/verify_origin_pf5.py
python3 -m py_compile work/2026-07-16-rainstar-pf5-witness/verify_origin_pf5.py
```

The verifier uses only the Python standard library. Its proof arithmetic is
integer arithmetic on a fixed rational grid with outward rounding. No binary
floating point, Flint, Arb, NumPy, mpmath, or symbolic algebra package is
loaded. On the development machine the complete sign certificate runs in
about 0.05 seconds.

`certificate-output.txt` preserves the successful output. The displayed
eighteen-place endpoints are shortened views of thirty-six-place rational
grid endpoints; all decisions use the full stored integers.

SHA-256 at round completion:

```text
e5fced0ba1581ea50038b1bd5f4388676cae9939bf98ab3b3e0d5ddae7edf8b1
  verify_origin_pf5.py
f0d5fa4efc130eabb2b231314a84aec39f16bfc524f8fb2425640f34f86e9300
  candidate-main.pdf
```
