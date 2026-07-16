# Rainstar PF5 witness hardening

- Mode: advancement
- Date: 2026-07-16
- Model: OpenAI Codex
- Question: Can the Riemann kernel's failure of PF5 be proved directly from a
  negative origin-confluent determinant, with a small exact-rational
  certificate and without CITE4 or an external interval library?
- Starting MIND IDs: R4, R11, R13, R14, R16, R37, R145, R164, CITE2,
  CITE4, CERT2, CERT3, CERT5, CERT9
- Status: mathematics and candidate manuscript complete; MIND integration and
  maintained-paper replacement are reserved for the next refine round

## Rules for this round

- The old decimal witness is historical input, not a premise of the new proof.
- The certificate uses only exact rational arithmetic from the Python standard
  library. Transcendental quantities enter through proved rational bounds.
- The retained theta sum and its infinite tail are both enclosed.
- No MIND establishment or paper integration occurs in this advancement round.

## Result

The origin derivative Hankel matrices split by parity. A standard-library-only
exact-rational certificate retaining three theta modes proves

```text
445 < A < 446
189223 < B < 189228
-674000000 < C < -614000000
```

and hence `H4(0)=A*B>0` while `H5(0)=C*B<0`. The confluent divided-difference
limit transfers the negative order-five sign to the distinct equally spaced
nodes `x_i=y_i=i*h` for every sufficiently small positive `h`. This proves
failure of PF5 without CITE4 and without the decimal witness of CITE2.

The candidate manuscript compiles to `candidate-main.pdf` with the replacement
proof and no occurrence of the removed author or citation. The maintained
paper, citation graph, and certificate registry remain unchanged in accordance
with advancement mode.
