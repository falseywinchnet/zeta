# Sources and recovered follow-up

## Supplied manuscript, now historical only

- CITE2: `papers/The Riemann Kernel is Not a Polya Frequency Function of
  Infinite Order.pdf`
- SHA-256:
  `0472706dbbf3c74d4ac195e58786ea5683a21dccbbcafef572aa7bb6e1a304ca`
- Candidate decimal vectors are printed in Section 3.1. They are not premises
  of the retained proof.

## Lossless ChatGPT follow-up

The follow-up computation is preserved in
`sources/chatgpt-jacobian-conjecture-epistemics.txt`.

- Lines 12120--12430: 100 order-three and 25 order-four subminors of the
  displayed witness were reported positive; the order-five determinant was
  reported negative. The same response introduced Vandermonde division.
- Lines 12515--12724: parity-block diagnosis of the origin-confluent order-five
  obstruction.
- Lines 12730--13199: proposed three-mode derivative proof and tail bounds.

The follow-up is raw source evidence, not a theorem. It supplied the parity
factorization and suggested the origin route. Its polynomial recurrence
uses the combined normalization

`T_n(u)=exp(u/2) P_0(pi n^2 exp(2u))`,

differentiation gives exactly

`P_{j+1}=2x P_j' + (1/2-2x)P_j`.

The equivalent split normalization keeps the factor `2*pi*n^2` outside and
starts from `2x-3`; that version has `(5/2-2x)`. The first verifier attempt
mixed these normalizations and was rejected by the parity signs. The retained
verifier uses the combined normalization and independently recomputes every
interval.

The retained verifier independently regenerates the polynomials and derives
every interval from rational inequalities. The chat values are used only as a
cross-check and discovery trace.

## Prior advancement artifact, not a premise

`work/2026-07-13-pf4-vandermonde-certificate/audit_supplied_witness.py`
already evaluates the displayed decimals with Arb and a theta-tail enclosure.
It is an independent precursor. The retained proof does not import it, use its
decimal witness, or require its Flint backend.
