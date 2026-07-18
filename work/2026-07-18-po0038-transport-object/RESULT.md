# Result

PO-0038 has a complete Lean candidate in `TransportObject.lean`.

The proof defines independently:

- the paper primitive `paperPrimitive` (`A₀`);
- the elementary primitives `transportH` and `transportJ`;
- the expectation endpoint expression;
- `chordSlope`, `chordMoment`, and the paper's expanded transport object
  `expandedTransportK`.

It then proves:

1. `J' = H`;
2. `H' = κ A₀` under the paper's jet identities;
3. the increasing and decreasing triangular weighted FTC formulas;
4. the actual `nuMeasure`/`muMeasure` Bochner expectation difference equals
   the retained-boundary endpoint expression;
5. Appendix A3's cleared-denominator endpoint identity;
6. `expandedTransportK = Eν[A₀] - Eμ[A₀]`.

The final theorem is not tautological: `expandedTransportK` mentions no
measure or expectation, while the right side uses the previously constructed
measures and `measureExpectation`.

## Audit

The standalone Lean replay exits zero. Each exported candidate theorem depends
only on:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, custom axiom, unsafe bridge, symbolic certificate
assumption, or numerical sign decision in the candidate.

## Remaining edge

A refine round must audit naming and module placement, integrate the candidate
under `proof/formal/PF4/`, extend the formal axiom ledger, and decide whether
the generic smoothness/jet hypotheses exactly match the atomic PO-0038 closure
policy. The submitted paper remains unchanged.
