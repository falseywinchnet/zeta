# Next advancement cycle — terminal quotient and coordinate Psi

Mode: advancement

Starting evidence: P000111–P000112 and their maintained refine integration in
`PF4.TranslationQuotientSigns`.

## Maintained boundary

For ordered columns `a<c<b<d`, the proof system now contains:

```text
firstQuotD > 0
```

from positive exact kernel curvature, and

```text
secondQuotD > 0
```

from the exact S05 `lowerLambda>0` premise. These are conversion theorems, not
yet actual Riemann-kernel instances: the formal bridges for certified `q>0`
and `Lambda>0` remain explicit upstream work.

The sole new algebraic advancement boundary is the third sign:

```text
terminalQuotD Φ Φ1 Φ2 Φ3 a c b d > 0.
```

## Required exact bridges

1. Record the moving-point order
   `p_d=t-d < p_b=t-b < p_c=t-c < p_a=t-a` from strict column order.
2. Identify the maintained `secondQuot`/`secondQuotD` objects with the paper's
   `w_j` level using the checked lower quotient identities.
3. Prove positivity of `terminalQuot` from the two required
   `secondQuotD>0` instances; every denominator must use that strict sign.
4. Derive the exact logarithmic translation rate of `terminalQuot` and reduce
   it to

   ```text
   Psi(p_d;p_c,p_a) - Psi(p_b;p_c,p_a).
   ```

5. Prove that this `Psi` is the same endpoint object as
   `PF4.CoordinateSignBridge.coordinatePsi`, under an explicit coordinate map.
   Matching notation or an algebraically similar fresh definition is not an
   instance bridge.
6. Use `p_d<p_b` and strict decrease of that same coordinate `Psi` to obtain a
   positive difference, then combine it with positive `terminalQuot`.
7. State the strongest wrapper available. If `q>0`, `Lambda>0`, or coordinate
   `Psi` strict decrease still enters as a premise, name it literally and stop
   before claiming an unconditional actual-kernel theorem or completing
   PO-0042.

## No-cheating gates

- Do not assume `terminalQuotD>0`, an order-four Wronskian/minor sign, a finite
  difference sign, or a renamed version of the target rate.
- Do not replace `PF4.CoordinateSignBridge.coordinatePsi` with a detached
  three-point object without proving equality.
- Do not call `coordinatePartialXiPsi_neg_from_determinantC4` an actual
  Riemann-kernel theorem until its kernel, jet, curvature, and determinant-sign
  inputs are instantiated.
- Preserve strict orientation: `p_d<p_b` and decreasing `Psi` imply
  `Psi(p_d)>Psi(p_b)`.
- Keep Lean compilations serialized and prefer derivative uniqueness over
  expansion of nested rational quotients.

## Intended result

An exact maintained terminal quotient/coordinate-`Psi` conversion theorem,
with every remaining analytic or certificate instance premise exposed.
