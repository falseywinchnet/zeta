# Coordinate sign-bridge object identity

- Date: 2026-07-18
- Mode: advancement
- Model: OpenAI Codex (Sydney)
- Starting MIND references: R101, R111, R112, R113, R137, R138, R153, R83, R94
- Starting progress: P000099
- Target obligations: PO-0026 and PO-0027, then PO-0041
- Status: complete candidate preserved at P000100; PO-0041 reduced to one exact identity

## Question

Can the displayed identity

\[
\partial_\xi\Psi=-Q(p)\mathcal N/\Lambda^2
\]

be proved from independently defined coordinate objects, without assuming the
identity, its numerator, or mixed-derivative commutation as a scalar premise?

## Boundary

Define the simultaneous-translation terms from endpoint chords and jets.
Define `Psi` independently as `Lambda + T Lambda / Lambda`. Differentiate the
actual closed expression with respect to the left coordinate, then apply the
coordinate speed `Q(p)`. The numerator must subsequently be identified with
the already checked deterministic transport numerator; positivity is not an
input to the object identity.

## Source anchors

- `paper/manuscript/sections/S06-curvature-coordinate.tex`, equations
  `Lambda-coordinate`, `N-def`, and `sign-bridge`.
- `work/2026-07-14-pf4-compact-bridge/CURVATURE_COORDINATE.md`, equations
  (4)--(8), for independently derived endpoint forms.
- `PF4.TransportObject.expandedTransportK` and
  `PF4.Transport.coordinateTransportNumerator_pos_closed`.

## Result

`CoordinateSignBridge.lean` compiles the following non-vacuous chain:

1. exact endpoint definitions of `T Lambda`, `T delta`, the coordinate
   numerator, and `Psi`;
2. direct differentiation of the left chord moment;
3. direct differentiation of `T Lambda` and `Psi`;
4. the exact PO-0027 identity after multiplying by the coordinate speed;
5. exact equality `N = delta Lambda expandedTransportK`;
6. strict negativity from a positive coordinate numerator;
7. a PO-0041 assembly theorem whose sole unresolved premise is the exact
   equality of `expandedTransportK` with the deterministic transport integral.

The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry`, `admit`, detached positive numerator, or assumed sign.

## Next boundary

Prove the named central identity by joining the independently checked
`expandedTransportK` expectation identity, compact-support integration by
parts, the `paperPrimitive` derivative/curvature-weight identity, and the
pointwise CDF-to-coordinate-gap bridge. That will remove the last premise from
the PO-0041 assembly theorem.
