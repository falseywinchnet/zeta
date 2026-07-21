# Next boundary: range-local final assembly

The curvature-coordinate construction now supplies the complete derivative
jet and the `q`, `F₂`, and determinant `C₄` signs on

```text
range (kernelCoordinate S).
```

It intentionally makes no derivative or determinant claim about the arbitrary
values of `Function.invFun` outside that range.

The maintained theorem
`PF4.FinalAssembly.coordinatePartialXiPsi_neg_from_determinantC4` currently
asks for global derivative and positivity inputs on all `ℝ`. Its proof only
uses the coordinate interval from `p` to `w`. The next advancement should:

1. prove that for original ordered points `x<m<r`, the whole coordinate
   interval `Icc (y x) (y r)` lies in `range y`;
2. formulate a range- or interval-local version of the final coordinate
   assembly, replacing global derivatives/continuity/signs by the precise
   local hypotheses consumed by the transport integral;
3. instantiate those local hypotheses with `coordinateJet_on_range` and
   `coordinateSigns_on_range`;
4. retain the actual-kernel derivative tower `q₁,...,q₄` and the CERT12
   `q/F₂/C₄` statements as explicit certificate-to-Lean boundaries until they
   are constructed;
5. do not make a smooth arbitrary extension outside `range y`, and do not
   assume `range y = ℝ` without separately proving endpoint behavior.

After that localization, the coordinate inverse and determinant realization
will plug into the terminal quotient theorem without its current global
extension mismatch.
