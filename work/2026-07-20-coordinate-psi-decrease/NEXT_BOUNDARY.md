# Next boundary after integration

Combining this round with P000115 removes the terminal `coordinatePsi`
monotonicity premise. The remaining instance edges are:

1. construct the curvature-coordinate function `Q` from the kernel coordinate
   `y=-logSlope`, preferably through a global inverse or an explicit
   range-restricted equivalence;
2. prove the realization identities `Q(y(u))=q(u)` and
   `Q'(y(u))=q'(u)/q(u)` rather than carrying them as premises;
3. connect the coordinate jet `Q,Q1,…,Q4` and its determinant function to the
   kernel jet and the certified `C4>0` input;
4. formalize or import the certified actual-kernel `q>0` and lower-`Lambda>0`
   analytic instances.

Do not define an arbitrary extension of `Q` outside the range of `y` unless
the derivative and determinant theorems are explicitly restricted to that
range; otherwise the global coordinate hypotheses would be unjustified.
