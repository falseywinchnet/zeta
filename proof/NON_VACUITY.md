# Non-vacuity audit

Status: first target-reachable pass

## NV-001 — ordered node domains

T1 quantifies over strictly increasing tuples for `1 ≤ k ≤ 4`. These domains
are inhabited: `x_i = i` and `y_i = 2i` give concrete examples after the index
coercion is fixed. This witness prevents the theorem from succeeding through
an empty ordered-node subtype.

Open: formalize the witness for the chosen Lean representation.

## NV-002 — kernel existence before positivity

`Φ` must be constructed from a convergent series or an already constructed
analytic function. Its existence, differentiability, and equality to the
positive-side series precede `Φ > 0`. Defining `Φ` as a positive function would
launder the central instance property.

Open: PO-0002 through PO-0007.

## NV-003 — logarithmic derivatives

`ℓ = log Φ`, `s = ℓ'`, and `q = -ℓ''` are used only after global `Φ > 0`.
Every quotient involving `q`, `A`, `Λ`, `δ`, or `κ` has a separate nonzero or
positive-denominator obligation.

Open: PO-0008, PO-0010, PO-0015, PO-0022, PO-0028.

## NV-004 — curvature coordinate

The coordinate `y(t) = -s(t)` is strictly increasing because `dy/dt = q > 0`.
Only its image is needed. No surjectivity onto all real numbers may be assumed.
For `ξ < m < r`, strict monotonicity constructs `p < z < w`, hence `L,R > 0`.

Open: formal inverse-on-image and derivative transport lemmas.

## NV-005 — triangular integrals

The formulas

\[
\Lambda=\frac1L\int_p^z(t-p)\kappa(t)dt+
\frac1R\int_z^w(w-t)\kappa(t)dt
\]

and

\[
\delta=\frac1{L^2}\int_p^z(z-t)\kappa(t)dt
\]

derive positivity because `L,R > 0`, `κ > 1`, and both intervals have positive
length. Positivity is not attached to fresh symbols `Λ` or `δ`.

Open: PO-0023 through PO-0025.

## NV-006 — probability measures

`μ` and `ν` become probability measures only after proving:

- their densities are measurable and nonnegative;
- their denominators are positive;
- the integral of the `μ` density is one by the definition of `δ`;
- the integral of both pieces of the `ν` density is one by the triangular
  formula for `Λ`;
- their support intervals are nonempty.

Until then, expectation and CDF notation is syntactic shorthand only.

Open: PO-0030 and PO-0031.

## NV-007 — strict right mass

The statement `ν((z,w]) > 0` must be derived from the second density

\[
\frac{(w-t)\kappa(t)}{R\Lambda}
\]

which is strictly positive for `z < t < w`, together with `z < w`. It must not
be represented by `Wz : ℝ` carrying an assumed `Wz > 0` proof.

Open: PO-0032.

## NV-008 — density ratio

On `p < t < z`, both densities are positive and their ratio simplifies to

\[
\frac{\Lambda(z-t)}{L\delta(t-p)}.
\]

The derivative identity is useful only after proving `L,δ,Λ,t-p > 0` and
proving that this expression is the ratio of the actual densities. Endpoint
limits then provide values above and below one, so the intermediate-value and
strict-monotonicity arguments produce a real, unique crossing.

Open: PO-0033 through PO-0036.

## NV-009 — CDF gap sign

The CDF difference starts at zero, increases before the crossing, and decreases
after it. This alone does not exclude a return to zero before `z`; the strict
right mass gives `Δ(z) > 0`. Monotonic decrease from a positive endpoint value
then keeps `Δ` positive on the post-crossing segment. The left segment is
positive because it rises from zero. On `(z,w)`, positive remaining `ν` mass
gives `Δ > 0` directly.

Closed: `PF4.Cumulative.coordinateGap_pos` derives the normalizers and mass
identities, proves the positive pre-crossing integral, and rewrites the
post-crossing gap using a concrete positive right-tail integral. No endpoint
gap or tail mass is assumed.

## NV-010 — positive transport integral

Strict positivity requires more than nonnegative factors. The interval
`(p,w)` is nonempty, `Δ > 0` there, and `D > 0` there, so the continuous
integrand is positive on a nonempty open set. This discharges the equality
case.

Closed: `PF4.Transport.coordinateTransportNumerator_pos_closed` derives the
closed-gap sign and continuity and supplies an explicit midpoint witness for
the positive weighted integrand. No positive integral is passed as a premise.

## NV-011 — finite PF5 witness

The index expression `(i-j)` must use signed integers. The spacing `211/2000`
is strictly positive, so row and column nodes are distinct and ordered. The
certificate must reconstruct the same `Φ` as T0 and must prove a rational
upper bound below zero.

Open: PO-0044 and PO-0045.

## NV-012 — transport object identity

The paper primitive `A₀`, the concrete measure integrals, and expanded `K` are
separate definitions. In particular, `expandedTransportK` contains only
endpoint jets, chord slopes, chord moments, gaps, and normalizers; it does not
mention a measure, integral, expectation, or the equality to be proved. The
expectation side uses the previously constructed `muMeasure`, `nuMeasure`, and
`measureExpectation` objects. Appendix A3's `δ` and `Λ` endpoint formulas are
explicit hypotheses, and every cleared denominator has a proved positivity
hypothesis.

Checked: `PF4.TransportObject.expandedTransportK_eq_concrete_expectationDifference`.
The upstream derivation that makes the measures probabilities remains isolated
in PO-0023/0024 and PO-0030/0031; it is not smuggled into PO-0038.
