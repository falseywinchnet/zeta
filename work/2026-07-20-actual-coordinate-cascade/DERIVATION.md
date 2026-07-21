# Derivation

Let

```text
y(x) = -S(x),
Q(y(x)) = q(x),
g(x) = Psi(Q,Q1; y(x), y(m), y(r)).
```

The maintained actual-coordinate theorem gives, for `x < m < r`,

```text
Q(y(x)) * partial_y Psi(Q,Q1; y(x), y(m), y(r)) < 0.
```

Because `y'(x)=q(x)` and `Q(y(x))=q(x)`, the chain rule gives the exact
identity

```text
g'(x) = q(x) * partial_y Psi(Q,Q1; y(x), y(m), y(r)) < 0.
```

The derivative criterion on the convex interval `(-infinity,m)` therefore
makes `g` strictly decreasing.  This proof never needs `Q` or its derivative
tower away from the attained range of `y`.

For `x < m < r`, the exact translation-coordinate identity is

```text
lowerLambda(S,q;x,m,r)
  = coordinateLambda(Q; y(x), y(m), y(r)).
```

Every point of the compact coordinate interval from `y(x)` to `y(r)` lies in
the actual range.  On that interval the constructed jet supplies the two
derivative identities required by the closed integral formula, while
`F2 > 0` supplies positive coordinate curvature.  Hence both triangular
weighted integrals in `coordinateLambda` are strictly positive, so
`lowerLambda > 0`.  The lower-cascade sign is therefore a consequence rather
than a hypothesis.

Finally, for `a < c < b < d`, the exact terminal factorization is

```text
terminalQuotD(t)
  = terminalQuot(t)
      * (Psi(y(t-d),y(t-c),y(t-a))
         - Psi(y(t-b),y(t-c),y(t-a))).
```

The derived lower-Lambda signs make both second quotients positive and thus
`terminalQuot(t)>0`.  Since

```text
t-d < t-b < t-c < t-a,
```

the derived strict decrease makes the displayed `Psi` difference positive.
Both factors are strict, so `terminalQuotD(t)>0`.

## Non-vacuity boundary

The terminal sign, coordinate monotonicity, coordinate realization, lower
Lambda sign, closed gap, and central identity do not occur as theorem premises.
The theorem still requires the genuine analytic inequalities `q > 0`,
`F2 > 0`, and `det C4 > 0`; proving them for the literal Riemann kernel is the
next substantive mathematical boundary.
