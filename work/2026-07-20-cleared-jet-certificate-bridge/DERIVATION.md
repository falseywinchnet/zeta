# Derivation

## One recurrence for the raw jet

Let `Phi_j` denote the ordinary derivative jet and put

```text
m_j = Phi_j / Phi_0.
```

If `Phi_j' = Phi_(j+1)` and `Phi_0' = Phi_1`, then the quotient rule gives

```text
m_j' = m_(j+1) - m_1 m_j.
```

This single identity generates the logarithmic cumulants:

```text
c2 = m2 - m1^2
c3 = c2'
c4 = c3'
c5 = c4'
c6 = c5'.
```

Lean checks the expanded cumulant polynomials and each derivative equality.
The maintained curvature tower is then

```text
q  = -c2,
q1 = -c3,
q2 = -c4,
q3 = -c5,
q4 = -c6.
```

Thus an ordinary derivative tower through `Phi6`, plus continuity of `Phi6`,
constructs every derivative and continuity input required downstream.

## Cleared certificate forms

CERT12 evaluates three raw polynomials.  Lean proves the exact identities

```text
clearedQ  = Phi0^2 * q,
clearedF2 = Phi0^6 * kernelF2(q,q1,q2),
clearedC4 = Phi0^4 * kernelDeterminantC4(q,q1,q2,q3,q4).
```

The powers of `Phi0` are strictly positive when `Phi0 > 0`, so strict
positivity transfers in the required direction without introducing an
unrelated positive scalar.

The third raw polynomial is also proved equal to

```text
det [Phi_(i+j)]_(i,j=0,...,3).
```

This closes the representation boundary between the matrix constructed by the
Python certificate, its expanded polynomial, and the maintained central-moment
determinant in Lean.

## Cascade

The three transferred signs supply the maintained actual-coordinate derivative
theorem.  After composition with `y=-S`, the derivative is

```text
d/dx Psi(y(x);y(m),y(r)) = q(x) * partial_y Psi < 0.
```

Hence `Psi` is strictly decreasing on the original interval.  Separately,
`F2 > 0` gives positive coordinate curvature, so the two triangular integral
pieces of lower `Lambda` are positive.  The exact terminal factorization then
has two strictly positive factors and yields

```text
terminalQuotD > 0.
```

## Candidate paper backport

The normalized recurrence plus the three cleared identities is materially
tighter than presenting the high logarithmic derivatives independently.  A
future paper revision can use it as the analytic/formal interface:

1. prove the ordinary theta derivative jet;
2. prove three raw polynomial signs;
3. invoke the recurrence and positive-denominator identities.

No paper revision is made in this advancement round.
