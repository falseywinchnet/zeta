# Explicit dominant-theta lower bounds

## Coordinates

On the positive tail let

```text
X = pi exp(2x),   U = exp(2b),   V = exp(2d),
b = m-x,          d = r-m,       rho = b+d,
theta = b/rho.
```

For the first theta term, write `q1` for its curvature, `s1` for its
logarithmic slope, and

```text
B = s1(x)-s1(m) = integral_x^m q1,
C = s1(m)-s1(r) = integral_m^r q1.
```

The exact formulas used by the verifier are

```text
s1(X) = 5/2 + 4X/(2X-3) - 2X,
q1(X) = 4X(4X^2-12X+15)/(2X-3)^2.
```

All statements below hold for `X>=23`, `U>=1`, and `V>=1`, with strict gaps
for the original rational densities and continuous extension to collisions.

## Edge density

Set

```text
lambda_S = 12874546322/6441186049
         = 1.9987850411491817...
```

After putting `X=23+y` and `V=1+c`, the numerator of

```text
S_r - lambda_S q1(r)
```

has 80 coefficients and every coefficient is nonnegative.  The constant
coefficient is zero and every other coefficient is positive.  The denominator
is the square

```text
(-A^2 q(r) + A q'(r) + q(m)q(r)-q(r)^2)^2,
```

so it is positive away from collision.  Therefore

```text
S_r >= lambda_S q1(r).
```

Since `S(m,m)=0`, integration gives the collision-divided form

```text
S(m,r)/A(m,r) >= lambda_S.
```

Also `q1(X)>4X`, hence

```text
S_r > (51498185288/6441186049) X_r
    > 7.9951401645 X_r.
```

## Full reopening density

Set

```text
lambda_J = 40692340696264827889/40743983163526890625
         = 0.9987325130423603...
```

After `X=23+y`, `U=1+a`, and `V=1+c`, the numerator of

```text
J_b - lambda_J q1(x)(B+C)(3B+C)
```

has 1,386 coefficients and every coefficient is nonnegative.  Exactly three
coefficients vanish:

```text
y^0 a^2 c^0,   y^0 a^1 c^1,   y^0 a^0 c^2.
```

These are precisely the quadratic full-collision terms at the threshold
`X=23`.  The denominator is `B^2 C q1(x)^2>0`.  Thus

```text
J_b >= lambda_J q1(x)(B+C)(3B+C).
```

The constant is sharp for this coefficientwise comparison: increasing it
makes one of the three displayed collision coefficients negative.  No claim
is made that it is the optimal pointwise constant.

## Collision division without loss

The exact derivative of the forced collision factor is

```text
d/db [b(b+d)^2] = (b+d)(3b+d).
```

The dominant curvature is increasing for `X>=23`, while

```text
B >= q1(x)b,   C >= q1(x)d.
```

During reopening from `b=0` to the final gap, every intermediate left endpoint
has curvature at least the final `q1(x)`.  Since `J(0)=0`, integration of the
`J_b` bound gives

```text
J >= lambda_J q1(x)^3 b(b+d)^2.
```

Consequently the collision-divided numerator has the uniform bound

```text
Jhat = J/[b rho^2] >= lambda_J q1(x)^3
     > (2604309804560948984896/40743983163526890625) X^3
     > 63.9188808347 X^3.
```

This bound survives `b->0`, `d->0`, and simultaneous collision.  It removes
the vanishing-margin obstruction that defeated an absolute perturbation bound
for raw `J`.

The differential version is

```text
J_b/rho^2 >= lambda_J q1(x)^3(1+2theta).
```

## Scope

These are exact bounds for the first theta term on the positive-tail chart.
They are not yet bounds for the full Riemann kernel.  Transferring them requires
a directed estimate for the `n>=2` correction after the same collision
division.  The negative-tail orientation must also be checked explicitly;
reflection reverses the ordered endpoints and should not be applied by name
alone to `J_b`.
