# Exact terminal-rate derivation

Write `S = Phi1/Phi`, `q = -S'`,

```text
A(x,r) = S(x)-S(r),
M(x,r) = (q(r)-q(x))/A(x,r),
Lambda(x;m,r) = A(x,r)+M(x,m)-M(m,r),
g(x;m,r) = A(x,m)/A(x,r) * Lambda(x;m,r).
```

The maintained second-level factorization is

```text
w_x = secondQuotD = secondQuot * g(x;m,r).
```

Under simultaneous translation, `T A = A M`. Therefore

```text
T log g = M(x,m)-M(x,r)+T Lambda/Lambda,
T log secondQuot = g.
```

The weighted-mean identity gives the exact cancellation

```text
g + M(x,m)-M(x,r) = Lambda(x;m,r)-A(m,r).
```

Consequently

```text
T log w_x = Psi(x;m,r)-A(m,r),
Psi = Lambda + T Lambda/Lambda.
```

The common `-A(m,r)` cancels between the `d` and `b` columns, so

```text
terminalQuotD
  = terminalQuot * (Psi(p_d;p_c,p_a)-Psi(p_b;p_c,p_a)).
```

For the coordinate realization `Y(x)=-S(x)`, assume the literal instance
relations

```text
Q(Y(x)) = q(x),
Q1(Y(x)) = q'(x)/q(x).
```

Then `A(x,r)=Y(r)-Y(x)`, the curvature means become chord slopes of `Q`, and

```text
Lambda(x;m,r) = coordinateLambda Q (Y x) (Y m) (Y r).
```

Moreover the closed simultaneous derivative of `Lambda` is exactly

```text
coordinateTLambda Q Q1 (Y x) (Y m) (Y r),
```

because `Q*Q1=q'` turns each coordinate `chordMoment` into
`q(x)+q(m)-N(x,m)+M(x,m)^2`. Thus the endpoint object is not a detached Psi:
it is `PF4.CoordinateSignBridge.coordinatePsi` under this explicit map.
