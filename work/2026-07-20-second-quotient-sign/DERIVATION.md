# Closed second-level sign derivation

Write

```text
S = Phi1/Phi
q = (Phi1^2-Phi*Phi2)/Phi^2
A(x,r) = S(x)-S(r)
M(x,r) = (q(r)-q(x))/A(x,r)
Lambda(x;m,r) = A(x,r)+M(x,m)-M(m,r).
```

P000111 proves `S'=-q` and the first-level identity

```text
v_b = firstQuotD(a,b) = firstQuot(a,b) * A(p_b,p_a).
```

Differentiating this product under simultaneous translation gives the exact
logarithmic rate

```text
v_b' = v_b * (A(p_b,p_a)+M(p_b,p_a)).
```

The Lean proof obtains this without expanding all nested quotients. It
differentiates `firstQuot * A` using `S'=-q`, converts that product back to
the maintained `firstQuotD` pointwise, and invokes uniqueness against the
maintained quotient-rule derivative `firstQuotD2`.

Therefore

```text
(v_b/v_c)'
  = (v_b/v_c) *
      (A(p_b,p_c)+M(p_b,p_a)-M(p_c,p_a)).
```

The additive identities for `A` and the weighted-mean identity for `M` give

```text
A(p_b,p_c)+M(p_b,p_a)-M(p_c,p_a)
  = A(p_b,p_c)/A(p_b,p_a) * Lambda(p_b;p_c,p_a).
```

Every factor outside `Lambda` is strictly positive from `Phi>0`, `q>0`, and
ordered columns. Thus the exact upstream `Lambda>0` statement proves the
maintained `secondQuotD>0` premise without assuming that premise or a
determinant sign.

The result is conditional precisely where the current formal graph is
conditional: the analytic R141 lower bound proving `Lambda>0` has not yet
been converted to Lean.
