# Closed first-level sign derivation

Let `p_b=t-b`, `p_a=t-a` with `a<b`, so `p_b<p_a`. Define

```text
S(x) = Φ1(x)/Φ(x)
q(x) = (Φ1(x)^2 - Φ(x)Φ2(x))/Φ(x)^2.
```

The quotient rule gives, with no logarithm object required,

```text
S'(x) = (Φ2(x)Φ(x)-Φ1(x)^2)/Φ(x)^2 = -q(x).
```

Thus the independently supplied analytic boundary `q(x)>0` implies `S'(x)<0`
and hence strict antitonicity of `S`. The maintained quotient derivative has
the exact factorization

```text
firstQuotD Φ Φ1 a b t
  = firstQuot Φ a b t * (S(p_b)-S(p_a)).
```

Both factors are positive: the first from `Φ>0`, the second from `p_b<p_a`
and strict antitonicity. This discharges the entire first-level sign premise of
`translationMinor_pos_of_quotient_tower_signs` once the actual-kernel jet and
`q>0` certificate statement are instantiated.
