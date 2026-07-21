# Derivation

Write

```text
y(u) = -S(u),    S'(u) = -q(u),    q(u) > 0.
```

Then `y'(u)=q(u)>0`, so `y` is strictly increasing and injective. The honest
coordinate domain is `range y`, represented by `Equiv.ofInjective y`.

If `q'=q₁`, continuity of `q` upgrades the derivative of `y` to a strict
derivative. The inverse-function theorem then applies at every `u`. The global
`Function.invFun y` extension is used only at `y(u)`, where injectivity gives

```text
invFun y (y(u)) = u.
```

Consequently its derivative there is `1/q(u)`. Defining

```text
Q(y) = q(invFun y y)
```

and differentiating only at range points gives

```text
Q(y(u))  = q,
Q₁(y(u)) = q₁/q,
Q₂(y(u)) = (q q₂-q₁²)/q³,
Q₃(y(u)) = (q²q₃-4qq₁q₂+3q₁³)/q⁵,
Q₄(y(u)) =
  (q³q₄-7q²q₁q₃+25qq₁²q₂-4q²q₂²-15q₁⁴)/q⁷.
```

The maintained curvature is defined as `κ=2-Q₂`. With

```text
F₂ = q³-(q q₂-q₁²),
```

the exact identity is

```text
κ(y(u)) = 1 + F₂(u)/q(u)³.
```

This corrects the tempting but false simplification `κ=F₂/q³`.

Finally the coordinate cumulants generated from `Q,Q₁,...,Q₄` simplify to

```text
-q, -q₁, -q₂, -q₃, -q₄.
```

Therefore the maintained `determinantC4Function` at `y(u)` is literally the
paper's central-moment determinant formed from those cumulants.
