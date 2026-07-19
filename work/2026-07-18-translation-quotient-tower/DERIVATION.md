# Derivative ladder for the translation quotient tower

Fixed pivot `a = y₁`. Write `g = Φ(·-a)`, `f = Φ(·-b)` for a moving column
`b`, with jets `g1,g2,g3` and `f1,f2,f3` given by translates of `Φ1,Φ2,Φ3`.

## Level one

`firstQuot = f/g`. Quotient rule:

```
firstQuotD = (f1 g - f g1) / g²          (N := f1 g - f g1)
```

`N' = f2 g - f g2` (the cross terms `f1 g1` cancel), `(g²)' = 2 g g1`, so

```
firstQuotD2 = (N1 g² - N (2 g g1)) / g⁴   (N1 := f2 g - f g2, M := numerator)
```

`N1' = f3 g + f2 g1 - f1 g2 - f g3 =: N2`, `(2 g g1)' = 2 g1² + 2 g g2`,
`(g⁴)' = 4 g³ g1`, and `M' = N2 g² - N (2 g1² + 2 g g2) =: M1` (the
`N1 · 2 g g1` terms cancel), so

```
firstQuotD3 = (M1 g⁴ - M (4 g³ g1)) / g⁸
```

## Level two

`v_b := firstQuotD(a,b)`, second pivot `c = y₂`.
`secondQuot = v_b / v_c`; quotient rule with the level-one jets gives

```
secondQuotD  = (v_b' v_c - v_b v_c') / v_c²
secondQuotD2 = ((v_b'' v_c - v_b v_c'') v_c² -
                (v_b' v_c - v_b v_c') (2 v_c v_c')) / v_c⁴
```

where `v' = firstQuotD2`, `v'' = firstQuotD3`, and the cross terms
`v_b' v_c'` cancel in the numerator derivative exactly as at level one.

## Level three

`w_b := secondQuotD(a,c,b)`, third pivot `d = y₃`, moving column `e = y₄`.
`terminalQuot = w_e / w_d` and one more quotient rule gives `terminalQuotD`.

## Nonvanishing discipline

Every division in the ladder carries a proved nonzero denominator:
`g ≠ 0` from `Φ > 0`; `v_c ≠ 0` from the named premise `v₂ > 0`;
`w_d ≠ 0` from the named premise `w₃ > 0`. The three named premises are the
strict level signs the next rounds must derive; they are never concluded
here and never applied to any determinant, difference, or integral.

## Row factorization

`Φ(tᵢ - yⱼ) = Φ(tᵢ - y₁) · firstQuot(y₁,yⱼ)(tᵢ)` with `Φ(tᵢ - y₁) > 0`
identifies `translationMinor Φ ![t] ![y]` with the engine's
`rawFactoredDet4` at the tower values, entry by entry over `Fin 4`.
