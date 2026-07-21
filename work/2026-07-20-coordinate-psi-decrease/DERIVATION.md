# Derivative sign to the ordered endpoint inequality

The maintained theorem gives, for every `p<z<w`,

```text
Q(p) * deriv (fun x => coordinatePsi Q Q1 x z w) p < 0.
```

Because `Q(p)>0`, this implies the literal derivative inequality

```text
deriv (fun x => coordinatePsi Q Q1 x z w) p < 0.
```

Fix `z<w` and put `f(p)=coordinatePsi Q Q1 p z w`. The admissible domain
`Iio z` is convex and open. A nonzero derivative gives differentiability and
therefore continuity at every point of this domain. Mathlib's
`strictAntiOn_of_deriv_neg` then gives

```text
StrictAntiOn f (Iio z).
```

Thus for `p₁<p₂<z<w`,

```text
coordinatePsi Q Q1 p₂ z w < coordinatePsi Q Q1 p₁ z w.
```

This is precisely the orientation used by the terminal quotient:
`p_d<p_b` implies `Psi(p_d)>Psi(p_b)`.
