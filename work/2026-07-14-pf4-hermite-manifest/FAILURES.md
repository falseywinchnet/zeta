# Preserved limitation

The one-center Hermite series becomes too wide when its center must span
separated off-origin nodes.  At zero-width test points such as

```text
(m,rho,theta)=(0.2,0.1,0.2)
```

the independent `Jhat` enclosure is strictly positive, while the degree-ten
Hermite determinant enclosure spans zero.  This is interval dependency and
truncation loss, not a counterexample.

Blind subdivision is the wrong response: node separation does not disappear
when only parameter-box radii shrink.  The separated evaluator must instead
use multiple local centers or recursive divided differences, reserving the
one-center Hermite formula for collision and near-face transitions.
