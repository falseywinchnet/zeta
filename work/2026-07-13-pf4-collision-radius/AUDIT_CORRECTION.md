# Refine audit correction

The first advancement verifier used a uniform fourth-order Taylor remainder
for every endpoint jet.  For `q'''(m+h)` this reached derivatives beyond the
certified inventory, and two remainder constants were smaller by a factor of
two.  The refine audit rejected that parametrization before certification.

The corrected verifier expands each `q^(j)(m+h)` only through the common jet
`q^(4)`:

```text
q       through order 4, remainder q^(5)
q'      through order 3, remainder q^(5)
q''     through order 2, remainder q^(5)
q'''    through order 1, remainder q^(5)
```

Differentiating the integral remainders then uses only `q^(6)`, which is in
the certified theta-tail inventory.  The corrected exact bounds are

```text
NUMERATOR_LIPSCHITZ = 9691662950748701720576/3875090625
DENOMINATOR_LIPSCHITZ = 3595695104/18225
EDGE_COLLISION_RADIUS = 7167625959375/4845831475374350860288
```

The new radius is approximately `1.47913e-9`.  It still satisfies
`2*EDGE_COLLISION_RADIUS > 2^-29`, so the separated-gap coefficient proof
applies without changing its rational gap floor.
