# Preserved obstruction

The current `Jhat` Taylor evaluator returns an enclosure spanning zero on the
broad mixed cell

```text
m in [-0.001,0.001], rho in [1,1.002], theta in [0.49,0.51].
```

Its enclosure is approximately `[-1.57e5,1.77e5]`, despite the positive
pointwise margin observed in earlier raw work.  This is dependency loss, not a
negative value and not evidence against PF4.  The cell was deliberately left
undecided.  The next evaluator should use the regular Hermite divided-
difference columns directly, then subdivide only under a replayable exhaustive
manifest.
