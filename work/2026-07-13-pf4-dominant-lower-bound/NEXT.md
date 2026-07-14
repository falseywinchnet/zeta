# Next proof step

Write the full kernel as the first theta term times `1+R`.  Express the full
`Jhat` and the collision-divided edge density in the same normalized variables,
then bound their difference from the dominant objects using the existing
directed estimates for derivatives of `log(1+R)` through order eight.

The target inequalities are now explicit:

```text
|Jhat_full-Jhat_1| < lambda_J q1(x)^3,
|S_r_full-S_r_1|   < lambda_S q1(r).
```

The error bounds should retain the exponential factor from the first omitted
theta mode and be split only by derivative order, not by sampled gap boxes.
Repeat the coefficient calculation in the reflected orientation before using
the result on the negative tail.
