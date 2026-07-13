# Same-tail normalization

For `u>=1`, put `X=pi exp(2u)`.  The existing theta-tail analysis gives, for
`j=0,1,2,3,4`,

\[
q^{(j)}(u)=2^{j+2}X+\delta_j(u),
\qquad
|\delta_j(u)|\le E_{j+2}/X,
\]

with

\[
E_2=19.8,\ E_3=176,\ E_4=2082,\ E_5=30770,\ E_6=545900.
\]

For an interval `u<v`, `Y=pi exp(2v)`, integration gives the sharper exact
primitive enclosure

\[
\left|A(u,v)-2(Y-X)\right|
\le 9.9\left(\frac1X-\frac1Y\right).
\]

The new densities `S_r` and `J_b` use jets only through `q'''`, so `E2` through
`E5` suffice.  At `X>=128`, their endpoint relative errors satisfy

\[
\frac{E_2}{4X^2}<3.1\cdot10^{-4},\quad
\frac{E_3}{8X^2}<1.4\cdot10^{-3},\quad
\frac{E_4}{16X^2}<8.0\cdot10^{-3},\quad
\frac{E_5}{32X^2}<5.9\cdot10^{-2}.
\]

Thus `u>=0.5 log(128/pi)`, approximately `1.854`, is a natural initial
same-tail threshold for a perturbative proof.

The remaining analytic work is not to sample this region.  Normalize

\[
U=X_m/X_x\ge1,\qquad V=X_r/X_m\ge1,
\]

substitute the endpoint and primitive error boxes into the 24-term `S_r`
numerator and 74-term `J_b` numerator, and prove positivity in two regimes:

1. `U-1` or `V-1` bounded below: perturb the exact exponential margins;
2. both ratios near one: use the `C4` collision expansion with a directed
   analytic remainder.

Reflection supplies the negative same-tail case.  Mixed-tail escape remains a
separate endpoint-dominance lemma.

