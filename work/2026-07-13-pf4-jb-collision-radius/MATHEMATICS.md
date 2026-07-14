# Full J_b collision radius

Normalize `alpha+beta=1` and write

\[
x=m-\beta\varepsilon,\qquad r=m+\alpha\varepsilon.
\]

Each endpoint jet is expanded only through the common central jet `q^(4)`.
The integral remainders use `q^(5)`:

```text
B,C: remainder order 6
q(x),q(r): remainder order 5
q'(x),q'(r): remainder order 4
q''(x): remainder order 3
q'''(x): remainder order 2
```

On `epsilon<=1/4`, every intermediate tail coordinate has `X_t<2X_m`.
The certified jet scale gives the exact rational remainder boxes used by
`prove_jb_collision_radius.py`.

The 74-term cleared numerator is evaluated in a sparse epsilon ring through
its exact terminal order 45.  Coefficients below order five vanish.  Every
higher coefficient divides exactly by `alpha beta^2`; division is performed
before absolute majorization.  The collision coefficient is

\[
{\alpha\beta^2(\alpha+\beta)(\alpha+3\beta)q^2C_4\over12}.
\]

After division, the forty nonzero higher orders have total coefficient norm

\[
M={343446590091059391889408\over24911296875}X^8.
\]

Since `q^2 C4/12 >=44392 X^8/12`, choosing

\[
\boxed{\varepsilon_0=
{46077595453125\over343446590091059391889408}}
\]

makes `epsilon M` at most half the collision margin.  Therefore the full
`J_b` numerator is positive throughout the normalized collision cone
`0<epsilon<=epsilon0`.

The angular quotient is polynomial at both faces.  Its leading geometry is

\[
(\alpha+\beta)(\alpha+3\beta)=1\quad(\beta=0),
\]

and

\[
(\alpha+\beta)(\alpha+3\beta)=3\quad(\alpha=0).
\]

Thus neither face is inferred from an interior sample or identified with the
other by reflection.
