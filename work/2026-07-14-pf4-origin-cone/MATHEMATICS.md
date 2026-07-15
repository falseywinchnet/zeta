# The origin collision cone

Let

\[
g(t)=\left(1,\frac{\Phi'}\Phi,\frac{\Phi''}\Phi,
                 \frac{\Phi'''}\Phi\right)^T(t)
\]

and let `r_j=Phi^(j)/Phi`.  The ratio differentiation rule

\[
(r_j)'=r_{j+1}-r_1r_j
\]

gives the exact identity

\[
\det[g,g',g''/2,g'''/6]
=\frac1{12}\det[r_{i+j}]_{i,j=0}^3=\frac{C_4}{12}.
\]

For the x-confluent order-four minor use ordered nodes `(x,x,m,r)` and
Newton--Hermite columns

\[
g[x],\quad g[x,x],\quad g[x,x,m],\quad g[x,x,m,r].
\]

Their determinant is the finite Wronskian divided by the positive confluent
Vandermonde

\[
(m-x)^2(r-x)^2(r-m).
\]

This fixes the orientation: positivity is the PF4 target.  Unlike `Jhat`, this
representation exists without division by `theta` or `1-theta`.  At
`theta=0` it has a triple left node; at `theta=1` it has a repeated right
node.  Both are ordinary Hermite divided differences.

## Directed derivative bounds

On `[-1,1]`, directed theta-series arithmetic proves the safe one-norm bounds

```text
||g||_1       <= 66414
||g'||_1      <= 851436
||g''||_1     <= 74267900
||g'''||_1    <= 16979795470
||g''''||_1   <= 5075221028119.
```

The calculation covers `[0,1]` by interval cells and uses parity for
`[-1,0]`.  These are uniform derivative bounds, not sampled sign evidence.

Write `rho=r-x`.  Hermite--Genocchi gives column perturbations from the fully
confluent columns at `m` bounded by

\[
E_0\le\rho M_1,\quad E_1\le\rho M_2,\quad
E_2\le\rho M_3/2,\quad E_3\le\rho M_4/6.
\]

Multilinearity and the one-norm Hadamard bound therefore give

\[
|\det C-\det C_0|\le
\prod_{j=0}^3(A_j+E_j)-\prod_{j=0}^3A_j,
\qquad A_j=M_j/j!.
\]

For `rho<=1`, the right side is at most `rho L`, where

```text
L = 498971334735264400683948242783793000.
```

The established directed bound on `[0,1]` is `C4>=28172286`.  Consequently

\[
\boxed{\rho_0=
\frac{521709}{221765037660117511415088107903908000}
\approx2.352530432680664\,10^{-30}}
\]

makes `rho_0 L=(C4_floor/12)/2`.  The divided determinant is thus at least
`C4_floor/24>0` whenever `rho<=rho0`.

The remaining, not-already-tail collision triples lie in `[-1,1]`: the tail
seam `a23=log(23/pi)/2` satisfies `a23<999/1000`, while `rho0<1/1000`.
Thus the cone joins the existing positive and reflected tail charts without a
gap.

# The separated compact complement

Put

\[
x=m-\theta\rho,\qquad r=m+(1-\theta)\rho.
\]

After the two escape lemmas, same-tail charts, and the collision cone, the
only remaining closed atlas is

\[
\rho_0\le\rho\le2R_{64},\quad0\le\theta\le1,
\]
\[
-R_{64}+\theta\rho\le m\le
R_{64}-(1-\theta)\rho,
\]

with `R64=log(64/pi)/2`, `x<=a23`, and `r>=-a23`.  This is compact.  The
radial boundary belongs to the proved cone.  The two angular faces must remain
in the cover; the Hermite determinant supplies a single regular target for
the interior and both faces.

The current `Jhat` Taylor model passes origin-crossing and near-face
calibration cells.  A deliberately broad mixed cell remains undecided from
dependency loss.  These tests validate pieces of the evaluator only.  They
are not an exhaustive complement certificate.

The next implementation should evaluate the Hermite divided-difference
determinant directly, adaptively subdivide this exact semialgebraic atlas, and
emit every accepted box and every analytic overlap in a replayable manifest.
