# Multi-center separated determinant

The one-center Hermite series loses accuracy because its Taylor radius is set
by node separation even after a parameter box shrinks.  The separated chart
instead builds local Taylor models at the three endpoints:

\[
g(x),\quad g'(x),\quad g(m),\quad g(r).
\]

Use affine positive gaps

\[
b=m-x>0,\qquad a=r-m>0,\qquad \rho=a+b.
\]

The Newton--Hermite columns are reconstructed recursively:

\[
d_{xm}=\frac{g(m)-g(x)}b,
\qquad
d_{mr}=\frac{g(r)-g(m)}a,
\]

\[
C_2=\frac{d_{xm}-g'(x)}b,
\qquad
d_{xmr}=\frac{d_{mr}-d_{xm}}{a+b},
\qquad
C_3=\frac{d_{xmr}-C_2}{a+b}.
\]

Together with `C0=g(x)` and `C1=g'(x)`, exact symbolic column algebra gives

\[
\det[C_0,C_1,C_2,C_3]
=\frac{\det[g(x),g'(x),g(m),g(r)]}
       {a b^2(a+b)^2}.
\]

The denominator is positive, so orientation is preserved.  The formula is
the same normalized x-confluent determinant used by the one-center chart.

Each endpoint model is expanded about its own box center to total degree ten.
Theta-series tails and Taylor remainders are directed.  The first component of
`g` is retained exactly as one, and its derivatives exactly as zero; this
removes a large artificial determinant radius.

# Why affine gaps matter

In `(rho,theta)` coordinates the separated denominators are `theta*rho` and
`(1-theta)*rho`.  A generic Taylor enclosure can contain zero even when the
true rectangular domain has positive lower endpoints.  In `(m,b,a)`, every
denominator is affine (`a`, `b`, or `a+b`), so its positivity is represented
without dependency loss.

# Directed overlap

On the closed box

```text
m in [-0.0001,0.0001]
rho in [0.04,0.0402]
theta in [0.49,0.51]
```

both the one-center Hermite determinant and the multi-center determinant have
strictly positive directed enclosures.  Thus the charts join without relying
on a midpoint comparison.

# Manifested bands

The replayable manifest proves the determinant positive on both closed bands

```text
-0.25 <= m <= 0.25
0.015 <= b <= 0.025
0.075 <= a <= 0.085
```

and

```text
-0.25 <= m <= 0.25
0.075 <= b <= 0.085
0.015 <= a <= 0.025.
```

The `m` interval is partitioned into 25 exact closed pieces in each band.  All
50 boxes have positive directed lower endpoints; replay reports no unresolved
box.  These bands pass through positive, negative, and mixed-sign endpoint
patterns.  They are continuum certificates, not a numerical sweep.

The manifest explicitly keeps `global_pf4_claim=false` because other gap
bands, near-face transitions, and larger anchors remain uncovered.
