# Hermite face and intermediate atlas

Write the ordered nodes as

\[
x=m-b,\qquad x,\qquad m,\qquad r=m+a,
\]

and use the normalized Newton-column determinant.  The separated chart from
P000055 is effective when both `a` and `b` have positive lower endpoints, but
its recursive quotients lose cancellation on either collision face.

## Local Hermite divided differences

For a node cluster `z_0,...,z_k`, repeated nodes included, choose a local
center `c` and put `d_i=z_i-c`.  The exact analytic identity

\[
[z_0,\ldots,z_k]g
=\sum_{j\geq0}\frac{g^{(k+j)}(c)}{(k+j)!}
 h_j(d_0,\ldots,d_k)
\]

uses the complete homogeneous polynomial `h_j`.  `face_tm.py` retains degrees
zero through ten and encloses the remainder with componentwise derivative
bounds from the repaired endpoint jet.  Repetitions therefore represent
derivatives exactly; no division by a vanishing node gap occurs.

On the left face `b=0`, the first three columns are evaluated as
`g(x)`, `g'(x)`, and `[x,x,m]g`; only the final nonzero separations are divided.
The right chart is the reflected construction at `a=0`.  Both charts were
checked on their positive-gap overlap against the separated chart.

At simultaneous collision the four columns are evaluated directly as

\[
[x]g,\quad[x,x]g,\quad[x,x,m]g,\quad[x,x,m,r]g.
\]

This formula remains regular at `a=b=0`.  The square
`0<=a,b<=0.015` is divided at increments of `0.00375`.  Each cell is first
enclosed by the all-Hermite chart; an interior cell whose Hermite enclosure is
undecided is enclosed by the separated chart.  Cells touching an axis never
use a singular quotient.  Coarse anchor cells that remain undecided are
replaced, not supplemented, by their two half-width anchor children.

## Closed regions

The manifest covers the following continua:

- `0.1<=|m|<=0.48`, `0.015<=a,b<=0.095`;
- `-0.5<=m<=0.5`, `0<=b<=0.015`, `0.015<=a<=0.095`;
- `-0.5<=m<=0.5`, `0<=a<=0.015`, `0.015<=b<=0.095`;
- `-0.5<=m<=0.5`, `0<=a,b<=0.015`.

Together with the P000055 central and endpoint rectangles, these finish the
gap square `0<=a,b<=0.095` for every `|m|<=0.5`, including both collision
faces and their intersection.  This is a bounded regional result, not global
PF4.

## Large-gap trial

Two dependency-preserving reformulations were tested beyond `0.095`: the
affine-gap Peano quantity `J/(b(a+b)^2)` and exact Gaussian reduction of the
Newton determinant.  Broad large-gap boxes remained undecided because interval
division and subtraction lost correlation.  No such box is included in the
manifest and no negative determinant was obtained.
