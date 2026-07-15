# Regular Hermite Taylor model

For vector-valued `g` and nodes `z_0,...,z_j`, expansion about `c` gives

\[
g[z_0,\ldots,z_j]
=\sum_{k=0}^N\frac{g^{(j+k)}(c)}{(j+k)!}
 h_k(z_0-c,\ldots,z_j-c)+R_{j,N},
\]

where `h_k` is the complete homogeneous symmetric polynomial.  This is the
Hermite--Genocchi formula with its simplex moments evaluated exactly.  Repeated
nodes require no limiting branch and no division by a gap.

For `d=max_i|z_i-c|`, the implementation uses the safe vector remainder

\[
\|R_{j,N}\|_1\le
\frac{M_{j+N+1}d^{N+1}}{j!(N+1)!},
\]

where `M_l` is a directed interval bound for `||g^(l)||_1` on the whole
argument interval.  Those derivative bounds are obtained from the theta
series in cells of width below `0.01`; parity covers negative arguments.

For nodes `(x,x,m,r)` the four columns are produced at orders zero through
three and their determinant is evaluated as a degree-ten three-variable
Taylor model.  The variables are

\[
x=m-\theta\rho,\qquad r=m+(1-\theta)\rho.
\]

Because complete homogeneous polynomials accept repetitions, the same code
handles:

- `rho=0`: fourfold collision;
- `theta=0`: the triple node `(m,m,m)`;
- `theta=1`: the two pairs `(x,x,m,m)`;
- `0<theta<1`: the ordinary x-confluent interior.

Degree eight proved the radial and interior calibration but lost both angular
face signs.  Degree ten restores the necessary cancellation and proves all
four calibration cells.

# Manifest result

`manifest.json` records a complete directed cover of

```text
-0.002 <= m <= 0.002
0 <= rho <= 0.05
0 <= theta <= 1.
```

Six closed boxes cover this slab; every stored determinant lower endpoint is
positive and replay recomputes the sign.  The manifest stores:

- the precise local statement and hypotheses;
- precision, Taylor degree, theta truncation, and subdivision limit;
- Python, python-flint, SymPy, platform, and interpreter checksum;
- checksums of every verifier source;
- verifier commands and a stable expected-outcome hash;
- every accepted box and its directed enclosure;
- an explicit statement that no global PF4 claim is made.

The local host has no environment-image digest, so the manifest says
`unavailable-local-host` and supplies an environment fingerprint instead of
inventing an image identity.

# Cross-check boundary

At three interior points, both the new divided determinant and the independent
`Jhat` Taylor evaluator have positive directed enclosures.  Exact symbolic
modules separately recover

```text
rho=0:   Jhat = C4/(12q^3)
theta=0: Jhat = E/rho^2
theta=1: the finite 21-term two-point limit.
```

This checks orientation and face compatibility; it is not used as substitute
support for the six manifest boxes.
