# Endpoint-local remainder repair

The P000054 endpoint model expanded `g` locally but bounded its Taylor
remainder using derivative maxima on the symmetric interval

\[
[-(|c|+d),|c|+d],
\]

where `c` was the endpoint center and `d` its box radius.  Near `c=±0.5`, that
needlessly included the entire interval back to the origin.  The determinant
then inherited a large false uncertainty through recursive gap divisions.

The repaired endpoint jet bounds each component of every required derivative
only on

\[
[c-d,c+d].
\]

Negative intervals are reflected by parity before directed theta evaluation.
Intervals meeting zero use the smallest symmetric positive chart required.
Each positive interval is subdivided into cells of width below `0.005` before
the component bound is taken.  For component `i` and derivative order `j`, the
degree-ten remainder is

\[
|R_{i,j}|\le
\sup_{[c-d,c+d]}|g_i^{(j+11)}|\frac{d^{11}}{11!}.
\]

The first component is handled exactly: `g_0=1` and every positive derivative
of `g_0` is zero.  Thus neither the constant row nor its derivatives receive a
spurious remainder.

# Resolved endpoint failures

The four P000054 failures were the two gap orientations on each anchor box

```text
m in [-0.50,-0.48]
m in [ 0.48, 0.50]
```

with gap intervals `[0.015,0.025]` and `[0.075,0.085]`.  All four now have
strictly positive directed determinant lower endpoints.  No increase in
precision or Taylor degree was needed; localizing the remainder was the
decisive correction.

# Expanded tiled regions

The manifest proves three region families.

## 1. Extended asymmetric ribbons

For every `-0.5<=m<=0.5`, positivity holds on both

```text
b in [0.015,0.025], a in [0.075,0.085]
b in [0.075,0.085], a in [0.015,0.025].
```

The anchor is divided into 50 closed cells of width `0.02`.

## 2. Central complete gap rectangle

For every `-0.1<=m<=0.1`, positivity holds throughout

```text
0.015 <= b <= 0.095
0.015 <= a <= 0.095.
```

The anchor has ten cells of width `0.02`; each gap has four cells of width
`0.02`.  This contributes 160 directed boxes and fills the space between the
two earlier ribbons at central anchors.

## 3. Complete endpoint gap rectangles

On each anchor box `[-0.50,-0.48]` and `[0.48,0.50]`, positivity holds on the
same full gap rectangle `0.015<=a,b<=0.095`.  Each gap is tiled at width `0.01`
to retain recursive cancellation.  These 128 boxes resolve the full local
neighborhood around the formerly failing endpoints, not just the two original
orientations.

Together the three families contain 388 closed directed boxes.  Generation
and replay report 388 accepted and zero unresolved.  They cover continua; box
count is manifest structure rather than sampled evidence.

# Remaining complement

The tiled rectangle is not yet complete for intermediate anchors
`0.1<|m|<0.48`.  Gaps below `0.015` require face expansions rather than the
separated division chart.  Gaps above `0.095` require additional bands and
eventually the existing escape overlaps.  Accordingly the manifest records
`global_pf4_claim=false`.
