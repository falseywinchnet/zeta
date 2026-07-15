# Preserved limitations

## Multiplicative angular denominators

A broad `(rho,theta)` box can make the generic Taylor enclosure of
`theta*rho` cross zero although both factors have positive interval lower
bounds.  The separated proof chart now uses affine gaps `(b,a)` instead.

## Larger anchors

With gap bands fixed at the manifested widths, boxes near `|m|=0.5` remain
undecided under the present degree-ten endpoint models.  For example, most
orientations tested on `m in [0.48,0.50]` or `[-0.50,-0.48]` span zero.  This
is not a negative determinant.  The rapidly varying theta jet requires either
smaller anchor cells or an x-frame endpoint evaluator.

## Broad gap rectangles

Rectangles simultaneously widening `m`, `a`, and `b` lose too much recursive
subtraction cancellation.  The two narrow manifested bands are proved; their
surrounding gap rectangle is not.
