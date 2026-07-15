# Preserved failures and open complement

The first two-chart split of the simultaneous corner was too coarse at the
outer anchors.  In particular, mixed `0..0.0075` by `0.0075..0.015` cells had
interval enclosures meeting zero.  Narrowing both gaps to `0.00375` and using
the all-Hermite and separated charts according to conditioning resolved the
cover.  The coarse undecided enclosures were not treated as negative values.

Five earlier outer-anchor face boxes, and further coarse corner cells in the
final atlas, required one exact bisection in `m`.  The manifest contains only
their positive children, not the undecided parent boxes.

Broad-cell large-gap trials with `large_gap_tm.py` and
`reduced_large_gap.py` remain undecided.  They expose dependency loss in the
current coordinates; they are not counterexamples and are not certified
regions.

The unproved compact complement is:

- one or both gaps above `0.095`, pending overlap with the escape lemmas;
- anchors beyond `|m|=0.5`, pending the x-frame/tail transition.

No negative directed determinant was found in this round.
