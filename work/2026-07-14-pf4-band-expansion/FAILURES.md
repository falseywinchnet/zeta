# Remaining regions

The repaired endpoint jet removed every failure targeted in this round.  The
following domains were not silently reclassified as failures; they were not
yet covered:

- the full gap rectangle `0.015<=a,b<=0.095` for intermediate anchors
  `0.1<|m|<0.48`;
- near-face strips `min(a,b)<0.015`, where recursive divided differences become
  poorly conditioned and a face expansion is the correct chart;
- separated gaps above `0.095`, which must be tiled toward the escape overlaps;
- anchors beyond `|m|=0.5` in the compact residual atlas.

No negative directed determinant was found in the boxes evaluated here.
