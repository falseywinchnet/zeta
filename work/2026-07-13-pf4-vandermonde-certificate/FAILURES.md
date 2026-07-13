# Preserved failures

## Source mismatch

The first inspection followed a different published PF5 argument.  It was
discarded when the intended source was identified as CITE2.  No conclusion from
the mismatched paper is used here.

## Natural interval extension

`certify_jhat_rectangle.py` applies a centered first-order enclosure to a broad
rectangle.  Dependency loss in differences such as `s(x)-s(m)` makes useful
leaf widths extremely small.  The run reaches its cell budget without a global
certificate.  Increasing that budget would be a computational sweep, not a
mathematical improvement.

## Broad high-jet balls

`certify_jhat_divided.py` correctly removes gap denominators using integral
means, but obtains high derivatives by direct evaluation on broad balls.
Correlation loss in the cumulant recursion inflates the highest jets and
produces indeterminate enclosures.  The required repair is a centered
univariate Taylor-jet certificate feeding a dependency-aware multivariate
Taylor model.
