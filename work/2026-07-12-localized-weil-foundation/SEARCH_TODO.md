# Search cutoff refinement request

Observed ordinary-query relevance wall: `0.3279`.

Proposed constant: `1 - 1/e = 0.6321205588...`, corresponding to retained
relevance ratio `1/e = 0.3678794412...`.

The current documented rule stops when the next item has at most 36% of the
preceding item's relevance. Before changing it in a refine round, distinguish:

1. adjacent ratio: `score[n+1] / score[n] <= 1/e`;
2. leading ratio: `score[n+1] / score[1] <= 1/e`;
3. absolute cutoff: normalized `score[n+1] < 1/e`;
4. dropoff language: a drop of at least `1-1/e` is mathematically the same as
   adjacent retention at most `1/e`.

The reported wall at an absolute score of `0.3279` points toward either leading
ratio or absolute cutoff, not necessarily the existing adjacent-ratio rule.
Dogfood all three against the query that produced the wall before selecting one.
