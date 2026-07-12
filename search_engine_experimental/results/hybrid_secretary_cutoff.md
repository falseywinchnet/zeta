# Hybrid secretary cutoff

## Rule

Let ranked scores satisfy `s_1 >= s_2 >= ...`, let `tau=1/e`, and let the
safety ceiling be `L`.

1. Compute `m = #{i : s_i >= tau}` over the ranked candidate pool.
2. If `m >= 8`, return the first `min(m,L)` results.
3. If `m < 8`, return the prefix ending immediately before the first `i+1`
   satisfying `s_(i+1)/s_i < tau`.
4. If no fallback break appears before `L`, return the first `L` results.

The floor comparison is inclusive. The fallback drop is strict: retention
exactly `1/e` does not stop the list.

## Interpretation

The primary branch asks whether a secretary-sized set of eight already clears
the absolute relevance floor. If so, every result clearing the same floor is
kept. If not, absolute relevance alone is too sparse, so the first relative
loss greater than `1-1/e` terminates the list.

## Tests

Production tests cover:

- exactly eight results at or above `1/e`;
- the under-eight adjacent fallback;
- strictness at an adjacent ratio exactly `1/e`;
- the `--limit` ceiling when no fallback break occurs;
- unrestricted merged-search testing through a zero floor and secretary count
  one.

`MIND SEARCH --explain` reports `score-floor` or `adjacent-fallback`, the
qualifying count, threshold, and excluded next score.
