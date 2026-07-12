# Production search promotion

## Public query surface

- `R<num>` resolves reversibly to stored `F%06d` references.
- `CITE<num>` resolves reversibly to stored `C%06d` citation boundaries.
- Exact public or legacy identities bypass ranking and return the full tracemap or
  citation object.
- Ordinary text searches references, citations, topic leaves, progress, work,
  and raw source turns in one pool.

No graph identity or support edge was rewritten. Public aliases are presentation
and command identities over the validated JSON graph.

## Relevance

The production utility combines normalized lexical/graph relevance at weight
0.78 and promoted ConeDAG plus directional containment at weight 0.22. Kind
priors remain explicit. Containment is activated only when the query is shorter
than a candidate. Every component is emitted by `--explain`.

The original P000007 policy stopped before the first adjacent item satisfying

\[
\frac{\operatorname{relevance}_{n+1}}
{\operatorname{relevance}_{n}}\le 0.36.
\]

Under that historical policy, `--limit` was a safety ceiling, default 25, and
the ratio boundary was inclusive.

The current hybrid secretary policy supersedes that boundary:

1. Count the results with absolute relevance at least `1/e`.
2. If the count is at least eight, return the complete `score >= 1/e` prefix.
3. If the count is below eight, stop before the first adjacent result satisfying
   `score[n+1] / score[n] < 1/e`, a drop greater than `1-1/e`.
4. If neither boundary fires first, `--limit` remains the safety ceiling.

The absolute branch prevents a gradual tail from overrunning a well-populated
high-relevance set. The adjacent fallback avoids returning too little when a
query has fewer than eight high-relevance candidates.

## Static index

Index version 3 stores lexical postings, the causal/taxonomic graph, a 390-value
ConeDAG vector, and the 256-entry stratified containment sketch for every record.
Similarity encoding is bounded to the first 48 normalized tokens; lossless
lexical indexing remains untruncated.

On the P000006 corpus:

- 403 indexed records;
- 18,175,734-byte JSON index;
- 7.3-second rebuild;
- 0.15-second load;
- 26.4 ms median and 62.6 ms p95 query time across 140 warm searches;
- 21.6 mean returned records for the seven-query suite;
- the ratio boundary fired in 14.3% of those searches, otherwise the safety
  ceiling applied.

## Retrieval checks

The existing seven-case lexical, typo, graph-anchor, work, and identity benchmark
remains 7/7. The 12-query semantic benchmark remains 75% Recall@1, 83.3%
Recall@5, and 91.7% Recall@10. Exact `R14` and `CITE4` manual checks returned the
complete expected objects.

## Limits

ConeDAG remains lexical/structural, not semantic. The 48-token structural bound
means deep passages in long raw records rely on the untruncated inverted index.
The historical 36% adjacent boundary often did not fire on gradually decaying
result lists. The current hybrid retains an explicit safety ceiling for the same
case.
