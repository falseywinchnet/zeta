# Initial results

## Production retrieval baseline

The seven-case smoke benchmark passes 7/7:

- exact theorem lookup;
- two simultaneous spelling errors (`reimann kernal`);
- comma-anchor graph reranking;
- author/citation lookup;
- artifact-status lookup;
- raw advancement-work lookup;
- exact factoid ID.

This is a smoke test, not a quality estimate. A later corpus should add hard
negatives, paraphrases, relevance grades, reciprocal rank, and ablations for
lexical, fuzzy, and graph components.

Before raw source turns were enabled, the 121-document, 930-term MIND/work index
was 447,068 bytes, rebuilt in about 32 ms, and averaged about 2.19 ms per loaded
query. After adding all 278 lossless conversation turns, the index held 399
documents and 8,193 terms, occupied about 8.1 MB, rebuilt in about 326 ms, and
initially averaged about 23.4 ms per loaded query. Adding a character-bigram
candidate map removed the full-vocabulary edit-distance scan: the index grew to
about 9.5 MB while the same loaded-query mix fell to about 12.7 ms. The source layer is
comprehensive and visibly more expensive, but still interactive. If it grows by
orders of magnitude, compressed postings or SQLite FTS become justified.

## Continuous sequence sketch

The first deterministic content/edge/path sketch produced:

| relation | cosine | length distance |
|---|---:|---:|
| one typo | 0.709640 | 0.000000 |
| rephrase | 0.224289 | 0.000000 |
| reorder | 0.096615 | 0.000000 |
| unrelated | 0.000000 | 0.000000 |
| append | 0.785076 | 0.223144 |

It distinguishes reorder from append and keeps a typo closer than an unrelated
sentence. It handles the tested rephrase poorly. That is expected: random lexical
features do not create semantic equivalence. The length channel also cannot
distinguish equal-length relations by itself.

The experimental sketch is not ready for production ranking. Its next fair test is
candidate generation for spelling, shingling, or near-duplicate recovery, where its
feature geometry matches the task.

For the prefix walk `content position combination anchors meaning in context`, the
successive normalized step distances were 0.851, 0.819, 0.656, 0.614, 0.443, and
0.394. The tested walk therefore deforms continuously and each added token moves a
longer context less. This is one example, not a general smoothness guarantee; the
distribution across vocabulary, length, edits, and hash seeds still needs testing.
