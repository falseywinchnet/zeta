# Next experiments

## Retrieval baseline

Build at least 100 relevance-judged queries split among exact ID, author, theorem,
misspelling, phrase, paraphrase, raw-source recovery, and comma-anchor context.
Record MRR, recall at 5/10, latency, and failure class. Ablate field weighting,
character correction, source prior, phrase bonus, and graph distance separately.

## ConeDAG follow-ups

The present benchmark supports local deformation and order discrimination, but
the next round should:

1. expand the 12-query semantic set to at least 100 independently judged queries;
2. run at least 10 seeds and report confidence intervals;
3. return minimum-edit ambiguity classes and test graph-context tie-breaking;
4. measure approximate-neighbor latency and recall at 10k, 100k, and 1m records;
5. measure collision and near-collision rates at each width;
6. test directional containment fusion with BM25F and graph anchors;
7. compare learned or external semantic embeddings only if they can be stored and
   reproduced locally;
8. replace cubic degree-3 enumeration with a streaming bottom-k construction and
   prove that its sampling distribution is unchanged.

Keep exact anchors. Report distributions and failure classes, not selected pairs.

## Training prototype

Before training, define the alignment exactly: which context prefix produces which
target. Add a test that perturbs the target while holding the legal prefix fixed;
the fingerprint must not change. Compare fixed and learned `direction_proj`
explicitly. Separate normalized direction from length-dependent magnitude and
measure whether any benefit survives removal of target leakage.

## Adoption gate

Do not add ConeDAG to production MIND unless a fused search improves judged recall
or latency over the exact index at a stated resource budget. Any returned candidate
must still be verified against the exact stored record and graph.
