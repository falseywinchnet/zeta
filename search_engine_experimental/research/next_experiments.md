# Next experiments

## Retrieval baseline

Build at least 100 relevance-judged queries split among exact ID, author, theorem,
misspelling, phrase, paraphrase, raw-source recovery, and comma-anchor context.
Record MRR, recall at 5/10, latency, and failure class. Ablate field weighting,
character correction, source prior, phrase bonus, and graph distance separately.

## Sequence sketch

Test these hypotheses across at least 10 hash seeds:

1. one-character edits move less than unrelated replacements;
2. one-token append distance decreases in expectation as prefix length grows;
3. reorder distance remains greater than append distance at matched length;
4. collision rate stays below a declared threshold for the target corpus;
5. candidate recall improves over character n-grams at equal memory.

Vary character versus word units, normalization, edge width, path depth, and
absolute-position phase. Report distributions, not hand-picked pairs.

## Training prototype

Before training, define the alignment exactly: which context prefix produces which
target. Add a test that perturbs the target while holding the legal prefix fixed;
the fingerprint must not change. Compare fixed and learned `direction_proj`
explicitly. Separate normalized direction from length-dependent magnitude and
measure whether any benefit survives removal of target leakage.

## Adoption gate

Do not add a continuous sketch to production MIND unless it improves judged recall
or latency over the exact index at a stated resource budget. Any returned candidate
must still be verified against the exact stored record and graph.
