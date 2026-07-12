# ConeDAG experimental report

## Decision

Keep ConeDAG as an experimental candidate generator. Do not replace MIND search.
It substantially improves recovery under spelling, insertion, deletion, crop,
and adversarial word-order variants at equal sketch width, but it loses to the
production lexical/graph search on the small semantic-query set.

## Main retrieval benchmark

The hard benchmark used 180 exact MIND records, six transformations of each, and
six order-altered siblings per original: 1,258 candidates and 1,080 queries.
Every sketch is approximately equal width (384–390 dimensions).

| Method | MRR | Recall@1 | Recall@5 |
|---|---:|---:|---:|
| Word bag | 0.735 | 0.615 | 0.934 |
| Character 3–5 grams | 0.882 | 0.797 | 1.000 |
| Prior sequence sketch | 0.799 | 0.652 | 0.987 |
| ConeDAG | **0.955** | **0.919** | **1.000** |

The first 180-record benchmark without order siblings was rejected as too easy:
both bag and character baselines were perfect. The adversarial siblings are
necessary to measure position and combination rather than corpus uniqueness.

## Geometry

Across 120 records, mean hyperspherical distance from the original was 0.156 for
an adjacent swap, 0.193 for deletion, 0.205 for insertion, 0.259 for a spelling
edit, 0.292 for append, and 0.685 for crop. Unrelated-record distance averaged
1.277. Mean one-token prefix steps fell from 0.676 at lengths 2–5 to 0.184 at
lengths 21–40, the desired smooth-deformation behavior.

Deletion is the weak relation: the exact target beat its adversarial siblings in
only 50.8% of deletion cases in the geometry audit. This is consistent with
deletion shifting every following relative position.

## Ablations

On 60 originals with order siblings, Recall@1 was 0.722 for content alone, 0.836
for path alone, 0.908 for position alone, 0.917 for content+position, 0.928 for
path+position, and 0.919 for the default full mixture. Width improved Recall@1
from 0.872 at 102 dimensions to 0.928 at 774. Four dyadic levels reached 0.919;
a fifth added no gain. Five seeds ranged from 0.900 to 0.931, so results are not
fully seed-stable.

The selected path weight is 0.20. In a separate grid it achieved 0.920 Recall@1
and 0.540 deletion Recall@1; heavier path weights degraded both. This is retained
despite the small aggregate ablation difference because the larger benchmark and
relation grid cover more cases.

Shifted-Legendre position modes were smoother in the earliest prefix range but
worse at retrieval: soft dyadic position reached 0.925 Recall@1 on 100 originals,
versus about 0.900 for moments and 0.905 for a hybrid. Soft bins remain default.

## Corrupted spelling and anagrams

For the supplied corrupted sentence, the prior sketch cosine was 0.048 and the
default ConeDAG cosine was 0.233. Character unigrams and bigrams provided the
gain. Anagram signatures raised it to 0.286 but lowered overall retrieval, so
they remain an opt-in experiment.

## Semantic boundary

Twelve manually judged paraphrase queries over factoids produced:

| Method | MRR | Recall@1 | Recall@5 | Recall@10 |
|---|---:|---:|---:|---:|
| Word bag | 0.754 | 0.667 | 0.833 | 0.833 |
| Character grams | 0.751 | 0.667 | 0.917 | 0.917 |
| Prior sequence sketch | 0.511 | 0.333 | 0.750 | 0.750 |
| ConeDAG | 0.672 | 0.583 | 0.833 | 0.833 |
| MIND search | **0.805** | **0.750** | 0.833 | **0.917** |

This set is too small for a general semantic claim, but it is sufficient to deny
the current adoption gate. ConeDAG complements exact lexical and graph retrieval;
it does not replace them.

Raw measurements and executable benchmarks are in this directory and
`../experiments/`.
