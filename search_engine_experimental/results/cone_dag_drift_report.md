# ConeDAG drift report

## Decision

Retain the symmetric ConeDAG vector. Add stratified subsequence containment as an
experimental reranker only when the query has fewer tokens than a candidate.
Use weight 0.20. Evaluate deletions with strict identity and minimum-edit
equivalence.

## Failed direct channel

An added hyperspherical channel containing global order pairs and winnowed local
anchors failed. On 60 originals, baseline deletion Recall@1 was 0.567. Equal-
dimension variants ranged from 0.183 to 0.417; the best 518-dimensional variant
reached 0.517. Symmetric cosine still penalized the undeleted candidate's extra
evidence, while the added channel diluted useful position discrimination.

## Ambiguity audit

The original middle-deletion benchmark was not a valid unique-ID test. Every one
of 180 queries had multiple minimum-edit sibling parents, averaging 2.81. For
adjacent double deletion, every query was ambiguous, averaging 3.01 parents.
Baseline's earlier 50–57% strict deletion score was mostly arbitrary selection
inside these equivalence classes. Its edit-equivalent deletion score was 99.8%.

## Drift stress benchmark

The final benchmark used 180 originals, 1,258 candidates, and 2,160 queries:
single deletions at five relative positions, adjacent and separated double
deletions, four separated deletions, three insertion positions, and a middle crop.

| Method | Strict Recall@1 | Edit-equivalent Recall@1 | Deletion Recall@1 |
|---|---:|---:|---:|
| Symmetric ConeDAG | 0.920 | 0.997 | 0.998 |
| + directional containment, 0.10 | 0.913 | 1.000 | 0.999 |
| + directional containment, 0.20 | 0.906 | **1.000** | **1.000** |

Strict identity falls because containment can select another equally minimal
parent. This is not a retrieval failure under erased evidence. At weight 0.20,
every query returned a minimum-edit sibling first. Insertions remain on symmetric
ConeDAG and retain perfect top-1 in this benchmark.

The sketch stores 256 total 128-bit hashes, stratified 60% to global degree-2/3
subsequences and 40% to contiguous degree-2–5 paths.

## Estimator audit

Across 180 random record pairs, five seeds, and sample sizes 32–256, the
256-sample estimator had mean absolute error 0.0021–0.0039 and 95th-percentile
error 0.0099–0.0164. The ordered-subsequence stratum returned exact containment
one on every tested deletion/crop subset at sample sizes 64 and above. At size 32,
one of 1,200 seed/case combinations had no sampled query order feature and
returned zero, the declared zero-sample behavior.

## Remaining work

- Test independently judged queries instead of generated siblings.
- Measure latency and candidate recall at larger corpus sizes.
- Replace repeated combination enumeration with dynamic or streaming bottom-k
  generation for long records.
- Calibrate weight 0.20 on a held-out corpus.
- Return ambiguity classes explicitly so graph context can break ties.
