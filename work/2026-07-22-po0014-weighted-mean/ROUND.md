# PO-0014 weighted-mean support closure

- Mode: advancement
- Date: 2026-07-22
- Model: OpenAI Codex
- Starting MIND IDs: R202–R205, CERT22, CERT26, CERT27
- Question: can the paper's S04 weighted-mean and positive-variation proof of
  the lower bound for `Lambda` be kernel-checked for the literal actual
  objects?
- Status: closed; focused compilation, standard-axiom audit, full build, and
  CERT28 replay complete

## Gates

- complete ordered real intervals, with no sampling;
- literal actual `A`, `M`, `q`, and `F2` objects;
- positive denominators proved before division;
- compact extrema and the positive-variation bound constructed, not assumed;
- no appeal to the already-proved `actual_lowerLambda_pos` in the displayed
  lower-bound proof.

## Result

- `actualM_eq_weightedMean` identifies the literal quotient with its exact
  `q`-weighted integral.
- `weightedMean_ge/le` and `actual_weightedMean_extrema` construct the compact
  extremizer bounds.
- `sub_le_integral_max_deriv` proves the general positive-variation estimate.
- `actual_lowerLambda_ge_integral_min` proves the displayed S04 lower bound.
- `actual_weightedMeanVariation_lowerLambda` proves the lower integral and
  maintained `Lambda` are strictly positive without importing the older
  `actual_lowerLambda_pos` conclusion.
- The focused build passes 3729 jobs; the full build passes 3736 jobs.
- All audited declarations use exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- CERT28 records and replays the six-declaration public audit.
