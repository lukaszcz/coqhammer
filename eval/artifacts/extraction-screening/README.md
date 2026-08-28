# Extraction screening artifacts

Committed TASK_10 extraction-option screening metrics for candidate commit
`5cb0bfd36c7f14149ee2fd9f09d188a8c69b1a6a`. The complete sample grid uses
15 labels over three corpora, premise counts `{64,256,1024}`, and E prover and
Vampire. Its consistency watch point is `knn-64` with both provers.

- `summary.tsv` — one row per (label, corpus, premise count, prover) cell;
- `analysis.md` — the generated configuration, corpus, and prover aggregates;
- `provenance.env` — commit, configuration manifests, corpus digests, harness
  digests, timeouts, and digests of the two generated files above.

The headline result is 86/108 successful ATP attempts and 15/18 goals for the
clean `current` winner, versus 80/108 and 14/18 for the clean controlled
`all-on + declaration skips` reference. The scan reports eight consistency
hits, all on `dep_ibval_bound` in four no-declaration-skip configurations;
`current` and every declaration-skip configuration report zero hits. See
`analysis.md` and `eval/artifacts/task10-comparison/report.md` for the precise
scope and interpretation.

These files are tracked because TASK_10 cites this option sweep. Regenerate them
with `./evaluate.sh screening` from `eval/`; do not combine a regenerated
summary or analysis with the existing provenance.
