# Extraction confirmation artifacts

No confirmation metrics for the current source tree are committed here.

The previous `analysis.md` and `summary.tsv` were produced on 2026-07-09 from
sample corpora with:

- selected configuration `loo-erasure-guards-decl-skips`, built from commit
  `e17084b2dcfb5c79b3240cca8fdf18c753725ae4`;
- baseline commit `ce33d4479adc520804aa56740b8ab0ae8efbf6ae`;
- 10-second prover and 2-second consistency-check timeouts.

They were committed by `be4530177d27c27d8f7748d534f0f4f2d520d827`
and later renamed into this directory. The translator and extraction corpora
changed after that run, so those numbers do not describe the current tree.
They remain available in Git history, but must not be presented as current
confirmation evidence. Locally retained raw checkpoints have the same stale
inputs and cannot be used to regenerate current metrics.

Run `eval/run-confirmation-grid.sh` to create new `analysis.md`, `summary.tsv`,
and `provenance.env`. Commit replacements only after a complete run; the
provenance file ties the aggregates to the source and installed plugin revisions,
configuration, corpus content, timeouts, scripts, and successful checkpoint set.
