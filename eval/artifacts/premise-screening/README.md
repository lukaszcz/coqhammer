# Premise-selection screening artifacts

Committed screening metrics for the definitional-premise work. The numbers here
were produced by a complete `run-premise-screening-grid.sh` run;
`provenance.env` records the exact commit, install manifest, corpora, scripts,
and timeouts they belong to. Treat the summaries as valid only together with
that provenance file.

This is the one screening grid whose artifacts are tracked, because the branch's
premise-selection claim rests on it; every other screening summary is rerun
rather than cited (see the artifact policy in `eval/README.md`).

- `summary.tsv` — one row per (label, scope, corpus, premise selector, prover,
  occurrence bucket) cell, where a label is one
  `DefinitionPremises`/`DefinitionFeatures` pair.
- `analysis.md` — solved-goal tables against the `ds0-df0` baseline
  (aggregate, per corpus, per occurrence bucket), the goal-level N=32
  regression guard, and the attempt-level diagnostics.
- `provenance.env` — the run's commit, timeouts, corpus modes, stage and
  attempt counts, and the digests of the two files above.

Those three are written by the grid; this README is prose about them. It
therefore quotes as few numbers as it can, and `analysis.md` is authoritative
wherever the two disagree — the per-corpus and per-bucket tables are
deliberately not copied here, because a hand-maintained copy of a generated
table is stale from the next run onwards.

Regenerate with `./run-premise-screening-grid.sh --full-corpus` from `eval/`.
On a fresh switch, run `./install-external-libs.sh` there first to install the
external libraries the full corpora need.

## What the grid measures

`DefinitionPremises {0,8,32} x DefinitionFeatures {0,4,16}`, nine labels over
one shared `current` install, each evaluated with `{knn,nbayes}` at `{32,1024}`
premises against E prover and Vampire, over `stdlib-regression`,
`dependent-slice` and `external-equations`.

The decision metric is solved `GoalKey = (corpus, relative goal path)` sets: a
goal counts as solved when any active selector/prover attempt solves it, and
gains and losses are paired set differences against `ds0-df0`. Attempt totals
are reported alongside but are diagnostics, not decisions. Enabling the
definitional slots is a solved-goal gain at every label above the baseline; the
gain saturates well before `ds32`, and it concentrates in the rare-occurrence
buckets the slots are meant to reach.

## Reading the provenance

`provenance.env` classifies this run's evidence rather than asserting it is a
stock grid: `measurement_policy` and `evidence_classification` record that the
goal-incidence diagnostic and part of the success-checkpoint protocol are
non-standard and not resumable, and the stage, attempt, marker and consistency
counts state exactly how much of the factorial was covered. Read those fields
before quoting the tables; they, not this README, bound what the numbers claim.
