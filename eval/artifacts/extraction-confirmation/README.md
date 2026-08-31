# Extraction confirmation artifacts

Committed confirmation metrics for the extraction branch. The numbers here were
produced by a complete `run-confirmation-grid.sh` run; `provenance.env` records
the exact commit, install manifest, corpora, scripts, and timeouts they belong
to. Treat the summaries as valid only together with that provenance file.

- `summary.tsv` — one row per (corpus, premise selector, prover) cell.
- `analysis.md` — aggregated rates (overall, per prover, per corpus, per
  premise selector) plus the eq_rect/WF watch points.
- `provenance.env` — the run's commit, timeouts, corpus modes, and the digests
  of the two files above.

Those three are written by the grid; this README is prose about them. It
therefore quotes as few numbers as it can, and `analysis.md` is authoritative
wherever the two disagree — the per-prover, per-corpus and per-selector tables
are deliberately not copied here, because a hand-maintained copy of a generated
table is stale from the next run onwards.

Regenerate from the raw checkpoints under `eval/results/confirmation` with
`./evaluate.sh confirmation` from `eval/` (or re-run the grid). On a fresh
switch, add `--setup` (or run `./install-external-libs.sh` first) to install
the external libraries the full corpora need.

## Headline: soundness

**Consistency hits: 0** across 14,800 consistency checks — every corpus, every
premise selector, both consistency provers. Each corpus's curated
`consistency-lemmas.txt` is checked by rewriting the conjecture to `$false` and
confirming E prover and Vampire cannot derive it from the selected axioms; a
`ContradictoryAxioms`/`Unsatisfiable` verdict is a reported consistency hit
requiring investigation, not an automatic hard gate on its own.
This includes the lemmas that previously exposed the Curry/Russell paradox
(`Proper`/`complement`) and the Type:Type/Hurkens universe collapse, both of
which are now blocked by the restored premise filters (see `features.ml`).

The list is curated rather than exhaustive on purpose: a vacuously true lemma is
refutable however faithful the translation is (the rewritten problem keeps the
goal's own hypotheses as axioms), so only lemmas with satisfiable hypotheses can
distinguish a sound translation from an unsound one.

## Performance

The grid is `{knn,nbayes} x {32,64,128,256,1024} x {E prover,Vampire,Z3,CVC4}`
over seven corpora, 280 cells, 276,840 generated problems.

| metric | value |
| --- | --- |
| Successful ATP attempts | 29.1% (80,454 / 276,840) |
| Reconstruction on successful ATP attempts | 87.3% (70,241 / 80,454) |

See `analysis.md` for the breakdown by prover, corpus and premise selector, and
for the eq_rect/WF watch points.
