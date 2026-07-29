# Extraction confirmation artifacts

Committed confirmation metrics for the extraction branch. The numbers here were
produced by a complete `run-confirmation-grid.sh` run; `provenance.env` records
the exact commit, install manifest, corpora, scripts, and timeouts they belong
to. Treat the summaries as valid only together with that provenance file.

- `summary.tsv` — one row per (corpus, premise selector, prover) cell.
- `analysis.md` — aggregated rates (overall, per prover, per corpus, per
  premise selector) plus the eq_rect/WF watch points.
- `provenance.env` — commit `bf435563`, prover timeout 10s, consistency
  timeout 2s, all seven corpora in `full` mode.

Regenerate from the raw checkpoints under `eval/results/confirmation` with
`../../evaluate.sh confirmation` from `eval/` (or re-run the grid). On a fresh
switch, add `--setup` (or run `eval/install-external-libs.sh` first) to install
the external libraries the full corpora need.

## Headline: soundness

**Consistency hits: 0** across 14,660 consistency checks — every corpus, every
premise selector, both consistency provers. Each corpus's curated
`consistency-lemmas.txt` is checked by rewriting the conjecture to `$false` and
confirming E prover and Vampire cannot derive it from the selected axioms; a
`ContradictoryAxioms`/`Unsatisfiable` verdict would be a fatal soundness hit.
This includes the lemmas that previously exposed the Curry/Russell paradox
(`Proper`/`complement`) and the Type:Type/Hurkens universe collapse, both of
which are now blocked by the restored premise filters (see `features.ml`).

The list is curated rather than exhaustive on purpose: a vacuously true lemma is
refutable however faithful the translation is (the rewritten problem keeps the
goal's own hypotheses as axioms), so only lemmas with satisfiable hypotheses can
distinguish a sound translation from an unsound one.

## Performance

The grid is `{knn,nbayes} x {32,64,128,256,1024} x {E prover,Vampire,Z3,CVC4}`
over seven corpora, 280 cells, 205,960 generated problems.

| metric | value |
| --- | --- |
| ATP success rate | 32.7% (67,286 / 205,960) |
| Reconstruction on ATP-proved goals | 85.8% (57,708 / 67,286) |

Per prover (ATP success / reconstruction-on-ATP):

| prover | success | recon-on-ATP |
| --- | --- | --- |
| CVC4 | 37.6% | 85.6% |
| Vampire | 36.9% | 85.5% |
| E prover | 29.6% | 85.5% |
| Z3 | 26.6% | 86.6% |

Per corpus (ATP success / reconstruction-on-ATP):

| corpus | success | recon-on-ATP |
| --- | --- | --- |
| stdlib-regression | 55.5% | 93.9% |
| dependent-slice | 82.9% | 100.0% |
| external-equations | 31.2% | 61.4% |
| dependent-stdlib | 30.8% | 75.8% |
| color-vector | 28.1% | 90.8% |
| stdpp | 21.7% | 86.8% |
| equations-examples | 20.4% | 68.5% |

See `analysis.md` for the per-premise-selector breakdown and the full tables.
