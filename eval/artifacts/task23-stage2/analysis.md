# Phase 6 Stage 2 confirmation analysis

Rows summarized: 240.
Grid: {knn,nbayes} x {32,64,128,256,1024} x {E,Vampire,Z3,CVC4} over the three committed Phase-6 corpora.
Consistency hits: 0.
Consistency scope: exhaustive scan of every generated Stage-2 problem in the committed corpora with E and Vampire after rewriting the conjecture to `$false`.

## Overall rates

| label | config | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | max_bytes | consistency_outputs | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-merge-base | baseline | 440 | 196 | 44.5% | 196 | 100.0% | 1113 | 421605.4 | 3470827 | 220 | 0 |
| stage2-winner | loo-erasure-guards-decl-skips | 440 | 385 | 87.5% | 385 | 100.0% | 1117 | 548698.3 | 8846736 | 220 | 0 |

## Per-prover ATP and reconstruction rates

| label | prover | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-merge-base | cvc4 | 110 | 49 | 44.5% | 49 | 100.0% | 0 |
| baseline-merge-base | eprover | 110 | 50 | 45.5% | 50 | 100.0% | 0 |
| baseline-merge-base | vampire | 110 | 50 | 45.5% | 50 | 100.0% | 0 |
| baseline-merge-base | z3 | 110 | 47 | 42.7% | 47 | 100.0% | 0 |
| stage2-winner | cvc4 | 110 | 85 | 77.3% | 85 | 100.0% | 0 |
| stage2-winner | eprover | 110 | 100 | 90.9% | 100 | 100.0% | 0 |
| stage2-winner | vampire | 110 | 100 | 90.9% | 100 | 100.0% | 0 |
| stage2-winner | z3 | 110 | 100 | 90.9% | 100 | 100.0% | 0 |

## Per-corpus rates

| label | corpus | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-merge-base | dependent-slice | 240 | 79 | 32.9% | 79 | 100.0% | 836 | 565641.6 | 0 |
| baseline-merge-base | external-equations | 80 | 0 | 0.0% | 0 | 0.0% | 259 | 373819.5 | 0 |
| baseline-merge-base | stdlib-regression | 120 | 117 | 97.5% | 117 | 100.0% | 561 | 325355.1 | 0 |
| stage2-winner | dependent-slice | 240 | 191 | 79.6% | 191 | 100.0% | 839 | 991143.0 | 0 |
| stage2-winner | external-equations | 80 | 74 | 92.5% | 74 | 100.0% | 261 | 322364.0 | 0 |
| stage2-winner | stdlib-regression | 120 | 120 | 100.0% | 120 | 100.0% | 562 | 332587.9 | 0 |

## Per-premise-selector/count rates

| label | premise | generated | theorems | success_rate | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- | --- | --- |
| baseline-merge-base | knn-1024 | 44 | 19 | 43.2% | 19 | 100.0% |
| baseline-merge-base | knn-128 | 44 | 20 | 45.5% | 20 | 100.0% |
| baseline-merge-base | knn-256 | 44 | 21 | 47.7% | 21 | 100.0% |
| baseline-merge-base | knn-32 | 44 | 19 | 43.2% | 19 | 100.0% |
| baseline-merge-base | knn-64 | 44 | 20 | 45.5% | 20 | 100.0% |
| baseline-merge-base | nbayes-1024 | 44 | 19 | 43.2% | 19 | 100.0% |
| baseline-merge-base | nbayes-128 | 44 | 20 | 45.5% | 20 | 100.0% |
| baseline-merge-base | nbayes-256 | 44 | 19 | 43.2% | 19 | 100.0% |
| baseline-merge-base | nbayes-32 | 44 | 19 | 43.2% | 19 | 100.0% |
| baseline-merge-base | nbayes-64 | 44 | 20 | 45.5% | 20 | 100.0% |
| stage2-winner | knn-1024 | 44 | 39 | 88.6% | 39 | 100.0% |
| stage2-winner | knn-128 | 44 | 40 | 90.9% | 40 | 100.0% |
| stage2-winner | knn-256 | 44 | 40 | 90.9% | 40 | 100.0% |
| stage2-winner | knn-32 | 44 | 35 | 79.5% | 35 | 100.0% |
| stage2-winner | knn-64 | 44 | 37 | 84.1% | 37 | 100.0% |
| stage2-winner | nbayes-1024 | 44 | 39 | 88.6% | 39 | 100.0% |
| stage2-winner | nbayes-128 | 44 | 40 | 90.9% | 40 | 100.0% |
| stage2-winner | nbayes-256 | 44 | 40 | 90.9% | 40 | 100.0% |
| stage2-winner | nbayes-32 | 44 | 38 | 86.4% | 38 | 100.0% |
| stage2-winner | nbayes-64 | 44 | 37 | 84.1% | 37 | 100.0% |

## Eq_rect / WF watch points

| label | problem | atp_successes | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- |
| baseline-merge-base | dep_eq_rect_refl | 0 | 0 | 0.0% |
| stage2-winner | dep_eq_rect_refl | 37 | 37 | 100.0% |
| baseline-merge-base | dep_idiv_zero | 0 | 0 | 0.0% |
| stage2-winner | dep_idiv_zero | 0 | 0 | 0.0% |

## Newly found winner proofs

Winner ATP successes absent from baseline: 191.
Reconstructed among those: 191 (100.0%).

## Definitional-equation footprint

Unique `$_def_*` constants in baseline problems: 1113.
Unique `$_def_*` constants in winner problems: 1117.
Winner-only constants gaining `$_def_*` equations: 4.
Sample winner-only constants: Corelib.BinNums.PosDef.Pos.add_carry, Corelib.Init.Wf.Acc_rect, Stdlib.Sets.Relations_1.Order_rect, program_equations_smoke.fuel_drop.
Baseline-only constants absent from winner generated problems: 0.

## Verdict inputs

Overall ATP delta (winner - baseline): +43.0 percentage points.
Overall reconstruction-on-ATP delta: +0.0 percentage points.
Dependent-slice ATP delta: +46.7 percentage points.
Stdlib-regression ATP delta: +2.5 percentage points.
External Program/WF ATP delta: +92.5 percentage points.
