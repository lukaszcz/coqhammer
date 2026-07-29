# Extraction confirmation analysis

Rows summarized: 280.
Grid: {knn,nbayes} x {32,64,128,256,1024} x {E prover,Vampire,Z3,CVC4} over 7 extraction corpora (color-vector, dependent-slice, dependent-stdlib, equations-examples, external-equations, stdlib-regression, stdpp).
Consistency hits: 0.
Consistency scope: the lemmas listed in each corpus's consistency-lemmas.txt, run with E prover and Vampire after rewriting the conjecture to `$false`. The list is curated rather than exhaustive because a vacuously true lemma is refutable however faithful the translation is: the rewritten problem keeps the goal's own hypotheses as axioms, so only lemmas with satisfiable hypotheses can distinguish a sound translation from an unsound one.

## Overall rates

| label | config | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | max_bytes | consistency_outputs | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| current | current | 205960 | 67286 | 32.7% | 57708 | 85.8% | 6483 | 728341.2 | 15887295 | 14660 | 0 |

## Per-prover ATP and reconstruction rates

| label | prover | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- |
| current | cvc4 | 51490 | 19340 | 37.6% | 16548 | 85.6% | 0 |
| current | eprover | 51490 | 15242 | 29.6% | 13037 | 85.5% | 0 |
| current | vampire | 51490 | 18996 | 36.9% | 16251 | 85.5% | 0 |
| current | z3 | 51490 | 13708 | 26.6% | 11872 | 86.6% | 0 |

## Per-corpus rates

| label | corpus | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| current | color-vector | 12480 | 3504 | 28.1% | 3180 | 90.8% | 1771 | 413020.2 | 0 |
| current | dependent-slice | 240 | 199 | 82.9% | 199 | 100.0% | 819 | 1018154.9 | 0 |
| current | dependent-stdlib | 69720 | 21477 | 30.8% | 16279 | 75.8% | 2718 | 848835.4 | 0 |
| current | equations-examples | 2840 | 578 | 20.4% | 396 | 68.5% | 1725 | 949254.5 | 0 |
| current | external-equations | 1960 | 612 | 31.2% | 376 | 61.4% | 1482 | 841814.2 | 0 |
| current | stdlib-regression | 44840 | 24888 | 55.5% | 23361 | 93.9% | 1565 | 406040.6 | 0 |
| current | stdpp | 73880 | 16028 | 21.7% | 13917 | 86.8% | 3153 | 621268.5 | 0 |

## Per-premise-selector/count rates

| label | premise | generated | theorems | success_rate | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- | --- | --- |
| current | knn-1024 | 20596 | 5660 | 27.5% | 4844 | 85.6% |
| current | knn-128 | 20596 | 7102 | 34.5% | 6075 | 85.5% |
| current | knn-256 | 20596 | 6674 | 32.4% | 5718 | 85.7% |
| current | knn-32 | 20596 | 7132 | 34.6% | 6131 | 86.0% |
| current | knn-64 | 20596 | 7294 | 35.4% | 6252 | 85.7% |
| current | nbayes-1024 | 20596 | 5698 | 27.7% | 4930 | 86.5% |
| current | nbayes-128 | 20596 | 7062 | 34.3% | 6048 | 85.6% |
| current | nbayes-256 | 20596 | 6720 | 32.6% | 5735 | 85.3% |
| current | nbayes-32 | 20596 | 6855 | 33.3% | 5898 | 86.0% |
| current | nbayes-64 | 20596 | 7089 | 34.4% | 6077 | 85.7% |

## Eq_rect / WF watch points

| label | problem | atp_successes | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- |
| current | dep_eq_rect_refl | 40 | 40 | 100.0% |
| current | dep_idiv_zero | 0 | 0 | 0.0% |

## Current configuration

ATP success rate: 32.7%.
Reconstruction-on-ATP rate: 85.8%.
