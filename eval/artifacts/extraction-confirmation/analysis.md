# Extraction confirmation analysis

Rows summarized: 280.
Grid: {knn,nbayes} x {32,64,128,256,1024} x {E prover,Vampire,Z3,CVC4} over 7 extraction corpora (color-vector, dependent-slice, dependent-stdlib, equations-examples, external-equations, stdlib-regression, stdpp).
Consistency hits: 0.
Consistency scope: the lemmas listed in each corpus's consistency-lemmas.txt, run with E prover and Vampire after rewriting the conjecture to `$false`. The list is curated rather than exhaustive because a vacuously true lemma is refutable however faithful the translation is: the rewritten problem keeps the goal's own hypotheses as axioms, so only lemmas with satisfiable hypotheses can distinguish a sound translation from an unsound one.

## Overall rates

| label | config | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | max_bytes | consistency_outputs | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| current | current | 276560 | 80631 | 29.2% | 70195 | 87.1% | 6899 | 692559.4 | 12482310 | 14660 | 0 |

## Per-prover ATP and reconstruction rates

| label | prover | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- |
| current | cvc4 | 69140 | 23868 | 34.5% | 20689 | 86.7% | 0 |
| current | eprover | 69140 | 18277 | 26.4% | 15852 | 86.7% | 0 |
| current | vampire | 69140 | 23925 | 34.6% | 20899 | 87.4% | 0 |
| current | z3 | 69140 | 14561 | 21.1% | 12755 | 87.6% | 0 |

## Per-corpus rates

| label | corpus | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| current | color-vector | 12480 | 3421 | 27.4% | 3113 | 91.0% | 1764 | 453987.0 | 0 |
| current | dependent-slice | 240 | 204 | 85.0% | 204 | 100.0% | 822 | 1032493.9 | 0 |
| current | dependent-stdlib | 70880 | 24649 | 34.8% | 19079 | 77.4% | 2573 | 859651.3 | 0 |
| current | equations-examples | 3320 | 695 | 20.9% | 488 | 70.2% | 1917 | 747010.6 | 0 |
| current | external-equations | 1960 | 679 | 34.6% | 367 | 54.1% | 1380 | 762237.6 | 0 |
| current | stdlib-regression | 44840 | 26092 | 58.2% | 24526 | 94.0% | 1427 | 422429.3 | 0 |
| current | stdpp | 142840 | 24891 | 17.4% | 22418 | 90.1% | 3227 | 570105.9 | 0 |

## Per-premise-selector/count rates

| label | premise | generated | theorems | success_rate | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- | --- | --- |
| current | knn-1024 | 27656 | 6750 | 24.4% | 5879 | 87.1% |
| current | knn-128 | 27656 | 8673 | 31.4% | 7512 | 86.6% |
| current | knn-256 | 27656 | 8040 | 29.1% | 6978 | 86.8% |
| current | knn-32 | 27656 | 8445 | 30.5% | 7363 | 87.2% |
| current | knn-64 | 27656 | 8911 | 32.2% | 7768 | 87.2% |
| current | nbayes-1024 | 27656 | 6749 | 24.4% | 5898 | 87.4% |
| current | nbayes-128 | 27656 | 8538 | 30.9% | 7440 | 87.1% |
| current | nbayes-256 | 27656 | 7907 | 28.6% | 6872 | 86.9% |
| current | nbayes-32 | 27656 | 7998 | 28.9% | 6979 | 87.3% |
| current | nbayes-64 | 27656 | 8620 | 31.2% | 7506 | 87.1% |

## Eq_rect / WF watch points

| label | problem | atp_successes | reconstructable | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- | --- |
| current | dep_eq_rect_refl | 40 | 40 | 40 | 100.0% |
| current | dep_idiv_zero | 6 | 6 | 6 | 100.0% |

## Current configuration

ATP success rate: 29.2%.
Reconstruction-on-ATP rate: 87.1%.
