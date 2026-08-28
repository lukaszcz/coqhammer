# Extraction confirmation analysis

Rows summarized: 280.
Grid: {knn,nbayes} x {32,64,128,256,1024} x {E prover,Vampire,Z3,CVC4} over 7 extraction corpora (color-vector, dependent-slice, dependent-stdlib, equations-examples, external-equations, stdlib-regression, stdpp).
Consistency hits: 0.
Consistency scope: the lemmas listed in each corpus's consistency-lemmas.txt, run with E prover and Vampire after rewriting the conjecture to `$false`. The list is curated rather than exhaustive because a vacuously true lemma is refutable however faithful the translation is: the rewritten problem keeps the goal's own hypotheses as axioms, so only lemmas with satisfiable hypotheses can distinguish a sound translation from an unsound one.

## Overall rates

| label | config | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | max_bytes | consistency_outputs | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| current | current | 276840 | 80454 | 29.1% | 70241 | 87.3% | 6934 | 678635.1 | 12501363 | 14800 | 0 |

## Per-prover ATP and reconstruction rates

| label | prover | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- |
| current | cvc4 | 69210 | 23996 | 34.7% | 20851 | 86.9% | 0 |
| current | eprover | 69210 | 17980 | 26.0% | 15642 | 87.0% | 0 |
| current | vampire | 69210 | 23919 | 34.6% | 20969 | 87.7% | 0 |
| current | z3 | 69210 | 14559 | 21.0% | 12779 | 87.8% | 0 |

## Per-corpus rates

| label | corpus | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| current | color-vector | 12480 | 3450 | 27.6% | 3128 | 90.7% | 1763 | 451232.5 | 0 |
| current | dependent-slice | 520 | 375 | 72.1% | 375 | 100.0% | 1132 | 970312.1 | 0 |
| current | dependent-stdlib | 70880 | 23770 | 33.5% | 18512 | 77.9% | 2573 | 860569.0 | 0 |
| current | equations-examples | 3320 | 695 | 20.9% | 487 | 70.1% | 1916 | 716298.9 | 0 |
| current | external-equations | 1960 | 682 | 34.8% | 370 | 54.3% | 1379 | 758977.4 | 0 |
| current | stdlib-regression | 44840 | 25760 | 57.4% | 24239 | 94.1% | 1425 | 422892.8 | 0 |
| current | stdpp | 142840 | 25722 | 18.0% | 23130 | 89.9% | 3226 | 570163.1 | 0 |

## Per-premise-selector/count rates

| label | premise | generated | theorems | success_rate | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- | --- | --- |
| current | knn-1024 | 27684 | 6871 | 24.8% | 5982 | 87.1% |
| current | knn-128 | 27684 | 8700 | 31.4% | 7556 | 86.9% |
| current | knn-256 | 27684 | 8098 | 29.3% | 7048 | 87.0% |
| current | knn-32 | 27684 | 8497 | 30.7% | 7424 | 87.4% |
| current | knn-64 | 27684 | 8874 | 32.1% | 7759 | 87.4% |
| current | nbayes-1024 | 27684 | 6462 | 23.3% | 5679 | 87.9% |
| current | nbayes-128 | 27684 | 8486 | 30.7% | 7433 | 87.6% |
| current | nbayes-256 | 27684 | 7839 | 28.3% | 6823 | 87.0% |
| current | nbayes-32 | 27684 | 8015 | 29.0% | 7015 | 87.5% |
| current | nbayes-64 | 27684 | 8612 | 31.1% | 7522 | 87.3% |

## Eq_rect / WF watch points

| label | problem | atp_successes | reconstructable | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- | --- |
| current | dep_eq_rect_refl | 40 | 40 | 40 | 100.0% |
| current | dep_idiv_zero | 5 | 5 | 5 | 100.0% |

## Current configuration

ATP success rate: 29.1%.
Reconstruction-on-ATP rate: 87.3%.
