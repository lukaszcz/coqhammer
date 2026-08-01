# Extraction confirmation analysis

Rows summarized: 280.
Grid: {knn,nbayes} x {32,64,128,256,1024} x {E prover,Vampire,Z3,CVC4} over 7 extraction corpora (color-vector, dependent-slice, dependent-stdlib, equations-examples, external-equations, stdlib-regression, stdpp).
Consistency hits: 0.
Consistency scope: the lemmas listed in each corpus's consistency-lemmas.txt, run with E prover and Vampire after rewriting the conjecture to `$false`. The list is curated rather than exhaustive because a vacuously true lemma is refutable however faithful the translation is: the rewritten problem keeps the goal's own hypotheses as axioms, so only lemmas with satisfiable hypotheses can distinguish a sound translation from an unsound one.

## Overall rates

| label | config | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | max_bytes | consistency_outputs | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| current | current | 205960 | 68442 | 33.2% | 58964 | 86.2% | 6483 | 727928.3 | 15985909 | 14660 | 0 |

## Per-prover ATP and reconstruction rates

| label | prover | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- |
| current | cvc4 | 51490 | 19676 | 38.2% | 16926 | 86.0% | 0 |
| current | eprover | 51490 | 15881 | 30.8% | 13637 | 85.9% | 0 |
| current | vampire | 51490 | 19982 | 38.8% | 17186 | 86.0% | 0 |
| current | z3 | 51490 | 12903 | 25.1% | 11215 | 86.9% | 0 |

## Per-corpus rates

| label | corpus | generated | theorems | success_rate | recon_successes | recon_rate_on_atp | def_constants | avg_bytes_mean | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| current | color-vector | 12480 | 3437 | 27.5% | 3120 | 90.8% | 1771 | 413566.8 | 0 |
| current | dependent-slice | 240 | 199 | 82.9% | 199 | 100.0% | 819 | 1018103.6 | 0 |
| current | dependent-stdlib | 69720 | 22063 | 31.6% | 16950 | 76.8% | 2718 | 844939.1 | 0 |
| current | equations-examples | 2840 | 573 | 20.2% | 395 | 68.9% | 1725 | 961108.2 | 0 |
| current | external-equations | 1960 | 602 | 30.7% | 366 | 60.8% | 1482 | 836591.7 | 0 |
| current | stdlib-regression | 44840 | 25454 | 56.8% | 23885 | 93.8% | 1565 | 405267.0 | 0 |
| current | stdpp | 73880 | 16114 | 21.8% | 14049 | 87.2% | 3153 | 615921.8 | 0 |

## Per-premise-selector/count rates

| label | premise | generated | theorems | success_rate | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- | --- | --- |
| current | knn-1024 | 20596 | 5744 | 27.9% | 4935 | 85.9% |
| current | knn-128 | 20596 | 7280 | 35.3% | 6255 | 85.9% |
| current | knn-256 | 20596 | 6713 | 32.6% | 5773 | 86.0% |
| current | knn-32 | 20596 | 7357 | 35.7% | 6345 | 86.2% |
| current | knn-64 | 20596 | 7541 | 36.6% | 6488 | 86.0% |
| current | nbayes-1024 | 20596 | 5672 | 27.5% | 4914 | 86.6% |
| current | nbayes-128 | 20596 | 7158 | 34.8% | 6178 | 86.3% |
| current | nbayes-256 | 20596 | 6646 | 32.3% | 5716 | 86.0% |
| current | nbayes-32 | 20596 | 7051 | 34.2% | 6086 | 86.3% |
| current | nbayes-64 | 20596 | 7280 | 35.3% | 6274 | 86.2% |

## Eq_rect / WF watch points

| label | problem | atp_successes | recon_successes | recon_rate_on_atp |
| --- | --- | --- | --- | --- |
| current | dep_eq_rect_refl | 40 | 40 | 100.0% |
| current | dep_idiv_zero | 0 | 0 | 0.0% |

## Current configuration

ATP success rate: 33.2%.
Reconstruction-on-ATP rate: 86.2%.
