# Extraction screening analysis

Rows summarized: 270.
Consistency hits: 8.

## Overall configuration ranking

| label | config | decl_skips | generated | theorems | success_rate | def_constants_mean | avg_bytes_mean | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| current | current | true | 108 | 86 | 79.6% | 307.3 | 866592.6 | 0 |
| screening-loo-erasure-guards-decl-skips | loo-erasure-guards | true | 108 | 86 | 79.6% | 307.3 | 866592.6 | 0 |
| screening-loo-erasure-guards | loo-erasure-guards | false | 108 | 83 | 76.9% | 307.3 | 866689.3 | 2 |
| screening-all-on-decl-skips | all-on | true | 108 | 80 | 74.1% | 307.3 | 877758.6 | 0 |
| screening-loo-rigid-clash-pruning-decl-skips | loo-rigid-clash-pruning | true | 108 | 80 | 74.1% | 307.7 | 878038.8 | 0 |
| screening-loo-indexed-families | loo-indexed-families | false | 108 | 79 | 73.1% | 307.3 | 873921.6 | 0 |
| screening-loo-indexed-families-decl-skips | loo-indexed-families | true | 108 | 79 | 73.1% | 307.3 | 873847.6 | 0 |
| screening-all-on | all-on | false | 108 | 78 | 72.2% | 307.3 | 877857.6 | 2 |
| screening-loo-rigid-clash-pruning | loo-rigid-clash-pruning | false | 108 | 78 | 72.2% | 307.7 | 878137.5 | 2 |
| screening-loo-prop-case-erasure-decl-skips | loo-prop-case-erasure | true | 108 | 74 | 68.5% | 303.6 | 865828.0 | 0 |
| screening-loo-prop-case-erasure | loo-prop-case-erasure | false | 108 | 71 | 65.7% | 303.6 | 865927.2 | 2 |
| screening-loo-refinement-types | loo-refinement-types | false | 108 | 67 | 62.0% | 307.3 | 821135.7 | 0 |
| screening-loo-refinement-types-decl-skips | loo-refinement-types | true | 108 | 67 | 62.0% | 307.3 | 821135.7 | 0 |
| screening-all-off | all-off | false | 108 | 61 | 56.5% | 303.9 | 805136.7 | 0 |
| screening-all-off-decl-skips | all-off | true | 108 | 61 | 56.5% | 303.9 | 805136.7 | 0 |

## Per-corpus rates

| label | corpus | generated | theorems | success_rate | def_constants_mean | avg_bytes_mean | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- |
| current | dependent-slice | 78 | 56 | 71.8% | 575.0 | 1493403.6 | 0 |
| current | external-equations | 12 | 12 | 100.0% | 108.7 | 448222.3 | 0 |
| current | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 658151.9 | 0 |
| screening-all-off | dependent-slice | 78 | 37 | 47.4% | 570.0 | 1390401.6 | 0 |
| screening-all-off | external-equations | 12 | 6 | 50.0% | 108.0 | 443755.5 | 0 |
| screening-all-off | stdlib-regression | 18 | 18 | 100.0% | 233.7 | 581253.0 | 0 |
| screening-all-off-decl-skips | dependent-slice | 78 | 37 | 47.4% | 570.0 | 1390401.6 | 0 |
| screening-all-off-decl-skips | external-equations | 12 | 6 | 50.0% | 108.0 | 443755.5 | 0 |
| screening-all-off-decl-skips | stdlib-regression | 18 | 18 | 100.0% | 233.7 | 581253.0 | 0 |
| screening-all-on | dependent-slice | 78 | 48 | 61.5% | 575.0 | 1509394.7 | 2 |
| screening-all-on | external-equations | 12 | 12 | 100.0% | 108.7 | 464908.3 | 0 |
| screening-all-on | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 659269.7 | 0 |
| screening-all-on-decl-skips | dependent-slice | 78 | 50 | 64.1% | 575.0 | 1509089.9 | 0 |
| screening-all-on-decl-skips | external-equations | 12 | 12 | 100.0% | 108.7 | 464915.3 | 0 |
| screening-all-on-decl-skips | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 659270.4 | 0 |
| screening-loo-erasure-guards | dependent-slice | 78 | 53 | 67.9% | 575.0 | 1493705.8 | 2 |
| screening-loo-erasure-guards | external-equations | 12 | 12 | 100.0% | 108.7 | 448211.2 | 0 |
| screening-loo-erasure-guards | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 658151.1 | 0 |
| screening-loo-erasure-guards-decl-skips | dependent-slice | 78 | 56 | 71.8% | 575.0 | 1493403.6 | 0 |
| screening-loo-erasure-guards-decl-skips | external-equations | 12 | 12 | 100.0% | 108.7 | 448222.3 | 0 |
| screening-loo-erasure-guards-decl-skips | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 658151.9 | 0 |
| screening-loo-indexed-families | dependent-slice | 78 | 49 | 62.8% | 575.0 | 1499615.3 | 0 |
| screening-loo-indexed-families | external-equations | 12 | 12 | 100.0% | 108.7 | 463491.5 | 0 |
| screening-loo-indexed-families | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 658658.0 | 0 |
| screening-loo-indexed-families-decl-skips | dependent-slice | 78 | 49 | 62.8% | 575.0 | 1499385.4 | 0 |
| screening-loo-indexed-families-decl-skips | external-equations | 12 | 12 | 100.0% | 108.7 | 463498.5 | 0 |
| screening-loo-indexed-families-decl-skips | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 658658.8 | 0 |
| screening-loo-prop-case-erasure | dependent-slice | 78 | 41 | 52.6% | 569.0 | 1493717.6 | 2 |
| screening-loo-prop-case-erasure | external-equations | 12 | 12 | 100.0% | 108.0 | 457105.8 | 0 |
| screening-loo-prop-case-erasure | stdlib-regression | 18 | 18 | 100.0% | 233.7 | 646958.2 | 0 |
| screening-loo-prop-case-erasure-decl-skips | dependent-slice | 78 | 44 | 56.4% | 569.0 | 1493412.6 | 0 |
| screening-loo-prop-case-erasure-decl-skips | external-equations | 12 | 12 | 100.0% | 108.0 | 457112.8 | 0 |
| screening-loo-prop-case-erasure-decl-skips | stdlib-regression | 18 | 18 | 100.0% | 233.7 | 646958.4 | 0 |
| screening-loo-refinement-types | dependent-slice | 78 | 43 | 55.1% | 575.0 | 1407043.2 | 0 |
| screening-loo-refinement-types | external-equations | 12 | 6 | 50.0% | 108.7 | 463272.8 | 0 |
| screening-loo-refinement-types | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 593091.0 | 0 |
| screening-loo-refinement-types-decl-skips | dependent-slice | 78 | 43 | 55.1% | 575.0 | 1407043.2 | 0 |
| screening-loo-refinement-types-decl-skips | external-equations | 12 | 6 | 50.0% | 108.7 | 463272.8 | 0 |
| screening-loo-refinement-types-decl-skips | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 593091.0 | 0 |
| screening-loo-rigid-clash-pruning | dependent-slice | 78 | 48 | 61.5% | 576.0 | 1510235.9 | 2 |
| screening-loo-rigid-clash-pruning | external-equations | 12 | 12 | 100.0% | 108.7 | 464908.3 | 0 |
| screening-loo-rigid-clash-pruning | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 659268.2 | 0 |
| screening-loo-rigid-clash-pruning-decl-skips | dependent-slice | 78 | 50 | 64.1% | 576.0 | 1509930.7 | 0 |
| screening-loo-rigid-clash-pruning-decl-skips | external-equations | 12 | 12 | 100.0% | 108.7 | 464915.3 | 0 |
| screening-loo-rigid-clash-pruning-decl-skips | stdlib-regression | 18 | 18 | 100.0% | 238.3 | 659270.4 | 0 |

## Per-prover rates

| label | prover | generated | theorems | success_rate | consistency_hits |
| --- | --- | --- | --- | --- | --- |
| current | eprover | 54 | 42 | 77.8% | 0 |
| current | vampire | 54 | 44 | 81.5% | 0 |
| screening-all-off | eprover | 54 | 29 | 53.7% | 0 |
| screening-all-off | vampire | 54 | 32 | 59.3% | 0 |
| screening-all-off-decl-skips | eprover | 54 | 29 | 53.7% | 0 |
| screening-all-off-decl-skips | vampire | 54 | 32 | 59.3% | 0 |
| screening-all-on | eprover | 54 | 39 | 72.2% | 1 |
| screening-all-on | vampire | 54 | 39 | 72.2% | 1 |
| screening-all-on-decl-skips | eprover | 54 | 39 | 72.2% | 0 |
| screening-all-on-decl-skips | vampire | 54 | 41 | 75.9% | 0 |
| screening-loo-erasure-guards | eprover | 54 | 42 | 77.8% | 1 |
| screening-loo-erasure-guards | vampire | 54 | 41 | 75.9% | 1 |
| screening-loo-erasure-guards-decl-skips | eprover | 54 | 42 | 77.8% | 0 |
| screening-loo-erasure-guards-decl-skips | vampire | 54 | 44 | 81.5% | 0 |
| screening-loo-indexed-families | eprover | 54 | 38 | 70.4% | 0 |
| screening-loo-indexed-families | vampire | 54 | 41 | 75.9% | 0 |
| screening-loo-indexed-families-decl-skips | eprover | 54 | 38 | 70.4% | 0 |
| screening-loo-indexed-families-decl-skips | vampire | 54 | 41 | 75.9% | 0 |
| screening-loo-prop-case-erasure | eprover | 54 | 36 | 66.7% | 1 |
| screening-loo-prop-case-erasure | vampire | 54 | 35 | 64.8% | 1 |
| screening-loo-prop-case-erasure-decl-skips | eprover | 54 | 36 | 66.7% | 0 |
| screening-loo-prop-case-erasure-decl-skips | vampire | 54 | 38 | 70.4% | 0 |
| screening-loo-refinement-types | eprover | 54 | 32 | 59.3% | 0 |
| screening-loo-refinement-types | vampire | 54 | 35 | 64.8% | 0 |
| screening-loo-refinement-types-decl-skips | eprover | 54 | 32 | 59.3% | 0 |
| screening-loo-refinement-types-decl-skips | vampire | 54 | 35 | 64.8% | 0 |
| screening-loo-rigid-clash-pruning | eprover | 54 | 39 | 72.2% | 1 |
| screening-loo-rigid-clash-pruning | vampire | 54 | 39 | 72.2% | 1 |
| screening-loo-rigid-clash-pruning-decl-skips | eprover | 54 | 39 | 72.2% | 0 |
| screening-loo-rigid-clash-pruning-decl-skips | vampire | 54 | 41 | 75.9% | 0 |

## Current configuration

Current ATP success rate: 79.6% overall.
Leave-one-out configurations exceeding all-on: loo-erasure-guards exceeds all-on (76.9% vs 72.2%); loo-indexed-families exceeds all-on (73.1% vs 72.2%).
