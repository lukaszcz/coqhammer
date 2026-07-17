# Extraction screening analysis

Rows summarized: 198.
Baseline sanity success rate: 43.9% overall.
Consistency hits: 0.
Generation failures recorded as screened regressions: none.

## Overall configuration ranking

| label | config | decl_skips | generated | theorems | success_rate | def_constants_mean | avg_bytes_mean | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| screening-loo-erasure-guards-decl-skips | loo-erasure-guards | true | 66 | 56 | 84.8% | 217.0 | 862855.5 | 0 |
| screening-all-on-decl-skips | all-on | true | 66 | 50 | 75.8% | 217.0 | 862896.8 | 0 |
| screening-loo-prop-case-erasure-decl-skips | loo-prop-case-erasure | true | 66 | 50 | 75.8% | 216.7 | 924775.5 | 0 |
| screening-loo-wf-recursion-eqs-decl-skips | loo-wf-recursion-eqs | true | 66 | 44 | 66.7% | 216.8 | 860713.1 | 0 |
| screening-loo-erasure-guards | loo-erasure-guards | false | 66 | 43 | 65.2% | 217.0 | 865327.8 | 0 |
| screening-loo-refinement-types | loo-refinement-types | false | 66 | 41 | 62.1% | 217.0 | 751963.6 | 0 |
| screening-loo-refinement-types-decl-skips | loo-refinement-types | true | 66 | 41 | 62.1% | 217.0 | 751963.6 | 0 |
| screening-loo-prop-case-erasure | loo-prop-case-erasure | false | 66 | 38 | 57.6% | 216.7 | 927259.9 | 0 |
| screening-all-on | all-on | false | 66 | 37 | 56.1% | 217.0 | 865369.1 | 0 |
| screening-loo-wf-recursion-eqs | loo-wf-recursion-eqs | false | 66 | 33 | 50.0% | 216.8 | 863198.2 | 0 |
| baseline-merge-base | baseline | false | 66 | 29 | 43.9% | 215.2 | 717443.9 | 0 |

## Per-corpus rates

| label | corpus | generated | theorems | success_rate | def_constants_mean | avg_bytes_mean | consistency_hits |
| --- | --- | --- | --- | --- | --- | --- | --- |
| baseline-merge-base | dependent-slice | 36 | 12 | 33.3% | 310.0 | 923634.7 | 0 |
| baseline-merge-base | external-equations | 12 | 0 | 0.0% | 109.7 | 688615.2 | 0 |
| baseline-merge-base | stdlib-regression | 18 | 17 | 94.4% | 226.0 | 540081.9 | 0 |
| screening-all-on | dependent-slice | 36 | 18 | 50.0% | 313.0 | 1461371.9 | 0 |
| screening-all-on | external-equations | 12 | 7 | 58.3% | 111.7 | 578435.8 | 0 |
| screening-all-on | stdlib-regression | 18 | 12 | 66.7% | 226.3 | 556299.5 | 0 |
| screening-all-on-decl-skips | dependent-slice | 36 | 23 | 63.9% | 313.0 | 1459139.5 | 0 |
| screening-all-on-decl-skips | external-equations | 12 | 12 | 100.0% | 111.7 | 574689.7 | 0 |
| screening-all-on-decl-skips | stdlib-regression | 18 | 15 | 83.3% | 226.3 | 554861.1 | 0 |
| screening-loo-erasure-guards | dependent-slice | 36 | 24 | 66.7% | 313.0 | 1461284.3 | 0 |
| screening-loo-erasure-guards | external-equations | 12 | 7 | 58.3% | 111.7 | 578399.5 | 0 |
| screening-loo-erasure-guards | stdlib-regression | 18 | 12 | 66.7% | 226.3 | 556299.5 | 0 |
| screening-loo-erasure-guards-decl-skips | dependent-slice | 36 | 29 | 80.6% | 313.0 | 1459052.0 | 0 |
| screening-loo-erasure-guards-decl-skips | external-equations | 12 | 12 | 100.0% | 111.7 | 574653.3 | 0 |
| screening-loo-erasure-guards-decl-skips | stdlib-regression | 18 | 15 | 83.3% | 226.3 | 554861.1 | 0 |
| screening-loo-prop-case-erasure | dependent-slice | 36 | 18 | 50.0% | 312.3 | 1506812.5 | 0 |
| screening-loo-prop-case-erasure | external-equations | 12 | 8 | 66.7% | 111.3 | 717936.2 | 0 |
| screening-loo-prop-case-erasure | stdlib-regression | 18 | 12 | 66.7% | 226.3 | 557031.0 | 0 |
| screening-loo-prop-case-erasure-decl-skips | dependent-slice | 36 | 23 | 63.9% | 312.3 | 1504580.1 | 0 |
| screening-loo-prop-case-erasure-decl-skips | external-equations | 12 | 12 | 100.0% | 111.3 | 714153.8 | 0 |
| screening-loo-prop-case-erasure-decl-skips | stdlib-regression | 18 | 15 | 83.3% | 226.3 | 555592.7 | 0 |
| screening-loo-refinement-types | dependent-slice | 36 | 18 | 50.0% | 313.0 | 1155217.2 | 0 |
| screening-loo-refinement-types | external-equations | 12 | 6 | 50.0% | 111.7 | 569150.2 | 0 |
| screening-loo-refinement-types | stdlib-regression | 18 | 17 | 94.4% | 226.3 | 531523.3 | 0 |
| screening-loo-refinement-types-decl-skips | dependent-slice | 36 | 18 | 50.0% | 313.0 | 1155217.2 | 0 |
| screening-loo-refinement-types-decl-skips | external-equations | 12 | 6 | 50.0% | 111.7 | 569150.2 | 0 |
| screening-loo-refinement-types-decl-skips | stdlib-regression | 18 | 17 | 94.4% | 226.3 | 531523.3 | 0 |
| screening-loo-wf-recursion-eqs | dependent-slice | 36 | 18 | 50.0% | 312.7 | 1460132.7 | 0 |
| screening-loo-wf-recursion-eqs | external-equations | 12 | 3 | 25.0% | 111.3 | 573162.3 | 0 |
| screening-loo-wf-recursion-eqs | stdlib-regression | 18 | 12 | 66.7% | 226.3 | 556299.5 | 0 |
| screening-loo-wf-recursion-eqs-decl-skips | dependent-slice | 36 | 23 | 63.9% | 312.7 | 1457900.3 | 0 |
| screening-loo-wf-recursion-eqs-decl-skips | external-equations | 12 | 6 | 50.0% | 111.3 | 569377.8 | 0 |
| screening-loo-wf-recursion-eqs-decl-skips | stdlib-regression | 18 | 15 | 83.3% | 226.3 | 554861.1 | 0 |

## Per-prover rates

| label | prover | generated | theorems | success_rate | consistency_hits |
| --- | --- | --- | --- | --- | --- |
| baseline-merge-base | eprover | 33 | 14 | 42.4% | 0 |
| baseline-merge-base | vampire | 33 | 15 | 45.5% | 0 |
| screening-all-on | eprover | 33 | 23 | 69.7% | 0 |
| screening-all-on | vampire | 33 | 14 | 42.4% | 0 |
| screening-all-on-decl-skips | eprover | 33 | 24 | 72.7% | 0 |
| screening-all-on-decl-skips | vampire | 33 | 26 | 78.8% | 0 |
| screening-loo-erasure-guards | eprover | 33 | 26 | 78.8% | 0 |
| screening-loo-erasure-guards | vampire | 33 | 17 | 51.5% | 0 |
| screening-loo-erasure-guards-decl-skips | eprover | 33 | 27 | 81.8% | 0 |
| screening-loo-erasure-guards-decl-skips | vampire | 33 | 29 | 87.9% | 0 |
| screening-loo-prop-case-erasure | eprover | 33 | 24 | 72.7% | 0 |
| screening-loo-prop-case-erasure | vampire | 33 | 14 | 42.4% | 0 |
| screening-loo-prop-case-erasure-decl-skips | eprover | 33 | 24 | 72.7% | 0 |
| screening-loo-prop-case-erasure-decl-skips | vampire | 33 | 26 | 78.8% | 0 |
| screening-loo-refinement-types | eprover | 33 | 20 | 60.6% | 0 |
| screening-loo-refinement-types | vampire | 33 | 21 | 63.6% | 0 |
| screening-loo-refinement-types-decl-skips | eprover | 33 | 20 | 60.6% | 0 |
| screening-loo-refinement-types-decl-skips | vampire | 33 | 21 | 63.6% | 0 |
| screening-loo-wf-recursion-eqs | eprover | 33 | 21 | 63.6% | 0 |
| screening-loo-wf-recursion-eqs | vampire | 33 | 12 | 36.4% | 0 |
| screening-loo-wf-recursion-eqs-decl-skips | eprover | 33 | 21 | 63.6% | 0 |
| screening-loo-wf-recursion-eqs-decl-skips | vampire | 33 | 23 | 69.7% | 0 |

## Decision inputs

Winner by screening ATP success rate: `screening-loo-erasure-guards-decl-skips` (84.8%).
Dependent-slice delta for winner vs baseline: +47.2 percentage points.
Flagged options: loo-erasure-guards improved over all-on (65.2% vs 56.1%); loo-prop-case-erasure improved over all-on (57.6% vs 56.1%); loo-refinement-types improved over all-on (62.1% vs 56.1%).
