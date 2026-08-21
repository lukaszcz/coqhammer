# Premise-selection screening analysis

## Corpus mode: `FULL`

**FULL-CORPUS MODE.**

Decision metrics use solved `GoalKey = (corpus, relative goal path)` sets. A goal is solved when any active premise-selector/prover attempt solves it. Gains and losses are paired set differences against `ds0-df0`; they are not attempt totals.

## Aggregate solved goals vs `ds0-df0`

| label | solved goals | baseline | net | gains | losses |
| --- | --- | --- | --- | --- | --- |
| ds0-df0 | 754 | 754 | +0 | 0 | 0 |
| ds0-df4 | 758 | 754 | +4 | 12 | 8 |
| ds0-df16 | 766 | 754 | +12 | 17 | 5 |
| ds8-df0 | 776 | 754 | +22 | 27 | 5 |
| ds8-df4 | 777 | 754 | +23 | 29 | 6 |
| ds8-df16 | 782 | 754 | +28 | 32 | 4 |
| ds32-df0 | 778 | 754 | +24 | 27 | 3 |
| ds32-df4 | 779 | 754 | +25 | 30 | 5 |
| ds32-df16 | 782 | 754 | +28 | 31 | 3 |

## Per-corpus solved goals

| label | corpus | solved goals | baseline | net | gains | losses |
| --- | --- | --- | --- | --- | --- | --- |
| ds0-df0 | stdlib-regression | 731 | 731 | +0 | 0 | 0 |
| ds0-df0 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds0-df0 | external-equations | 18 | 18 | +0 | 0 | 0 |
| ds0-df4 | stdlib-regression | 735 | 731 | +4 | 12 | 8 |
| ds0-df4 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds0-df4 | external-equations | 18 | 18 | +0 | 0 | 0 |
| ds0-df16 | stdlib-regression | 743 | 731 | +12 | 17 | 5 |
| ds0-df16 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds0-df16 | external-equations | 18 | 18 | +0 | 0 | 0 |
| ds8-df0 | stdlib-regression | 753 | 731 | +22 | 27 | 5 |
| ds8-df0 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds8-df0 | external-equations | 18 | 18 | +0 | 0 | 0 |
| ds8-df4 | stdlib-regression | 754 | 731 | +23 | 29 | 6 |
| ds8-df4 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds8-df4 | external-equations | 18 | 18 | +0 | 0 | 0 |
| ds8-df16 | stdlib-regression | 759 | 731 | +28 | 32 | 4 |
| ds8-df16 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds8-df16 | external-equations | 18 | 18 | +0 | 0 | 0 |
| ds32-df0 | stdlib-regression | 755 | 731 | +24 | 27 | 3 |
| ds32-df0 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds32-df0 | external-equations | 18 | 18 | +0 | 0 | 0 |
| ds32-df4 | stdlib-regression | 756 | 731 | +25 | 30 | 5 |
| ds32-df4 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds32-df4 | external-equations | 18 | 18 | +0 | 0 | 0 |
| ds32-df16 | stdlib-regression | 759 | 731 | +28 | 31 | 3 |
| ds32-df16 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds32-df16 | external-equations | 18 | 18 | +0 | 0 | 0 |

## Per-bucket solved goals

Buckets are exclusive: `<=4` means 2--4 after removing `<=1`; `rest` means greater than 4 or an empty seed (`d_size=0`, occurrence statistics `none`).

| label | bucket | solved goals | baseline | net | gains | losses |
| --- | --- | --- | --- | --- | --- | --- |
| ds0-df0 | <=1 | 67 | 67 | +0 | 0 | 0 |
| ds0-df0 | <=4 | 90 | 90 | +0 | 0 | 0 |
| ds0-df0 | rest | 597 | 597 | +0 | 0 | 0 |
| ds0-df4 | <=1 | 78 | 67 | +11 | 12 | 1 |
| ds0-df4 | <=4 | 87 | 90 | -3 | 0 | 3 |
| ds0-df4 | rest | 593 | 597 | -4 | 0 | 4 |
| ds0-df16 | <=1 | 79 | 67 | +12 | 13 | 1 |
| ds0-df16 | <=4 | 89 | 90 | -1 | 0 | 1 |
| ds0-df16 | rest | 598 | 597 | +1 | 4 | 3 |
| ds8-df0 | <=1 | 82 | 67 | +15 | 17 | 2 |
| ds8-df0 | <=4 | 90 | 90 | +0 | 0 | 0 |
| ds8-df0 | rest | 604 | 597 | +7 | 10 | 3 |
| ds8-df4 | <=1 | 83 | 67 | +16 | 18 | 2 |
| ds8-df4 | <=4 | 89 | 90 | -1 | 0 | 1 |
| ds8-df4 | rest | 605 | 597 | +8 | 11 | 3 |
| ds8-df16 | <=1 | 83 | 67 | +16 | 18 | 2 |
| ds8-df16 | <=4 | 90 | 90 | +0 | 1 | 1 |
| ds8-df16 | rest | 609 | 597 | +12 | 13 | 1 |
| ds32-df0 | <=1 | 82 | 67 | +15 | 16 | 1 |
| ds32-df0 | <=4 | 90 | 90 | +0 | 0 | 0 |
| ds32-df0 | rest | 606 | 597 | +9 | 11 | 2 |
| ds32-df4 | <=1 | 84 | 67 | +17 | 19 | 2 |
| ds32-df4 | <=4 | 89 | 90 | -1 | 0 | 1 |
| ds32-df4 | rest | 606 | 597 | +9 | 11 | 2 |
| ds32-df16 | <=1 | 83 | 67 | +16 | 18 | 2 |
| ds32-df16 | <=4 | 89 | 90 | -1 | 0 | 1 |
| ds32-df16 | rest | 610 | 597 | +13 | 13 | 0 |

## Goal-level N=32 regression guard

`REGRESSION` means at least one N=32 GoalKey solved by the baseline is no longer solved by any active N=32 selector/prover for that label. Attempt-level losses cannot trigger this guard, and gains cannot hide a GoalKey loss.

| label | N=32 solved goals | baseline | net | gains | losses | flag |
| --- | --- | --- | --- | --- | --- | --- |
| ds0-df0 | 697 | 697 | +0 | 0 | 0 | baseline |
| ds0-df4 | 707 | 697 | +10 | 14 | 4 | REGRESSION |
| ds0-df16 | 713 | 697 | +16 | 19 | 3 | REGRESSION |
| ds8-df0 | 743 | 697 | +46 | 49 | 3 | REGRESSION |
| ds8-df4 | 750 | 697 | +53 | 56 | 3 | REGRESSION |
| ds8-df16 | 755 | 697 | +58 | 59 | 1 | REGRESSION |
| ds32-df0 | 745 | 697 | +48 | 49 | 1 | REGRESSION |
| ds32-df4 | 753 | 697 | +56 | 58 | 2 | REGRESSION |
| ds32-df16 | 753 | 697 | +56 | 57 | 1 | REGRESSION |

## Exact-attempt diagnostics (not decision metrics)

| label | solved attempts | baseline | net | gains | losses |
| --- | --- | --- | --- | --- | --- |
| ds0-df0 | 5043 | 5043 | +0 | 0 | 0 |
| ds0-df4 | 5069 | 5043 | +26 | 90 | 64 |
| ds0-df16 | 5117 | 5043 | +74 | 121 | 47 |
| ds8-df0 | 5251 | 5043 | +208 | 243 | 35 |
| ds8-df4 | 5309 | 5043 | +266 | 300 | 34 |
| ds8-df16 | 5331 | 5043 | +288 | 318 | 30 |
| ds32-df0 | 5277 | 5043 | +234 | 249 | 15 |
| ds32-df4 | 5311 | 5043 | +268 | 300 | 32 |
| ds32-df16 | 5327 | 5043 | +284 | 320 | 36 |

Per-corpus/premise/prover attempt diagnostics are available in `summary.tsv` rows with `scope=exact_attempt`.
