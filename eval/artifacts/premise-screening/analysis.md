# Premise-selection screening analysis

## Corpus mode: `FULL`

**FULL-CORPUS MODE.**

Decision metrics use solved `GoalKey = (corpus, relative goal path)` sets. A goal is solved when any active premise-selector/prover attempt solves it. Gains and losses are paired set differences against `ds0-df0`; they are not attempt totals.

## Aggregate solved goals vs `ds0-df0`

| label | solved goals | baseline | net | gains | losses |
| --- | --- | --- | --- | --- | --- |
| ds0-df0 | 747 | 747 | +0 | 0 | 0 |
| ds0-df4 | 761 | 747 | +14 | 17 | 3 |
| ds0-df16 | 762 | 747 | +15 | 19 | 4 |
| ds8-df0 | 769 | 747 | +22 | 25 | 3 |
| ds8-df4 | 772 | 747 | +25 | 30 | 5 |
| ds8-df16 | 775 | 747 | +28 | 31 | 3 |
| ds32-df0 | 770 | 747 | +23 | 26 | 3 |
| ds32-df4 | 775 | 747 | +28 | 32 | 4 |
| ds32-df16 | 775 | 747 | +28 | 32 | 4 |

## Per-corpus solved goals

| label | corpus | solved goals | baseline | net | gains | losses |
| --- | --- | --- | --- | --- | --- | --- |
| ds0-df0 | stdlib-regression | 726 | 726 | +0 | 0 | 0 |
| ds0-df0 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds0-df0 | external-equations | 16 | 16 | +0 | 0 | 0 |
| ds0-df4 | stdlib-regression | 740 | 726 | +14 | 17 | 3 |
| ds0-df4 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds0-df4 | external-equations | 16 | 16 | +0 | 0 | 0 |
| ds0-df16 | stdlib-regression | 741 | 726 | +15 | 19 | 4 |
| ds0-df16 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds0-df16 | external-equations | 16 | 16 | +0 | 0 | 0 |
| ds8-df0 | stdlib-regression | 748 | 726 | +22 | 25 | 3 |
| ds8-df0 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds8-df0 | external-equations | 16 | 16 | +0 | 0 | 0 |
| ds8-df4 | stdlib-regression | 751 | 726 | +25 | 30 | 5 |
| ds8-df4 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds8-df4 | external-equations | 16 | 16 | +0 | 0 | 0 |
| ds8-df16 | stdlib-regression | 754 | 726 | +28 | 31 | 3 |
| ds8-df16 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds8-df16 | external-equations | 16 | 16 | +0 | 0 | 0 |
| ds32-df0 | stdlib-regression | 749 | 726 | +23 | 26 | 3 |
| ds32-df0 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds32-df0 | external-equations | 16 | 16 | +0 | 0 | 0 |
| ds32-df4 | stdlib-regression | 754 | 726 | +28 | 32 | 4 |
| ds32-df4 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds32-df4 | external-equations | 16 | 16 | +0 | 0 | 0 |
| ds32-df16 | stdlib-regression | 754 | 726 | +28 | 32 | 4 |
| ds32-df16 | dependent-slice | 5 | 5 | +0 | 0 | 0 |
| ds32-df16 | external-equations | 16 | 16 | +0 | 0 | 0 |

## Per-bucket solved goals

Buckets are exclusive: `<=4` means 2--4 after removing `<=1`; `rest` means greater than 4 or an empty seed (`d_size=0`, occurrence statistics `none`).

| label | bucket | solved goals | baseline | net | gains | losses |
| --- | --- | --- | --- | --- | --- | --- |
| ds0-df0 | <=1 | 64 | 64 | +0 | 0 | 0 |
| ds0-df0 | <=4 | 89 | 89 | +0 | 0 | 0 |
| ds0-df0 | rest | 594 | 594 | +0 | 0 | 0 |
| ds0-df4 | <=1 | 76 | 64 | +12 | 13 | 1 |
| ds0-df4 | <=4 | 89 | 89 | +0 | 1 | 1 |
| ds0-df4 | rest | 596 | 594 | +2 | 3 | 1 |
| ds0-df16 | <=1 | 76 | 64 | +12 | 13 | 1 |
| ds0-df16 | <=4 | 88 | 89 | -1 | 0 | 1 |
| ds0-df16 | rest | 598 | 594 | +4 | 6 | 2 |
| ds8-df0 | <=1 | 79 | 64 | +15 | 15 | 0 |
| ds8-df0 | <=4 | 89 | 89 | +0 | 0 | 0 |
| ds8-df0 | rest | 601 | 594 | +7 | 10 | 3 |
| ds8-df4 | <=1 | 80 | 64 | +16 | 17 | 1 |
| ds8-df4 | <=4 | 89 | 89 | +0 | 1 | 1 |
| ds8-df4 | rest | 603 | 594 | +9 | 12 | 3 |
| ds8-df16 | <=1 | 80 | 64 | +16 | 17 | 1 |
| ds8-df16 | <=4 | 89 | 89 | +0 | 1 | 1 |
| ds8-df16 | rest | 606 | 594 | +12 | 13 | 1 |
| ds32-df0 | <=1 | 79 | 64 | +15 | 15 | 0 |
| ds32-df0 | <=4 | 89 | 89 | +0 | 0 | 0 |
| ds32-df0 | rest | 602 | 594 | +8 | 11 | 3 |
| ds32-df4 | <=1 | 80 | 64 | +16 | 17 | 1 |
| ds32-df4 | <=4 | 89 | 89 | +0 | 1 | 1 |
| ds32-df4 | rest | 606 | 594 | +12 | 14 | 2 |
| ds32-df16 | <=1 | 81 | 64 | +17 | 18 | 1 |
| ds32-df16 | <=4 | 89 | 89 | +0 | 1 | 1 |
| ds32-df16 | rest | 605 | 594 | +11 | 13 | 2 |

## Goal-level N=32 regression guard

`REGRESSION` means at least one N=32 GoalKey solved by the baseline is no longer solved by any active N=32 selector/prover for that label. Attempt-level losses cannot trigger this guard, and gains cannot hide a GoalKey loss.

| label | N=32 solved goals | baseline | net | gains | losses | flag |
| --- | --- | --- | --- | --- | --- | --- |
| ds0-df0 | 691 | 691 | +0 | 0 | 0 | baseline |
| ds0-df4 | 706 | 691 | +15 | 17 | 2 | REGRESSION |
| ds0-df16 | 709 | 691 | +18 | 21 | 3 | REGRESSION |
| ds8-df0 | 738 | 691 | +47 | 48 | 1 | REGRESSION |
| ds8-df4 | 746 | 691 | +55 | 57 | 2 | REGRESSION |
| ds8-df16 | 748 | 691 | +57 | 58 | 1 | REGRESSION |
| ds32-df0 | 737 | 691 | +46 | 47 | 1 | REGRESSION |
| ds32-df4 | 747 | 691 | +56 | 58 | 2 | REGRESSION |
| ds32-df16 | 749 | 691 | +58 | 59 | 1 | REGRESSION |

## Exact-attempt diagnostics (not decision metrics)

| label | solved attempts | baseline | net | gains | losses |
| --- | --- | --- | --- | --- | --- |
| ds0-df0 | 5025 | 5025 | +0 | 0 | 0 |
| ds0-df4 | 5099 | 5025 | +74 | 105 | 31 |
| ds0-df16 | 5096 | 5025 | +71 | 123 | 52 |
| ds8-df0 | 5236 | 5025 | +211 | 231 | 20 |
| ds8-df4 | 5286 | 5025 | +261 | 295 | 34 |
| ds8-df16 | 5296 | 5025 | +271 | 309 | 38 |
| ds32-df0 | 5245 | 5025 | +220 | 235 | 15 |
| ds32-df4 | 5280 | 5025 | +255 | 291 | 36 |
| ds32-df16 | 5293 | 5025 | +268 | 309 | 41 |

Per-corpus/premise/prover attempt diagnostics are available in `summary.tsv` rows with `scope=exact_attempt`.
