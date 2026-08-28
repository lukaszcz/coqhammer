# Indexed-families baseline/candidate comparison

This compact artifact preserves the cross-commit claims of the indexed-family
extraction evaluation without committing the 45 MiB per-attempt/per-goal
snapshot pair. The source snapshots remain workspace-local under
`eval/results/indexed-families-evidence/`; their digests are recorded in
`provenance.env`.

## Chronology and scope

The baseline commit is `790aaa110b601313c85430432b1bf02361cc6e16`; the
candidate is `5cb0bfd36c7f14149ee2fd9f09d188a8c69b1a6a`. The detached baseline
confirmation completed first on 2026-08-25 and its snapshot was written at
2026-08-25T18:10:03+02:00. The candidate option screening completed later that
day. The selected candidate confirmation snapshot was written at
2026-08-28T06:05:03+02:00.

Both confirmations used all seven full corpora, ten selector/count choices,
and four provers. Baseline `dependent-slice` predates the seven indexed-family
fixtures added with the candidate;
the other six corpus digests match. A common attempt key is
`(corpus, premise selector/count, prover, relative problem path)`. There are
276,560 common attempt keys and 6,914 common goal keys. The candidate has 280
additional attempts, exactly seven new fixtures times 40 cells, and the
baseline has no unmatched attempt.

## Confirmation totals

| metric | baseline | candidate |
|---|---:|---:|
| successful ATP attempts | 80,580 / 276,560 | 80,454 / 276,840 |
| successful reconstructions / successful ATP attempts | 70,371 / 80,580 | 70,241 / 80,454 |
| goals solved by at least one ATP attempt | 3,447 / 6,914 | 3,448 / 6,921 |
| goals reconstructed by at least one attempt | 3,091 / 6,914 | 3,092 / 6,921 |
| consistency hits / outputs | 0 / 14,660 | 0 / 14,800 |

On common attempts, candidate ATP successes are 80,282: 516 gains and 814
losses, net -298 (-0.108 percentage points on the common denominator). On
common goals it gains 7 and loses 11 ATP-solved goals, net -4. It has 3,087
common reconstructed goals versus 3,091 at baseline. The detailed overall,
per-corpus, and per-prover common-attempt counts are in
`common-key-stats.tsv`.

Five of the seven new fixtures are ATP-solved and all five reconstruct. Their
successful-attempt counts are `dep_cast_compose` 40/40, `dep_cast_refl` 40/40,
`dep_fin_zero_elim` 30/40, `dep_ibval_bound` 40/40, and
`dep_vector_hd_cons` 22/40; `dep_reflect_elim` and `dep_reflect_intro` are 0/40.
Across the 688 candidate ATP successes absent from baseline (516 common-key
gains plus 172 new-fixture successes), 600 reconstruct. Inspection found 52 of
those 600 using a `dep: on` tacbest variant.

For the 69,140 common generated selector/problem pairs (before four-prover
duplication), mean problem size changes from 618,985 to 618,835 bytes (-0.024%).
At premise counts 256 and 1024 it changes from 1,361,516 to 1,361,357 bytes
(-0.012%); the maximum changes from 12,482,310 to 12,501,363 bytes (+0.15%).

## Screening conclusion

The tracked screening artifact has 15 labels, three sample corpora, premise
counts 64/256/1024, and E prover/Vampire. `current` is the clean winner at
86/108 successful ATP attempts and 15/18 goals. The controlled clean
`all-on + declaration skips` reference has 80/108 and 14/18. All eight reported
consistency hits are `dep_ibval_bound`, once per consistency prover in four
no-declaration-skip configurations; `current` and every declaration-skip
configuration have zero hits.

The recommendation is to retain current defaults. The owner decision remains
whether the indexed-family coverage and clean selected consistency scan justify
the small old-goal regression, or whether the Z3/large-premise losses need a
focused follow-up. The tracked extraction screening and candidate confirmation
artifacts contain the generated tables; `provenance.env` records their digests
and the workspace-local source-snapshot digests.
