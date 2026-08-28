# TASK_10 D3 follow-up

Commit `62fc0708997c4a65a09b63902df85c1921e2201e` fixes the D3 screening discrepancy: with erasure guards enabled and indexed families disabled, indexed Prop-singleton collapse now uses the legacy source-proposition premise. The two affected TASK_10 labels were rerun to completion through separate harness `--only-label` runs. The original 15-label artifact remains unchanged and is used only for the historical rows and controlled references in `table.tsv`.

## Scope and validation

Both runs used the committed sample corpora (`stdlib-regression`, `dependent-slice`, and `external-equations`), `knn-{64,256,1024}`, E prover and Vampire, ATP timeout 5 seconds, consistency timeout 2 seconds, and compile timeout 43,200 seconds. Each label has all 108 ATP outputs and all 36 `knn-64` consistency outputs. Both semantic manifests record `opt_erasure_guards=true` and `opt_indexed_families=false`; declaration skips are respectively false and true. Installation also passed the `guards-legacy` singleton-premise assertions.

| label | ATP successes | goals solved | consistency | high-premise mean bytes |
|---|---:|---:|---:|---:|
| `screening-loo-indexed-families` | 79/108 | 14/18 | 0/36 | 1,810,443.500 |
| `screening-loo-indexed-families-decl-skips` | 79/108 | 14/18 | 0/36 | 1,810,233.194 |

The generated 36-row follow-up summary is field-for-field identical to the two corresponding historical rows across every corpus, premise count, and prover cell. Thus every recorded formula-size aggregate is also unchanged, not only the displayed high-premise metric. The solved-goal unions are identical between the two follow-up labels.

## Revised ablation interpretation

The earlier leave-one-out rows accidentally retained forded singleton premises, so they were not a complete `opt_indexed_families=false` ablation even though their labels said otherwise. The fixed, complete reruns happen to reproduce their measurements exactly. Against the clean controlled `all-on + declaration skips` reference, indexed-family extraction therefore has a validated contribution of **+1 ATP success, no additional union-level goal, and +0.538% high-premise formula bytes** (350,452 additional bytes over 65,168,395). Both cells remain consistency-clean. Without declaration skips, enabling indexed families changes 79 to 78 ATP successes and retains two consistency hits; that comparison is not the selected clean control.

The committed current defaults are unaffected by the fix (`opt_erasure_guards=false`), and their original screening result remains the winner at 86/108 ATP successes, 15/18 goals, and 0/36 consistency hits. No full confirmation rerun is needed for a change confined to `guards=true,indexed=false` configurations.

Harness invocations and digests are recorded in `provenance.env`; detailed per-cell values remain reproducible from the ignored checkpoints using the summarizer command listed there.
