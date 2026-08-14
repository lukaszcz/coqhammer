#!/usr/bin/env bash
# The GRID_* spec is consumed indirectly by the sourced engine.
# shellcheck disable=SC2034
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./run-screening-grid.sh [options]

Run the extraction screening grid for the current checkout in a resumable
layout:
  premise counts {64,256,1024} x {Vampire,E prover} x
  {current, all-off, all-on, three leave-one-out configurations} x
  {decl-skips off,on for configuration variants} over the three prepared corpora.

Results are checkpointed under eval/results/screening/ and summarized under
  eval/artifacts/extraction-screening/summary.tsv. Checkpoints are reused only
  when their recorded commit, configuration, corpus, and timeout provenance
  matches the current run.

Options:
  -j, --jobs N          parallel jobs for Rocq/prover make invocations
                        (default: sized from cores and available memory)
  --tim SEC             ATP timeout per problem for screening prover runs (default: 5)
  --consistency-tim S  ATP timeout per false-conjecture consistency run (default: 2)
  --compile-timeout S  per-file Rocq compile timeout (default: 600)
  --compile-timeout-grace S
                       TERM grace before process-group KILL (default: 10)
  --skip-builds        require install prefixes to already exist; do not build them
  --only-label LABEL   run only one install label (debug/resume convenience)
  --only-corpus CORPUS run only one corpus (debug/resume convenience)
  --sample-corpus      use the small committed smoke corpora (default)
  --full-corpus        use full committed corpora instead of sample subdirectories
                        (dependent-slice has no full-corpus fixture and
                        always stays on its sample subdirectory)
  --external-source DIR
                       use DIR as the source for the external-equations corpus
  --force              rerun checkpoints even when done markers exist
  -h, --help           show this help

The script is safe to stop and restart.  It writes .done markers only after each
label/corpus generation, each prover/premise run, and each consistency scan
finishes successfully.
USAGE
}

grid_usage() {
  usage
}

eval_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)

GRID_NAME=screening
GRID_TIM=5
GRID_CONSISTENCY_TIM=2
GRID_RESULTS_ROOT="$eval_dir/results/screening"
GRID_ARTIFACTS_DIR="$eval_dir/artifacts/extraction-screening"
GRID_SUMMARIZER="$eval_dir/tools/summarize-screening.py"
GRID_COMPLETION_MESSAGE="Extraction screening checkpoints complete."
GRID_CONSISTENCY_PREMISE=knn-64
# Checkpoints produced by the extraction screening script before it moved onto
# grid-engine.sh carry this script digest and no hook-preamble fields. Keep
# accepted migrations explicit and narrowly scoped; do not add generic hashes.
GRID_LEGACY_SCRIPT_SHA256=(
  0a4af3b6fb21c4b53f0d6193714981b2c7d9e42c6ed39bf7325fa028e93ab563
)
GRID_PREMISES=(knn-64 knn-256 knn-1024)
GRID_PROVERS=(eprover vampire)
GRID_CORPORA=(stdlib-regression dependent-slice external-equations)

configs=(
  all-off
  all-on
  loo-prop-case-erasure
  loo-erasure-guards
  loo-refinement-types
)

GRID_LABELS=(current)
declare -A screening_label_install
screening_label_install[current]=current
for cfg in "${configs[@]}"; do
  label="screening-$cfg"
  GRID_LABELS+=("$label")
  screening_label_install[$label]="$cfg"
  label="screening-$cfg-decl-skips"
  GRID_LABELS+=("$label")
  screening_label_install[$label]="$cfg-decl-skips"
done

# Declarative label callbacks consumed by grid-engine.sh.
grid_label_install() {
  printf %s "${screening_label_install[$1]}"
}

grid_label_preamble() {
  # Extraction screening has no runtime-option axis.
  printf ''
}

# shellcheck source=eval/grid-engine.sh
# shellcheck disable=SC1091
source "$eval_dir/grid-engine.sh"
grid_run "$@"
