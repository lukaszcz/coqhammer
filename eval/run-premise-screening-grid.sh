#!/usr/bin/env bash
# The GRID_* spec is consumed indirectly by the sourced engine.
# shellcheck disable=SC2034
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./run-premise-screening-grid.sh [options]

Run the premise-selection screening grid for the current checkout in a
resumable layout:
  DefinitionPremises {0,8,32} x DefinitionFeatures {0,4,16} x
  {knn,nbayes} at {32,1024} premises x {E prover,Vampire} x
  {stdlib-regression,dependent-slice,external-equations}.

All nine runtime-option labels share one current install. Results are
checkpointed under eval/results/premise-screening/ and summarized under
  eval/artifacts/premise-screening/summary.tsv.

Options:
  -j, --jobs N          parallel jobs for Rocq/prover make invocations
                        (default: sized from cores and available memory)
  --tim SEC             ATP timeout per problem (default: 5)
  --consistency-tim S  false-conjecture timeout per problem (default: 2)
  --skip-builds        require the shared current install; do not build it
  --only-label LABEL   run only one runtime-option label
  --only-corpus CORPUS run only one corpus
  --sample-corpus      use the small committed smoke corpora (default)
  --full-corpus        use full committed corpora where available
  --external-source DIR
                       use DIR as the external-equations source
  --force              rerun checkpoints even when done markers are valid
  -h, --help           show this help

A partial --only-label/--only-corpus run updates checkpoints but deliberately
does not replace the complete-grid summary.
USAGE
}

grid_usage() {
  usage
}

eval_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)

GRID_NAME='premise-screening'
GRID_TIM=5
GRID_CONSISTENCY_TIM=2
GRID_RESULTS_ROOT="$eval_dir/results/premise-screening"
GRID_ARTIFACTS_DIR="$eval_dir/artifacts/premise-screening"
GRID_SUMMARIZER="$eval_dir/tools/summarize-premise-screening.py"
GRID_COMPLETION_MESSAGE="Premise-selection screening checkpoints complete."
GRID_CONSISTENCY_PREMISE=knn-32
GRID_PREMISES=(knn-32 knn-1024 nbayes-32 nbayes-1024)
GRID_PROVERS=(eprover vampire)
GRID_CORPORA=(stdlib-regression dependent-slice external-equations)

# Each runtime axis is adjustable with one array edit. Labels and preambles are
# derived from these two arrays rather than maintained independently.
DEFINITION_PREMISES=(0 8 32)
DEFINITION_FEATURES=(0 4 16)
GRID_LABELS=()
declare -A premise_grid_slots premise_grid_features
for slots in "${DEFINITION_PREMISES[@]}"; do
  for features in "${DEFINITION_FEATURES[@]}"; do
    label="ds$slots-df$features"
    GRID_LABELS+=("$label")
    premise_grid_slots[$label]=$slots
    premise_grid_features[$label]=$features
  done
done

# All labels are runtime configurations of one shared installation.
grid_label_install() {
  printf current
}

grid_label_preamble() {
  local label="$1"
  printf 'Set Hammer DefinitionPremises %s.\nSet Hammer DefinitionFeatures %s.\n' \
    "${premise_grid_slots[$label]}" "${premise_grid_features[$label]}"
}

# shellcheck source=eval/grid-engine.sh
# shellcheck disable=SC1091
source "$eval_dir/grid-engine.sh"
grid_run "$@"
