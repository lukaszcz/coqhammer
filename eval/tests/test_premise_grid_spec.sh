#!/usr/bin/env bash
# SC2031 is a false positive from grid_run's same-name subshell local.
# shellcheck disable=SC2031,SC2034
set -euo pipefail

eval_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
# --help validates the complete spec without creating roots or building, then
# leaves its declarations/callbacks available because this test sources it.
# shellcheck source=eval/run-premise-screening-grid.sh
# shellcheck disable=SC1091
source "$eval_dir/run-premise-screening-grid.sh" --help >/dev/null

fail() {
  echo "test_premise_grid_spec: $*" >&2
  exit 1
}

expected_labels=(
  ds0-df0 ds0-df4 ds0-df16
  ds8-df0 ds8-df4 ds8-df16
  ds32-df0 ds32-df4 ds32-df16
)
[ "${GRID_LABELS[*]}" = "${expected_labels[*]}" ] || fail "wrong factorial labels"
[ "${GRID_PREMISES[*]}" = "knn-32 knn-1024 nbayes-32 nbayes-1024" ] ||
  fail "wrong premise selector/count axis"
[ "${GRID_PROVERS[*]}" = "eprover vampire" ] || fail "wrong prover axis"
[ "${GRID_CORPORA[*]}" = "stdlib-regression dependent-slice external-equations" ] ||
  fail "wrong corpus axis"
[ "$GRID_CONSISTENCY_PREMISE" = knn-32 ] || fail "wrong consistency watch point"

for label in "${GRID_LABELS[@]}"; do
  [ "$(grid_label_install "$label")" = current ] || fail "$label does not share current"
done
# The engine captures the callback through a file, so the trailing newline is
# part of what a label's preamble is. The sentinel keeps command substitution
# from stripping it, which would hide a preamble that ran the two settings
# together with the line that follows them.
expected_preamble=$'Set Hammer DefinitionPremises 8.\nSet Hammer DefinitionFeatures 16.\n'
actual_preamble=$(grid_label_preamble ds8-df16; printf x)
[ "${actual_preamble%x}" = "$expected_preamble" ] ||
  fail "wrong ds8-df16 preamble"
baseline_preamble=$'Set Hammer DefinitionPremises 0.\nSet Hammer DefinitionFeatures 0.\n'
actual_baseline=$(grid_label_preamble ds0-df0; printf x)
[ "${actual_baseline%x}" = "$baseline_preamble" ] ||
  fail "wrong pure-predictor baseline preamble"

case "$GRID_RESULTS_ROOT" in
  "$eval_dir/results/premise-screening") ;;
  *) fail "unexpected results root: $GRID_RESULTS_ROOT" ;;
esac
[ "$GRID_RESULTS_ROOT" != "$eval_dir/results/screening" ] || fail "shares extraction root"
[ "$GRID_RESULTS_ROOT" != "$eval_dir/results/confirmation" ] || fail "shares confirmation root"
[ "$GRID_ARTIFACTS_DIR" = "$eval_dir/artifacts/premise-screening" ] ||
  fail "unexpected artifacts root"

echo "test_premise_grid_spec: ok"
