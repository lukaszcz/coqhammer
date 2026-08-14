#!/usr/bin/env bash
set -euo pipefail

# shellcheck source=eval/cli-lib.sh
# shellcheck disable=SC1091
source "$(dirname "${BASH_SOURCE[0]}")/cli-lib.sh"

usage() {
  cat <<'USAGE'
Usage: ./run-dry-sample.sh --label LABEL --corpus CORPUS [--prefix PREFIX]
                           [--prover eprover] [--premise knn-32]
                           [--compile-timeout SEC]
                           [--compile-timeout-grace SEC]

Compile timeout defaults: 600 seconds per file, with 10 seconds of TERM grace
before process-group KILL.

Run the eval harness on a small committed sample: compile/check, generate ATP
problems with hammer_hook, run one prover on one premise-selection directory,
run reconstruction parsing, and write a summary under eval/results/.
USAGE
}

label=
corpus=
prefix=
prover=eprover
premise=knn-32
jobs=1
compile_timeout=600
compile_timeout_grace=10

while [ "$#" -gt 0 ]; do
  case "$1" in
    --label) need_value "$@"; label="$2"; shift 2 ;;
    --corpus) need_value "$@"; corpus="$2"; shift 2 ;;
    --prefix) need_value "$@"; prefix="$2"; shift 2 ;;
    --prover) need_value "$@"; prover="$2"; shift 2 ;;
    --premise) need_value "$@"; premise="$2"; shift 2 ;;
    -j|--jobs) need_value "$@"; jobs="$2"; shift 2 ;;
    --compile-timeout) need_value "$@"; compile_timeout="$2"; shift 2 ;;
    --compile-timeout-grace) need_value "$@"; compile_timeout_grace="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [ -z "$label" ] || [ -z "$corpus" ]; then
  usage >&2
  exit 2
fi
for value in "$jobs" "$compile_timeout" "$compile_timeout_grace"; do
  if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
    echo "Jobs and compile timeouts must be positive integers: $value" >&2
    exit 2
  fi
done

# label/corpus/prover/premise all end up in derived paths (results/, atp/o/,
# atp/i/f) and prover additionally names a `make -C atp` target, so they are
# restricted to known-safe shapes before anything is deleted or built from
# them: no traversal segments, no globbing, no word splitting.
name_re='^[A-Za-z0-9][A-Za-z0-9._-]*$'
if ! [[ "$label" =~ $name_re ]]; then
  echo "Invalid --label: $label" >&2
  exit 2
fi
if ! [[ "$corpus" =~ $name_re ]]; then
  echo "Invalid --corpus: $corpus" >&2
  exit 2
fi
case "$prover" in
  eprover|vampire|z3|cvc4) ;;
  *) echo "Invalid --prover: $prover (expected one of: eprover, vampire, z3, cvc4)" >&2; exit 2 ;;
esac
if ! [[ "$premise" =~ ^(knn|nbayes)-[0-9]+$ ]]; then
  echo "Invalid --premise: $premise (expected knn-N or nbayes-N)" >&2
  exit 2
fi

repo=$(git rev-parse --show-toplevel)
eval_dir="$repo/eval"
if [ -z "$prefix" ]; then
  prefix="$eval_dir/_installs/$label"
fi
if [ ! -d "$prefix" ]; then
  echo "Install prefix does not exist: $prefix" >&2
  exit 1
fi
if [ ! -e "$prefix/manifest.env" ]; then
  echo "Install prefix $prefix has no manifest.env; it was not built by rebuild-config.sh, so its freshness cannot be checked. Rebuild it with rebuild-config.sh first." >&2
  exit 1
fi
prefix_commit=$(sed -n 's/^commit=//p' "$prefix/manifest.env")
current_commit=$(git -C "$repo" rev-parse HEAD)
if [ "$prefix_commit" != "$current_commit" ]; then
  echo "Install prefix $prefix was built from commit ${prefix_commit:-<unknown>}, but this checkout is at $current_commit; rebuild it with rebuild-config.sh before running the dry sample." >&2
  exit 1
fi

cd "$eval_dir"
./prepare-corpus.sh "$corpus" --sample >/dev/null
rm -rf logs atp/problems atp/i atp/o out statistics.html check.log gen-atp.log gen-atp.log.bak coqhammer.opt
mkdir -p atp/o out

export PATH="$prefix/bin:$PATH"
export OCAMLPATH="$prefix${OCAMLPATH:+:$OCAMLPATH}"
coqc_cmd="rocq c -coqlib $prefix/coq"
compile_supervisor="$eval_dir/tools/rocq-compile-supervisor.sh"

run_compile_make() {
  local phase="$1" target="$2" compile_log_dir="$3" status=0
  make -k -j "$jobs" "$target" COQC="$coqc_cmd" \
    COMPILE_SUPERVISOR="$compile_supervisor" \
    COMPILE_TIMEOUT="$compile_timeout" \
    COMPILE_TIMEOUT_GRACE="$compile_timeout_grace" \
    COMPILE_PHASE="$phase" || status=$?
  if [ "$status" -ne 0 ]; then
    report_compile_timeouts "$compile_log_dir"
    return "$status"
  fi
}

# shellcheck source=eval/grid-checkpoint-lib.sh
# shellcheck disable=SC1091
source "$eval_dir/grid-checkpoint-lib.sh"

run_compile_make init init logs/init
echo "check" > coqhammer.opt
rm -rf logs/check/ check.log
check_status=0
run_compile_make check check logs/check 2>&1 | tee check.log.bak || check_status=$?
grep Error check.log.bak > check.log || true
rm check.log.bak
[ "$check_status" -eq 0 ] || exit "$check_status"

echo "gen-atp" > coqhammer.opt
rm -rf logs/atp/ atp/problems gen-atp.log
generation_status=0
run_compile_make gen-atp atp logs/atp 2>&1 | tee gen-atp.log.bak || generation_status=$?
cleanup_paired_output_temporaries atp/problems
grep Error gen-atp.log.bak > gen-atp.log || true
rm gen-atp.log.bak
[ "$generation_status" -eq 0 ] || exit "$generation_status"

if [ ! -d "atp/problems/$premise" ]; then
  echo "No generated ATP directory for premise selector: $premise" >&2
  exit 1
fi

rm -rf atp/i "atp/o/$prover" "atp/o/$prover-$premise"
mkdir -p atp/i atp/o
ln -s "../problems/$premise" atp/i/f
if make -C atp -k -j "$jobs" TIM=5 "$prover"; then
  prover_status=0
else
  prover_status=$?
  echo "[prover] $prover/$premise exited with status $prover_status; keeping partial outputs"
fi
mkdir -p "atp/o/$prover"
echo "prover_exit=$prover_status" > "atp/o/$prover.status"
mv "atp/o/$prover" "atp/o/$prover-$premise"

make clean-vo
echo "reconstr" > coqhammer.opt
reconstr_jobs=$(echo "($jobs-4)/4+1" | bc)
jobs=$reconstr_jobs run_compile_make reconstruction reconstr logs/reconstr

result_dir="results/$label/$corpus"
rm -rf "$result_dir"
mkdir -p "$result_dir"
find "atp/problems/$premise" -name '*.p' | sort > "$result_dir/generated.lst"
find "atp/o/$prover-$premise" -type f | sort > "$result_dir/prover-outputs.lst"
find out -type f | sort > "$result_dir/reconstruction-outputs.lst"
{
  echo "label=$label"
  echo "corpus=$corpus"
  echo "prefix=$prefix"
  echo "prover=$prover"
  echo "premise=$premise"
  echo "compile_timeout=$compile_timeout"
  echo "compile_timeout_grace=$compile_timeout_grace"
  echo "compile_supervisor_sha256=$(sha256sum "$compile_supervisor" | awk '{ print $1 }')"
  echo "generated=$(wc -l < "$result_dir/generated.lst")"
  echo "prover_outputs=$(wc -l < "$result_dir/prover-outputs.lst")"
  echo "theorems=$( (grep -R "SZS status Theorem" "atp/o/$prover-$premise" 2>/dev/null || true) | wc -l )"
  echo "reconstruction_outputs=$(wc -l < "$result_dir/reconstruction-outputs.lst")"
  echo "reconstruction_successes=$( (grep -R "^Success" out 2>/dev/null || true) | wc -l )"
} | tee "$result_dir/summary.txt"

if [ ! -s "$result_dir/prover-outputs.lst" ]; then
  echo "Dry run produced no prover outputs" >&2
  exit 1
fi
