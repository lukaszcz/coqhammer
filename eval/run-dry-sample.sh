#!/usr/bin/env bash
set -euo pipefail

# shellcheck source=eval/cli-lib.sh
source "$(dirname "${BASH_SOURCE[0]}")/cli-lib.sh"

usage() {
  cat <<'USAGE'
Usage: ./run-dry-sample.sh --label LABEL --corpus CORPUS [--prefix PREFIX]
                           [--prover eprover] [--premise knn-32]

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

while [ "$#" -gt 0 ]; do
  case "$1" in
    --label) need_value "$@"; label="$2"; shift 2 ;;
    --corpus) need_value "$@"; corpus="$2"; shift 2 ;;
    --prefix) need_value "$@"; prefix="$2"; shift 2 ;;
    --prover) need_value "$@"; prover="$2"; shift 2 ;;
    --premise) need_value "$@"; premise="$2"; shift 2 ;;
    -j|--jobs) need_value "$@"; jobs="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

if [ -z "$label" ] || [ -z "$corpus" ]; then
  usage >&2
  exit 2
fi

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

make -k -j "$jobs" init COQC="$coqc_cmd"
echo "check" > coqhammer.opt
rm -rf logs/check/ check.log
make -k -j "$jobs" check COQC="$coqc_cmd" 2>&1 | tee check.log
mv check.log check.log.bak
grep Error check.log.bak > check.log || true
rm check.log.bak

echo "gen-atp" > coqhammer.opt
rm -rf logs/atp/ atp/problems gen-atp.log
make -k -j "$jobs" atp COQC="$coqc_cmd" 2>&1 | tee gen-atp.log
mv gen-atp.log gen-atp.log.bak
grep Error gen-atp.log.bak > gen-atp.log || true
rm gen-atp.log.bak

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
make -k -j "$reconstr_jobs" reconstr COQC="$coqc_cmd"

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
