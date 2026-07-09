#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./run-screening-grid.sh [options]

Run the extraction screening grid in a resumable layout:
  premise counts {64,256,1024} x {Vampire,E prover} x
  {baseline, all-on, five leave-one-out ablations} x {decl-skips off,on for refactor configs}
  over the three prepared corpora.

Results are checkpointed under eval/results/screening/ and summarized under
  eval/artifacts/extraction-screening/summary.tsv

Options:
  -j, --jobs N          parallel jobs for Rocq/prover make invocations (default: 1)
  --tim SEC            ATP timeout per problem for screening prover runs (default: 5)
  --consistency-tim S  ATP timeout per false-conjecture consistency run (default: 2)
  --skip-builds        require install prefixes to already exist; do not build them
  --only-label LABEL   run only one install label (debug/resume convenience)
  --only-corpus CORPUS run only one corpus (debug/resume convenience)
  --force              rerun checkpoints even when done markers exist
  -h, --help           show this help

The script is safe to stop and restart.  It writes .done markers only after each
label/corpus generation, each prover/premise run, and each consistency scan
finishes successfully.
USAGE
}

jobs=1
tim=5
consistency_tim=2
skip_builds=false
only_label=
only_corpus=
force=false

while [ "$#" -gt 0 ]; do
  case "$1" in
    -j|--jobs) jobs="$2"; shift 2 ;;
    --tim) tim="$2"; shift 2 ;;
    --consistency-tim) consistency_tim="$2"; shift 2 ;;
    --skip-builds) skip_builds=true; shift ;;
    --only-label) only_label="$2"; shift 2 ;;
    --only-corpus) only_corpus="$2"; shift 2 ;;
    --force) force=true; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

repo=$(git rev-parse --show-toplevel)
eval_dir="$repo/eval"
results_root="$eval_dir/results/screening"
artifacts_dir="$eval_dir/artifacts/extraction-screening"
mkdir -p "$results_root" "$artifacts_dir"

premises=(knn-64 knn-256 knn-1024)
provers=(eprover vampire)
corpora=(stdlib-regression dependent-slice external-equations)
configs=(
  all-on
  loo-split-case-axioms
  loo-prop-case-erasure
  loo-erasure-guards
  loo-refinement-types
  loo-wf-recursion-eqs
)

labels=(baseline-merge-base)
declare -A label_config
label_config[baseline-merge-base]=baseline
for cfg in "${configs[@]}"; do
  label="screening-$cfg"
  labels+=("$label")
  label_config[$label]="$cfg"
  label_ds="screening-$cfg-decl-skips"
  labels+=("$label_ds")
  label_config[$label_ds]="$cfg-decl-skips"
done

have_done() {
  [ "$force" = false ] && [ -f "$1.done" ]
}

prepare_prefix_env() {
  local prefix="$1"
  export PATH="$prefix/bin:$base_path"
  if [ -n "$base_ocamlpath" ]; then
    export OCAMLPATH="$prefix:$base_ocamlpath"
  else
    export OCAMLPATH="$prefix"
  fi
}

require_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "Required command not found: $1" >&2
    exit 1
  fi
}

require_prover() {
  case "$1" in
    eprover) require_cmd eprover ;;
    vampire) require_cmd htimeout; require_cmd vampire ;;
    *) echo "Unknown prover: $1" >&2; exit 1 ;;
  esac
}

base_path="$PATH"
base_ocamlpath="${OCAMLPATH:-}"

build_label() {
  local label="$1"
  local prefix="$eval_dir/_installs/$label"
  if [ -f "$prefix/manifest.env" ]; then
    echo "[build] $label already installed"
    return 0
  fi
  if [ "$skip_builds" = true ]; then
    echo "Missing install prefix for $label: $prefix" >&2
    exit 1
  fi
  echo "[build] installing $label"
  export PATH="$base_path"
  if [ -n "$base_ocamlpath" ]; then
    export OCAMLPATH="$base_ocamlpath"
  else
    unset OCAMLPATH
  fi
  if [ "$label" = baseline-merge-base ]; then
    (cd "$eval_dir" && ./build-baseline.sh --label "$label")
  else
    (cd "$eval_dir" && ./rebuild-config.sh "${label_config[$label]}" --label "$label")
  fi
}

run_generation() {
  local label="$1" corpus="$2" prefix="$3"
  local outdir="$results_root/$label/$corpus"
  mkdir -p "$outdir"
  if have_done "$outdir/generate"; then
    echo "[gen] $label/$corpus already done"
    return 0
  fi

  echo "[gen] $label/$corpus"
  prepare_prefix_env "$prefix"
  cd "$eval_dir"
  ./prepare-corpus.sh "$corpus" --sample > "$outdir/prepared-files.lst"
  rm -rf logs atp/problems atp/i atp/o out statistics.html check.log gen-atp.log gen-atp.log.bak coqhammer.opt
  mkdir -p atp/o out

  coqc_cmd="rocq c -coqlib $prefix/coq"
  make -k -j "$jobs" init COQC="$coqc_cmd" > "$outdir/init.log" 2>&1
  echo check > coqhammer.opt
  make -k -j "$jobs" check COQC="$coqc_cmd" > "$outdir/check.full.log" 2>&1
  grep Error "$outdir/check.full.log" > "$outdir/check.log" || true
  if [ -s "$outdir/check.log" ]; then
    echo "Check errors for $label/$corpus; see $outdir/check.log" >&2
    exit 1
  fi

  echo gen-atp > coqhammer.opt
  if ! make -k -j "$jobs" atp COQC="$coqc_cmd" > "$outdir/gen-atp.full.log" 2>&1; then
    grep Error "$outdir/gen-atp.full.log" > "$outdir/gen-atp.log" || true
    if [ "$label" = baseline-merge-base ]; then
      echo "Baseline ATP generation failed for $label/$corpus; see $outdir/gen-atp.full.log" >&2
      exit 1
    fi
    {
      echo "generation_failed=1"
      for premise in "${premises[@]}"; do
        baseline_list="$results_root/baseline-merge-base/$corpus/generated-$premise.lst"
        if [ -f "$baseline_list" ]; then
          count=$(grep -cve '^[[:space:]]*$' "$baseline_list")
        else
          count=0
        fi
        echo "generated_count $premise $count"
      done
    } > "$outdir/generation.status"
    echo "ATP generation failed for $label/$corpus; recording as a screened regression" >&2
    rm -rf "$outdir/atp-problems"
    mkdir -p "$outdir/atp-problems"
    for premise in "${premises[@]}"; do
      mkdir -p "$outdir/atp-problems/$premise"
      : > "$outdir/generated-$premise.lst"
    done
    touch "$outdir/generate.done"
    return 0
  fi
  grep Error "$outdir/gen-atp.full.log" > "$outdir/gen-atp.log" || true
  if [ -s "$outdir/gen-atp.log" ]; then
    echo "ATP-generation errors for $label/$corpus; see $outdir/gen-atp.log" >&2
    exit 1
  fi

  rm -rf "$outdir/atp-problems"
  mkdir -p "$outdir/atp-problems"
  for premise in "${premises[@]}"; do
    if [ ! -d "atp/problems/$premise" ]; then
      echo "No generated ATP directory for $premise in $label/$corpus" >&2
      exit 1
    fi
    cp -R "atp/problems/$premise" "$outdir/atp-problems/$premise"
    find "$outdir/atp-problems/$premise" -name '*.p' | sort > "$outdir/generated-$premise.lst"
  done
  echo "generation_failed=0" > "$outdir/generation.status"
  touch "$outdir/generate.done"
}

run_prover() {
  local label="$1" corpus="$2" premise="$3" prover="$4" prefix="$5"
  local outdir="$results_root/$label/$corpus"
  local marker="$outdir/prover-$prover-$premise"
  if have_done "$marker"; then
    echo "[prover] $label/$corpus/$prover/$premise already done"
    return 0
  fi

  echo "[prover] $label/$corpus/$prover/$premise"
  prepare_prefix_env "$prefix"
  require_prover "$prover"
  cd "$eval_dir"
  rm -rf atp/i "atp/o/$prover" "atp/o/$prover-$premise"
  mkdir -p atp/i atp/o
  ln -s "$outdir/atp-problems/$premise" atp/i/f
  make -C atp -k -j "$jobs" TIM="$tim" "$prover" > "$outdir/$prover-$premise.log" 2>&1
  rm -rf "$outdir/prover-outputs/$prover-$premise"
  mkdir -p "$outdir/prover-outputs" "atp/o/$prover"
  mv "atp/o/$prover" "$outdir/prover-outputs/$prover-$premise"
  while IFS= read -r problem; do
    [ -n "$problem" ] || continue
    touch "$outdir/prover-outputs/$prover-$premise/$(basename "$problem")"
  done < "$outdir/generated-$premise.lst"
  find "$outdir/prover-outputs/$prover-$premise" -type f | sort > "$outdir/prover-outputs-$prover-$premise.lst"
  touch "$marker.done"
}

run_consistency() {
  local label="$1" corpus="$2" premise="$3" prover="$4" prefix="$5"
  local outdir="$results_root/$label/$corpus"
  local marker="$outdir/consistency-$prover-$premise"
  if have_done "$marker"; then
    echo "[consistency] $label/$corpus/$prover/$premise already done"
    return 0
  fi

  echo "[consistency] $label/$corpus/$prover/$premise"
  prepare_prefix_env "$prefix"
  require_prover "$prover"
  local work="$outdir/consistency/$prover-$premise"
  rm -rf "$work"
  mkdir -p "$work/problems" "$work/outputs"

  python3 - "$outdir/atp-problems/$premise" "$work/problems" <<'PY'
import pathlib
import re
import sys
src = pathlib.Path(sys.argv[1])
dst = pathlib.Path(sys.argv[2])
files = sorted(src.glob('*.p'))
# The committed screening corpora are small; scan all generated problems.  The
# selection code is deterministic and can be narrowed later for larger corpora.
for path in files:
    text = path.read_text()
    text, n = re.subn(r"fof\(([^,]+),\s*conjecture,\s*.*?\)\.\s*$",
                      r"fof(\1, conjecture, $false).",
                      text, count=1, flags=re.M)
    if n != 1:
        raise SystemExit(f"did not rewrite exactly one conjecture in {path}")
    (dst / path.name).write_text(text)
PY

  local problems=("$work/problems"/*.p)
  if [ ! -e "${problems[0]}" ]; then
    problems=()
  fi
  for problem in "${problems[@]}"; do
    local name
    name=$(basename "$problem")
    if [ "$prover" = eprover ]; then
      (eprover -s --cpu-limit="$consistency_tim" --auto-schedule -R --print-statistics -p --tstp-format "$problem" || true) \
        | grep "file[(]'\|# SZS\|SZS status" > "$work/outputs/$name" || true
    else
      (htimeout "$consistency_tim" vampire --mode casc -t "$consistency_tim" --proof tptp --output_axiom_names on "$problem" || true) \
        | grep "file[(]'\|% SZS\|SZS status" > "$work/outputs/$name" || true
    fi
  done
  if grep -R "SZS status Theorem" "$work/outputs" >/dev/null 2>&1; then
    echo "Inconsistency hit for $label/$corpus/$prover/$premise; see $work/outputs" >&2
    exit 1
  fi
  find "$work/outputs" -type f | sort > "$outdir/consistency-outputs-$prover-$premise.lst"
  touch "$marker.done"
}

for label in "${labels[@]}"; do
  if [ -n "$only_label" ] && [ "$label" != "$only_label" ]; then
    continue
  fi
  build_label "$label"
  prefix="$eval_dir/_installs/$label"
  for corpus in "${corpora[@]}"; do
    if [ -n "$only_corpus" ] && [ "$corpus" != "$only_corpus" ]; then
      continue
    fi
    run_generation "$label" "$corpus" "$prefix"
    for premise in "${premises[@]}"; do
      for prover in "${provers[@]}"; do
        run_prover "$label" "$corpus" "$premise" "$prover" "$prefix"
      done
    done
    # Scan one representative premise level per label/corpus; all generated
    # problems in that directory are scanned, which includes the committed canary
    # fixtures when present in the corpus.
    for prover in "${provers[@]}"; do
      run_consistency "$label" "$corpus" knn-64 "$prover" "$prefix"
    done
  done
done

python3 "$eval_dir/tools/summarize-screening.py" "$results_root" "$artifacts_dir/summary.tsv" "$artifacts_dir/analysis.md"

echo "Extraction screening complete."
echo "  raw checkpoints: $results_root"
echo "  summary:         $artifacts_dir/summary.tsv"
echo "  analysis:        $artifacts_dir/analysis.md"
