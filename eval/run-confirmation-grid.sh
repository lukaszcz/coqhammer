#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./run-confirmation-grid.sh [options]

Run the extraction confirmation grid for the current checkout:
  all standard hammer_hook premise-selector/count directories
  ({knn,nbayes} x {32,64,128,256,1024}) x all four provers.

Results are checkpointed under eval/results/confirmation/ and summarized under
  eval/artifacts/extraction-confirmation/{summary.tsv,analysis.md}. Checkpoints
  are reused only when their recorded commit, configuration, corpus, and timeout
  provenance matches the current run.

Options:
  -j, --jobs N          parallel jobs for Rocq/prover make invocations
                        (default: sized from cores and available memory)
  --tim SEC             ATP timeout per problem for confirmation prover runs (default: 10)
  --consistency-tim S   ATP timeout per false-conjecture consistency run (default: 2)
  --skip-builds         require install prefixes to already exist; do not build them
  --only-label LABEL    run only one install label (debug/resume convenience)
  --only-corpus CORPUS  run only one corpus (debug/resume convenience)
  --sample-corpus       use the small committed smoke corpora instead of the
                        full corpora built from the installed libraries
  --full-corpus         use the full corpora (default)
  --stdlib-modules "A B"
                        Stdlib modules for the stdlib-regression corpus
                        (default: Arith Bool Vectors Lists NArith)
  --external-source DIR
                        use DIR as the source for the external-equations corpus
  --force               rerun checkpoints even when done markers exist
  -h, --help            show this help
USAGE
}

jobs=
tim=10
consistency_tim=2
skip_builds=false
only_label=
only_corpus=
sample_corpora=false
stdlib_modules=${STDLIB_CORPUS_MODULES:-"Arith Bool Vectors Lists NArith"}
external_source=
force=false

while [ "$#" -gt 0 ]; do
  case "$1" in
    -j|--jobs) jobs="$2"; shift 2 ;;
    --tim) tim="$2"; shift 2 ;;
    --consistency-tim) consistency_tim="$2"; shift 2 ;;
    --skip-builds) skip_builds=true; shift ;;
    --only-label) only_label="$2"; shift 2 ;;
    --only-corpus) only_corpus="$2"; shift 2 ;;
    --full-corpus) sample_corpora=false; shift ;;
    --sample-corpus) sample_corpora=true; shift ;;
    --stdlib-modules) stdlib_modules="$2"; shift 2 ;;
    --external-source) external_source="$2"; shift 2 ;;
    --force) force=true; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

for value in "$tim" "$consistency_tim"; do
  if [[ ! "$value" =~ ^[1-9][0-9]*$ ]]; then
    echo "Timeouts must be positive integers: $value" >&2
    exit 2
  fi
done

repo=$(git rev-parse --show-toplevel)
if ! git -C "$repo" diff --quiet HEAD --; then
  echo "Evaluation grids require a clean tracked worktree so build and checkpoint provenance is exact." >&2
  exit 1
fi
eval_dir="$repo/eval"
# shellcheck source=eval/grid-checkpoint-lib.sh
source "$eval_dir/grid-checkpoint-lib.sh"

# An unset -j means "use the machine": one job by default wasted almost all of
# it, which is the difference between a smoke test and an evaluation.
if [ -z "$jobs" ]; then
  jobs=$(detect_jobs) || exit 2
  echo "[jobs] using $jobs parallel jobs"
fi
if [[ ! "$jobs" =~ ^[1-9][0-9]*$ ]]; then
  echo "Jobs must be a positive integer: $jobs" >&2
  exit 2
fi
repo_commit=$(git rev-parse HEAD)
grid_script_digest=$(hash_file "${BASH_SOURCE[0]}")
grid_helper_digest=$(hash_file "$eval_dir/grid-checkpoint-lib.sh")
results_root="$eval_dir/results/confirmation"
artifacts_dir="$eval_dir/artifacts/extraction-confirmation"
mkdir -p "$results_root" "$artifacts_dir"

premises=(knn-32 knn-64 knn-128 knn-256 knn-1024 nbayes-32 nbayes-64 nbayes-128 nbayes-256 nbayes-1024)
provers=(eprover vampire z3 cvc4)
consistency_provers=(eprover vampire)
corpora=(stdlib-regression dependent-slice external-equations)
labels=(current)

declare -A label_config
label_config[current]=current

if [ -n "$only_label" ] && ! array_contains "$only_label" "${labels[@]}"; then
  echo "Unknown confirmation label: $only_label" >&2
  exit 2
fi
if [ -n "$only_corpus" ] && ! array_contains "$only_corpus" "${corpora[@]}"; then
  echo "Unknown corpus: $only_corpus" >&2
  exit 2
fi

if [ "$sample_corpora" = true ]; then
  corpus_mode=sample
else
  corpus_mode=full
fi
declare -A corpus_source corpus_digest

if [ -n "$external_source" ] && [ ! -d "$external_source" ]; then
  echo "External source directory not found: $external_source" >&2
  exit 1
fi

# The full corpora are generated from the installed libraries rather than read
# out of eval/corpora, so their provenance is the library the run installed.
# That is only known once the label prefix exists, hence computing this per
# corpus at run time instead of once at startup.
compute_corpus_provenance() {
  local corpus="$1" prefix="$2" source_dir module digests=
  if [ "$corpus" = external-equations ] && [ -n "$external_source" ]; then
    source_dir=$(cd "$external_source" && pwd -P)
    corpus_source[$corpus]="$source_dir"
    corpus_digest[$corpus]=$(hash_tree "$source_dir")
    return 0
  fi
  if [ "$sample_corpora" = true ]; then
    source_dir="$eval_dir/corpora/$corpus/sample"
    corpus_source[$corpus]="${source_dir#"$repo"/}"
    corpus_digest[$corpus]=$(hash_tree "$source_dir")
    return 0
  fi
  case "$corpus" in
    stdlib-regression)
      corpus_source[$corpus]="installed-Stdlib modules=$stdlib_modules"
      for module in $stdlib_modules; do
        source_dir="$prefix/coq/user-contrib/Stdlib/$module"
        if [ ! -d "$source_dir" ]; then
          echo "Installed Stdlib module not found: $source_dir" >&2
          return 1
        fi
        digests+=$(hash_tree "$source_dir")
      done
      corpus_digest[$corpus]=$(printf '%s' "$digests" | sha256sum | awk '{ print $1 }')
      ;;
    external-equations)
      source_dir="$prefix/coq/user-contrib/Equations"
      if [ ! -d "$source_dir" ]; then
        echo "Installed Equations library not found: $source_dir" >&2
        echo "Install rocq-equations into the switch, or pass --external-source DIR." >&2
        return 1
      fi
      corpus_source[$corpus]="installed-Equations"
      corpus_digest[$corpus]=$(hash_tree "$source_dir")
      ;;
    *)
      source_dir="$eval_dir/corpora/$corpus"
      corpus_source[$corpus]="${source_dir#"$repo"/}"
      corpus_digest[$corpus]=$(hash_tree "$source_dir")
      ;;
  esac
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
    z3) require_cmd htimeout; require_cmd z3_tptp ;;
    cvc4) require_cmd htimeout; require_cmd cvc4 ;;
    *) echo "Unknown prover: $1" >&2; exit 1 ;;
  esac
}

base_path="$PATH"
base_ocamlpath="${OCAMLPATH:-}"

manifest_get() {
  local file="$1" key="$2"
  awk -F= -v key="$key" '$1 == key { print substr($0, index($0, "=") + 1); found=1; exit } END { if (!found) exit 1 }' "$file"
}

expect_manifest_value() {
  local manifest="$1" key="$2" expected="$3" actual
  actual=$(manifest_get "$manifest" "$key") || return 1
  [ "$actual" = "$expected" ]
}

manifest_matches_label() {
  local label="$1" prefix="$2" expected_commit
  local manifest="$prefix/manifest.env"
  [ "$label" = current ] && [ -f "$manifest" ] || return 1
  expected_commit=$(git rev-parse HEAD)
  expect_manifest_value "$manifest" kind current &&
    expect_manifest_value "$manifest" config current &&
    expect_manifest_value "$manifest" commit "$expected_commit"
}

prepare_corpus() {
  local corpus="$1" prefix="$2"
  local args=("$corpus" --coqlib "$prefix/coq")
  if [ "$sample_corpora" = true ]; then
    args+=(--sample)
  else
    args+=(--modules "$stdlib_modules")
  fi
  if [ "$corpus" = external-equations ] && [ -n "$external_source" ]; then
    args+=(--source "$external_source")
  fi
  ./prepare-corpus.sh "${args[@]}"
}

validate_generation() {
  local outdir="$1" premise
  status_is "$outdir/generation.status" generation_failed=0 || return 1
  [ -s "$outdir/prepared-files.lst" ] || return 1
  for premise in "${premises[@]}"; do
    list_is_nonempty_and_complete "$outdir/generated-$premise.lst" || return 1
  done
}

validate_prover_run() {
  local outdir="$1" prover="$2" premise="$3" prover_status
  status_has_integer "$outdir/prover-$prover-$premise.status" prover_exit || return 1
  list_is_nonempty_and_complete "$outdir/generated-$premise.lst" || return 1
  expected_atp_outputs_are_complete \
    "$outdir/generated-$premise.lst" "$outdir/atp-problems/$premise" \
    "$outdir/prover-outputs/$prover-$premise" "$prover" \
    "$outdir/prover-outputs-$prover-$premise.lst" "$outdir/$prover-$premise.log" || return 1
  if [ "$prover" = z3 ] && find "$outdir/prover-outputs/$prover-$premise" -type f -size 0 -print -quit | grep -q .; then
    prover_status=$(status_integer_value "$outdir/prover-$prover-$premise.status" prover_exit)
    [ "$prover_status" -ne 0 ]
  fi
}

validate_reconstruction_run() {
  local outdir="$1" premise prover problem atp_output recon_output
  local expected_count=0 actual_count reconstruction_status
  status_has_integer "$outdir/reconstruction.status" reconstruction_exit || return 1
  [ -s "$outdir/reconstr-prepared-files.lst" ] || return 1
  list_is_complete "$outdir/reconstr-outputs.lst" || return 1
  [ -f "$outdir/reconstr.full.log" ] && ! log_has_crash_or_error "$outdir/reconstr.full.log" || return 1
  for premise in "${premises[@]}"; do
    for prover in "${provers[@]}"; do
      while IFS= read -r problem; do
        [ -n "$problem" ] || continue
        atp_output="$outdir/prover-outputs/$prover-$premise/$(basename "$problem")"
        if grep -Eq 'SZS status Theorem' "$atp_output"; then
          recon_output="$outdir/reconstr-outputs/$prover-$premise/$(basename "${problem%.p}").out"
          [ -f "$recon_output" ] && grep -Eq '^(Success|Failure)( |$)' "$recon_output" || return 1
          grep -Fqx "$recon_output" "$outdir/reconstr-outputs.lst" || return 1
          expected_count=$((expected_count + 1))
        fi
      done < "$outdir/generated-$premise.lst"
    done
  done
  actual_count=$(list_nonempty_count "$outdir/reconstr-outputs.lst")
  [ "$actual_count" -eq "$expected_count" ] || return 1
  reconstruction_status=$(status_integer_value "$outdir/reconstruction.status" reconstruction_exit)
  [ "$reconstruction_status" -eq 0 ]
}

validate_consistency_run() {
  local outdir="$1" prover="$2" premise="$3" work
  work="$outdir/consistency/$prover-$premise"
  # Completeness is measured against the lemmas actually selected for this
  # cell, not every generated problem: the check deliberately covers only the
  # curated list.
  status_is "$outdir/consistency-$prover-$premise.status" consistency_exit=0 &&
    consistency_outputs_are_complete \
      "$outdir/consistency-selected-$prover-$premise.lst" \
      "$work/outputs" "$work/raw" "$work/status" \
      "$outdir/consistency-outputs-$prover-$premise.lst"
}

build_label() {
  local label="$1"
  local prefix="$eval_dir/_installs/$label"
  if [ -f "$prefix/manifest.env" ]; then
    if manifest_matches_label "$label" "$prefix"; then
      echo "[build] $label already installed"
      return 0
    fi
    if [ "$skip_builds" = true ]; then
      echo "Install prefix for $label is stale or mismatched: $prefix" >&2
      exit 1
    fi
    echo "[build] $label install is stale or mismatched; rebuilding"
    rm -rf "$prefix"
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
  if [ "$label" = current ]; then
    (cd "$eval_dir" && ./rebuild-config.sh current --label "$label")
  else
    (cd "$eval_dir" && ./rebuild-config.sh "${label_config[$label]}" --label "$label")
  fi
}

run_generation() {
  local label="$1" corpus="$2" prefix="$3"
  local outdir="$results_root/$label/$corpus"
  mkdir -p "$outdir"
  local marker="$outdir/generate"
  if checkpoint_done "$marker" generation "$label" "$corpus" "$prefix"; then
    if validate_generation "$outdir"; then
      echo "[gen] $label/$corpus already done"
      return 0
    fi
    invalidate_checkpoint "$marker" "generation artifacts are incomplete or invalid"
  fi

  rm -f "$outdir/generation.status" "$marker.done"
  clear_downstream_results "$outdir"
  echo "[gen] $label/$corpus"
  prepare_prefix_env "$prefix"
  cd "$eval_dir"
  prepare_corpus "$corpus" "$prefix" > "$outdir/prepared-files.lst"
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
    echo "ATP generation failed for $label/$corpus; see $outdir/gen-atp.full.log" >&2
    exit 1
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
    if ! list_is_nonempty_and_complete "$outdir/generated-$premise.lst"; then
      echo "No generated ATP problems for $premise in $label/$corpus" >&2
      exit 1
    fi
  done
  echo "generation_failed=0" > "$outdir/generation.status"
  mark_checkpoint "$marker" generation "$label" "$corpus" "$prefix"
}

run_prover() {
  local label="$1" corpus="$2" premise="$3" prover="$4" prefix="$5"
  local outdir="$results_root/$label/$corpus"
  local marker="$outdir/prover-$prover-$premise" input_digest
  input_digest=$(hash_tree "$outdir/atp-problems/$premise")
  if checkpoint_done "$marker" prover "$label" "$corpus" "$prefix" \
      "premise=$premise" "prover=$prover" "timeout=$tim" "input_sha256=$input_digest"; then
    if validate_prover_run "$outdir" "$prover" "$premise"; then
      echo "[prover] $label/$corpus/$prover/$premise already done"
      return 0
    fi
    invalidate_checkpoint "$marker" "prover status or outputs are incomplete or invalid"
  fi

  rm -f "$marker.done" "$outdir/prover-$prover-$premise.status"
  if ! list_is_nonempty_and_complete "$outdir/generated-$premise.lst"; then
    echo "Cannot run $prover: no generated problems for $label/$corpus/$premise" >&2
    return 1
  fi
  echo "[prover] $label/$corpus/$prover/$premise"
  prepare_prefix_env "$prefix"
  require_prover "$prover"
  cd "$eval_dir"
  rm -rf atp/i "atp/o/$prover" "atp/o/$prover-$premise"
  mkdir -p atp/i atp/o
  ln -s "$outdir/atp-problems/$premise" atp/i/f
  if make -C atp -k -j "$jobs" TIM="$tim" "$prover" > "$outdir/$prover-$premise.log" 2>&1; then
    prover_status=0
  else
    prover_status=$?
    echo "[prover] $label/$corpus/$prover/$premise exited with status $prover_status; keeping partial outputs"
  fi
  echo "prover_exit=$prover_status" > "$outdir/prover-$prover-$premise.status"
  rm -rf "$outdir/prover-outputs/$prover-$premise"
  mkdir -p "$outdir/prover-outputs" "atp/o/$prover"
  mv "atp/o/$prover" "$outdir/prover-outputs/$prover-$premise"
  find "$outdir/prover-outputs/$prover-$premise" -type f | sort > "$outdir/prover-outputs-$prover-$premise.lst"
  if ! validate_prover_run "$outdir" "$prover" "$premise"; then
    echo "Prover run produced incomplete, malformed, or crashed outputs for $label/$corpus/$prover/$premise" >&2
    return 1
  fi
  mark_checkpoint "$marker" prover "$label" "$corpus" "$prefix" \
    "premise=$premise" "prover=$prover" "timeout=$tim" "input_sha256=$input_digest"
}

run_reconstruction() {
  local label="$1" corpus="$2" prefix="$3"
  local outdir="$results_root/$label/$corpus"
  local marker="$outdir/reconstruction" input_digest reconstruction_status
  input_digest=$(hash_tree "$outdir/prover-outputs")
  if checkpoint_done "$marker" reconstruction "$label" "$corpus" "$prefix" \
      "prover_timeout=$tim" "input_sha256=$input_digest"; then
    if validate_reconstruction_run "$outdir"; then
      echo "[reconstr] $label/$corpus already done"
      return 0
    fi
    invalidate_checkpoint "$marker" "reconstruction status or outputs are incomplete or invalid"
  fi

  rm -f "$marker.done" "$outdir/reconstruction.status"
  echo "[reconstr] $label/$corpus"
  prepare_prefix_env "$prefix"
  cd "$eval_dir"
  prepare_corpus "$corpus" "$prefix" > "$outdir/reconstr-prepared-files.lst"
  rm -rf logs/reconstr atp/o out coqhammer.opt
  mkdir -p atp/o out
  for premise in "${premises[@]}"; do
    for prover in "${provers[@]}"; do
      ln -s "$outdir/prover-outputs/$prover-$premise" "atp/o/$prover-$premise"
    done
  done
  echo reconstr > coqhammer.opt
  coqc_cmd="rocq c -coqlib $prefix/coq"
  if make -k -j "$jobs" reconstr COQC="$coqc_cmd" > "$outdir/reconstr.full.log" 2>&1; then
    reconstruction_status=0
  else
    reconstruction_status=$?
  fi
  echo "reconstruction_exit=$reconstruction_status" > "$outdir/reconstruction.status"
  rm -rf "$outdir/reconstr-outputs"
  mkdir -p "$outdir/reconstr-outputs"
  if [ -d out ]; then
    cp -R out/. "$outdir/reconstr-outputs/"
  fi
  find "$outdir/reconstr-outputs" -type f | sort > "$outdir/reconstr-outputs.lst"
  if ! validate_reconstruction_run "$outdir"; then
    echo "Reconstruction produced incomplete or invalid outputs for $label/$corpus; see $outdir/reconstr.full.log" >&2
    return 1
  fi
  mark_checkpoint "$marker" reconstruction "$label" "$corpus" "$prefix" \
    "prover_timeout=$tim" "input_sha256=$input_digest"
}

# Run one false-conjecture problem and record its raw log, filtered output, and
# exit status.  Kept separate so the consistency pool can run it in background
# workers; it must not depend on any state the parent mutates concurrently.
run_consistency_problem() {
  local prover="$1" problem="$2" work="$3"
  local name command_status
  name=$(basename "$problem")
  if [ "$prover" = eprover ]; then
    if eprover -s --cpu-limit="$consistency_tim" --auto-schedule -R --print-statistics -p --tstp-format "$problem" \
        > "$work/raw/$name" 2>&1; then
      command_status=0
    else
      command_status=$?
    fi
    grep "file[(]'\|# SZS\|SZS status" "$work/raw/$name" > "$work/outputs/$name" || true
  else
    # Give the external kill a grace margin over Vampire's own deadline, so a
    # loaded machine cannot SIGKILL it before it reports its SZS status.
    if htimeout "$((consistency_tim + 5))" vampire --mode casc -t "$consistency_tim" --proof tptp \
        --output_axiom_names on "$problem" > "$work/raw/$name" 2>&1; then
      command_status=0
    else
      command_status=$?
    fi
    grep "file[(]'\|% SZS\|SZS status" "$work/raw/$name" > "$work/outputs/$name" || true
  fi
  echo "command_exit=$command_status" > "$work/status/$name.status"
}

run_consistency() {
  local label="$1" corpus="$2" premise="$3" prover="$4" prefix="$5"
  local outdir="$results_root/$label/$corpus"
  local marker="$outdir/consistency-$prover-$premise" input_digest
  # Restrict the check to lemmas whose hypotheses are known to be satisfiable.
  # The rewritten problems keep the goal's own hypotheses as axioms, so a
  # vacuously true lemma is refutable no matter how faithful the translation
  # is; see the corpus list for the worked stdlib example.
  local lemma_list="$eval_dir/corpora/$corpus/consistency-lemmas.txt" lemmas_digest=none
  [ -f "$lemma_list" ] && lemmas_digest=$(hash_file "$lemma_list")
  input_digest=$(hash_tree "$outdir/atp-problems/$premise")
  if checkpoint_done "$marker" consistency "$label" "$corpus" "$prefix" \
      "premise=$premise" "prover=$prover" "timeout=$consistency_tim" \
      "lemmas_sha256=$lemmas_digest" \
      "input_sha256=$input_digest"; then
    if validate_consistency_run "$outdir" "$prover" "$premise"; then
      echo "[consistency] $label/$corpus/$prover/$premise already done"
      return 0
    fi
    invalidate_checkpoint "$marker" "consistency status or outputs are incomplete or invalid"
  fi

  rm -f "$marker.done" "$outdir/consistency-$prover-$premise.status"
  if ! list_is_nonempty_and_complete "$outdir/generated-$premise.lst"; then
    echo "Cannot run consistency check: no problems for $label/$corpus/$premise" >&2
    return 1
  fi
  echo "[consistency] $label/$corpus/$prover/$premise"
  prepare_prefix_env "$prefix"
  require_prover "$prover"
  local work="$outdir/consistency/$prover-$premise"
  rm -rf "$work"
  mkdir -p "$work/problems" "$work/outputs" "$work/raw" "$work/status"

  if [ ! -f "$lemma_list" ]; then
    # No curated list means this corpus cannot be checked yet.  Skip it rather
    # than abort the grid, but leave no checkpoint, so the check runs as soon
    # as a list exists.  The skip is recorded so a summary never reads as if
    # the corpus had passed.
    echo "consistency_skipped=no_lemma_list" > "$outdir/consistency-$prover-$premise.status"
    echo "[consistency] SKIPPED $label/$corpus/$prover/$premise: no curated lemma list" >&2
    echo "  Create $lemma_list to enable the check for this corpus." >&2
    return 0
  fi

  python3 - "$outdir/atp-problems/$premise" "$work/problems" "$lemma_list" <<'PY'
import pathlib
import re
import sys
src = pathlib.Path(sys.argv[1])
dst = pathlib.Path(sys.argv[2])
listed = []
for line in pathlib.Path(sys.argv[3]).read_text().splitlines():
    line = line.strip()
    if line and not line.startswith('#'):
        listed.append(line)
for name in listed:
    path = src / (name + '.p')
    if not path.exists():
        continue
    text = path.read_text()
    text, n = re.subn(r"fof\(([^,]+),\s*conjecture,\s*.*?\)\.\s*$",
                      r"fof(\1, conjecture, $false).",
                      text, count=1, flags=re.M)
    if n != 1:
        raise SystemExit(f"did not rewrite exactly one conjecture in {path}")
    (dst / path.name).write_text(text)
PY

  # Record which lemmas this cell is expected to cover, derived from the
  # curated list and the problems actually generated for this premise.  The
  # validator compares outputs against this, so a lemma that was selected but
  # produced nothing is still caught.
  local selected_list="$outdir/consistency-selected-$prover-$premise.lst"
  local lemma
  : > "$selected_list"
  while IFS= read -r lemma; do
    lemma=${lemma%%#*}
    lemma=$(printf '%s' "$lemma" | tr -d '[:space:]')
    [ -n "$lemma" ] || continue
    [ -f "$outdir/atp-problems/$premise/$lemma.p" ] || continue
    echo "$work/problems/$lemma.p" >> "$selected_list"
  done < "$lemma_list"

  local problems=("$work/problems"/*.p)
  if [ ! -e "${problems[0]}" ]; then
    echo "No listed consistency lemma is present in $label/$corpus/$premise" >&2
    echo "Check $lemma_list against the generated problem names." >&2
    return 1
  fi
  # Every problem here is independent, so run them through a worker pool rather
  # than one at a time: this phase covers the same problem set as the prover
  # phase, and serialised it dominated the whole grid.  The pool follows
  # tests/plugin/check-consistency.sh -- fill up to $jobs background jobs, then
  # wait for the batch.  Crash and missing-status detection moves to a scan
  # after the joins, since a worker cannot abort the loop from a subshell.
  local job_pids=() running=0 problem name
  for problem in "${problems[@]}"; do
    run_consistency_problem "$prover" "$problem" "$work" &
    job_pids+=("$!")
    running=$((running + 1))
    if [ "$running" -ge "$jobs" ]; then
      wait "${job_pids[@]}" || true
      job_pids=()
      running=0
    fi
  done
  if [ "$running" -gt 0 ]; then
    wait "${job_pids[@]}" || true
  fi

  for problem in "${problems[@]}"; do
    name=$(basename "$problem")
    if log_has_crash_or_error_ignoring_strategy_aborts "$work/raw/$name" ||
        ! szs_terminal_status "$work/outputs/$name"; then
      echo "consistency_exit=1" > "$outdir/consistency-$prover-$premise.status"
      echo "Consistency prover crashed or produced no terminal status for $label/$corpus/$prover/$premise/$name" >&2
      return 1
    fi
  done
  if grep -RE "SZS status (Theorem|Unsatisfiable|ContradictoryAxioms)|^unsat$" "$work/outputs" >/dev/null 2>&1; then
    echo "consistency_exit=1" > "$outdir/consistency-$prover-$premise.status"
    echo "Inconsistency hit for $label/$corpus/$prover/$premise; see $work/outputs" >&2
    return 1
  fi
  find "$work/outputs" -type f | sort > "$outdir/consistency-outputs-$prover-$premise.lst"
  echo "consistency_exit=0" > "$outdir/consistency-$prover-$premise.status"
  if ! validate_consistency_run "$outdir" "$prover" "$premise"; then
    echo "Consistency check produced incomplete outputs for $label/$corpus/$prover/$premise" >&2
    return 1
  fi
  mark_checkpoint "$marker" consistency "$label" "$corpus" "$prefix" \
    "premise=$premise" "prover=$prover" "timeout=$consistency_tim" \
    "lemmas_sha256=$lemmas_digest" \
    "input_sha256=$input_digest"
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
    compute_corpus_provenance "$corpus" "$prefix"
    run_generation "$label" "$corpus" "$prefix"
    for premise in "${premises[@]}"; do
      for prover in "${provers[@]}"; do
        run_prover "$label" "$corpus" "$premise" "$prover" "$prefix"
      done
      # The committed confirmation corpora are intentionally small, so scan all
      # generated problems (rather than a sample) with E prover and Vampire.  This
      # includes every canary/eq_rect/WF problem in the confirmation configurations.
      for prover in "${consistency_provers[@]}"; do
        run_consistency "$label" "$corpus" "$premise" "$prover" "$prefix"
      done
    done
    run_reconstruction "$label" "$corpus" "$prefix"
  done
done

echo "Extraction confirmation checkpoints complete."
echo "  raw checkpoints: $results_root"
if [ -n "$only_label" ] || [ -n "$only_corpus" ]; then
  echo "  summary:         not updated by a partial run"
else
  summarizer="$eval_dir/tools/summarize-confirmation.py"
  python3 "$summarizer" \
    "$results_root" "$artifacts_dir/summary.tsv" "$artifacts_dir/analysis.md" \
    "${labels[@]}"
  write_grid_provenance "$artifacts_dir/provenance.env" confirmation \
    "$summarizer" "$artifacts_dir/summary.tsv" "$artifacts_dir/analysis.md"
  echo "  summary:         $artifacts_dir/summary.tsv"
  echo "  analysis:        $artifacts_dir/analysis.md"
  echo "  provenance:      $artifacts_dir/provenance.env"
fi
