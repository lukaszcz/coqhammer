#!/usr/bin/env bash
# Shared checkpoint provenance and artifact validation for extraction grids.

# Shared by detect_jobs for its three tunables (EVAL_JOBS,
# EVAL_MEMORY_PER_JOB_MB, EVAL_RESERVE_MB): all three must be positive
# integers, since any of them being zero or non-numeric would otherwise reach
# an arithmetic context below and fail with an opaque shell error.  A leading
# zero is rejected too: "00" is zero and would divide by zero, and the shell
# reads "010" in an arithmetic context as octal, silently using a different
# value than the one written.
validate_positive_int() {
  local name="$1" value="$2"
  case "$value" in
    ''|*[!0-9]*|0*) echo "$name must be a positive integer" >&2; return 1 ;;
  esac
}

# Size a job pool from the machine rather than defaulting to one job.  Follows
# tests/plugin/check-consistency.sh: take the core count, then cap it so the
# concurrent ATP processes fit in available memory, since a prover on a large
# problem is far more likely to exhaust RAM than CPU.  EVAL_JOBS pins the value
# outright; EVAL_MEMORY_PER_JOB_MB and EVAL_RESERVE_MB tune the memory model.
detect_jobs() {
  local cores available_kb reserve_kb per_job_kb memory_jobs
  local per_job_mb=${EVAL_MEMORY_PER_JOB_MB:-4096}
  local reserve_mb=${EVAL_RESERVE_MB:-4096}

  cores=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
  case "$cores" in
    ''|*[!0-9]*|0) cores=1 ;;
  esac

  if [ -n "${EVAL_JOBS:-}" ]; then
    validate_positive_int EVAL_JOBS "$EVAL_JOBS" || return 1
    echo "$EVAL_JOBS"
    return 0
  fi

  validate_positive_int EVAL_MEMORY_PER_JOB_MB "$per_job_mb" || return 1
  validate_positive_int EVAL_RESERVE_MB "$reserve_mb" || return 1

  available_kb=$(awk '$1 == "MemAvailable:" { print $2; exit }' /proc/meminfo 2>/dev/null || true)
  case "$available_kb" in
    ''|*[!0-9]*) echo "$cores"; return 0 ;;
  esac

  reserve_kb=$((reserve_mb * 1024))
  per_job_kb=$((per_job_mb * 1024))
  if [ "$available_kb" -le "$reserve_kb" ]; then
    echo 1
    return 0
  fi

  memory_jobs=$(( (available_kb - reserve_kb) / per_job_kb ))
  [ "$memory_jobs" -ge 1 ] || memory_jobs=1
  if [ "$memory_jobs" -lt "$cores" ]; then
    echo "$memory_jobs"
  else
    echo "$cores"
  fi
}

hash_tree() {
  local root="$1"
  python3 - "$root" <<'PY'
import hashlib
import pathlib
import sys

root = pathlib.Path(sys.argv[1]).resolve()
if not root.is_dir():
    raise SystemExit(f"checkpoint input directory not found: {root}")
digest = hashlib.sha256()
for path in sorted(p for p in root.rglob("*") if p.is_file()):
    relative_path = path.relative_to(root)
    if ".git" in relative_path.parts or "_build" in relative_path.parts:
        continue
    relative = relative_path.as_posix().encode()
    digest.update(len(relative).to_bytes(8, "big"))
    digest.update(relative)
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
print(digest.hexdigest())
PY
}

hash_file() {
  sha256sum "$1" | awk '{ print $1 }'
}

# Hash a sequence of NAME FILE pairs with boundaries, so callers can record a
# composite runtime harness without depending on path spelling or concatenation.
hash_harness_sources() {
  python3 - "$@" <<'PY'
import hashlib
import pathlib
import sys

arguments = sys.argv[1:]
if len(arguments) % 2:
    raise SystemExit("internal error: unpaired harness provenance argument")
digest = hashlib.sha256()
for name, filename in zip(arguments[::2], arguments[1::2]):
    data = pathlib.Path(filename).read_bytes()
    encoded_name = name.encode()
    digest.update(len(encoded_name).to_bytes(8, "big"))
    digest.update(encoded_name)
    digest.update(len(data).to_bytes(8, "big"))
    digest.update(data)
print(digest.hexdigest())
PY
}

compile_checkpoint_fields() {
  local stage="$1"
  case "$stage" in
    generation|reconstruction)
      # Globals are initialized by each grid before checkpoints are inspected.
      # shellcheck disable=SC2154
      printf '%s\n' \
        "compile_supervisor_sha256=$compile_supervisor_digest" \
        "compile_timeout=$compile_timeout" \
        "compile_timeout_grace=$compile_timeout_grace"
      ;;
  esac
}

report_compile_timeouts() {
  local source="$1"
  [ -e "$source" ] || return 0
  grep -rhF 'rocq-compile-supervisor: TIMEOUT ' -- "$source" >&2 || true
}

# SIGKILL can interrupt paired_output.ml between creating its same-directory
# temporaries and its cleanup handler. Delete regular temporary files only;
# never follow or remove a symlink with a matching hostile name.
cleanup_paired_output_temporaries() {
  local root="$1"
  [ -d "$root" ] || return 0
  find "$root" -type f -name '.coqhammer-pair-*.tmp' -delete
}

hash_checkpoint_markers() {
  local root="$1"
  python3 - "$root" <<'PY'
import hashlib
import pathlib
import sys

root = pathlib.Path(sys.argv[1]).resolve()
digest = hashlib.sha256()
markers = sorted(root.rglob("*.done")) if root.is_dir() else []
if not markers:
    raise SystemExit(f"no completed checkpoint markers found under {root}")
for path in markers:
    relative = path.relative_to(root).as_posix().encode()
    content = path.read_bytes()
    digest.update(len(relative).to_bytes(8, "big"))
    digest.update(relative)
    digest.update(len(content).to_bytes(8, "big"))
    digest.update(content)
print(digest.hexdigest())
PY
}

# The grid scripts define the arrays and scalar values referenced here.
# shellcheck disable=SC2154
write_grid_provenance() {
  local output="$1" grid_name="$2" summarizer="$3" summary="$4" analysis="$5"
  local temporary="$output.tmp.$$" label corpus
  {
    printf '%s\n' \
      'provenance_version=1' \
      "grid=$grid_name" \
      "repository_commit=$repo_commit" \
      "grid_script_sha256=$grid_script_digest" \
      "checkpoint_helper_sha256=$grid_helper_digest" \
      "summarizer_sha256=$(hash_file "$summarizer")" \
      "compile_supervisor_sha256=$compile_supervisor_digest" \
      "compile_timeout=$compile_timeout" \
      "compile_timeout_grace=$compile_timeout_grace" \
      "prover_timeout=$tim" \
      "consistency_timeout=$consistency_tim" \
      "checkpoint_markers_sha256=$(hash_checkpoint_markers "$results_root")" \
      "summary_sha256=$(hash_file "$summary")" \
      "analysis_sha256=$(hash_file "$analysis")"
    for label in "${labels[@]}"; do
      printf '%s\n' \
        "label.$label.config=${label_config[$label]}" \
        "label.$label.install_commit=$(manifest_value "$eval_dir/_installs/$label/manifest.env" commit)" \
        "label.$label.install_kind=$(manifest_value "$eval_dir/_installs/$label/manifest.env" kind)" \
        "label.$label.install_manifest_sha256=$(hash_file "$eval_dir/_installs/$label/manifest.env")"
    done
    for corpus in "${corpora[@]}"; do
      printf '%s\n' \
        "corpus.$corpus.mode=$corpus_mode" \
        "corpus.$corpus.source=${corpus_source[$corpus]}" \
        "corpus.$corpus.sha256=${corpus_digest[$corpus]}"
    done
  } > "$temporary"
  mv "$temporary" "$output"
}

manifest_value() {
  local manifest="$1" key="$2"
  awk -F= -v key="$key" '$1 == key { print substr($0, index($0, "=") + 1); exit }' "$manifest"
}

checkpoint_contents() {
  # These globals are initialized by the grid script after sourcing this file.
  # shellcheck disable=SC2154
  local stage="$1" label="$2" corpus="$3" prefix="$4"
  shift 4
  # shellcheck disable=SC2154
  printf '%s\n' \
    'checkpoint_version=3' \
    "stage=$stage" \
    "repository_commit=$repo_commit" \
    "grid_script_sha256=$grid_script_digest" \
    "checkpoint_helper_sha256=$grid_helper_digest" \
    "label=$label" \
    "config=${label_config[$label]}" \
    "install_commit=$(manifest_value "$prefix/manifest.env" commit)" \
    "install_kind=$(manifest_value "$prefix/manifest.env" kind)" \
    "install_manifest_sha256=$(hash_file "$prefix/manifest.env")" \
    "corpus=$corpus" \
    "corpus_mode=$corpus_mode" \
    "corpus_source=${corpus_source[$corpus]}" \
    "corpus_sha256=${corpus_digest[$corpus]}" \
    "$@"
}

checkpoint_matches() {
  local marker="$1"
  shift
  [ -f "$marker.done" ] || return 1
  if checkpoint_contents "$@" | cmp -s - "$marker.done"; then
    return 0
  fi
  echo "[checkpoint] stale provenance in $marker.done; rerunning" >&2
  rm -f "$marker.done"
  return 1
}

checkpoint_done() {
  local marker="$1"
  shift
  # shellcheck disable=SC2154
  if [ "$force" = true ]; then
    rm -f "$marker.done"
    return 1
  fi
  checkpoint_matches "$marker" "$@"
}

mark_checkpoint() {
  local marker="$1"
  shift
  local temporary="$marker.done.tmp.$$"
  checkpoint_contents "$@" > "$temporary"
  mv "$temporary" "$marker.done"
}

invalidate_checkpoint() {
  local marker="$1" reason="$2"
  echo "[checkpoint] $reason; rerunning $marker" >&2
  rm -f "$marker.done"
}

array_contains() {
  local needle="$1" item
  shift
  for item in "$@"; do
    [ "$item" = "$needle" ] && return 0
  done
  return 1
}

status_is() {
  local file="$1" expected="$2"
  [ -f "$file" ] && [ "$(wc -l < "$file")" -eq 1 ] && grep -Fqx "$expected" "$file"
}

status_has() {
  local file="$1" expected="$2"
  [ -f "$file" ] && grep -Fqx "$expected" "$file"
}

status_has_integer() {
  local file="$1" key="$2"
  [ -f "$file" ] && [ "$(wc -l < "$file")" -eq 1 ] &&
    grep -Eq "^${key}=[0-9]+$" "$file"
}

status_integer_value() {
  local file="$1" key="$2"
  status_has_integer "$file" "$key" || return 1
  sed -n "s/^${key}=//p" "$file"
}

list_is_complete() {
  local list="$1" require_nonempty="${2:-false}" entry count=0
  [ -f "$list" ] || return 1
  while IFS= read -r entry; do
    [ -n "$entry" ] || continue
    if [[ "$entry" != /* ]]; then
      # prepare-corpus.sh reports paths relative to eval/.
      # shellcheck disable=SC2154
      entry="$eval_dir/$entry"
    fi
    [ -f "$entry" ] || return 1
    count=$((count + 1))
  done < "$list"
  [ "$require_nonempty" = false ] || [ "$count" -gt 0 ]
}

list_is_nonempty_and_complete() {
  list_is_complete "$1" true
}

list_nonempty_count() {
  awk 'NF { count++ } END { print count + 0 }' "$1"
}

szs_terminal_status() {
  local file="$1" statuses count
  [ -s "$file" ] || return 1
  statuses=$(grep -Eo 'SZS status [[:alpha:]]+' "$file" || true)
  count=$(printf '%s\n' "$statuses" | awk 'NF { count++ } END { print count + 0 }')
  [ "$count" -eq 1 ] || return 1
  grep -Eq '^SZS status (Theorem|CounterTheorem|Unsatisfiable|Satisfiable|CounterSatisfiable|ContradictoryAxioms|GaveUp|Timeout|ResourceOut|MemoryOut|Unknown|Incomplete)$' <<< "$statuses"
}

atp_output_is_complete() {
  local prover="$1" output="$2"
  [ -f "$output" ] || return 1
  if [ ! -s "$output" ]; then
    # The htimeout backstop is the enforced limit: a prover's own deadline is
    # advisory and not all of them honour it (CVC4 can overrun --tlimit several
    # times over on a hard problem).  A prover killed before it printed a status
    # found no proof within the budget, which is a result, not a broken run.
    # The empty output records that; it never counts as a success downstream.
    # E prover is not run under htimeout (see eval/atp/Makefile): nothing
    # external kills it before it reports its own SZS status, so an empty
    # output from it is not that backstop outcome but a broken run.
    [ "$prover" = eprover ] && return 1
    return 0
  fi
  szs_terminal_status "$output"
}

log_has_crash_or_infrastructure_error() {
  local log="$1"
  [ -f "$log" ] || return 0
  grep -Eiq '(segmentation fault|segfault|core dumped|bus error|floating point exception|aborted|anomaly|assertion[^[:cntrl:]]*failed|uncaught exception|traceback|command not found|no such file or directory|no rule to make target|permission denied|cannot execute|exec[^[:cntrl:]]*failed|(^|[^[:alpha:]])killed([^[:alpha:]]|$)|out of memory|cannot allocate memory|no space left on device|input/output error|stack overflow|broken pipe|(^|[^[:alpha:]])(fatal|internal|system)[[:space:]_-]+(error|exception)([[:space:]:]|$))' "$log"
}

# Portfolio provers report the death of an individual child strategy in their
# own output and then carry on with the remaining schedule.  Vampire prints
# "% Aborted by signal SIGSEGV on FILE" for such a strategy; the run as a whole
# still terminates with a regular SZS status.  Callers that separately require a
# terminal SZS status use this to scan a raw prover log without mistaking a
# recovered per-strategy abort for a crash of the prover invocation.
strip_portfolio_strategy_aborts() {
  # Vampire's portfolio reports each child strategy that dies while the run
  # itself continues and still ends with a terminal SZS status.  The strategies
  # write concurrently, so the notice frequently lands in the middle of another
  # line rather than on one of its own -- match it anywhere, not just at the
  # start, or the interleaved copies read as a crash.  A crashed strategy also
  # prints a fixed hint pointing at --traceback; that hint belongs to the same
  # recovered abort, and the word "traceback" in it trips the crash scan on its
  # own, so drop it as well.
  sed -E \
    -e 's/% Aborted by signal [[:upper:]]+ on [^[:space:]]*//g' \
    -e "s/use '--traceback on' to invoke a debugger and get a human-readable stack trace//g" \
    "$1"
}

log_has_crash_or_error_ignoring_strategy_aborts() {
  local log="$1" filtered
  [ -f "$log" ] || return 0
  filtered=$(mktemp)
  strip_portfolio_strategy_aborts "$log" > "$filtered"
  if log_has_crash_or_error "$filtered"; then
    rm -f "$filtered"
    return 0
  fi
  rm -f "$filtered"
  return 1
}

# When htimeout kills a prover that overran its own deadline, the shell reports
# "Killed" and make reports the resulting 137 (128 + SIGKILL) exit.  That is the
# backstop doing its job, and the prover's empty output already records that it
# produced no result; see atp_output_is_complete.  Drop just those two lines so
# the remaining scan still catches genuine infrastructure failures.
strip_backstop_kill_reports() {
  grep -Ev "^(Killed|make(\[[0-9]+\])?: \*\*\* \[[^]]*\] Error 137)$" "$1" || true
}

log_has_crash_or_error_ignoring_backstop_kills() {
  local log="$1" filtered status
  [ -f "$log" ] || return 0
  filtered=$(mktemp)
  strip_backstop_kill_reports "$log" | strip_portfolio_strategy_aborts /dev/stdin > "$filtered"
  if log_has_crash_or_error "$filtered"; then
    status=0
  else
    status=1
  fi
  rm -f "$filtered"
  return "$status"
}

log_has_crash_or_error() {
  local log="$1"
  log_has_crash_or_infrastructure_error "$log" && return 0
  grep -Eiv '^(make(\[[0-9]+\])?: (\*\*\* .* Error [0-9]+|Target .* not remade because of errors\.|Entering directory|Leaving directory))$' "$log" |
    grep -Eiq '((^|[^[:alpha:]])(parse|input)?[[:space:]_-]*error([:[:space:]]|$))'
}

expected_atp_outputs_are_complete() {
  local generated="$1" problem_root="$2" output_dir="$3" prover="$4" output_list="$5" log="$6"
  local problem relative output expected_count=0 actual_count
  [ -f "$generated" ] && [ -f "$output_list" ] && [ -f "$log" ] || return 1
  log_has_crash_or_error_ignoring_backstop_kills "$log" && return 1
  while IFS= read -r problem; do
    [ -n "$problem" ] || continue
    case "$problem" in
      "$problem_root"/*) relative=${problem#"$problem_root"/} ;;
      *) return 1 ;;
    esac
    output="$output_dir/$relative"
    atp_output_is_complete "$prover" "$output" || return 1
    grep -Fqx "$output" "$output_list" || return 1
    expected_count=$((expected_count + 1))
  done < "$generated"
  actual_count=$(list_nonempty_count "$output_list")
  [ "$expected_count" -gt 0 ] && [ "$actual_count" -eq "$expected_count" ] &&
    list_is_nonempty_and_complete "$output_list"
}

consistency_outputs_are_complete() {
  local generated="$1" output_dir="$2" raw_dir="$3" status_dir="$4" output_list="$5"
  local problem name output raw command_status expected_count=0 actual_count
  [ -f "$generated" ] && [ -f "$output_list" ] || return 1
  while IFS= read -r problem; do
    [ -n "$problem" ] || continue
    name=$(basename "$problem")
    output="$output_dir/$name"
    raw="$raw_dir/$name"
    command_status="$status_dir/$name.status"
    [ -f "$raw" ] && ! log_has_crash_or_error_ignoring_strategy_aborts "$raw" || return 1
    szs_terminal_status "$output" || return 1
    status_has_integer "$command_status" command_exit || return 1
    grep -Fqx "$output" "$output_list" || return 1
    expected_count=$((expected_count + 1))
  done < "$generated"
  actual_count=$(list_nonempty_count "$output_list")
  [ "$expected_count" -gt 0 ] && [ "$actual_count" -eq "$expected_count" ] &&
    list_is_nonempty_and_complete "$output_list"
}
