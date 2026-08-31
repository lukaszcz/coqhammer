#!/bin/sh
set -eu

TIMEOUT=${CONSISTENCY_TIMEOUT:-15}
TMPDIR_BASE=${TMPDIR:-/tmp}

# The statuses `timeout` reports when it has to kill the command it wraps: 124
# for its default SIGTERM, and 128 + 9 for the SIGKILL we ask it for.
TIMEOUT_SIGTERM_STATUS=124
TIMEOUT_SIGKILL_STATUS=137

# The cleanup trap below cannot run when the script is hard-killed (SIGKILL, or
# a session teardown that kills the process group), and each run leaves over a
# hundred megabytes of TPTP problems behind.  Sweep our own leftovers first, as
# src/plugin/opt.ml does for invocation directories.  The sweep is confined to
# directories of this name form that we own and that nothing has touched for a
# day, so a concurrent run is never disturbed.
sweep_stale_tmpdirs() {
  find "$TMPDIR_BASE" -maxdepth 1 -type d -name 'coqhammer-consistency.*' \
    -user "$(id -u)" -mtime +0 -exec rm -rf {} + 2>/dev/null || true
}
sweep_stale_tmpdirs

tmpdir=$(mktemp -d "$TMPDIR_BASE/coqhammer-consistency.XXXXXX")
cleanup() {
  rm -rf "$tmpdir"
}
trap cleanup EXIT HUP INT TERM

fail() {
  echo "consistency canary FAILED: $*" >&2
  exit 1
}

show_prover_output() {
  prover=$1
  out=$2
  label=$3

  echo "----- $prover output for $label -----" >&2
  cat "$out" >&2
}

positive_integer() {
  case "$1" in
    ''|*[!0-9]*|0) return 1 ;;
    *) return 0 ;;
  esac
}

detect_workers() {
  cores=$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)
  case "$cores" in
    ''|*[!0-9]*|0) cores=1 ;;
  esac

  if [ -n "${CONSISTENCY_JOBS:-}" ]; then
    positive_integer "$CONSISTENCY_JOBS" || fail "CONSISTENCY_JOBS must be a positive integer"
    if [ "$CONSISTENCY_JOBS" -lt "$cores" ]; then
      cores=$CONSISTENCY_JOBS
    fi
    echo "$cores"
    return
  fi

  per_job_mb=${CONSISTENCY_MEMORY_PER_JOB_MB:-2048}
  reserve_mb=${CONSISTENCY_RESERVE_MB:-4096}
  positive_integer "$per_job_mb" || fail "CONSISTENCY_MEMORY_PER_JOB_MB must be a positive integer"
  positive_integer "$reserve_mb" || fail "CONSISTENCY_RESERVE_MB must be a positive integer"

  available_kb=$(awk '$1 == "MemAvailable:" { print $2; exit }' /proc/meminfo 2>/dev/null || true)
  case "$available_kb" in
    ''|*[!0-9]*) echo "$cores"; return ;;
  esac

  reserve_kb=$((reserve_mb * 1024))
  per_job_kb=$((per_job_mb * 1024))
  if [ "$available_kb" -le "$reserve_kb" ]; then
    echo 1
    return
  fi

  memory_workers=$(( (available_kb - reserve_kb) / per_job_kb ))
  [ "$memory_workers" -ge 1 ] || memory_workers=1
  if [ "$memory_workers" -lt "$cores" ]; then
    echo "$memory_workers"
  else
    echo "$cores"
  fi
}

WORKERS=$(detect_workers)
echo "INFO: using $WORKERS ATP workers"

next_job_id=0
job_pids=
job_count=0
job_successes=0

run_job() {
  trap - EXIT HUP INT TERM
  mode=$1
  prover=$2
  problem=$3
  timeout=$4
  label=$5
  out=$6

  case "$mode:$prover" in
    negative:E) run_eprover "$problem" "$timeout" "$label" "$out" ;;
    negative:Vampire) run_vampire "$problem" "$timeout" "$label" "$out" ;;
    negative:Z3) run_z3 "$problem" "$timeout" "$label" "$out" ;;
    negative:CVC4) run_cvc4 "$problem" "$timeout" "$label" "$out" ;;
    positive:E) try_eprover_theorem "$problem" "$timeout" "$label" "$out" ;;
    positive:Vampire) try_vampire_theorem "$problem" "$timeout" "$label" "$out" ;;
    positive:Z3) try_z3_theorem "$problem" "$timeout" "$label" "$out" ;;
    positive:CVC4) try_cvc4_theorem "$problem" "$timeout" "$label" "$out" ;;
    *) echo "consistency canary FAILED: unknown ATP job $mode:$prover" >&2; exit 1 ;;
  esac
}

# Each pending job is recorded as a "pid:job_dir" token so that reap_jobs can
# recover the mode and label of the job that actually failed from that job's
# own directory, rather than a single global shared by every pending job
# (which a later start_job call could clobber before the earlier jobs it
# queued were reaped).
reap_jobs() {
  batch_failed=0
  failed_label=
  for entry in $job_pids; do
    pid=${entry%%:*}
    dir=${entry#*:}
    if wait "$pid"; then
      job_successes=$((job_successes + 1))
    else
      status=$?
      mode=$(cat "$dir/mode" 2>/dev/null || true)
      if [ "$mode" = negative ] || [ "$status" -eq 2 ]; then
        batch_failed=1
        failed_label=$(cat "$dir/label" 2>/dev/null || true)
      fi
    fi
  done
  job_pids=
  job_count=0

  if [ "$batch_failed" -ne 0 ]; then
    fail "a consistency prover check failed for $failed_label"
  fi
}

start_job() {
  mode=$1
  prover=$2
  problem=$3
  label=$4
  out=$5

  job_dir="$tmpdir/jobs/$next_job_id"
  next_job_id=$((next_job_id + 1))
  mkdir -p "$job_dir"
  printf '%s\n' "$mode" >"$job_dir/mode"
  printf '%s\n' "$label" >"$job_dir/label"
  [ -n "$out" ] || out="$job_dir/$prover.out"

  run_job "$mode" "$prover" "$problem" "$TIMEOUT" "$label" "$out" &
  job_pids="$job_pids $!:$job_dir"
  job_count=$((job_count + 1))
  if [ "$job_count" -ge "$WORKERS" ]; then
    reap_jobs
  fi
}

note_nonzero_exit() {
  prover=$1
  status=$2
  out=$3
  label=$4
  # Whether the prover ran under the `timeout` wrapper, so that the statuses
  # and the diagnostics that wrapper produces can be told apart from the
  # prover's own.
  wrapped=${5:-0}

  if [ "$wrapped" -eq 1 ] &&
     { [ "$status" -eq "$TIMEOUT_SIGTERM_STATUS" ] ||
       [ "$status" -eq "$TIMEOUT_SIGKILL_STATUS" ]; }; then
    echo "NOTE: $prover was killed at the ${TIMEOUT}s wall-clock limit on $label; treating the result as inconclusive"
    return 0
  fi

  # `timeout` prints its own lines into the captured output, and they can
  # report a core dump left behind by the prover it killed; read only what the
  # prover itself wrote when deciding whether it crashed.  A portfolio prover
  # also reports the crashes of the strategy processes it forks while itself
  # surviving to deliver a verdict, so this says nothing about whether the
  # prover answered: the captured output is still classified by the caller.
  if [ "$status" -gt 128 ] ||
     grep -Ev '^timeout: ' "$out" |
       grep -Eiq 'segmentation fault|sigsegv|dumped core|core dumped|aborted|assertion.*failed|bus error|floating point exception|illegal instruction'; then
    echo "NOTE: $prover reported a crash while checking $label; not treating the nonzero exit as a failure"
    return 0
  fi

  case "$status" in
    8)
      echo "NOTE: $prover exited with status 8 (resource exhaustion) on $label; treating the result as inconclusive"
      ;;
    *)
      echo "NOTE: $prover exited with status $status on $label; treating the result as inconclusive"
      ;;
  esac
  return 0
}

have_eprover=0
have_vampire=0
have_z3=0
have_cvc4=0
z3_bin=
z3_style=

if command -v eprover >/dev/null 2>&1; then
  have_eprover=1
else
  echo "SKIP: eprover not found; skipping E consistency checks"
fi
if command -v vampire >/dev/null 2>&1; then
  have_vampire=1
else
  echo "SKIP: vampire not found; skipping Vampire consistency checks"
fi

z3_detect_problem=$tmpdir/z3-detect.p
printf '%s\n' 'fof(coqhammer_z3_detect, conjecture, $true).' >"$z3_detect_problem"
if command -v z3_tptp >/dev/null 2>&1 &&
   z3_tptp -c -t:1 -file:"$z3_detect_problem" >/dev/null 2>&1; then
  have_z3=1
  z3_bin=z3_tptp
  z3_style=z3_tptp
elif command -v z3 >/dev/null 2>&1 &&
     z3 -tptp -t:1000 "$z3_detect_problem" >/dev/null 2>&1; then
  have_z3=1
  z3_bin=z3
  z3_style=z3
else
  echo "SKIP: z3 with TPTP support not found; skipping Z3 consistency checks"
fi

if command -v cvc4 >/dev/null 2>&1; then
  have_cvc4=1
else
  echo "SKIP: cvc4 not found; skipping CVC4 consistency checks"
fi

if command -v timeout >/dev/null 2>&1; then
  have_timeout=1
else
  have_timeout=0
  echo "SKIP: timeout not found; CVC4 is bounded only by its own --tlimit" >&2
fi

if [ "$have_eprover" -eq 0 ] && [ "$have_vampire" -eq 0 ] &&
   [ "$have_z3" -eq 0 ] && [ "$have_cvc4" -eq 0 ]; then
  fail "no supported ATP binary found; dumped consistency canaries were not ATP-checked"
fi

check_unprovable_status() {
  prover=$1
  out=$2
  label=$3

  if grep -Eq 'SZS status (Theorem|Unsatisfiable|ContradictoryAxioms)|^unsat$' "$out"; then
    show_prover_output "$prover" "$out" "$label"
    fail "$prover proved a false consistency canary for $label"
  fi

  if grep -Eiq '(syntax|parse|parser)[[:space:]_-]*error' "$out"; then
    show_prover_output "$prover" "$out" "$label"
    fail "$prover reported a parser error on $label"
  fi

  if grep -Eiq 'unsupported|exception' "$out"; then
    echo "NOTE: $prover reported an unsupported feature or exception on $label; skipping this prover for this check" >&2
    return 0
  fi

  if grep -Eq 'SZS status (CounterSatisfiable|Satisfiable)|^sat$' "$out"; then
    return 0
  fi

  echo "NOTE: $prover did not report an explicit satisfiable/counter-satisfiable status for $label" >&2
  return 0
}

check_provable_status() {
  prover=$1
  out=$2
  label=$3

  if grep -Eiq '(syntax|parse|parser)[[:space:]_-]*error' "$out"; then
    show_prover_output "$prover" "$out" "$label"
    echo "consistency canary FAILED: $prover reported a parser error on $label" >&2
    return 2
  fi

  grep -Eq 'SZS status Theorem' "$out"
}

run_eprover() {
  problem=$1
  timeout=$2
  label=$3
  out=$4

  echo "CHECK: E consistency on $label"
  if eprover -s --cpu-limit="$timeout" --auto-schedule -R --print-statistics -p --tstp-format "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    if ! note_nonzero_exit "E" "$status" "$out" "$label"; then
      return 1
    fi
  fi
  check_unprovable_status "E" "$out" "$label"
}

run_vampire() {
  problem=$1
  timeout=$2
  label=$3
  out=$4

  echo "CHECK: Vampire consistency on $label"
  if vampire --mode casc -t "$timeout" --proof tptp --output_axiom_names on "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    if ! note_nonzero_exit "Vampire" "$status" "$out" "$label"; then
      return 1
    fi
  fi
  check_unprovable_status "Vampire" "$out" "$label"
}

run_z3() {
  problem=$1
  timeout=$2
  label=$3
  out=$4

  echo "CHECK: Z3 consistency on $label"
  if [ "$z3_style" = z3_tptp ]; then
    if "$z3_bin" -c -t:"$timeout" -file:"$problem" >"$out" 2>&1; then
      :
    else
      status=$?
      if ! note_nonzero_exit "Z3" "$status" "$out" "$label"; then
        return 1
      fi
    fi
  else
    if "$z3_bin" -tptp -t:$((timeout * 1000)) "$problem" >"$out" 2>&1; then
      :
    else
      status=$?
      if ! note_nonzero_exit "Z3" "$status" "$out" "$label"; then
        return 1
      fi
    fi
  fi
  check_unprovable_status "Z3" "$out" "$label"
}

# CVC4 does not reliably honour its own --tlimit on these problems: it can run
# for minutes past the limit inside quantifier instantiation, so the external
# wrapper is the real bound.  Kill it outright rather than with the wrapper's
# default SIGTERM, whose handler in CVC4 exits through abort(): that leaves a
# core file behind for every check and makes `timeout` announce the core dump
# in the captured output.
invoke_cvc4() {
  problem=$1
  timeout=$2
  out=$3

  if [ "$have_timeout" -eq 1 ]; then
    timeout -s KILL "$((timeout + 1))" cvc4 --tlimit "$((timeout * 1000))" "$problem" >"$out" 2>&1
  else
    cvc4 --tlimit "$((timeout * 1000))" "$problem" >"$out" 2>&1
  fi
}

run_cvc4() {
  problem=$1
  timeout=$2
  label=$3
  out=$4

  echo "CHECK: CVC4 consistency on $label"
  if invoke_cvc4 "$problem" "$timeout" "$out"; then
    :
  else
    status=$?
    if ! note_nonzero_exit "CVC4" "$status" "$out" "$label" "$have_timeout"; then
      return 1
    fi
  fi
  check_unprovable_status "CVC4" "$out" "$label"
}

try_eprover_theorem() {
  problem=$1
  timeout=$2
  label=$3
  out=$4

  echo "CHECK: E proves $label"
  if eprover -s --cpu-limit="$timeout" --auto-schedule -R --print-statistics -p --tstp-format "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    if ! note_nonzero_exit "E" "$status" "$out" "$label"; then
      return 1
    fi
  fi
  check_provable_status "E" "$out" "$label"
}

try_vampire_theorem() {
  problem=$1
  timeout=$2
  label=$3
  out=$4

  echo "CHECK: Vampire proves $label"
  if vampire --mode casc -t "$timeout" --proof tptp --output_axiom_names on "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    if ! note_nonzero_exit "Vampire" "$status" "$out" "$label"; then
      return 1
    fi
  fi
  check_provable_status "Vampire" "$out" "$label"
}

try_z3_theorem() {
  problem=$1
  timeout=$2
  label=$3
  out=$4

  echo "CHECK: Z3 proves $label"
  if [ "$z3_style" = z3_tptp ]; then
    if "$z3_bin" -c -t:"$timeout" -file:"$problem" >"$out" 2>&1; then
      :
    else
      status=$?
      if ! note_nonzero_exit "Z3" "$status" "$out" "$label"; then
        return 1
      fi
    fi
  else
    if "$z3_bin" -tptp -t:$((timeout * 1000)) "$problem" >"$out" 2>&1; then
      :
    else
      status=$?
      if ! note_nonzero_exit "Z3" "$status" "$out" "$label"; then
        return 1
      fi
    fi
  fi
  if grep -Eiq '(syntax|parse|parser)[[:space:]_-]*error' "$out"; then
    show_prover_output "Z3" "$out" "$label"
    echo "consistency canary FAILED: Z3 reported a parser error on $label" >&2
    return 2
  fi
  grep -Eq 'SZS status (Theorem|Unsatisfiable)|^unsat$' "$out"
}

try_cvc4_theorem() {
  problem=$1
  timeout=$2
  label=$3
  out=$4

  echo "CHECK: CVC4 proves $label"
  if invoke_cvc4 "$problem" "$timeout" "$out"; then
    :
  else
    status=$?
    if ! note_nonzero_exit "CVC4" "$status" "$out" "$label" "$have_timeout"; then
      return 1
    fi
  fi
  if grep -Eiq '(syntax|parse|parser)[[:space:]_-]*error' "$out"; then
    show_prover_output "CVC4" "$out" "$label"
    echo "consistency canary FAILED: CVC4 reported a parser error on $label" >&2
    return 2
  fi
  grep -Eq 'SZS status (Theorem|Unsatisfiable)|^unsat$' "$out"
}

# Helper kept separate for negative consistency checks: those tests can pass an
# already-formed conjecture here and assert that ATPs do not prove it.
assert_unprovable_problem() {
  problem=$1
  timeout=$2
  label=$3
  [ -f "$problem" ] || fail "missing dumped problem $problem"
  if [ "$have_eprover" -eq 1 ]; then
    start_job negative E "$problem" "$label" ""
  fi
  if [ "$have_vampire" -eq 1 ]; then
    start_job negative Vampire "$problem" "$label" ""
  fi
  if [ "$have_z3" -eq 1 ]; then
    start_job negative Z3 "$problem" "$label" ""
  fi
  if [ "$have_cvc4" -eq 1 ]; then
    start_job negative CVC4 "$problem" "$label" ""
  fi
}

check_index=0
assert_unprovable() {
  source_problem=$1
  timeout=$2

  [ -f "$source_problem" ] || fail "missing dumped problem $source_problem"
  false_problem=$tmpdir/false-$check_index.p
  check_index=$((check_index + 1))

  conjectures=$(grep -Ec '^fof\(.*,[[:space:]]*conjecture,[[:space:]]*' "$source_problem" || true)
  [ "$conjectures" -eq 1 ] || fail "expected exactly one conjecture in $source_problem, found $conjectures"
  sed 's/^fof(.*,[[:space:]]*conjecture,[[:space:]]*.*$/fof(goal, conjecture, $false)./' \
    "$source_problem" >"$false_problem"

  assert_unprovable_problem "$false_problem" "$timeout" "$source_problem"
}

make_bad_successor_problem() {
  source_problem=$1
  bad_problem=$2
  label=$3

  [ -f "$source_problem" ] || fail "missing dumped problem $source_problem"
  conjectures=$(grep -Ec '^fof\(.*,[[:space:]]*conjecture,[[:space:]]*' "$source_problem" || true)
  [ "$conjectures" -eq 1 ] || fail "expected exactly one conjecture in $source_problem, found $conjectures"

  goal_line=$(grep '^fof(.*,[[:space:]]*conjecture,[[:space:]]*' "$source_problem")
  lhs=$(printf '%s\n' "$goal_line" |
    sed -n 's/^fof(.*,[[:space:]]*conjecture,[[:space:]]*.*(\([A-Za-z0-9_][A-Za-z0-9_]*(V[^)]*)\)[[:space:]]*=[[:space:]]*\([A-Za-z0-9_][A-Za-z0-9_]*\)).*$/\1/p')
  zero_symbol=$(printf '%s\n' "$goal_line" |
    sed -n 's/^fof(.*,[[:space:]]*conjecture,[[:space:]]*.*(\([A-Za-z0-9_][A-Za-z0-9_]*(V[^)]*)\)[[:space:]]*=[[:space:]]*\([A-Za-z0-9_][A-Za-z0-9_]*\)).*$/\2/p')
  [ -n "$lhs" ] || fail "could not find the dumped conclusion function in $source_problem for $label"
  [ -n "$zero_symbol" ] || fail "could not find the dumped zero constructor in $source_problem for $label"

  successor_line=$(awk -v zero="$zero_symbol" 'index($0, " = " zero ") | ?[") { print; exit }' "$source_problem")
  [ -n "$successor_line" ] || fail "could not find the successor constructor line in $source_problem for $label"
  successor_symbol=$(printf '%s\n' "$successor_line" |
    sed -n 's/.*& (.* = \([A-Za-z0-9_][A-Za-z0-9_]*\)(.*/\1/p')
  [ -n "$successor_symbol" ] || fail "could not find the successor constructor symbol in $source_problem for $label"

  function_symbol=${lhs%%(*}
  arglist=${lhs#"$function_symbol("}
  arglist=${arglist%)}
  [ -n "$arglist" ] || fail "could not determine the arity of $function_symbol in $source_problem for $label"
  arity=$(printf '%s\n' "$arglist" | awk -F, '{ print NF }')

  args=
  i=0
  while [ "$i" -lt "$arity" ]; do
    if [ "$i" -eq 0 ]; then
      args=$zero_symbol
    else
      args=$args,$zero_symbol
    fi
    i=$((i + 1))
  done

  bad_term="$function_symbol($args)"
  conjecture="fof(goal, conjecture, $bad_term = $successor_symbol($bad_term))."
  awk -v conjecture="$conjecture" '
    /^fof\(.*,[[:space:]]*conjecture,[[:space:]]*/ { print conjecture; next }
    { print }
  ' "$source_problem" >"$bad_problem"
}

assert_provable() {
  problem=$1
  timeout=$2
  label=$3
  job_successes=0
  positive_eprover_out="$tmpdir/jobs/positive-eprover.out"
  positive_vampire_out="$tmpdir/jobs/positive-vampire.out"
  positive_z3_out="$tmpdir/jobs/positive-z3.out"
  positive_cvc4_out="$tmpdir/jobs/positive-cvc4.out"

  [ -f "$problem" ] || fail "missing dumped problem $problem"
  if [ "$have_eprover" -eq 1 ]; then
    start_job positive E "$problem" "$label" "$positive_eprover_out"
  fi
  if [ "$have_vampire" -eq 1 ]; then
    start_job positive Vampire "$problem" "$label" "$positive_vampire_out"
  fi
  if [ "$have_z3" -eq 1 ]; then
    start_job positive Z3 "$problem" "$label" "$positive_z3_out"
  fi
  if [ "$have_cvc4" -eq 1 ]; then
    start_job positive CVC4 "$problem" "$label" "$positive_cvc4_out"
  fi
  if [ "$job_count" -gt 0 ]; then
    reap_jobs
  fi
  if [ "$job_successes" -eq 0 ]; then
    [ "$have_eprover" -eq 1 ] && show_prover_output "E" "$positive_eprover_out" "$label"
    [ "$have_vampire" -eq 1 ] && show_prover_output "Vampire" "$positive_vampire_out" "$label"
    [ "$have_z3" -eq 1 ] && show_prover_output "Z3" "$positive_z3_out" "$label"
    [ "$have_cvc4" -eq 1 ] && show_prover_output "CVC4" "$positive_cvc4_out" "$label"
    fail "no available prover reported a proving status for $label"
  fi
}

# Generate the canary problem dumps into the private temp directory (kept out
# of the source tree via COQHAMMER_DUMP_DIR), rather than littering the
# working directory.
COQC=${COQC:-rocq c}
echo "GEN: dumping consistency canaries into $tmpdir"
COQHAMMER_DUMP_DIR="$tmpdir" $COQC consistency_canaries.v >"$tmpdir/gen.log" 2>&1 \
  || { cat "$tmpdir/gen.log" >&2; fail "compiling consistency_canaries.v"; }

assert_provable "$tmpdir/transport-tr-refl.p" "$TIMEOUT" "transport tr reflexivity"

assert_unprovable "$tmpdir/consistency-idiv.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-idiv2.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-idiv3.p" "$TIMEOUT"

bad_idiv=$tmpdir/bad-idiv.p
make_bad_successor_problem "$tmpdir/consistency-idiv.p" "$bad_idiv" \
  "idiv violated-premise unfolding instance"
assert_unprovable_problem "$bad_idiv" "$TIMEOUT" "idiv violated-premise unfolding instance"

bad_idiv2=$tmpdir/bad-idiv2.p
make_bad_successor_problem "$tmpdir/consistency-idiv2.p" "$bad_idiv2" \
  "idiv2 violated-premise unfolding instance"
assert_unprovable_problem "$bad_idiv2" "$TIMEOUT" "idiv2 violated-premise unfolding instance"

bad_idiv3=$tmpdir/bad-idiv3.p
make_bad_successor_problem "$tmpdir/consistency-idiv3.p" "$bad_idiv3" \
  "idiv3 violated-premise unfolding instance"
assert_unprovable_problem "$bad_idiv3" "$TIMEOUT" "idiv3 violated-premise unfolding instance"

assert_unprovable "$tmpdir/consistency-h.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-indexed-poly-subset.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-dsize.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-dheight.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-eq-rect.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-nat-add.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-prop-or-match.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-false-case-prop.p" "$TIMEOUT"

if [ "$job_count" -gt 0 ]; then
  reap_jobs
fi

echo "consistency canaries passed"
