#!/bin/sh
set -eu

TIMEOUT=${CONSISTENCY_TIMEOUT:-15}
TMPDIR_BASE=${TMPDIR:-/tmp}

tmpdir=$(mktemp -d "$TMPDIR_BASE/coqhammer-consistency.XXXXXX")
cleanup() {
  rm -rf "$tmpdir"
}
trap cleanup EXIT HUP INT TERM

fail() {
  echo "consistency canary FAILED: $*" >&2
  exit 1
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

if [ "$have_eprover" -eq 0 ] && [ "$have_vampire" -eq 0 ] &&
   [ "$have_z3" -eq 0 ] && [ "$have_cvc4" -eq 0 ]; then
  fail "no supported ATP binary found; dumped consistency canaries were not ATP-checked"
fi

check_unprovable_status() {
  prover=$1
  out=$2
  label=$3

  if grep -Eq 'SZS status (Theorem|Unsatisfiable|ContradictoryAxioms|Error|SyntaxError|TypeError)|^unsat$' "$out" ||
     grep -Eiq '(syntax|parse)[[:space:]_-]*error|unsupported|exception' "$out"; then
    cat "$out" >&2
    fail "$prover reported a proving, inconsistency, or error status for $label"
  fi
}

run_eprover() {
  problem=$1
  timeout=$2
  label=$3
  out=$tmpdir/eprover.out

  echo "CHECK: E consistency on $label"
  if eprover -s --cpu-limit="$timeout" --auto-schedule -R --print-statistics -p --tstp-format "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    echo "NOTE: eprover exited with status $status on $label; checking SZS status anyway"
  fi
  check_unprovable_status "E" "$out" "$label"
}

run_vampire() {
  problem=$1
  timeout=$2
  label=$3
  out=$tmpdir/vampire.out

  echo "CHECK: Vampire consistency on $label"
  if vampire --mode casc -t "$timeout" --proof tptp --output_axiom_names on "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    echo "NOTE: vampire exited with status $status on $label; checking SZS status anyway"
  fi
  check_unprovable_status "Vampire" "$out" "$label"
}

run_z3() {
  problem=$1
  timeout=$2
  label=$3
  out=$tmpdir/z3.out

  echo "CHECK: Z3 consistency on $label"
  if [ "$z3_style" = z3_tptp ]; then
    if "$z3_bin" -c -t:"$timeout" -file:"$problem" >"$out" 2>&1; then
      :
    else
      status=$?
      echo "NOTE: Z3 exited with status $status on $label; checking status anyway"
    fi
  else
    if "$z3_bin" -tptp -t:$((timeout * 1000)) "$problem" >"$out" 2>&1; then
      :
    else
      status=$?
      echo "NOTE: Z3 exited with status $status on $label; checking status anyway"
    fi
  fi
  check_unprovable_status "Z3" "$out" "$label"
}

run_cvc4() {
  problem=$1
  timeout=$2
  label=$3
  out=$tmpdir/cvc4.out

  echo "CHECK: CVC4 consistency on $label"
  if command -v timeout >/dev/null 2>&1; then
    cvc4_cmd="timeout $((timeout + 1)) cvc4 --tlimit $((timeout * 1000))"
  else
    cvc4_cmd="cvc4 --tlimit $((timeout * 1000))"
  fi
  # shellcheck disable=SC2086
  if $cvc4_cmd "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    echo "NOTE: cvc4 exited with status $status on $label; checking status anyway"
  fi
  check_unprovable_status "CVC4" "$out" "$label"
}

try_eprover_theorem() {
  problem=$1
  timeout=$2
  label=$3
  out=$tmpdir/eprover-theorem.out

  echo "CHECK: E proves $label"
  if eprover -s --cpu-limit="$timeout" --auto-schedule -R --print-statistics -p --tstp-format "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    echo "NOTE: eprover exited with status $status on $label; checking SZS status anyway"
  fi
  grep -q 'SZS status Theorem' "$out"
}

try_vampire_theorem() {
  problem=$1
  timeout=$2
  label=$3
  out=$tmpdir/vampire-theorem.out

  echo "CHECK: Vampire proves $label"
  if vampire --mode casc -t "$timeout" --proof tptp --output_axiom_names on "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    echo "NOTE: vampire exited with status $status on $label; checking SZS status anyway"
  fi
  grep -q 'SZS status Theorem' "$out"
}

try_z3_theorem() {
  problem=$1
  timeout=$2
  label=$3
  out=$tmpdir/z3-theorem.out

  echo "CHECK: Z3 proves $label"
  if [ "$z3_style" = z3_tptp ]; then
    if "$z3_bin" -c -t:"$timeout" -file:"$problem" >"$out" 2>&1; then
      :
    else
      status=$?
      echo "NOTE: Z3 exited with status $status on $label; checking status anyway"
    fi
  else
    if "$z3_bin" -tptp -t:$((timeout * 1000)) "$problem" >"$out" 2>&1; then
      :
    else
      status=$?
      echo "NOTE: Z3 exited with status $status on $label; checking status anyway"
    fi
  fi
  grep -Eq 'SZS status (Theorem|Unsatisfiable)|^unsat$' "$out"
}

try_cvc4_theorem() {
  problem=$1
  timeout=$2
  label=$3
  out=$tmpdir/cvc4-theorem.out

  echo "CHECK: CVC4 proves $label"
  if command -v timeout >/dev/null 2>&1; then
    cvc4_cmd="timeout $((timeout + 1)) cvc4 --tlimit $((timeout * 1000))"
  else
    cvc4_cmd="cvc4 --tlimit $((timeout * 1000))"
  fi
  # shellcheck disable=SC2086
  if $cvc4_cmd "$problem" >"$out" 2>&1; then
    :
  else
    status=$?
    echo "NOTE: cvc4 exited with status $status on $label; checking status anyway"
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
    run_eprover "$problem" "$timeout" "$label"
  fi
  if [ "$have_vampire" -eq 1 ]; then
    run_vampire "$problem" "$timeout" "$label"
  fi
  if [ "$have_z3" -eq 1 ]; then
    run_z3 "$problem" "$timeout" "$label"
  fi
  if [ "$have_cvc4" -eq 1 ]; then
    run_cvc4 "$problem" "$timeout" "$label"
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

assert_provable() {
  problem=$1
  timeout=$2
  label=$3
  proved=0

  [ -f "$problem" ] || fail "missing dumped problem $problem"
  if [ "$have_eprover" -eq 1 ] && try_eprover_theorem "$problem" "$timeout" "$label"; then
    proved=1
  fi
  if [ "$have_vampire" -eq 1 ] && try_vampire_theorem "$problem" "$timeout" "$label"; then
    proved=1
  fi
  if [ "$have_z3" -eq 1 ] && try_z3_theorem "$problem" "$timeout" "$label"; then
    proved=1
  fi
  if [ "$have_cvc4" -eq 1 ] && try_cvc4_theorem "$problem" "$timeout" "$label"; then
    proved=1
  fi
  [ "$proved" -eq 1 ] || fail "no available prover reported a proving status for $label"
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

bad_idiv=$tmpdir/bad-idiv.p
sed 's/^fof(.*,[[:space:]]*conjecture,[[:space:]]*.*$/fof(goal, conjecture, cextraction__deptypes_2eidiv___24a2(cCorelib_2eInit_2eDatatypes_2eO,cCorelib_2eInit_2eDatatypes_2eO) = cCorelib_2eInit_2eDatatypes_2eS___24a1(cextraction__deptypes_2eidiv___24a2(cCorelib_2eInit_2eDatatypes_2eO,cCorelib_2eInit_2eDatatypes_2eO)))./' \
  "$tmpdir/consistency-idiv.p" >"$bad_idiv"
assert_unprovable_problem "$bad_idiv" "$TIMEOUT" "idiv violated-premise unfolding instance"

bad_idiv2=$tmpdir/bad-idiv2.p
sed 's/^fof(.*,[[:space:]]*conjecture,[[:space:]]*.*$/fof(goal, conjecture, cextraction__deptypes_2eidiv2___24a2(cCorelib_2eInit_2eDatatypes_2eO,cCorelib_2eInit_2eDatatypes_2eO) = cCorelib_2eInit_2eDatatypes_2eS___24a1(cextraction__deptypes_2eidiv2___24a2(cCorelib_2eInit_2eDatatypes_2eO,cCorelib_2eInit_2eDatatypes_2eO)))./' \
  "$tmpdir/consistency-idiv2.p" >"$bad_idiv2"
assert_unprovable_problem "$bad_idiv2" "$TIMEOUT" "idiv2 violated-premise unfolding instance"

assert_unprovable "$tmpdir/consistency-h.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-eq-rect.p" "$TIMEOUT"
assert_unprovable "$tmpdir/consistency-nat-add.p" "$TIMEOUT"

echo "consistency canaries passed"
