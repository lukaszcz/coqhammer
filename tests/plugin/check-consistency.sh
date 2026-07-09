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
if [ "$have_eprover" -eq 0 ] && [ "$have_vampire" -eq 0 ]; then
  echo "SKIP: no E/Vampire binary found; dumped consistency canaries were not ATP-checked"
  exit 0
fi

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
  if grep -q 'SZS status Theorem' "$out"; then
    cat "$out" >&2
    fail "E reported SZS status Theorem for $label"
  fi
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
  if grep -q 'SZS status Theorem' "$out"; then
    cat "$out" >&2
    fail "Vampire reported SZS status Theorem for $label"
  fi
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

# Helper kept separate for Phase 4 negative instances: those tests can pass an
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
  [ "$proved" -eq 1 ] || fail "no available prover reported SZS status Theorem for $label"
}

assert_provable transport-tr-refl.p "$TIMEOUT" "transport tr reflexivity"

assert_unprovable consistency-idiv.p "$TIMEOUT"
assert_unprovable consistency-idiv2.p "$TIMEOUT"

bad_idiv=$tmpdir/bad-idiv.p
sed 's/^fof(.*,[[:space:]]*conjecture,[[:space:]]*.*$/fof(goal, conjecture, cextraction__deptypes_2eidiv___24a2(cCorelib_2eInit_2eDatatypes_2eO,cCorelib_2eInit_2eDatatypes_2eO) = cCorelib_2eInit_2eDatatypes_2eS___24a1(cextraction__deptypes_2eidiv___24a2(cCorelib_2eInit_2eDatatypes_2eO,cCorelib_2eInit_2eDatatypes_2eO)))./' \
  consistency-idiv.p >"$bad_idiv"
assert_unprovable_problem "$bad_idiv" "$TIMEOUT" "idiv violated-premise unfolding instance"

bad_idiv2=$tmpdir/bad-idiv2.p
sed 's/^fof(.*,[[:space:]]*conjecture,[[:space:]]*.*$/fof(goal, conjecture, cextraction__deptypes_2eidiv2___24a2(cCorelib_2eInit_2eDatatypes_2eO,cCorelib_2eInit_2eDatatypes_2eO) = cCorelib_2eInit_2eDatatypes_2eS___24a1(cextraction__deptypes_2eidiv2___24a2(cCorelib_2eInit_2eDatatypes_2eO,cCorelib_2eInit_2eDatatypes_2eO)))./' \
  consistency-idiv2.p >"$bad_idiv2"
assert_unprovable_problem "$bad_idiv2" "$TIMEOUT" "idiv2 violated-premise unfolding instance"

assert_unprovable consistency-h.p "$TIMEOUT"
assert_unprovable consistency-eq-rect.p "$TIMEOUT"
assert_unprovable consistency-nat-add.p "$TIMEOUT"

echo "consistency canaries passed"
