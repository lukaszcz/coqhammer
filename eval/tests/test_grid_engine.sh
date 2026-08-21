#!/usr/bin/env bash
# Test fixtures and callbacks are consumed indirectly by the sourced engine.
# SC2031 is a false positive from same-name assignments inside grid_run's
# subshell when ShellCheck follows that engine source.
# shellcheck disable=SC2030,SC2031,SC2034,SC2317
set -euo pipefail

eval_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
# shellcheck source=eval/grid-engine.sh
# shellcheck disable=SC1091
source "$eval_dir/grid-engine.sh"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fail() {
  echo "test_grid_engine: $*" >&2
  exit 1
}

expect_failure() {
  if "$@" >/dev/null 2>&1; then
    fail "command unexpectedly succeeded: $*"
  fi
}

legacy=0a4af3b6fb21c4b53f0d6193714981b2c7d9e42c6ed39bf7325fa028e93ab563
repo_commit=0123456789012345678901234567890123456789
grid_script_digest=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
grid_helper_digest=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
compile_supervisor_digest=dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
compile_timeout=600
compile_timeout_grace=10
legacy_grid_script_digests=("$legacy")
corpus_mode=sample
force=false
declare -A label_config=([label]=all-on)
declare -A label_preamble=([label]='')
declare -A label_preamble_digest=([label]="$(hash_text '')")
declare -A corpus_source=([corpus]=eval/corpora/corpus/sample)
declare -A corpus_digest=() corpus_legacy_digest=()
declare -A corpus_input_files=([corpus]='')
declare -A corpus_input_trees=([corpus]="$tmp/corpus-src")
prefix="$tmp/prefix"
mkdir -p "$prefix" "$tmp/checkpoint" "$tmp/timeout-logs/nested" "$tmp/corpus-src"
printf 'Lemma fixture : True.\nProof. exact I. Qed.\n' > "$tmp/corpus-src/fixture.v"
_grid_recompute_corpus_digest corpus
printf '%s\n' \
  'rocq-compile-supervisor: TIMEOUT phase=check source=fixture.v limit=1s grace=1s exit=124' \
  > "$tmp/timeout-logs/nested/fixture.log"
timeout_report=$(report_compile_timeouts "$tmp/timeout-logs" 2>&1)
[[ "$timeout_report" == *'phase=check source=fixture.v'* ]] ||
  fail "compile timeout report remained buried in per-file logs"

# "make -C" implies "-w", so its directory notices always carry a quoted path
# and are only stripped if the pattern allows for one. A log of nothing but
# routine make chatter records no failure, even when the build directory is
# spelled with the word "error" in it.
printf '%s\n' \
  "make: Entering directory '/tmp/build error 2/atp'" \
  'make[1]: *** [Makefile:9: all] Error 2' \
  "make: Leaving directory '/tmp/build error 2/atp'" \
  > "$tmp/routine-make.log"
expect_failure log_has_crash_or_error "$tmp/routine-make.log"
expect_failure log_has_crash_or_error_ignoring_backstop_kills "$tmp/routine-make.log"

printf 'one\n' > "$tmp/harness-source"
first_harness_hash=$(hash_harness_sources supervisor "$tmp/harness-source")
printf 'two\n' > "$tmp/harness-source"
second_harness_hash=$(hash_harness_sources supervisor "$tmp/harness-source")
[ "$first_harness_hash" != "$second_harness_hash" ] ||
  fail "composite harness hash ignored changed supervisor bytes"
eval_prefix_write_marker "$prefix"
cat > "$prefix/manifest.env" <<EOF
kind=configuration
config=all-on
commit=$repo_commit
prefix=$prefix
opt_prop_case_erasure=true
opt_erasure_guards=true
opt_refinement_types=true
opt_refinement_decl_skips=false
EOF
marker="$tmp/checkpoint/generate"
old_corpus_digest=${corpus_digest[corpus]}
# The pre-engine grid scripts recorded a single-tree corpus as that tree's own
# hash_tree digest, without the outer hash the engine now folds its inputs
# with. Compute that historical form here from the fixture corpus instead of
# reading the engine's current corpus_digest back out: seeding the marker from
# the value under test would make the migration check tautological and would
# not notice a change to how the engine renders the field.
legacy_corpus_digest=$(hash_tree "$tmp/corpus-src")
historical_corpus_digest=$legacy_corpus_digest

manifest_sha=$(sha256sum "$prefix/manifest.env" | awk '{ print $1 }')
# A genuinely historical marker was written at an older repository commit and
# against an older checkpoint helper. Both differ from the current run here, so
# the migration path is only reachable if it reads them back from the marker.
historical_commit=1111111111111111111111111111111111111111
historical_helper=2222222222222222222222222222222222222222222222222222222222222222
[ "$historical_commit" != "$repo_commit" ] || fail "historical commit fixture is not historical"
[ "$historical_helper" != "$grid_helper_digest" ] ||
  fail "historical helper fixture is not historical"
write_historical_marker() {
  local historical_digest="$1" stage="$2"
  shift 2
  # Golden historical engine schema: do not call checkpoint_contents here, or
  # a producer/checker schema change could make this integration test tautological.
  cat > "$marker.done" <<EOF
checkpoint_version=3
stage=$stage
repository_commit=$historical_commit
grid_script_sha256=$historical_digest
checkpoint_helper_sha256=$historical_helper
label=label
config=all-on
install_commit=$repo_commit
install_kind=configuration
install_manifest_sha256=$manifest_sha
corpus=corpus
corpus_mode=sample
corpus_source=eval/corpora/corpus/sample
corpus_sha256=$historical_corpus_digest
EOF
  [ "$#" -eq 0 ] || printf '%s\n' "$@" >> "$marker.done"
}

# The actual historical extraction-screening generation checkpoint predates
# compile supervision and must not be reused, even when all old fields match.
write_historical_marker "$legacy" generation
expect_failure checkpoint_matches "$marker" generation label corpus "$prefix"
[ ! -e "$marker.done" ] || fail "unsupervised historical generation marker survived"

# Historical downstream work is still safe when its generated-input hash and
# every other provenance field match the current run.
write_historical_marker "$legacy" prover \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest" ||
  fail "valid historical downstream checkpoint was not reused"
[ -f "$marker.done" ] || fail "valid historical downstream checkpoint was removed"

# The engine's own rendering of the same corpus inputs is accepted too, so a
# marker written by an early engine run migrates as readily as a pre-engine one.
historical_corpus_digest=$old_corpus_digest
write_historical_marker "$legacy" prover \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest" ||
  fail "historical checkpoint carrying the current corpus digest was not reused"
historical_corpus_digest=$legacy_corpus_digest

# An undeclared old digest is not a migration wildcard.
write_historical_marker \
  dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd prover \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
expect_failure checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
[ ! -e "$marker.done" ] || fail "unsupported historical marker survived"

# Historical markers are never valid for a nonempty preamble.
write_historical_marker "$legacy" prover \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
label_preamble[label]='Set Hammer DefinitionPremises 8.'
label_preamble_digest[label]=$(hash_text "${label_preamble[label]}")
expect_failure checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
label_preamble[label]=''
label_preamble_digest[label]=$(hash_text '')

# Tampering with a provenance field, or changing the downstream input hash,
# invalidates the otherwise accepted historical digest.
write_historical_marker "$legacy" prover \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
sed -i 's/^repository_commit=.*/repository_commit=tampered/' "$marker.done"
expect_failure checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
write_historical_marker "$legacy" prover \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
expect_failure checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 \
  input_sha256=eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee

# The two provenance fields the migration reads back from the marker are the
# only ones it may substitute. The semantic fields stay unfaked: an install or
# corpus identity that differs from the current run is rejected even though the
# marker's grid script digest is declared, and so is a marker written under a
# different checkpoint schema version.
for tamper in \
    's/^corpus_sha256=.*/corpus_sha256=ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff/' \
    's/^install_commit=.*/install_commit=3333333333333333333333333333333333333333/' \
    's/^install_manifest_sha256=.*/install_manifest_sha256=ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff/' \
    's/^corpus_source=.*/corpus_source=eval\/corpora\/other\/sample/' \
    's/^config=.*/config=all-off/' \
    's/^checkpoint_version=.*/checkpoint_version=2/'; do
  write_historical_marker "$legacy" prover \
    premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
  sed -i "$tamper" "$marker.done"
  expect_failure checkpoint_matches "$marker" prover label corpus "$prefix" \
    premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
  [ ! -e "$marker.done" ] || fail "tampered historical marker survived: $tamper"
done

# A harness-provenance field that is missing, duplicated, or malformed must fail
# the read rather than widen the migration.
write_historical_marker "$legacy" prover \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
sed -i '/^checkpoint_helper_sha256=/d' "$marker.done"
expect_failure checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
write_historical_marker "$legacy" prover \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
printf 'grid_script_sha256=%s\n' "$legacy" >> "$marker.done"
expect_failure checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
write_historical_marker "$legacy" prover \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
sed -i 's/^repository_commit=.*/repository_commit=/' "$marker.done"
expect_failure checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"

# A current marker must retain this literal engine schema and the golden SHA-256
# of an empty hook preamble. This is intentionally not generated by the helper.
mark_checkpoint "$marker" generation label corpus "$prefix"
cat > "$tmp/current-marker.golden" <<EOF
checkpoint_version=3
stage=generation
repository_commit=$repo_commit
grid_script_sha256=$grid_script_digest
checkpoint_helper_sha256=$grid_helper_digest
label=label
config=all-on
install_commit=$repo_commit
install_kind=configuration
install_manifest_sha256=$manifest_sha
corpus=corpus
corpus_mode=sample
corpus_source=eval/corpora/corpus/sample
corpus_sha256=$old_corpus_digest
compile_supervisor_sha256=$compile_supervisor_digest
compile_timeout=600
compile_timeout_grace=10
hook_preamble_sha256=e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
hook_preamble_file=hook-preamble.v
EOF
cmp -s "$tmp/current-marker.golden" "$marker.done" || fail "current marker schema drifted"
[ "$(sha256sum "$tmp/checkpoint/hook-preamble.v" | awk '{ print $1 }')" = \
  e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 ] ||
  fail "empty preamble sidecar hash drifted"

compile_timeout=601
expect_failure checkpoint_matches "$marker" generation label corpus "$prefix"
[ ! -e "$marker.done" ] || fail "changed compile timeout reused generation checkpoint"
compile_timeout=600
mark_checkpoint "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest"
compile_timeout=601
checkpoint_matches "$marker" prover label corpus "$prefix" \
  premise=knn-64 prover=eprover timeout=5 input_sha256="$old_corpus_digest" ||
  fail "compile policy invalidated a non-compile checkpoint"
compile_timeout=600

# Prefix reuse requires both the path-bound ownership marker and manifest path.
_grid_manifest_matches_install all-on "$prefix" || fail "owned prefix was rejected"
printf '%s\nprefix=%s\n' "$EVAL_PREFIX_MARKER_MAGIC" "$tmp/elsewhere" > \
  "$prefix/$EVAL_PREFIX_MARKER"
expect_failure _grid_manifest_matches_install all-on "$prefix"
eval_prefix_write_marker "$prefix"
# The marker is line-oriented, so a prefix spelled with a newline could never
# be recognized again; it is refused before anything is written or erased.
newline_prefix="$tmp/new"$'\n'"line"
mkdir -p "$newline_prefix"
expect_failure eval_prefix_write_marker "$newline_prefix"
[ ! -e "$newline_prefix/$EVAL_PREFIX_MARKER" ] ||
  fail "marker was written for a prefix that cannot be read back"
expect_failure eval_prefix_is_owned "$newline_prefix"
sed -i "s|^prefix=.*|prefix=$tmp/elsewhere|" "$prefix/manifest.env"
expect_failure _grid_manifest_matches_install all-on "$prefix"
sed -i "s|^prefix=.*|prefix=$prefix|" "$prefix/manifest.env"

# A stale prefix has to be erased before rebuild-config.sh can reinstall into
# it, and rebuild-config.sh itself refuses to erase what it cannot prove it
# created. Build a stale, unowned prefix and check both engine branches: one
# that the engine constructed under _installs, and one that is not.
build_install_fixture() {
  local relative="$1"
  rm -rf "$tmp/build-eval" "$tmp/build-repo" "$tmp/rebuild-args"
  mkdir -p "$tmp/build-eval" "$tmp/build-repo"
  eval_dir=$(cd "$tmp/build-eval" && pwd -P)
  repo=$(cd "$tmp/build-repo" && pwd -P)
  build_prefix="$eval_dir/$relative"
  mkdir -p "$build_prefix"
  # A prefix without the ownership marker, so rebuild-config.sh would refuse it.
  printf 'kind=configuration\nconfig=all-on\ncommit=stale\nprefix=%s\n' \
    "$build_prefix" > "$build_prefix/manifest.env"
  printf 'stale\n' > "$build_prefix/sentinel"
  cat > "$eval_dir/rebuild-config.sh" <<'SCRIPT'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$RECORD"
mkdir -p "$5"
printf 'rebuilt\n' > "$5/manifest.env"
SCRIPT
  chmod +x "$eval_dir/rebuild-config.sh"
  skip_builds=false
  base_path=$PATH
  base_ocamlpath=
  export RECORD="$tmp/rebuild-args"
  declare -gA install_label=([all-on]=stale-label)
  declare -gA install_prefix=([all-on]="$build_prefix")
}
(
  build_install_fixture _installs/stale-label
  output=$(_grid_build_install all-on 2>&1)
  [[ "$output" == *'stale or mismatched; rebuilding'* ]] ||
    fail "stale unowned prefix did not announce a rebuild: $output"
  [ ! -e "$build_prefix/sentinel" ] || fail "stale unowned prefix was not erased"
  mapfile -t rebuild_args < "$RECORD"
  [ "${rebuild_args[0]}" = all-on ] || fail "rebuild received config ${rebuild_args[0]}"
  [ "${rebuild_args[2]}" = stale-label ] || fail "rebuild received label ${rebuild_args[2]}"
  [ "${rebuild_args[4]}" = "$build_prefix" ] ||
    fail "rebuild received prefix ${rebuild_args[4]}"
) || fail "stale engine-managed prefix was not rebuilt"

# Ownership by construction, not by marker: anything the engine cannot re-derive
# as <eval_dir>/_installs/<component> aborts with the manual removal command and
# is left untouched.
for unmanaged in _installs/nested/stale-label not-installs/stale-label; do
  (
    build_install_fixture "$unmanaged"
    set +e
    output=$(_grid_build_install all-on 2>&1)
    status=$?
    set -e
    [ "$status" -eq 1 ] || fail "unmanaged stale prefix exited $status"
    [[ "$output" != *rebuilding* ]] ||
      fail "unmanaged stale prefix announced a rebuild it cannot perform"
    [[ "$output" == *"rm -rf $build_prefix"* ]] ||
      fail "unmanaged stale prefix gave no manual removal command: $output"
    [ -e "$build_prefix/sentinel" ] || fail "unmanaged stale prefix was erased"
    [ ! -e "$RECORD" ] || fail "unmanaged stale prefix still invoked a rebuild"
  ) || fail "unmanaged stale prefix policy drifted: $unmanaged"
done

# Atomic-write temporaries clean stale regular files for this target/PID, never
# follow stale symlinks, and remain registered for EXIT/signal cleanup.
target="$tmp/checkpoint/atomic"
touch "$target.tmp.$$" "$target.tmp.$$.stale"
_grid_new_atomic_temp "$target"
atomic_temp=$GRID_ATOMIC_TEMP
if [ -e "$target.tmp.$$" ] || [ -e "$target.tmp.$$.stale" ]; then
  fail "stale atomic temporaries were not removed"
fi
[ -f "$atomic_temp" ] || fail "atomic temporary was not created"
_grid_cleanup_temp_files
[ ! -e "$atomic_temp" ] || fail "registered atomic temporary was not cleaned"
mkdir -p "$tmp/paired/nested"
touch "$tmp/paired/.coqhammer-pair-stale.tmp" \
  "$tmp/paired/nested/.coqhammer-pair-stale.tmp"
ln -s "$prefix/manifest.env" "$tmp/paired/.coqhammer-pair-hostile.tmp"
cleanup_paired_output_temporaries "$tmp/paired"
[ ! -e "$tmp/paired/.coqhammer-pair-stale.tmp" ] ||
  fail "top-level paired-output temporary survived cleanup"
[ ! -e "$tmp/paired/nested/.coqhammer-pair-stale.tmp" ] ||
  fail "nested paired-output temporary survived cleanup"
[ -L "$tmp/paired/.coqhammer-pair-hostile.tmp" ] ||
  fail "paired-output cleanup removed or followed a symlink"
ln -s "$prefix/manifest.env" "$target.tmp.$$"
_grid_new_atomic_temp "$target"
[ -L "$target.tmp.$$" ] || fail "stale symlink was followed or removed"
_grid_cleanup_temp_files
rm -f "$target.tmp.$$"

# EXIT and signal traps remove a temporary even when an atomic write never
# reaches its rename.
for mode in exit term int; do
  record="$tmp/$mode-temp-path"
  set +e
  bash -c '
    set -euo pipefail
    source "$1"
    _grid_install_cleanup_traps
    _grid_new_atomic_temp "$2"
    printf "%s\n" "$GRID_ATOMIC_TEMP" > "$3"
    case "$4" in
      exit) exit 0 ;;
      term) kill -TERM "$$" ;;
      int) kill -INT "$$" ;;
    esac
  ' bash "$eval_dir/grid-engine.sh" "$tmp/checkpoint/$mode-atomic" "$record" "$mode"
  trap_status=$?
  set -e
  case "$mode:$trap_status" in
    exit:0|term:143|int:130) ;;
    *) fail "$mode cleanup trap exited $trap_status" ;;
  esac
  trapped_temp=$(cat "$record")
  [ ! -e "$trapped_temp" ] || fail "$mode cleanup trap left $trapped_temp"
done

mkdir -p "$tmp/preamble-tmp"
old_tmpdir=${TMPDIR-}
TMPDIR="$tmp/preamble-tmp"
grid_label_preamble() {
  printf 'first\036byte\nsecond\n\n'
}
_grid_capture_preamble label
[ "$GRID_CAPTURED_PREAMBLE" = $'first\036byte\nsecond\n\n' ] ||
  fail "preamble callback output or trailing newlines changed"

grid_label_preamble() {
  printf 'return output\n\n'
  return 7
}
set +e
_grid_capture_preamble label >/dev/null 2>&1
status=$?
set -e
[ "$status" -eq 7 ] || fail "preamble callback return became status $status"
[ "$GRID_CAPTURED_PREAMBLE" = $'return output\n\n' ] ||
  fail "failed return callback output was not captured verbatim"

grid_label_preamble() {
  printf 'exit output\n\n'
  exit 9
}
set +e
_grid_capture_preamble label >/dev/null 2>&1
status=$?
set -e
[ "$status" -eq 9 ] || fail "preamble callback exit became status $status"
[ "$GRID_CAPTURED_PREAMBLE" = $'exit output\n\n' ] ||
  fail "failed exit callback output was not captured verbatim"
[ -z "$(find "$TMPDIR" -mindepth 1 -print -quit)" ] ||
  fail "preamble capture left a temporary file"
if [ -n "$old_tmpdir" ]; then
  TMPDIR=$old_tmpdir
else
  unset TMPDIR
fi

# Validate representative malformed specs without creating output roots.
valid_spec() {
  GRID_NAME=test-grid
  GRID_RESULTS_ROOT="$tmp/results"
  GRID_ARTIFACTS_DIR="$tmp/artifacts"
  GRID_SUMMARIZER="$eval_dir/tools/summarize-screening.py"
  GRID_COMPLETION_MESSAGE='done'
  # This is indexed here; one negative test intentionally redeclares it below.
  # shellcheck disable=SC2190
  GRID_LABELS=(label)
  GRID_PREMISES=(knn-64)
  GRID_PROVERS=(eprover)
  GRID_CORPORA=(corpus)
  GRID_CONSISTENCY_PREMISE=knn-64
  GRID_LEGACY_SCRIPT_SHA256=()
  # shellcheck disable=SC2317
  grid_label_install() { printf current; }
  # shellcheck disable=SC2317
  grid_label_preamble() { printf ''; }
  # shellcheck disable=SC2317
  grid_usage() { printf 'usage\n'; }
}
(
  valid_spec
  _grid_require_spec
) || fail "valid spec was rejected"

# Running the driver installs its cleanup traps only in its subshell, leaving
# every trap in a sourcing caller byte-for-byte unchanged.
valid_spec
before_exit=$(trap -p EXIT)
trap 'printf caller-int >/dev/null' INT
trap 'printf caller-term >/dev/null' TERM
before_int=$(trap -p INT)
before_term=$(trap -p TERM)
grid_run --help >/dev/null
[ "$(trap -p EXIT)" = "$before_exit" ] || fail "grid driver replaced caller EXIT trap"
[ "$(trap -p INT)" = "$before_int" ] || fail "grid driver replaced caller INT trap"
[ "$(trap -p TERM)" = "$before_term" ] || fail "grid driver replaced caller TERM trap"
trap - INT TERM

# The label/corpus loop aggregates what each stage reports. Stages are stubbed
# here to fail in every way one can: by returning, by walking into an unchecked
# failing command, and by exiting the way a shared helper still may.
(
  cd "$eval_dir"
  valid_spec
  GRID_CORPORA=(corpus-a corpus-b)
  # Everything outside the run loop is neutralized; only the stages are of
  # interest, and none of them touches a real install, corpus, or summarizer.
  _grid_require_reviewable_worktree() { return 0; }
  _grid_build_install() { return 0; }
  _grid_set_corpus_inputs() { return 0; }
  _grid_require_consistent_corpus_provenance() { return 0; }
  _grid_run_summarizer() { echo summarized; }
  _grid_write_provenance() { return 0; }
  _grid_run_generation() { echo "gen $2"; }
  _grid_run_prover() { echo "prover $2"; }
  _grid_run_consistency() { echo "consistency $2"; }

  driver_out=
  driver_status=0
  run_driver() {
    local stage_override="$1"
    shift
    set +e
    driver_out=$( "$stage_override"; grid_run -j 2 "$@" 2>&1 )
    driver_status=$?
    set -e
  }
  expect_driver() {
    local description="$1" expected="$2" present="$3" absent="$4"
    if [ "$driver_status" -ne "$expected" ]; then
      fail "$description exited $driver_status, expected $expected"
    fi
    if [ -n "$present" ] && ! grep -qF -- "$present" <<< "$driver_out"; then
      fail "$description did not report: $present"
    fi
    if [ -n "$absent" ] && grep -qF -- "$absent" <<< "$driver_out"; then
      fail "$description still reported: $absent"
    fi
  }

  no_override() { :; }
  run_driver no_override
  expect_driver "a clean grid" 0 summarized ''

  # A generation failure skips the rest of its corpus, since every later stage
  # reads the problem trees it did not write, and leaves the next corpus alone.
  generation_returns() {
    _grid_run_generation() {
      echo "gen $2"
      [ "$2" != corpus-a ] || return 1
    }
  }
  run_driver generation_returns
  expect_driver "a failed generation" 1 'gen corpus-b' 'prover corpus-a'

  # Bash ignores errexit throughout a command run in a condition or on the left
  # of ||, so a stage invoked that way would walk past this unchecked failure.
  generation_walks_on() {
    _grid_run_generation() {
      echo "gen $2"
      false
      echo "gen $2 continued"
    }
  }
  run_driver generation_walks_on
  expect_driver "an unchecked stage failure" 1 '' 'continued'

  prover_exits() { _grid_run_prover() { echo "prover $2"; exit 1; }; }
  run_driver prover_exits
  expect_driver "a stage that exits" 1 'prover corpus-b' ''

  prover_returns() { _grid_run_prover() { echo "prover $2"; return 1; }; }
  run_driver prover_returns
  expect_driver "a failed prover" 1 'consistency corpus-a' ''

  # An inconsistency hit is a measurement the summarizer reads from the status
  # file, so it alone leaves the grid's own status clean.
  consistency_hits() {
    _grid_run_consistency() {
      echo "consistency $2"
      return "$_GRID_CONSISTENCY_HIT_STATUS"
    }
  }
  run_driver consistency_hits
  expect_driver "an inconsistency hit" 0 summarized 'stages failed'
  run_driver consistency_hits --only-label label
  expect_driver "an inconsistency hit in a partial run" 0 '' ''

  # A scan that could not run at all is an ordinary infrastructure failure, and
  # a partial run has no summarizer to report it in the engine's place.
  consistency_breaks() { _grid_run_consistency() { echo "consistency $2"; return 1; }; }
  run_driver consistency_breaks
  expect_driver "a failed consistency scan" 1 'stages failed' ''
  run_driver consistency_breaks --only-corpus corpus-a
  expect_driver "a failed consistency scan in a partial run" 1 \
    'not updated by a partial run' summarized
)

# The generic summarizer API supplies every active non-label axis and mode via
# environment while preserving the positional interface used by extraction.
(
  summary_probe="$tmp/summary-probe.py"
  cat > "$summary_probe" <<'PY'
import os
import pathlib
import sys
import json
provenance = json.loads(os.environ["COQHAMMER_GRID_EXPECTED_PROVENANCE"])
pathlib.Path(sys.argv[2]).write_text("\n".join((
    os.environ["COQHAMMER_GRID_PREMISES"],
    os.environ["COQHAMMER_GRID_PROVERS"],
    os.environ["COQHAMMER_GRID_CORPORA"],
    os.environ["COQHAMMER_GRID_CORPUS_MODE"],
    os.environ["COQHAMMER_GRID_CONSISTENCY_PREMISE"],
    provenance["repository_commit"],
    provenance["labels"]["candidate"]["config"],
    provenance["corpora"]["tiny-b"]["source"],
    "|".join(sys.argv[4:]),
)))
pathlib.Path(sys.argv[3]).write_text("compatible\n")
PY
  labels=(base candidate)
  premises=(knn-32 nbayes-1024)
  provers=(eprover vampire)
  corpora=(tiny-a tiny-b)
  corpus_mode=sample
  consistency_premise=knn-32
  tim=5
  consistency_tim=2
  compile_timeout=600
  compile_timeout_grace=10
  declare -A label_config=([base]=current [candidate]=current)
  declare -A label_prefix=([base]="$prefix" [candidate]="$prefix")
  declare -A corpus_source=([tiny-a]=fixture-a [tiny-b]=fixture-b)
  declare -A corpus_digest=([tiny-a]="$old_corpus_digest" [tiny-b]="$old_corpus_digest")
  declare -A corpus_input_trees=([tiny-a]="$tmp" [tiny-b]="$tmp")
  declare -A corpus_input_files=([tiny-a]='' [tiny-b]='')
  _grid_run_summarizer "$summary_probe" "$tmp/results-unused" \
    "$tmp/summary-probe.out" "$tmp/analysis-probe.out"
  expected_probe=$'knn-32\nnbayes-1024\neprover\nvampire\ntiny-a\ntiny-b\nsample\nknn-32\n0123456789012345678901234567890123456789\ncurrent\nfixture-b\nbase|candidate'
  [ "$(cat "$tmp/summary-probe.out")" = "$expected_probe" ] ||
    fail "summarizer did not receive dynamic axes and mode"
  [ "$(cat "$tmp/analysis-probe.out")" = compatible ] ||
    fail "positional summarizer API changed"
)

# A unique install named by its label can collide with a different shared
# install identity. Detect the normalized destination before creating it.
(
  collision_eval="$tmp/collision-eval"
  labels=(all-on shared-a shared-b)
  declare -A label_config=(
    [all-on]=current
    [shared-a]=all-on
    [shared-b]=all-on
  )
  declare -A install_label=([current]=all-on [all-on]=shared-a)
  declare -A install_count=([current]=1 [all-on]=2)
  declare -A install_prefix=()
  declare -A label_prefix=()
  ! _grid_resolve_install_prefixes "$collision_eval" >/dev/null 2>&1
  [ ! -e "$collision_eval" ]
) || fail "distinct install identities sharing a normalized prefix were accepted"
(
  valid_spec
  unset GRID_LABELS
  declare -A GRID_LABELS=([label]=label)
  ! _grid_require_spec >/dev/null 2>&1
) || fail "associative axis was accepted"
(
  valid_spec
  GRID_PREMISES=(knn-64 knn-64)
  ! _grid_require_spec >/dev/null 2>&1
) || fail "duplicate axis value was accepted"
(
  valid_spec
  GRID_PROVERS=(z3)
  ! _grid_require_spec >/dev/null 2>&1
) || fail "unsupported prover was accepted"
(
  valid_spec
  GRID_CONSISTENCY_PREMISE=knn-256
  ! _grid_require_spec >/dev/null 2>&1
) || fail "nonmember consistency premise was accepted"
(
  valid_spec
  GRID_CONSISTENCY_PREMISE=
  ! _grid_require_spec >/dev/null 2>&1
) || fail "empty consistency premise was accepted"
(
  valid_spec
  # shellcheck disable=SC2190
  GRID_LABELS=('../escape')
  ! _grid_require_spec >/dev/null 2>&1
) || fail "unsafe path key was accepted"

# Normalized ancestors, descendants, and symlink aliases of either protected
# confirmation root are rejected, as are overlapping grid output roots.
for protected in \
    "$eval_dir/results" \
    "$eval_dir/results/confirmation/child" \
    "$eval_dir/artifacts/extraction-confirmation" \
    "$eval_dir/artifacts"; do
  results_root=$(realpath -m -- "$protected")
  artifacts_dir=$(realpath -m -- "$tmp/artifacts-safe")
  expect_failure _grid_validate_output_roots
done
mkdir -p "$tmp/links"
ln -s "$eval_dir/results/confirmation" "$tmp/links/confirmation"
results_root=$(realpath -m -- "$tmp/links/confirmation/child")
artifacts_dir=$(realpath -m -- "$tmp/artifacts-safe")
expect_failure _grid_validate_output_roots
results_root=$(realpath -m -- "$tmp/overlap")
artifacts_dir=$(realpath -m -- "$tmp/overlap/child")
expect_failure _grid_validate_output_roots

# Engine and strict-summarizer tree hashing must agree with an independently
# frozen hash, not merely with each other's implementation.
hash_fixture="$tmp/hash-tree"
mkdir -p "$hash_fixture/sub" "$hash_fixture/.git" "$hash_fixture/_build"
printf 'alpha\n' > "$hash_fixture/a.txt"
printf 'beta\n' > "$hash_fixture/sub/b.txt"
printf 'ignored git\n' > "$hash_fixture/.git/ignored"
printf 'ignored build\n' > "$hash_fixture/_build/ignored"
golden_tree_hash=e316ab979d37ab94a8f0c9ff5959c94a43c811122785b33fef37526f3e7cdcc5
shell_tree_hash=$(hash_tree "$hash_fixture")
python_tree_hash=$(python3 - "$eval_dir/tools/summarize-premise-screening.py" "$hash_fixture" <<'PY'
import importlib.util
import pathlib
import sys

spec = importlib.util.spec_from_file_location("premise_summary_hash", sys.argv[1])
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
print(module.hash_tree(pathlib.Path(sys.argv[2])))
PY
)
[ "$shell_tree_hash" = "$golden_tree_hash" ] || fail "shell hash_tree schema drifted"
[ "$python_tree_hash" = "$golden_tree_hash" ] || fail "summarizer hash_tree schema drifted"

# The review guard permits only directly hashed runtime harness bytes plus
# non-runtime eval test registration. Dirty tracked/untracked source remains a
# hard failure, while unrelated untracked local files are irrelevant.
(
  guard_repo="$tmp/guard-repo"
  mkdir -p "$guard_repo/eval/tools" "$guard_repo/eval/tests" \
    "$guard_repo/eval/corpora/tiny" "$guard_repo/src/plugin"
  for file in grid-engine.sh grid-checkpoint-lib.sh rebuild-config.sh cli-lib.sh \
      install-prefix-lib.sh prepare-corpus.sh spec.sh; do
    printf 'original\n' > "$guard_repo/eval/$file"
  done
  printf 'original\n' > "$guard_repo/eval/Makefile"
  printf 'original\n' > "$guard_repo/eval/tools/summarizer.py"
  printf 'original\n' > "$guard_repo/eval/tools/rocq-compile-supervisor.sh"
  printf 'original\n' > "$guard_repo/eval/corpora/tiny/source.v"
  printf 'original\n' > "$guard_repo/src/plugin/runtime.ml"
  git -C "$guard_repo" init -q
  git -C "$guard_repo" config user.name fixture
  git -C "$guard_repo" config user.email fixture@example.invalid
  git -C "$guard_repo" add .
  git -C "$guard_repo" commit -qm fixture

  printf 'reviewed engine\n' > "$guard_repo/eval/grid-engine.sh"
  printf 'reviewed helper\n' > "$guard_repo/eval/grid-checkpoint-lib.sh"
  printf 'reviewed rebuild\n' > "$guard_repo/eval/rebuild-config.sh"
  printf 'reviewed CLI helper\n' > "$guard_repo/eval/cli-lib.sh"
  printf 'reviewed prefix helper\n' > "$guard_repo/eval/install-prefix-lib.sh"
  printf 'reviewed spec\n' > "$guard_repo/eval/spec.sh"
  printf 'reviewed summarizer\n' > "$guard_repo/eval/tools/summarizer.py"
  printf 'reviewed supervisor\n' > "$guard_repo/eval/tools/rocq-compile-supervisor.sh"
  printf 'reviewed test registration\n' > "$guard_repo/eval/Makefile"
  printf 'new test\n' > "$guard_repo/eval/tests/new-test.sh"
  printf 'unrelated\n' > "$guard_repo/local.notes"
  _grid_require_reviewable_worktree "$guard_repo" "$guard_repo/eval/spec.sh" \
    "$guard_repo/eval/tools/summarizer.py"

  printf 'dirty plugin\n' > "$guard_repo/src/plugin/runtime.ml"
  ! _grid_require_reviewable_worktree "$guard_repo" "$guard_repo/eval/spec.sh" \
    "$guard_repo/eval/tools/summarizer.py" >/dev/null 2>&1
  git -C "$guard_repo" checkout -q -- src/plugin/runtime.ml
  printf 'dirty corpus\n' > "$guard_repo/eval/corpora/tiny/source.v"
  ! _grid_require_reviewable_worktree "$guard_repo" "$guard_repo/eval/spec.sh" \
    "$guard_repo/eval/tools/summarizer.py" >/dev/null 2>&1
  git -C "$guard_repo" checkout -q -- eval/corpora/tiny/source.v
  printf 'dirty corpus builder\n' > "$guard_repo/eval/prepare-corpus.sh"
  ! _grid_require_reviewable_worktree "$guard_repo" "$guard_repo/eval/spec.sh" \
    "$guard_repo/eval/tools/summarizer.py" >/dev/null 2>&1
  git -C "$guard_repo" checkout -q -- eval/prepare-corpus.sh
  printf 'new plugin\n' > "$guard_repo/src/plugin/untracked.ml"
  ! _grid_require_reviewable_worktree "$guard_repo" "$guard_repo/eval/spec.sh" \
    "$guard_repo/eval/tools/summarizer.py" >/dev/null 2>&1
) || fail "reviewable-worktree allowed/blocked policy drifted"

# A relative external source is canonicalized once in the invocation directory.
# That exact path remains hashable and is passed to corpus generation after cwd
# changes.
(
  mkdir -p "$tmp/invocation/source" "$tmp/runner"
  printf 'source bytes\n' > "$tmp/invocation/source/input.v"
  cat > "$tmp/runner/prepare-corpus.sh" <<'SCRIPT'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$RECORD"
SCRIPT
  chmod +x "$tmp/runner/prepare-corpus.sh"
  cd "$tmp/invocation"
  external_source=source
  _grid_canonicalize_external_source
  expected=$(realpath "$tmp/invocation/source")
  [ "$external_source" = "$expected" ]
  before=$(hash_tree "$external_source")
  export RECORD="$tmp/external-source-args"
  sample_corpora=true
  cd "$tmp/runner"
  [ "$(hash_tree "$external_source")" = "$before" ]
  _grid_prepare_corpus external-equations "$tmp/prefix" >/dev/null
  mapfile -t args < "$RECORD"
  [ "${args[0]}" = external-equations ]
  [ "${args[1]}" = --coqlib ]
  [ "${args[2]}" = "$tmp/prefix/coq" ]
  [ "${args[3]}" = --sample ]
  [ "${args[4]}" = --source ]
  [ "${args[5]}" = "$expected" ]
) || fail "relative external source was not reused as one absolute path"

# Full-mode provenance follows the installed source tree used by
# prepare-corpus, while sample mode remains pinned to the committed fixture.
(
  fixture_eval="$tmp/provenance-eval"
  mkdir -p "$fixture_eval/corpora/stdlib-regression/sample"
  printf 'sample\n' > "$fixture_eval/corpora/stdlib-regression/sample/sample.v"
  for install_name in first second; do
    mkdir -p "$fixture_eval/_installs/$install_name/coq/user-contrib/Stdlib/Arith" \
      "$fixture_eval/_installs/$install_name/coq/user-contrib/Equations"
    printf 'installed\n' > \
      "$fixture_eval/_installs/$install_name/coq/user-contrib/Stdlib/Arith/source.v"
    printf 'equations\n' > \
      "$fixture_eval/_installs/$install_name/coq/user-contrib/Equations/source.v"
  done
  eval_dir=$fixture_eval
  repo=$tmp
  external_source=
  stdlib_modules=Arith
  dependent_stdlib_modules=Logic
  declare -A corpus_source=() corpus_digest=() corpus_input_trees=() corpus_input_files=()
  declare -A expected_corpus_source=() expected_corpus_digest=()

  sample_corpora=false
  first_prefix="$fixture_eval/_installs/first"
  cat > "$first_prefix/manifest.env" <<EOF
kind=current
config=current
commit=$repo_commit
prefix=$first_prefix
EOF
  _grid_set_corpus_inputs stdlib-regression "$first_prefix"
  installed_digest=${corpus_digest[stdlib-regression]}
  [ "${corpus_source[stdlib-regression]}" = 'installed-Stdlib modules=Arith' ]
  _grid_require_consistent_corpus_provenance stdlib-regression
  declare -A label_config=([fixture]=current)
  declare -A label_preamble=([fixture]='')
  declare -A label_preamble_digest=([fixture]="$(hash_text '')")
  legacy_grid_script_digests=()
  generation_marker="$fixture_eval/generation/generate"
  mkdir -p "$(dirname "$generation_marker")"
  mark_checkpoint "$generation_marker" generation fixture stdlib-regression "$first_prefix"
  printf 'changed installed source\n' > \
    "$first_prefix/coq/user-contrib/Stdlib/Arith/source.v"
  _grid_set_corpus_inputs stdlib-regression "$first_prefix"
  ! checkpoint_matches "$generation_marker" generation fixture \
    stdlib-regression "$first_prefix" >/dev/null 2>&1
  printf 'installed\n' > "$first_prefix/coq/user-contrib/Stdlib/Arith/source.v"
  _grid_set_corpus_inputs stdlib-regression "$first_prefix"
  _grid_set_corpus_inputs stdlib-regression "$fixture_eval/_installs/second"
  _grid_require_consistent_corpus_provenance stdlib-regression
  _grid_set_corpus_inputs external-equations "$first_prefix"
  equations_digest=${corpus_digest[external-equations]}
  [ "${corpus_source[external-equations]}" = installed-Equations ]
  printf 'changed equations source\n' > \
    "$first_prefix/coq/user-contrib/Equations/source.v"
  _grid_set_corpus_inputs external-equations "$first_prefix"
  [ "${corpus_digest[external-equations]}" != "$equations_digest" ]

  printf 'changed installed source\n' > \
    "$fixture_eval/_installs/second/coq/user-contrib/Stdlib/Arith/source.v"
  _grid_set_corpus_inputs stdlib-regression "$fixture_eval/_installs/second"
  [ "${corpus_digest[stdlib-regression]}" != "$installed_digest" ]
  ! _grid_require_consistent_corpus_provenance stdlib-regression >/dev/null 2>&1

  sample_corpora=true
  _grid_set_corpus_inputs stdlib-regression "$fixture_eval/_installs/first"
  sample_digest=${corpus_digest[stdlib-regression]}
  [ "${corpus_source[stdlib-regression]}" = \
    'provenance-eval/corpora/stdlib-regression/sample' ]
  printf 'another installed change\n' > \
    "$first_prefix/coq/user-contrib/Stdlib/Arith/source.v"
  _grid_set_corpus_inputs stdlib-regression "$first_prefix"
  [ "${corpus_digest[stdlib-regression]}" = "$sample_digest" ]

  # A corpus resolved from a directory in the tree is named relative to the
  # checkout on every branch that resolves one, not by the absolute path of the
  # worktree that happened to run the grid.
  sample_corpora=false
  examples="$fixture_eval/_external/Coq-Equations/_build/default/examples"
  mkdir -p "$examples"
  printf 'examples\n' > "$examples/source.v"
  _grid_set_corpus_inputs equations-examples "$first_prefix"
  [ "${corpus_source[equations-examples]}" = \
    'provenance-eval/_external/Coq-Equations/_build/default/examples' ]
  external_source="$fixture_eval/elsewhere/equations"
  mkdir -p "$external_source"
  printf 'external\n' > "$external_source/source.v"
  _grid_set_corpus_inputs external-equations "$first_prefix"
  [ "${corpus_source[external-equations]}" = 'provenance-eval/elsewhere/equations' ]
) || fail "installed/sample corpus provenance did not track actual sources"

# Only a source inside the checkout has a spelling relative to it -- the
# checkout itself included; one outside -- which only --external-source can be
# -- has to stay absolute.
(
  repo=/opt/checkout
  [ "$(corpus_source_path /opt/checkout/eval/corpora/tiny)" = eval/corpora/tiny ] &&
    [ "$(corpus_source_path /opt/checkout)" = . ] &&
    [ "$(corpus_source_path /opt/checkout-elsewhere)" = /opt/checkout-elsewhere ] &&
    [ "$(corpus_source_path /elsewhere/equations)" = /elsewhere/equations ]
) || fail "corpus source path did not relativize exactly inside the checkout"

# Missing operands must be normal usage errors, not nounset diagnostics.
for command in \
    "$eval_dir/run-screening-grid.sh --tim" \
    "$eval_dir/run-screening-grid.sh --consistency-tim" \
    "$eval_dir/run-screening-grid.sh --compile-timeout" \
    "$eval_dir/run-screening-grid.sh --compile-timeout-grace" \
    "$eval_dir/run-screening-grid.sh --only-label" \
    "$eval_dir/run-screening-grid.sh --only-corpus" \
    "$eval_dir/run-screening-grid.sh --external-source" \
    "$eval_dir/run-screening-grid.sh --jobs"; do
  set +e
  output=$(bash -c "$command" 2>&1)
  status=$?
  set -e
  [ "$status" -eq 2 ] || fail "missing operand exited $status: $command"
  [[ "$output" == *Usage:* ]] || fail "missing operand omitted usage: $command"
  [[ "$output" != *"unbound variable"* ]] || fail "missing operand raised nounset: $command"
done

set +e
output=$("$eval_dir/rebuild-config.sh" current --label ../bad 2>&1)
status=$?
set -e
if [ "$status" -ne 2 ] || [[ "$output" != *"safe single path component"* ]]; then
  fail "rebuild-config accepted an unsafe label"
fi

# The prefix is validated as it was spelled: command substitution around
# `realpath` drops a trailing newline, so a prefix that ends in one would
# otherwise be checked, and erased, as some other directory.
mkdir -p "$tmp/prefix-newline"
set +e
output=$("$eval_dir/rebuild-config.sh" current --prefix "$tmp/prefix-newline"$'\n' 2>&1)
status=$?
set -e
if [ "$status" -ne 1 ] || [[ "$output" != *"contains a newline"* ]]; then
  fail "rebuild-config accepted a prefix ending in a newline"
fi
[ -d "$tmp/prefix-newline" ] || fail "rebuild-config erased the newline-free prefix"

echo "test_grid_engine: ok"
