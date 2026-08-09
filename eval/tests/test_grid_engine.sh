#!/usr/bin/env bash
# Test fixtures and callbacks are consumed indirectly by the sourced engine.
# SC2031 is a false positive from same-name assignments inside grid_run's
# subshell when ShellCheck follows that engine source.
# shellcheck disable=SC2031,SC2034,SC2317
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
legacy_grid_script_digests=("$legacy")
corpus_mode=sample
force=false
declare -A label_config=([label]=all-on)
declare -A label_preamble=([label]='')
declare -A label_preamble_digest=([label]="$(_grid_hash_text '')")
declare -A corpus_source=([corpus]=eval/corpora/corpus/sample)
declare -A corpus_digest=([corpus]=cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc)
prefix="$tmp/prefix"
mkdir -p "$prefix" "$tmp/checkpoint"
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

write_historical_marker() {
  local historical_digest="$1"
  local grid_script_digest="$historical_digest"
  checkpoint_contents generation label corpus "$prefix" > "$marker.done"
}

# The actual historical extraction-screening digest is accepted with an empty
# preamble when all other provenance is current.
write_historical_marker "$legacy"
checkpoint_matches "$marker" generation label corpus "$prefix" ||
  fail "valid historical checkpoint was not reused"
[ -f "$marker.done" ] || fail "valid historical checkpoint was removed"

# An undeclared old digest is not a migration wildcard.
write_historical_marker dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd
expect_failure checkpoint_matches "$marker" generation label corpus "$prefix"
[ ! -e "$marker.done" ] || fail "unsupported historical marker survived"

# Historical markers are never valid for a nonempty preamble.
write_historical_marker "$legacy"
label_preamble[label]='Set Hammer DefinitionPremises 8.'
label_preamble_digest[label]=$(_grid_hash_text "${label_preamble[label]}")
expect_failure checkpoint_matches "$marker" generation label corpus "$prefix"
label_preamble[label]=''
label_preamble_digest[label]=$(_grid_hash_text '')

# Tampering with a provenance field, or merely changing an unrelated current
# input field, invalidates the otherwise accepted historical digest.
write_historical_marker "$legacy"
sed -i 's/^repository_commit=.*/repository_commit=tampered/' "$marker.done"
expect_failure checkpoint_matches "$marker" generation label corpus "$prefix"
write_historical_marker "$legacy"
old_corpus_digest=${corpus_digest[corpus]}
corpus_digest[corpus]=eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
expect_failure checkpoint_matches "$marker" generation label corpus "$prefix"
corpus_digest[corpus]=$old_corpus_digest

# Prefix reuse requires both the path-bound ownership marker and manifest path.
_grid_manifest_matches_install all-on "$prefix" || fail "owned prefix was rejected"
printf '%s\nprefix=%s\n' "$EVAL_PREFIX_MARKER_MAGIC" "$tmp/elsewhere" > \
  "$prefix/$EVAL_PREFIX_MARKER"
expect_failure _grid_manifest_matches_install all-on "$prefix"
eval_prefix_write_marker "$prefix"
sed -i "s|^prefix=.*|prefix=$tmp/elsewhere|" "$prefix/manifest.env"
expect_failure _grid_manifest_matches_install all-on "$prefix"
sed -i "s|^prefix=.*|prefix=$prefix|" "$prefix/manifest.env"

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
  _grid_prepare_corpus external-equations >/dev/null
  mapfile -t args < "$RECORD"
  [ "${args[0]}" = external-equations ]
  [ "${args[1]}" = --sample ]
  [ "${args[2]}" = --source ]
  [ "${args[3]}" = "$expected" ]
) || fail "relative external source was not reused as one absolute path"

# Missing operands must be normal usage errors, not nounset diagnostics.
for command in \
    "$eval_dir/run-screening-grid.sh --tim" \
    "$eval_dir/run-screening-grid.sh --consistency-tim" \
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

echo "test_grid_engine: ok"
