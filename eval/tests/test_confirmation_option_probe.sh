#!/usr/bin/env bash
# Checkpoint fixture globals are consumed dynamically by the sourced helper.
# shellcheck disable=SC2034
set -euo pipefail

eval_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
# shellcheck source=eval/confirmation-option-probe.sh
# shellcheck disable=SC1091
source "$eval_dir/confirmation-option-probe.sh"
# shellcheck source=eval/grid-checkpoint-lib.sh
# shellcheck disable=SC1091
source "$eval_dir/grid-checkpoint-lib.sh"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fail() {
  echo "test_confirmation_option_probe: $*" >&2
  exit 1
}

trap -p EXIT HUP INT TERM > "$tmp/caller-traps.before"

expect_parse() {
  local expected="$1" option="$2" fixture="$3" actual
  actual=$(confirmation_parse_option_value "$fixture" "$option") ||
    fail "did not parse $option from $(basename "$fixture")"
  [ "$actual" = "$expected" ] ||
    fail "parsed $option as $actual, expected $expected"
}

cat > "$tmp/current.out" <<'EOF'
Current value of Hammer DefinitionPremises is 32
Current value of Hammer DefinitionFeatures is 16
EOF
expect_parse 32 DefinitionPremises "$tmp/current.out"
expect_parse 16 DefinitionFeatures "$tmp/current.out"

cat > "$tmp/variant.out" <<'EOF'
  Hammer   DefinitionPremises : 8.
Hammer DefinitionFeatures = 16
EOF
expect_parse 8 DefinitionPremises "$tmp/variant.out"
expect_parse 16 DefinitionFeatures "$tmp/variant.out"

for malformed in wrong-key duplicate noninteger trailing; do
  case "$malformed" in
    wrong-key) printf '%s\n' 'Current value of Hammer DefinitionFeatures is 32' ;;
    duplicate) printf '%s\n' 'Hammer DefinitionPremises is 32' 'Hammer DefinitionPremises is 8' ;;
    noninteger) printf '%s\n' 'Hammer DefinitionPremises is undefined' ;;
    trailing) printf '%s\n' 'Hammer DefinitionPremises is 32 extra' ;;
  esac > "$tmp/$malformed.out"
  if confirmation_parse_option_value "$tmp/$malformed.out" DefinitionPremises >/dev/null; then
    fail "accepted malformed $malformed output"
  fi
done

mkdir -p "$tmp/probe-tmp" "$tmp/prefix/bin" "$tmp/prefix/coq"
cat > "$tmp/prefix/bin/rocq" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[ "${PATH%%:*}" = "$FAKE_PREFIX/bin" ]
[ "$OCAMLPATH" = "$FAKE_PREFIX:$FAKE_BASE_OCAMLPATH" ]
[ "$#" -eq 7 ]
[ "$1" = c ]
[ "$2" = -q ]
[ "$3" = -coqlib ]
[ "$4" = "$FAKE_PREFIX/coq" ]
[ "$5" = -require ]
[ "$6" = Hammer.Plugin.Hammer ]
probe=$7
expected=$'Test Hammer DefinitionPremises.\nTest Hammer DefinitionFeatures.\n'
[ "$(cat "$probe"; printf x)" = "${expected}x" ]
[ -z "${FAKE_ROCQ_FAIL:-}" ] || exit 9
[ -z "${FAKE_ROCQ_SLEEP:-}" ] || sleep 30
printf '%s\n' \
  'Current value of Hammer DefinitionPremises is 32' \
  'Hammer DefinitionFeatures : 16.'
EOF
chmod +x "$tmp/prefix/bin/rocq"
cat > "$tmp/probe-supervisor" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$@" > "$FAKE_SUPERVISOR_ARGS"
exec "$REAL_COMPILE_SUPERVISOR" "$@"
EOF
chmod +x "$tmp/probe-supervisor"
export FAKE_PREFIX="$tmp/prefix"
export FAKE_BASE_OCAMLPATH="$tmp/base-ocamlpath"
export FAKE_SUPERVISOR_ARGS="$tmp/supervisor.args"
export REAL_COMPILE_SUPERVISOR="$eval_dir/tools/rocq-compile-supervisor.sh"
export OCAMLPATH="$FAKE_BASE_OCAMLPATH"
export TMPDIR="$tmp/probe-tmp"
confirmation_probe_hammer_options "$tmp/prefix" "$tmp/probe-supervisor" \
  2 1 option-probe
[ "$CONFIRMATION_DEFINITION_PREMISES" = 32 ] || fail "probe returned wrong premise value"
[ "$CONFIRMATION_DEFINITION_FEATURES" = 16 ] || fail "probe returned wrong feature value"
mapfile -t supervisor_args < "$FAKE_SUPERVISOR_ARGS"
if ! { [ "${supervisor_args[0]}" = --timeout ] &&
    [ "${supervisor_args[1]}" = 2 ] &&
    [ "${supervisor_args[2]}" = --grace ] &&
    [ "${supervisor_args[3]}" = 1 ] &&
    [ "${supervisor_args[4]}" = --phase ] &&
    [ "${supervisor_args[5]}" = option-probe ] &&
    [ "${supervisor_args[6]}" = --source ] &&
    [ "$(basename "${supervisor_args[7]}")" = options.v ] &&
    [ "${supervisor_args[8]}" = -- ] &&
    [ "${supervisor_args[9]}" = rocq ]; }; then
  fail "probe did not pass its compile policy and phase to the supervisor"
fi
[ -z "$(find "$TMPDIR" -mindepth 1 -print -quit)" ] || fail "successful probe left a temporary"
if FAKE_ROCQ_FAIL=1 confirmation_probe_hammer_options "$tmp/prefix" \
    "$tmp/probe-supervisor" 2 1 option-probe >/dev/null 2>&1; then
  fail "accepted a failed Rocq probe"
fi
[ -z "$(find "$TMPDIR" -mindepth 1 -print -quit)" ] || fail "failed probe left a temporary"
if FAKE_ROCQ_SLEEP=1 confirmation_probe_hammer_options "$tmp/prefix" \
    "$tmp/probe-supervisor" 1 1 option-probe >"$tmp/slow.out" 2>"$tmp/slow.err"; then
  fail "accepted a timed-out Rocq probe"
fi
grep -Fq 'TIMEOUT phase=option-probe' "$tmp/slow.err" ||
  fail "timed-out probe omitted the supervisor phase diagnostic"
[ -z "$(find "$TMPDIR" -mindepth 1 -print -quit)" ] || fail "timed-out probe left a temporary"

# Exercise the checkpoint-manifest path in an isolated root. Both values are
# part of the exact marker, so changing either invalidates it.
repo_commit=0123456789012345678901234567890123456789
grid_script_digest=aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
grid_helper_digest=bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb
option_probe_digest=cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
compile_supervisor_digest=eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
compile_timeout=600
compile_timeout_grace=10
corpus_mode=sample
force=false
declare -A label_config=([current]=current)
declare -A label_definition_premises=([current]=32)
declare -A label_definition_features=([current]=16)
declare -A corpus_source=([sample]=fixture)
declare -A corpus_digest=([sample]=dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd)
cat > "$tmp/prefix/manifest.env" <<EOF
kind=current
config=current
commit=$repo_commit
EOF
chmod 0640 "$tmp/prefix/manifest.env"
confirmation_record_hammer_options "$tmp/prefix/manifest.env" \
  "$option_probe_digest" 8 4
confirmation_record_hammer_options "$tmp/prefix/manifest.env" \
  "$option_probe_digest" "$CONFIRMATION_DEFINITION_PREMISES" \
  "$CONFIRMATION_DEFINITION_FEATURES"
grep -Fqx 'definition_premises=32' "$tmp/prefix/manifest.env" ||
  fail "install manifest omitted DefinitionPremises"
grep -Fqx 'definition_features=16' "$tmp/prefix/manifest.env" ||
  fail "install manifest omitted DefinitionFeatures"
[ "$(grep -Ec '^(option_probe_sha256|definition_premises|definition_features)=' \
    "$tmp/prefix/manifest.env")" -eq 3 ] || fail "install manifest repeated option fields"
[ "$(stat -c %a "$tmp/prefix/manifest.env")" = 640 ] || fail "manifest mode changed during rewrite"
if confirmation_record_hammer_options "$tmp/missing-manifest.env" \
    "$option_probe_digest" 32 0 >/dev/null 2>&1; then
  fail "rewrote a missing manifest"
fi
if compgen -G "$tmp/missing-manifest.env.tmp.*" >/dev/null; then
  fail "failed manifest rewrite left a temporary"
fi

# _installs/current is shared with the screening grids, whose checkpoints hash
# its manifest.env into install_manifest_sha256, so recording the probed options
# must leave that file byte-identical.  Exercise the production
# probe_label_options against the fake install above rather than a copy of it.
extract_shell_function() {
  awk -v name="$2" '
    $0 == name "() {" { inside = 1 }
    inside { print }
    inside && $0 == "}" { exit }
  ' "$1"
}
eval "$(extract_shell_function "$eval_dir/run-confirmation-grid.sh" probe_label_options)"
compile_supervisor="$tmp/probe-supervisor"
option_probe_phase='option-probe'
shared_options="$tmp/prefix/confirmation-options.env"
# Reset the fixture to a manifest that carries no option fields; a manifest that
# already held the probed values would reproduce its own bytes under an in-place
# rewrite and hide exactly the regression this checks for.
cat > "$tmp/prefix/manifest.env" <<EOF
kind=current
config=current
commit=$repo_commit
EOF
cp "$tmp/prefix/manifest.env" "$tmp/shared-manifest.expected"
shared_manifest_digest=$(hash_file "$tmp/prefix/manifest.env")
label_definition_premises[current]=
label_definition_features[current]=
probe_label_options current "$tmp/prefix" > /dev/null
cmp -s "$tmp/prefix/manifest.env" "$tmp/shared-manifest.expected" ||
  fail "recording the probed options rewrote the shared install manifest"
[ "$(hash_file "$tmp/prefix/manifest.env")" = "$shared_manifest_digest" ] ||
  fail "recording the probed options changed install_manifest_sha256"
grep -Fqx 'definition_premises=32' "$shared_options" ||
  fail "option sidecar omitted DefinitionPremises"
grep -Fqx 'definition_features=16' "$shared_options" ||
  fail "option sidecar omitted DefinitionFeatures"
grep -Fqx "option_probe_sha256=$option_probe_digest" "$shared_options" ||
  fail "option sidecar omitted the probe digest"
[ "${label_definition_premises[current]}" = 32 ] &&
  [ "${label_definition_features[current]}" = 16 ] ||
  fail "probe_label_options did not publish the probed values"
cp "$shared_options" "$tmp/shared-options.expected"
probe_label_options current "$tmp/prefix" > /dev/null
cmp -s "$shared_options" "$tmp/shared-options.expected" ||
  fail "reprobing the same install rewrote the option sidecar differently"
cmp -s "$tmp/prefix/manifest.env" "$tmp/shared-manifest.expected" ||
  fail "reprobing the same install rewrote the shared install manifest"
[ -z "$(find "$TMPDIR" -mindepth 1 -print -quit)" ] ||
  fail "option recording left a temporary"
marker="$tmp/results/current/sample/generate"
mkdir -p "$(dirname "$marker")"
confirmation_mark_checkpoint "$marker" generation current sample "$tmp/prefix"
grep -Fqx 'definition_premises=32' "$marker.done" || fail "marker omitted DefinitionPremises"
grep -Fqx 'definition_features=16' "$marker.done" || fail "marker omitted DefinitionFeatures"
grep -Fqx "compile_supervisor_sha256=$compile_supervisor_digest" "$marker.done" ||
  fail "marker omitted compile supervisor hash"
grep -Fqx 'compile_timeout=600' "$marker.done" || fail "marker omitted compile timeout"
confirmation_checkpoint_done "$marker" generation current sample "$tmp/prefix" ||
  fail "fresh option/compile provenance did not match"
label_definition_premises[current]=8
if confirmation_checkpoint_done "$marker" generation current sample \
    "$tmp/prefix" >/dev/null 2>&1; then
  fail "changed option provenance reused a checkpoint"
fi
label_definition_premises[current]=32
confirmation_mark_checkpoint "$marker" generation current sample "$tmp/prefix"
compile_timeout=601
if confirmation_checkpoint_done "$marker" generation current sample \
    "$tmp/prefix" >/dev/null 2>&1; then
  fail "changed compile policy reused a generation checkpoint"
fi
compile_timeout=600

# Exercise the production final-provenance publisher, including the shared
# fields, install-manifest digest, confirmation fields, publication mode, and
# cleanup when its producer fails after creating both temporary files.
production_eval_dir=$eval_dir
eval_dir="$tmp/final-eval"
results_root="$eval_dir/results"
mkdir -p "$eval_dir/_installs/current" "$results_root/current/sample"
cp "$tmp/prefix/manifest.env" "$eval_dir/_installs/current/manifest.env"
printf 'done\n' > "$results_root/current/sample/generate.done"
printf 'summary\n' > "$eval_dir/summary.tsv"
printf 'analysis\n' > "$eval_dir/analysis.md"
printf '#!/usr/bin/env python3\n' > "$eval_dir/summarizer.py"
labels=(current)
corpora=(sample)
tim=10
consistency_tim=2
corpus_source[sample]=fixture
final_provenance="$eval_dir/provenance.env"
(
  umask 027
  confirmation_publish_final_provenance "$final_provenance" confirmation \
    "$eval_dir/summarizer.py" "$eval_dir/summary.tsv" "$eval_dir/analysis.md" \
    "$option_probe_digest"
)
[ "$(stat -c %a "$final_provenance")" = 640 ] ||
  fail "new final provenance did not honor 0666 & umask"
manifest_digest=$(hash_file "$eval_dir/_installs/current/manifest.env")
for expected in \
    'provenance_version=1' 'grid=confirmation' \
    "repository_commit=$repo_commit" \
    "grid_script_sha256=$grid_script_digest" \
    "checkpoint_helper_sha256=$grid_helper_digest" \
    "compile_supervisor_sha256=$compile_supervisor_digest" \
    'compile_timeout=600' 'compile_timeout_grace=10' \
    "option_probe_sha256=$option_probe_digest" \
    'label.current.config=current' \
    "label.current.install_commit=$repo_commit" \
    'label.current.install_kind=current' \
    "label.current.install_manifest_sha256=$manifest_digest" \
    'label.current.definition_premises=32' \
    'label.current.definition_features=16' \
    'corpus.sample.mode=sample' 'corpus.sample.source=fixture' \
    "corpus.sample.sha256=${corpus_digest[sample]}"; do
  grep -Fqx "$expected" "$final_provenance" ||
    fail "final provenance omitted $expected"
done
[ "$(grep -Ec '^(option_probe_sha256|label\.current\.definition_(premises|features))=' \
    "$final_provenance")" -eq 3 ] || fail "final provenance repeated option fields"
for field in compile_supervisor_sha256 compile_timeout compile_timeout_grace; do
  [ "$(grep -c "^$field=" "$final_provenance")" -eq 1 ] ||
    fail "final provenance did not record $field exactly once"
done
chmod 0604 "$final_provenance"
confirmation_publish_final_provenance "$final_provenance" confirmation \
  "$eval_dir/summarizer.py" "$eval_dir/summary.tsv" "$eval_dir/analysis.md" \
  "$option_probe_digest"
[ "$(stat -c %a "$final_provenance")" = 604 ] ||
  fail "final provenance rewrite did not preserve mode"
printf 'preserve-on-failure\n' > "$final_provenance"
write_grid_provenance() {
  printf 'partial\n' > "$1"
  printf 'nested partial\n' > "$1.tmp.$$"
  return 1
}
if confirmation_publish_final_provenance "$final_provenance" confirmation \
    "$eval_dir/summarizer.py" "$eval_dir/summary.tsv" "$eval_dir/analysis.md" \
    "$option_probe_digest"; then
  fail "published final provenance after producer failure"
fi
[ "$(cat "$final_provenance")" = preserve-on-failure ] ||
  fail "failed final provenance publication changed its target"
if compgen -G "$final_provenance.tmp.*" >/dev/null; then
  fail "failed final provenance publication left a temporary"
fi
write_grid_provenance() {
  printf 'interrupted partial\n' > "$1"
  kill -TERM "$BASHPID"
}
if confirmation_publish_final_provenance "$final_provenance" confirmation \
    "$eval_dir/summarizer.py" "$eval_dir/summary.tsv" "$eval_dir/analysis.md" \
    "$option_probe_digest"; then
  fail "published final provenance after interruption"
fi
[ "$(cat "$final_provenance")" = preserve-on-failure ] ||
  fail "interrupted final provenance publication changed its target"
if compgen -G "$final_provenance.tmp.*" >/dev/null; then
  fail "interrupted final provenance publication left a temporary"
fi

# Every checkpoint stage goes through wrappers that add all three fields.
python3 - "$production_eval_dir/run-confirmation-grid.sh" <<'PY'
import pathlib
import re
import sys

text = pathlib.Path(sys.argv[1]).read_text()
for function, stage in (
    ("run_generation", "generation"),
    ("run_prover", "prover"),
    ("run_reconstruction", "reconstruction"),
    ("run_consistency", "consistency"),
):
    match = re.search(rf"^{function}\(\) \{{\n(.*?)^\}}$", text, re.M | re.S)
    if match is None:
        raise SystemExit(f"missing checkpoint stage function: {function}")
    body = match.group(1)
    for helper in ("confirmation_checkpoint_done", "confirmation_mark_checkpoint"):
        if not re.search(rf"^  (?:if )?{helper} .* {stage} ", body, re.M):
            raise SystemExit(f"{function} does not use {helper} for {stage}")
if re.search(r"^  (?:if )?(?:checkpoint_done|mark_checkpoint) ", text, re.M):
    raise SystemExit("confirmation stage bypasses option-provenance wrappers")
if re.search(r"confirmation_record_hammer_options \"[^\"]*manifest\.env\"", text):
    raise SystemExit("confirmation options are recorded into the shared install manifest")
if not re.search(
    r'confirmation_probe_hammer_options "\$prefix" "\$compile_supervisor" \\\n'
    r'    "\$compile_timeout" "\$compile_timeout_grace" "\$option_probe_phase"',
    text,
):
    raise SystemExit("confirmation probe does not receive the configured compile policy")
PY

trap -p EXIT HUP INT TERM > "$tmp/caller-traps.after"
cmp -s "$tmp/caller-traps.before" "$tmp/caller-traps.after" ||
  fail "publication helpers clobbered caller traps"

echo "test_confirmation_option_probe: ok"
