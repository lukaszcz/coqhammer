#!/usr/bin/env bash
set -euo pipefail

eval_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

fail() {
  echo "test_rebuild_config: $*" >&2
  exit 1
}

repo="$tmp/repo"
mock_bin="$tmp/bin"
fake_coqlib="$tmp/runtime/coq"
validation_log="$tmp/validation.log"
mkdir -p "$repo/eval" "$repo/src/plugin" "$repo/tests/plugin" "$mock_bin" \
  "$fake_coqlib/theories" "$fake_coqlib/user-contrib" "$tmp/runtime/rocq-runtime"
cp "$eval_dir/rebuild-config.sh" "$eval_dir/cli-lib.sh" \
  "$eval_dir/install-prefix-lib.sh" "$repo/eval/"

cat > "$repo/src/plugin/coq_transl_opts.ml" <<'EOF'
let opt_erasure_guards = false
let opt_indexed_families = true
EOF
printf 'semantic fixture\n' > "$repo/tests/plugin/singleton_premises.v"
printf '# assertion library fixture\n' > "$repo/tests/plugin/transl-assert-lib.sh"
cat > "$repo/tests/plugin/check-singleton-premises.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
work=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
[ -f "$work/singleton_premises.v" ]
[ -f "$work/transl-assert-lib.sh" ]
[ "$2" = "$work/singleton_premises.out" ]
printf '%s\t%s\n' "$1" "$work" >> "$VALIDATION_LOG"
EOF
chmod +x "$repo/tests/plugin/check-singleton-premises.sh"
printf 'runtime\n' > "$tmp/runtime/rocq-runtime/fixture"

cat > "$mock_bin/rocq" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [ "$#" -eq 2 ] && [ "$1" = c ] && [ "$2" = -where ]; then
  printf '%s\n' "$FAKE_COQLIB"
  exit 0
fi
case " $* " in
  *" singleton_premises.v "*)
    [ -f singleton_premises.v ]
    printf 'mock singleton translation\n'
    ;;
  *" prop_case_ablation.v "*)
    [ -f prop_case_ablation.v ]
    printf 'mock proposition-case translation\n'
    ;;
  *) exit 1 ;;
esac
EOF
cat > "$mock_bin/make" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[ "$1" = install ]
[[ " $* " == *"COQFLAGS=-coqlib "* ]]
EOF
chmod +x "$mock_bin/rocq" "$mock_bin/make"

(
  cd "$repo"
  git init -q
  git config user.name test
  git config user.email test@example.invalid
  git add .
  git commit -qm fixture
)

export PATH="$mock_bin:$PATH"
export FAKE_COQLIB="$fake_coqlib"
export VALIDATION_LOG="$validation_log"

run_config() {
  local config=$1 expected_mode=$2 line mode work
  (cd "$repo" && ./eval/rebuild-config.sh "$config" >/dev/null)
  line=$(tail -n 1 "$validation_log")
  IFS=$'\t' read -r mode work <<< "$line"
  [ "$mode" = "$expected_mode" ] ||
    fail "$config selected $mode instead of $expected_mode"
  [ ! -d "$work" ] || fail "$config left semantic-validation temporary directory $work"
  (cd "$repo" && git diff --quiet -- src/plugin/coq_transl_opts.ml) ||
    fail "$config did not restore coq_transl_opts.ml"
}

run_config current guards-off
run_config all-on guards-indexed
run_config all-off guards-off
run_config loo-erasure-guards guards-off
run_config loo-indexed-families guards-legacy
sed -i \
  -e 's/^let opt_erasure_guards = false$/let opt_erasure_guards = true/' \
  -e 's/^let opt_indexed_families = true$/let opt_indexed_families = false/' \
  "$repo/src/plugin/coq_transl_opts.ml"
(cd "$repo" && git add src/plugin/coq_transl_opts.ml && git commit -qm guarded-legacy-current)
run_config current guards-legacy

[ "$(wc -l < "$validation_log")" -eq 6 ] ||
  fail "semantic validation did not run exactly once per rebuild"

echo "test_rebuild_config: ok"
