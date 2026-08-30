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
translation_log="$tmp/translation.log"
mkdir -p "$repo/eval" "$repo/src/plugin" "$repo/tests/plugin" "$mock_bin" \
  "$fake_coqlib/theories" "$fake_coqlib/user-contrib" "$tmp/runtime/rocq-runtime"
cp "$eval_dir/rebuild-config.sh" "$eval_dir/cli-lib.sh" \
  "$eval_dir/install-prefix-lib.sh" "$repo/eval/"

cat > "$repo/src/plugin/coq_transl_opts.ml" <<'EOF'
let opt_dependent_types = true
EOF
printf 'semantic fixture\n' > "$repo/tests/plugin/singleton_premises.v"
printf '# assertion library fixture\n' > "$repo/tests/plugin/transl-assert-lib.sh"
cat > "$repo/tests/plugin/check-singleton-premises.sh" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
work=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
[ -f "$work/singleton_premises.v" ]
[ -f "$work/transl-assert-lib.sh" ]
[ "$1" = "$work/singleton_premises.out" ]
expect=${SINGLETON_PREMISES_EXPECT:-present}
printf '%s %s\n' "$expect" "$work" >> "$VALIDATION_LOG"
# The dollar signs are literal parts of Hammer's generated identifiers.
# shellcheck disable=SC2016
grep -q '^\$_typeof_singleton_premises\.' "$1"
if [ "$expect" = absent ]; then
  # shellcheck disable=SC2016
  ! grep -q '^\$_def_singleton_premises\.' "$1"
else
  # shellcheck disable=SC2016
  grep -q '^\$_def_singleton_premises\.' "$1"
fi
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
    printf '%s\n' "$PWD" >> "$TRANSLATION_LOG"
    # What the probe translates with is the plugin in the prefix it is pointed
    # at, so read that prefix's option value rather than the checkout's.
    coqlib=
    prev=
    for arg in "$@"; do
      if [ "$prev" = -coqlib ]; then
        coqlib=$arg
      fi
      prev=$arg
    done
    [ -n "$coqlib" ]
    dependent=$(cat "$(dirname "$coqlib")/opt_dependent_types")
    # The dollar signs are literal parts of Hammer's generated identifiers.
    printf '%s\n' '$_typeof_singleton_premises.singleton_cast: mock translation'
    # STALE_DEPENDENT_ARTIFACT stands for a prefix whose plugin was never
    # rebuilt, so it still collapses singletons however it was installed.
    if [ "$dependent" = true ] || [ -n "${STALE_DEPENDENT_ARTIFACT:-}" ]; then
      printf '%s\n' '$_def_singleton_premises.singleton_cast: mock translation'
    fi
    ;;
  *) exit 1 ;;
esac
EOF
cat > "$mock_bin/make" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[ "$1" = install ]
[[ " $* " == *"COQFLAGS=-coqlib "* ]]
prefix=
for arg in "$@"; do
  case "$arg" in
    COQPLUGININSTALL=*) prefix=${arg#COQPLUGININSTALL=} ;;
  esac
done
[ -n "$prefix" ]
# A real install bakes the tree's option values into the installed plugin;
# record them beside it so the probe can be answered from the prefix.
sed -n 's/^let opt_dependent_types = \(true\|false\)$/\1/p' \
  src/plugin/coq_transl_opts.ml > "$prefix/opt_dependent_types"
[ -s "$prefix/opt_dependent_types" ]
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
export TRANSLATION_LOG="$translation_log"

# Every configuration translates the probe against the prefix it just
# installed and hands the output to the assertion script, in the mode its
# option value implies: the collapsed equations when dependent types are
# handled, their absence when they are not.
expect_counts() {
  local config=$1 validations=$2 translations=$3 mode=$4
  [ "$(wc -l < "$validation_log")" -eq "$validations" ] ||
    fail "$config did not run the singleton-premise check $validations time(s)"
  [ "$(wc -l < "$translation_log")" -eq "$translations" ] ||
    fail "$config did not translate the probe $translations time(s)"
  [ "$(tail -n 1 "$validation_log" | cut -d' ' -f1)" = "$mode" ] ||
    fail "$config did not run the singleton-premise check in $mode mode"
}

run_config() {
  local config=$1 work
  (cd "$repo" && ./eval/rebuild-config.sh "$config" >/dev/null)
  work=$(tail -n 1 "$translation_log")
  [ ! -d "$work" ] || fail "$config left semantic-validation temporary directory $work"
  (cd "$repo" && git diff --quiet -- src/plugin/coq_transl_opts.ml) ||
    fail "$config did not restore coq_transl_opts.ml"
}

run_config current
expect_counts current 1 1 present

run_config dependent-types-off
expect_counts dependent-types-off 2 2 absent

sed -i 's/^let opt_dependent_types = true$/let opt_dependent_types = false/' \
  "$repo/src/plugin/coq_transl_opts.ml"
(cd "$repo" && git add src/plugin/coq_transl_opts.ml && git commit -qm dependent-off-current)
run_config current
expect_counts "current with dependent types off" 3 3 absent

# A prefix whose artifact still emits the dependent-only equations is a stale
# build, not an off baseline: the rebuild must fail rather than leave the grids
# attributing the current translation to it.
if (cd "$repo" && STALE_DEPENDENT_ARTIFACT=1 ./eval/rebuild-config.sh \
      dependent-types-off >/dev/null 2>&1); then
  fail "a stale dependent-types artifact was accepted as dependent-types-off"
fi
expect_counts "the rejected stale artifact" 4 4 absent
work=$(tail -n 1 "$translation_log")
[ ! -d "$work" ] ||
  fail "the rejected stale artifact left semantic-validation temporary directory $work"
(cd "$repo" && git diff --quiet -- src/plugin/coq_transl_opts.ml) ||
  fail "the rejected stale artifact did not restore coq_transl_opts.ml"

echo "test_rebuild_config: ok"
