# Shared assertion helpers for the translation-shape check scripts.
#
# Hammer generates fresh identifiers for lifted symbols and their binders, so
# assertions must parse those identifiers out of the emitted line and correlate
# them, rather than baking a particular numbering into a regular expression.
#
# Sourcing scripts must set:
#   out             - path to the captured translator output
#   assert_context  - short name of the suite, used in failure messages
#
# Dollar signs in generated identifiers are literal, and parse_binders assigns
# its named arrays indirectly through a nameref.
# shellcheck disable=SC2016,SC2154

fail() {
  echo "$assert_context assertion FAILED: $*" >&2
  exit 1
}

# Every output line beginning with the given literal prefix.
lines_with_prefix() {
  awk -v prefix="$1" 'index($0, prefix) == 1' "$out"
}

# The single output line beginning with the given literal prefix.
get_unique_line() {
  local label=$1
  local prefix=$2
  local lines
  mapfile -t lines < <(lines_with_prefix "$prefix")
  if [ "${#lines[@]}" -ne 1 ]; then
    fail "$label (expected one line beginning with: $prefix; found ${#lines[@]})"
  fi
  printf '%s\n' "${lines[0]}"
}

# At least one output line begins with the given literal prefix.
require_line() {
  local label=$1
  local prefix=$2
  local lines
  mapfile -t lines < <(lines_with_prefix "$prefix")
  if [ "${#lines[@]}" -eq 0 ]; then
    fail "$label (expected a line beginning with: $prefix; found none)"
  fi
}

# No output line begins with the given literal prefix.
forbid_line() {
  local label=$1
  local prefix=$2
  local lines
  mapfile -t lines < <(lines_with_prefix "$prefix")
  if [ "${#lines[@]}" -ne 0 ]; then
    fail "$label (expected no line beginning with: $prefix; found ${#lines[@]})"
  fi
}

# The generated binder names of one quantifier, in order of occurrence.
parse_binders() {
  local label=$1
  local text=$2
  local quantifier=$3
  local expected=$4
  local result_name=$5
  local pattern
  local -n result=$result_name

  case "$quantifier" in
    universal) pattern='!\[[^ ]+ : \$Any\]' ;;
    existential) pattern='\?\[[^ ]+ : \$Any\]' ;;
    *) fail "$label (unknown binder quantifier: $quantifier)" ;;
  esac
  mapfile -t result < <(
    printf '%s\n' "$text" |
      grep -Eo -- "$pattern" |
      sed -E 's/^[!?]\[([^ ]+) : \$Any\]$/\1/'
  )
  if [ "${#result[@]}" -ne "$expected" ]; then
    fail "$label (expected $expected $quantifier binders; found ${#result[@]})"
  fi
}

require_text() {
  local label=$1
  local text=$2
  local needle=$3
  if [[ "$text" != *"$needle"* ]]; then
    fail "$label (missing fixed text: $needle)"
  fi
}

forbid_text() {
  local label=$1
  local text=$2
  local needle=$3
  if [[ "$text" == *"$needle"* ]]; then
    fail "$label (unexpected fixed text: $needle)"
  fi
}

require_text_count_exact() {
  local label=$1
  local text=$2
  local needle=$3
  local expected=$4
  local count
  count=$(printf '%s\n' "$text" | { grep -Fo -- "$needle" || true; } | wc -l)
  if [ "$count" -ne "$expected" ]; then
    fail "$label (expected $expected occurrences of $needle; found $count)"
  fi
}
