#!/usr/bin/env bash
set -euo pipefail

eval_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)
# shellcheck source=eval/cli-lib.sh
# shellcheck disable=SC1091
source "$eval_dir/cli-lib.sh"
# shellcheck source=eval/install-prefix-lib.sh
# shellcheck disable=SC1091
source "$eval_dir/install-prefix-lib.sh"

usage() {
  cat <<'USAGE'
Usage: ./rebuild-config.sh --list
       ./rebuild-config.sh CONFIG [--label LABEL] [--prefix PREFIX]

Build and install the current checkout into a switchable prefix. `current`
uses the option values in the checkout; other configurations temporarily change
src/plugin/coq_transl_opts.ml while building and restore it afterwards.

Core configs:
  current                  the current CoqHammer configuration
  dependent-types-off      opt_dependent_types=false: the translation as it was
                           before dependent types were handled
USAGE
}

config=
label=
prefix=

if [ "$#" -eq 0 ]; then
  usage >&2
  exit 2
fi

while [ "$#" -gt 0 ]; do
  case "$1" in
    --list)
      echo current
      echo dependent-types-off
      exit 0
      ;;
    --label) need_value "$@"; label="$2"; shift 2 ;;
    --prefix) need_value "$@"; prefix="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    --*) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
    *)
      if [ -n "$config" ]; then
        echo "Multiple configs supplied: $config and $1" >&2
        exit 2
      fi
      config="$1"
      shift
      ;;
  esac
done

if [ -z "$config" ]; then
  usage >&2
  exit 2
fi
if [ -z "$label" ]; then
  if [ "$config" = current ]; then
    label=current
  else
    label="config-$config"
  fi
fi
if ! eval_safe_component "$label"; then
  echo "Label must be a safe single path component: $label" >&2
  exit 2
fi

repo=$(git rev-parse --show-toplevel)
cd "$repo"

opts=src/plugin/coq_transl_opts.ml
if ! git diff --quiet -- "$opts" || ! git diff --cached --quiet -- "$opts"; then
  echo "$opts has uncommitted tracked changes; refusing to patch it" >&2
  exit 1
fi

core="$config"
patch_needed=true
if [ "$core" = current ]; then
  patch_needed=false
fi

dependent=true
case "$core" in
  current) ;;
  dependent-types-off) dependent=false ;;
  *) echo "Unknown configuration: $config" >&2; usage >&2; exit 2 ;;
esac

current_option_bool() {
  local name=$1
  local value
  value=$(sed -n "s/^let $name = \(true\|false\)$/\\1/p" "$opts")
  case "$value" in
    true|false) printf '%s\n' "$value" ;;
    *) echo "Could not read the current $name binding from $opts" >&2; exit 1 ;;
  esac
}

# The configuration boolean is explicit above.  For `current`, retain the
# tree's value while still selecting the matching post-install semantic check.
if [ "$core" = current ]; then
  dependent=$(current_option_bool opt_dependent_types)
fi

if [ -z "$prefix" ]; then
  prefix="$repo/eval/_installs/$label"
fi

require_markable_prefix() {
  if ! eval_prefix_path_is_markable "$1"; then
    echo "Install prefix contains a newline, which the ownership marker cannot record; refusing to use it" >&2
    exit 1
  fi
}

# prepare_prefix wipes the prefix with `rm -rf`, so a mistyped --prefix would
# erase the checkout or an unrelated directory.  Accept only a dedicated
# install directory: never the repository or one of its parents, inside the
# repository only under eval/_installs, and, when it already exists, only a
# directory carrying the marker a previous run wrote for that very path.
# Ownership has to be established, not read off contents the directory could
# have acquired any other way.  A manifest.env is not evidence: an unrelated
# project may ship a file of that name.  The shared marker records the path it
# was written for, so a prefix that was copied or moved stops counting as ours.
validate_prefix() {
  local p="$1"
  require_markable_prefix "$p"
  case "$p" in
    /|"${HOME:-}")
      echo "Refusing to use $p as the install prefix" >&2
      exit 1
      ;;
  esac
  if [ "$p" = "$repo" ] || [ "${repo#"$p"/}" != "$repo" ]; then
    echo "Install prefix $p is the repository or contains it; refusing to erase it" >&2
    exit 1
  fi
  if [ "${p#"$repo"/}" != "$p" ] && [ "${p#"$repo"/eval/_installs/}" = "$p" ]; then
    echo "Install prefix $p is inside the checkout but not under eval/_installs" >&2
    exit 1
  fi
  if [ -e "$p" ] && ! eval_prefix_is_owned "$p"; then
    echo "Install prefix $p exists but carries no $EVAL_PREFIX_MARKER written for it, so this script cannot establish that it created it; refusing to erase it" >&2
    echo "Prefixes built before the marker existed, and prefixes that were moved or copied, have to be removed by hand first: rm -rf $p" >&2
    exit 1
  fi
}

# Check the prefix as it was spelled first: `$(realpath ...)` reports the path
# on a line of its own, so command substitution would eat a trailing newline
# and hand validate_prefix a different, newline-free path -- one that may well
# be an owned prefix, which prepare_prefix would then erase instead of
# refusing the unusable path the caller asked for.
require_markable_prefix "$prefix"
# Resolve next: the prefix is later used from other working directories
# (-coqlib in validate_singleton_premises), so it has to be absolute.
# Resolution can reintroduce the very newline the check above ruled out -- a
# markable prefix may be a symlink to a target whose name ends in one -- so
# capture the output behind a sentinel and drop only the newline realpath
# itself terminates the path with.  Stripping with plain command substitution
# would eat the target's newline too, again yielding a different, newline-free
# path for prepare_prefix to erase.
resolved=$(realpath -m -- "$prefix" && printf x)
resolved=${resolved%x}
prefix=${resolved%$'\n'}
validate_prefix "$prefix"

restore_opts() {
  git checkout HEAD -- "$opts" >/dev/null 2>&1 || true
}
trap restore_opts EXIT INT TERM

if [ "$patch_needed" = true ]; then
python3 - "$opts" "$dependent" <<'PY'
import pathlib
import re
import sys

path = pathlib.Path(sys.argv[1])
values = {
    "opt_dependent_types": sys.argv[2],
}
text = path.read_text()
for name, value in values.items():
    text, n = re.subn(rf"^let {name} = (?:true|false)$", f"let {name} = {value}", text, flags=re.M)
    if n != 1:
        raise SystemExit(f"did not patch exactly one binding for {name} (patched {n})")
path.write_text(text)
PY
fi

prepare_prefix() {
  local p="$1"
  local coqlib
  coqlib=$(rocq c -where)
  rm -rf "$p"
  mkdir -p "$p/bin" "$p/coq/user-contrib" "$p/rocq-runtime"
  eval_prefix_write_marker "$p"
  ln -sfn "$coqlib/theories" "$p/coq/theories"
  # Borrow every installed library except Hammer, which this prefix installs
  # itself and must not shadow with the switch's copy.  Linking only Stdlib
  # left external corpora unbuildable: the external-equations corpus is built
  # from the installed Equations library and its hooked files then have to
  # resolve Require Import Equations against this prefix.
  for lib in "$coqlib"/user-contrib/*; do
    [ -e "$lib" ] || continue
    case "$(basename "$lib")" in
      Hammer) continue ;;
    esac
    ln -sfn "$lib" "$p/coq/user-contrib/$(basename "$lib")"
  done
  for f in "$(dirname "$coqlib")"/rocq-runtime/*; do
    ln -sfn "$f" "$p/rocq-runtime/$(basename "$f")"
  done
}

prepare_prefix "$prefix"
export PATH="$prefix/bin:$PATH"
export OCAMLPATH="$prefix${OCAMLPATH:+:$OCAMLPATH}"
make install \
  COQLIBINSTALL="$prefix/coq/user-contrib" \
  COQPLUGININSTALL="$prefix" \
  BINDIR="$prefix/bin/" \
  COQFLAGS="-coqlib $prefix/coq"

# What the grids measure is the installed prefix, not the checkout, and
# `make install` is incremental: a build that silently kept a stale artifact
# would still be described by a manifest written from this script's intent.
# So both configurations translate the shared singleton probe with the plugin
# that was just installed and assert what their option value implies -- the
# collapsed singleton equations when dependent types are handled, and the
# absence of every one of them when they are not.
validate_singleton_premises() (
  local tmp out
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  out="$tmp/singleton_premises.out"
  cp "$repo/tests/plugin/singleton_premises.v" \
    "$repo/tests/plugin/check-singleton-premises.sh" \
    "$repo/tests/plugin/transl-assert-lib.sh" "$tmp/"
  if ! (cd "$tmp" && rocq c -coqlib "$prefix/coq" singleton_premises.v) \
      >"$out" 2>&1; then
    cat "$out" >&2
    return 1
  fi
  if [ "$dependent" = true ]; then
    if ! bash "$tmp/check-singleton-premises.sh" "$out"; then
      cat "$out" >&2
      return 1
    fi
    return 0
  fi
  # With dependent types off, every elimination the probe defines is a match
  # on a proposition, and those are left opaque: none of the definition
  # equations the check script asserts may be emitted at all.  Anchor the
  # absence on a shape the configuration does not decide, so that an output
  # the probe never reached cannot satisfy it vacuously.
  # The dollar signs are literal parts of Hammer's generated identifiers.
  # shellcheck disable=SC2016
  if ! grep -Eq '^\$_typeof_singleton_premises\.' "$out"; then
    echo "the probe emitted no translation of its own definitions" >&2
    cat "$out" >&2
    return 1
  fi
  # shellcheck disable=SC2016
  if grep -Eq '^\$_def_(singleton_premises\.(singleton_cast|singleton_value|prop_index_value|singleton_jmeq)|Corelib\.Init\.Logic\.eq_rect):' "$out"; then
    echo "opt_dependent_types=false still emitted singleton-elimination equations" >&2
    cat "$out" >&2
    return 1
  fi
)

validate_singleton_premises

kind=configuration
if [ "$config" = current ]; then
  kind=current
fi
cat > "$prefix/manifest.env" <<MANIFEST
label=$label
kind=$kind
config=$config
commit=$(git rev-parse HEAD)
prefix=$prefix
MANIFEST
if [ "$patch_needed" = true ]; then
  cat >> "$prefix/manifest.env" <<MANIFEST
opt_dependent_types=$dependent
MANIFEST
fi
printf 'built_at=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >> "$prefix/manifest.env"

restore_opts
trap - EXIT INT TERM

if ! git diff --quiet -- "$opts"; then
  echo "Internal error: $opts was not restored" >&2
  exit 1
fi

cat <<EOF2
Configuration installed.
  label:  $label
  config: $config
  prefix: $prefix
$(if [ "$patch_needed" = true ]; then echo "Tree constants restored to the committed values."; else echo "Built from the current tree constants."; fi)
EOF2
