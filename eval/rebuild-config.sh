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
  all-off                  all extraction constants off
  all-on                   all extraction constants on, decl-level skips off
  loo-prop-case-erasure    all-on except opt_prop_case_erasure=false
  loo-erasure-guards       all-on except opt_erasure_guards=false
  loo-refinement-types     all-on except opt_refinement_types=false
  loo-indexed-families     all-on except opt_indexed_families=false
  loo-rigid-clash-pruning  all-on except opt_rigid_clash_pruning=false

Decl-skip variants:
  append -decl-skips to any core config other than `current` to set
  opt_refinement_decl_skips=true.  `current` already builds with
  declaration-level skips enabled, so `current-decl-skips` is rejected.
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
      for base in all-off all-on loo-prop-case-erasure loo-erasure-guards loo-refinement-types loo-indexed-families loo-rigid-clash-pruning; do
        echo "$base"
        echo "$base-decl-skips"
      done
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
decl_skips=false
patch_needed=true
if [ "$core" = current ]; then
  patch_needed=false
fi
case "$core" in
  *-decl-skips)
    decl_skips=true
    core=${core%-decl-skips}
    ;;
esac

# current-decl-skips cannot be built correctly: patching only decl_skips would
# still fall back to the generic prop/erasure/refinement defaults below,
# silently overriding whatever the tree's current constants actually are
# (right now opt_erasure_guards=false, so this would build all-on-decl-skips
# mislabeled as current-decl-skips). opt_refinement_decl_skips already
# defaults to true in src/plugin/coq_transl_opts.ml, so `current` alone
# already has declaration-level skips enabled and the suffix is redundant.
if [ "$core" = current ] && [ "$decl_skips" = true ]; then
  echo "current-decl-skips is not a supported configuration: declaration-level skips are already enabled by default in the current tree (opt_refinement_decl_skips); use 'current' instead." >&2
  exit 2
fi

prop=true
erasure=true
refinement=true
indexed=true
pruning=true
case "$core" in
  current) ;;
  all-off) prop=false; erasure=false; refinement=false; indexed=false; pruning=false ;;
  all-on) ;;
  loo-prop-case-erasure) prop=false ;;
  loo-erasure-guards) erasure=false ;;
  loo-refinement-types) refinement=false ;;
  loo-indexed-families) indexed=false ;;
  loo-rigid-clash-pruning) pruning=false ;;
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

# Core configuration booleans are explicit above.  For `current`, retain the
# tree's values while still selecting the matching post-install semantic check.
if [ "$core" = current ]; then
  prop=$(current_option_bool opt_prop_case_erasure)
  erasure=$(current_option_bool opt_erasure_guards)
  indexed=$(current_option_bool opt_indexed_families)
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
# (-coqlib in validate_prop_case_ablation), so it has to be absolute.
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
python3 - "$opts" "$prop" "$erasure" "$refinement" "$indexed" "$pruning" "$decl_skips" <<'PY'
import pathlib
import re
import sys

path = pathlib.Path(sys.argv[1])
values = {
    "opt_prop_case_erasure": sys.argv[2],
    "opt_erasure_guards": sys.argv[3],
    "opt_refinement_types": sys.argv[4],
    "opt_indexed_families": sys.argv[5],
    "opt_rigid_clash_pruning": sys.argv[6],
    "opt_refinement_decl_skips": sys.argv[7],
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

validate_prop_case_ablation() {
  local tmp out
  tmp=$(mktemp -d)
  out="$tmp/prop-case-ablation.out"
  cat > "$tmp/prop_case_ablation.v" <<'EOF'
From Hammer Require Import Hammer.
Definition prop_case_ablation (n : nat) : Prop :=
  match n with O => True | S _ => False end.
Hammer_transl "prop_case_ablation".
EOF
  if ! (cd "$tmp" && rocq c -coqlib "$prefix/coq" prop_case_ablation.v) >"$out" 2>&1; then
    cat "$out" >&2
    rm -rf "$tmp"
    return 1
  fi
  # The dollar signs are literal parts of Hammer's generated identifiers.
  # shellcheck disable=SC2016
  if grep -Eq '^\$_def_.*prop_case_ablation\$(lower|upper):' "$out"; then
    echo "opt_prop_case_erasure=false still emitted proposition-case bounds" >&2
    cat "$out" >&2
    rm -rf "$tmp"
    return 1
  fi
  rm -rf "$tmp"
}

if [ "$prop" = false ]; then
  validate_prop_case_ablation
fi

validate_singleton_premises() (
  local tmp out mode
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  out="$tmp/singleton_premises.out"
  cp "$repo/tests/plugin/singleton_premises.v" \
    "$repo/tests/plugin/check-singleton-premises.sh" "$tmp/"
  if ! (cd "$tmp" && rocq c -coqlib "$prefix/coq" singleton_premises.v) \
      >"$out" 2>&1; then
    cat "$out" >&2
    return 1
  fi
  if [ "$erasure" = false ]; then
    mode=guards-off
  elif [ "$indexed" = false ]; then
    mode=guards-legacy
  else
    mode=guards-indexed
  fi
  if ! bash "$tmp/check-singleton-premises.sh" "$mode" "$out"; then
    cat "$out" >&2
    return 1
  fi
)

if [ "$prop" = true ]; then
  validate_singleton_premises
fi

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
opt_prop_case_erasure=$prop
opt_erasure_guards=$erasure
opt_refinement_types=$refinement
opt_indexed_families=$indexed
opt_rigid_clash_pruning=$pruning
opt_refinement_decl_skips=$decl_skips
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
