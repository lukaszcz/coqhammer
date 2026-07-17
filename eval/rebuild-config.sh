#!/usr/bin/env bash
set -euo pipefail

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
  loo-wf-recursion-eqs     all-on except opt_wf_recursion_eqs=false

Decl-skip variants:
  append -decl-skips to any core config to set opt_refinement_decl_skips=true.
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
      for base in all-off all-on loo-prop-case-erasure loo-erasure-guards loo-refinement-types loo-wf-recursion-eqs; do
        echo "$base"
        echo "$base-decl-skips"
      done
      exit 0
      ;;
    --label) label="$2"; shift 2 ;;
    --prefix) prefix="$2"; shift 2 ;;
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

prop=true
erasure=true
refinement=true
wf=true
case "$core" in
  current) ;;
  all-off) prop=false; erasure=false; refinement=false; wf=false ;;
  all-on) ;;
  loo-prop-case-erasure) prop=false ;;
  loo-erasure-guards) erasure=false ;;
  loo-refinement-types) refinement=false ;;
  loo-wf-recursion-eqs) wf=false ;;
  *) echo "Unknown configuration: $config" >&2; usage >&2; exit 2 ;;
esac

if [ -z "$prefix" ]; then
  prefix="$repo/eval/_installs/$label"
fi

restore_opts() {
  git checkout HEAD -- "$opts" >/dev/null 2>&1 || true
}
trap restore_opts EXIT INT TERM

if [ "$patch_needed" = true ]; then
python3 - "$opts" "$prop" "$erasure" "$refinement" "$decl_skips" "$wf" <<'PY'
import pathlib
import re
import sys

path = pathlib.Path(sys.argv[1])
values = {
    "opt_prop_case_erasure": sys.argv[2],
    "opt_erasure_guards": sys.argv[3],
    "opt_refinement_types": sys.argv[4],
    "opt_refinement_decl_skips": sys.argv[5],
    "opt_wf_recursion_eqs": sys.argv[6],
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
  ln -sfn "$coqlib/theories" "$p/coq/theories"
  ln -sfn "$coqlib/user-contrib/Stdlib" "$p/coq/user-contrib/Stdlib"
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
opt_refinement_decl_skips=$decl_skips
opt_wf_recursion_eqs=$wf
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
