#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./diff-transl-configs.sh CONFIG_A CONFIG_B [CONSTANT]

Rebuild two named configurations, capture Hammer_transl output for CONSTANT
(default: Nat.add), and store/diff the outputs under eval/results/transl-diffs/.
The source tree's committed option constants are restored after each rebuild.
USAGE
}

if [ "$#" -lt 2 ] || [ "$#" -gt 3 ]; then
  usage >&2
  exit 2
fi

config_a="$1"
config_b="$2"
constant="${3:-Nat.add}"
repo=$(git rev-parse --show-toplevel)
eval_dir="$repo/eval"
out_dir="$eval_dir/results/transl-diffs/${config_a}_vs_${config_b}"
mkdir -p "$out_dir"

capture() {
  local config="$1"
  local label="transl-$config"
  local prefix="$eval_dir/_installs/$label"
  local safe
  safe=${config//-/_}
  "$eval_dir/rebuild-config.sh" "$config" --label "$label" --prefix "$prefix"
  cat > "$out_dir/sample_$safe.v" <<V
From Hammer Require Import Hammer.
From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Vector.
Hammer_transl "$constant".
V
  PATH="$prefix/bin:$PATH" \
  OCAMLPATH="$prefix${OCAMLPATH:+:$OCAMLPATH}" \
  rocq c -coqlib "$prefix/coq" "$out_dir/sample_$safe.v" > "$out_dir/$config.out" 2>&1
}

capture "$config_a"
capture "$config_b"

if diff -u "$out_dir/$config_a.out" "$out_dir/$config_b.out" > "$out_dir/diff.patch"; then
  echo "No Hammer_transl difference for $constant between $config_a and $config_b."
else
  echo "Hammer_transl outputs differ; see $out_dir/diff.patch"
fi
