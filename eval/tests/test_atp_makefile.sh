#!/usr/bin/env bash
set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf -- "$tmp"' EXIT HUP INT TERM

mkdir -p "$tmp/i/f/nested"
printf '%% problem\n' > "$tmp/i/f/nested/goal.p"
printf 'd_size=1 min_occ=1 median_occ=1 k=1\n' > "$tmp/i/f/nested/goal.meta"

output=$(cd "$tmp" && make -n -f "$SCRIPT_DIR/../atp/Makefile" all)

if printf '%s\n' "$output" | grep -F '.meta' >/dev/null; then
  echo "ATP Makefile passed a metadata sidecar to a prover" >&2
  exit 1
fi

for prover in eprover vampire z3_tptp cvc4; do
  if ! printf '%s\n' "$output" | grep -F "$prover" | grep -F 'i/f/nested/goal.p' >/dev/null; then
    echo "ATP Makefile did not pass the TPTP problem to $prover" >&2
    exit 1
  fi
done

echo "ATP Makefile input test passed"
