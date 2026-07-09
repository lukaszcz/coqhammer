#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: ./build-baseline.sh [--label LABEL] [--prefix PREFIX] [--worktree DIR]

Build and install the pre-refactor baseline at
  git merge-base extraction rocq-9.2
into a switchable local prefix. Defaults:
  LABEL=baseline-merge-base
  PREFIX=eval/_installs/$LABEL
  WORKTREE=eval/_worktrees/$LABEL
USAGE
}

label=baseline-merge-base
prefix=
worktree=

while [ "$#" -gt 0 ]; do
  case "$1" in
    --label) label="$2"; shift 2 ;;
    --prefix) prefix="$2"; shift 2 ;;
    --worktree) worktree="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done

repo=$(git rev-parse --show-toplevel)
cd "$repo"

if [ -z "$prefix" ]; then
  prefix="$repo/eval/_installs/$label"
fi
if [ -z "$worktree" ]; then
  worktree="$repo/eval/_worktrees/$label"
fi

base=$(git merge-base extraction rocq-9.2)
mkdir -p "$(dirname "$worktree")" "$(dirname "$prefix")"

if [ -d "$worktree/.git" ] || [ -f "$worktree/.git" ]; then
  current=$(git -C "$worktree" rev-parse HEAD)
  if [ "$current" != "$base" ]; then
    echo "Existing worktree $worktree is at $current, expected $base" >&2
    exit 1
  fi
else
  rm -rf "$worktree"
  git worktree add --detach "$worktree" "$base"
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
make -C "$worktree" install \
  COQLIBINSTALL="$prefix/coq/user-contrib" \
  COQPLUGININSTALL="$prefix" \
  BINDIR="$prefix/bin/" \
  COQFLAGS="-coqlib $prefix/coq"

cat > "$prefix/manifest.env" <<MANIFEST
label=$label
kind=baseline
commit=$base
prefix=$prefix
worktree=$worktree
built_at=$(date -u +%Y-%m-%dT%H:%M:%SZ)
MANIFEST

cat <<EOF2
Baseline installed.
  label:  $label
  commit: $base
  prefix: $prefix
To use it:
  export PATH="$prefix/bin:\$PATH"
  export OCAMLPATH="$prefix\${OCAMLPATH:+:\$OCAMLPATH}"
  export COQFLAGS="-coqlib $prefix/coq"
EOF2
