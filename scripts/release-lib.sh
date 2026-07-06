# shellcheck shell=bash
#
# Shared helpers for the CoqHammer release scripts.
#
# Conventions used throughout (derived from the existing tags/branches):
#
#   dev branch        rocq-<ROCQ>            e.g. rocq-9.1
#   release branch    v<CVER>-rocq<ROCQ>     e.g. v1.3.2-rocq9.1
#   release tag       v<CVER>+<ROCQ>         e.g. v1.3.2+9.1
#   opam version      <CVER>+<ROCQ>          e.g. 1.3.2+9.1
#
# where CVER is the CoqHammer version (X.Y.Z) and ROCQ is the Rocq
# major.minor version (e.g. 9.1, 8.20). On a development branch the two
# .opam files carry the placeholder version "<ROCQ>.dev".

set -euo pipefail

_release_lib_src="${BASH_SOURCE[0]:-}"
if [ -n "$_release_lib_src" ]; then
  REPO_ROOT="$(cd "$(dirname "$_release_lib_src")/.." && pwd)"
else
  REPO_ROOT="$(git rev-parse --show-toplevel)"
fi

# Maintainer used in the released .opam files (see the published
# opam-coq-archive entries and the historic release branches).
RELEASE_MAINTAINER="lukaszcz@mimuw.edu.pl"

# Upstream opam repository and the fork we publish through.
OPAM_UPSTREAM_URL="https://github.com/coq/opam-coq-archive.git"
OPAM_FORK_URL="git@github.com:lukaszcz/opam-coq-archive.git"

# GitHub repo (owner/name) that hosts the release tarballs.
GH_REPO="lukaszcz/coqhammer"

die()  { echo "error: $*" >&2; exit 1; }
info() { echo ">> $*" >&2; }

# require_clean_worktree
require_clean_worktree() {
  git -C "$REPO_ROOT" diff --quiet && git -C "$REPO_ROOT" diff --cached --quiet \
    || die "working tree is dirty; commit or stash first"
}

# current_branch
current_branch() { git -C "$REPO_ROOT" rev-parse --abbrev-ref HEAD; }

# rocq_version_from_opam
# Reads the Rocq version from the dev-branch placeholder "<ROCQ>.dev".
rocq_version_from_opam() {
  local v
  v="$(sed -n 's/^version: "\(.*\)\.dev"/\1/p' "$REPO_ROOT/coq-hammer.opam")"
  [ -n "$v" ] || die "coq-hammer.opam version is not '<rocq>.dev' -- not on a dev branch?"
  echo "$v"
}

# current_cver
# The most recent released CoqHammer version, taken from the top of
# CHANGES.md (the canonical "current version" marker).
current_cver() {
  local v
  v="$(grep -m1 -oE 'CoqHammer v\. [0-9]+(\.[0-9]+){1,2}' "$REPO_ROOT/CHANGES.md" \
        | grep -oE '[0-9]+(\.[0-9]+){1,2}')"
  [ -n "$v" ] || die "could not read current version from CHANGES.md"
  normalize_cver "$v"
}

# normalize_cver X.Y  ->  X.Y.0   (leaves X.Y.Z untouched)
normalize_cver() {
  case "$(grep -o '\.' <<<"$1" | wc -l)" in
    1) echo "$1.0" ;;
    *) echo "$1" ;;
  esac
}

# bump_cver <version> <patch|minor|major|none>
bump_cver() {
  local ver="$1" level="$2" maj min pat
  IFS=. read -r maj min pat <<<"$ver"
  case "$level" in
    major) echo "$((maj + 1)).0.0" ;;
    minor) echo "${maj}.$((min + 1)).0" ;;
    patch) echo "${maj}.${min}.$((pat + 1))" ;;
    none)  echo "$ver" ;;
    *)     die "unknown bump level: $level (expected patch|minor|major|none)" ;;
  esac
}

# next_rocq <rocq>   ->  next minor (9.1 -> 9.2, 8.20 -> 8.21)
next_rocq() {
  local maj min
  IFS=. read -r maj min <<<"$1"
  echo "${maj}.$((min + 1))"
}

# changes_section <cver>
# Prints the CHANGES.md section for the given version (empty if absent).
changes_section() {
  awk -v v="$1" '
    $0 ~ "^CoqHammer v\\. " v "([^0-9]|$)" { grab = 1; print; next }
    grab && /^CoqHammer v\. / { exit }
    grab { print }
  ' "$REPO_ROOT/CHANGES.md"
}
