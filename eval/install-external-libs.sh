#!/usr/bin/env bash
# Install the external Rocq libraries the full extraction corpora depend on into
# the active opam switch, and build the Coq-Equations checkout that the
# equations-examples corpus reads.
#
# Corpora and what they need (see run-confirmation-grid.sh):
#   stdpp             -> rocq-stdpp        (installed into the switch)
#   color-vector      -> rocq-color        (installed into the switch)
#   external-equations-> rocq-equations    (installed into the switch)
#   equations-examples-> eval/_external/Coq-Equations/_build/default/examples
#
# rocq-equations is pinned to the local checkout, so one checkout serves both
# the installed library and the examples corpus.  Stdlib ships with rocq-core;
# it is not installed here.
#
# The pinned versions match eval/artifacts/extraction-confirmation/provenance.env
# (commit bf435563).  The script is idempotent: it skips a package already
# installed at the pinned version and a checkout already at the pinned commit.
#
# Usage: ./install-external-libs.sh [--dry-run]
set -euo pipefail

# --- pinned versions -------------------------------------------------------
STDPP_VERSION=1.13.0
COLOR_VERSION=1.8.6
EQUATIONS_REPO=https://github.com/mattam82/Coq-Equations.git
# v1.3.2-9.2-5-gc4e99d8 -- builds against rocq-core 9.2.
EQUATIONS_COMMIT=c4e99d8953cee0396a391fe017204bbc2af1fb88
RELEASED_REPO_NAME=rocq-released
RELEASED_REPO_URL=https://rocq-prover.org/opam/released

dry_run=false
case "${1:-}" in
  --dry-run) dry_run=true ;;
  -h|--help)
    sed -n '2,20p' "$0" | sed 's/^# \{0,1\}//'
    exit 0 ;;
  "" ) ;;
  * ) echo "Unknown option: $1" >&2; exit 2 ;;
esac

eval_dir=$(cd "$(dirname "$0")" && pwd)
checkout="$eval_dir/_external/Coq-Equations"

log() { printf '[install-external-libs] %s\n' "$*"; }
run() {
  if [ "$dry_run" = true ]; then
    printf '[dry-run] %s\n' "$*"
  else
    log "+ $*"
    "$@"
  fi
}

command -v opam >/dev/null 2>&1 || { echo "opam not found on PATH" >&2; exit 1; }
command -v git  >/dev/null 2>&1 || { echo "git not found on PATH" >&2; exit 1; }

repo_root=$(cd "$eval_dir/.." && pwd)
expected_switch="${COQHAMMER_OPAM_SWITCH:-$repo_root}"
expected_prefix="$expected_switch/_opam"

prefix=$(opam var prefix 2>/dev/null || true)
[ -n "$prefix" ] || { echo "No active opam switch (opam var prefix is empty)." >&2; exit 1; }
if ! [ "$prefix" -ef "$expected_prefix" ]; then
  echo "Active opam switch prefix ($prefix) is not the repository-local switch" >&2
  echo "($expected_prefix); refusing to install into the wrong switch." >&2
  echo "Select the repository-local switch first, e.g.:" >&2
  echo "  eval \$(opam env --switch=\"$expected_switch\" --set-switch)" >&2
  echo "(override the expected switch dir with COQHAMMER_OPAM_SWITCH)." >&2
  exit 1
fi
log "target switch prefix: $prefix"

installed_version() {
  opam list --installed --short --columns=version "$1" 2>/dev/null | head -1
}

install_pkg() {
  local pkg="$1" want="$2" have
  have=$(installed_version "$pkg")
  if [ "$have" = "$want" ]; then
    log "$pkg $want already installed; skipping"
  else
    [ -n "$have" ] && log "$pkg $have installed, want $want; reinstalling"
    run opam install -y "$pkg.$want"
  fi
}

# --- 1. released repo ------------------------------------------------------
repo_url=$(opam repo list --all 2>/dev/null | awk -v name="$RELEASED_REPO_NAME" '$1 == name { print $2 }')
if [ -z "$repo_url" ]; then
  run opam repo add "$RELEASED_REPO_NAME" "$RELEASED_REPO_URL"
elif [ "$repo_url" = "$RELEASED_REPO_URL" ]; then
  log "$RELEASED_REPO_NAME repo already attached at $RELEASED_REPO_URL"
else
  log "$RELEASED_REPO_NAME repo attached at $repo_url, want $RELEASED_REPO_URL; updating"
  run opam repo set-url "$RELEASED_REPO_NAME" "$RELEASED_REPO_URL"
fi

# --- 2. stdpp and CoLoR ----------------------------------------------------
install_pkg rocq-stdpp "$STDPP_VERSION"
install_pkg rocq-color "$COLOR_VERSION"

# --- 3. Coq-Equations checkout ---------------------------------------------
if [ -d "$checkout/.git" ]; then
  have_commit=$(git -C "$checkout" rev-parse HEAD)
  if [ "$have_commit" = "$EQUATIONS_COMMIT" ]; then
    log "Coq-Equations checkout already at $EQUATIONS_COMMIT"
  else
    log "Coq-Equations at $have_commit, want $EQUATIONS_COMMIT"
    run git -C "$checkout" fetch --tags origin
    run git -C "$checkout" checkout "$EQUATIONS_COMMIT"
  fi
else
  run mkdir -p "$eval_dir/_external"
  run git clone "$EQUATIONS_REPO" "$checkout"
  run git -C "$checkout" checkout "$EQUATIONS_COMMIT"
fi

# --- 4. install rocq-equations from the checkout ---------------------------
if [ "$(installed_version rocq-equations)" = dev ] \
   && opam pin list 2>/dev/null | grep "rocq-equations.*$checkout" >/dev/null; then
  log "rocq-equations already pinned to the checkout and installed"
else
  run opam pin add -y rocq-equations "git+file://$checkout#HEAD"
fi

# --- 5. build the examples the equations-examples corpus reads --------------
# --root . keeps dune inside the checkout: it is nested under the coqhammer
# repo, which is itself a dune project, so a bare `dune build` would ascend to
# the outer root and fail with "Don't know how to build examples".
run sh -c 'cd "$1" && opam exec -- dune build --root . examples' sh "$checkout"

log "done."
log "External corpora ready. Run the grid with:  ./evaluate.sh confirmation"
