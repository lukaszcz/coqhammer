#!/usr/bin/env bash
#
# sync-merge-driver.sh %O %A %B %L %P
#
# Custom git merge driver used by `just sync` (see sync-branch.sh).
#
# It is registered locally (in .git/config + .git/info/attributes) for every
# file in the merge. Its job is to make the *trivial* per-branch differences --
# the Rocq-version-flavored tokens that identify which Rocq a CoqHammer branch
# targets -- disappear from the 3-way merge so that only genuine changes remain
# (and genuinely conflict).
#
# git invokes a merge driver with:
#   %O  path to a temp file holding the merge-base version
#   %A  path to a temp file holding *our* version -- the branch being merged
#       INTO (the branch you are on) -- also the output file
#   %B  path to a temp file holding *their* version -- the branch being merged
#   %L  conflict marker size
#   %P  the real pathname of the file being merged
#
# The driver is direction-agnostic: for each token class it reads the value
# from OUR side (%A, the current branch) and rewrites the base (%O) and theirs
# (%B) to that same value before handing off to `git merge-file`. Because the
# flavored tokens then match on all three sides they never conflict, while real
# edits to those same lines still merge cleanly. Rewriting base and theirs by
# the same rule is what makes this safe on files whose version numbers are not
# flavor at all (CHANGES.md): the two rewrites cancel out and OUR line survives.
# The token classes themselves live in sync-tokens.sh, shared with the
# post-merge pass in sync-branch.sh. Every rule derives its value from the file
# being merged and is a no-op on files that lack the token, so the driver is
# safe to attach to all files. The exit status of `git merge-file` (0 = clean,
# >0 = number of conflicts) is propagated so real conflicts still surface for
# manual resolution.

set -euo pipefail

O="$1"; A="$2"; B="$3"; L="${4:-7}"; P="${5:-}"

# shellcheck source=scripts/sync-tokens.sh
source "$(dirname "${BASH_SOURCE[0]}")/sync-tokens.sh"

# Sentinel that stands in for the standalone prover-name word ("Coq"/"Rocq")
# while merging Markdown; see rule 9. Chosen so it cannot occur in real text.
CQ_SENTINEL='@@RocqOrCoq@@'

# OUR side's prevailing prover word, used only to turn back any sentinel that
# survives into genuinely-new text taken from theirs (computed below).
ADOMWORD='Rocq'

do_merge() {
  set +e
  git merge-file --marker-size="$L" "$A" "$O" "$B"
  local rc=$?
  # Restore any sentinel that reached the output (only possible on lines that
  # came verbatim from theirs, or inside an unresolved conflict) to OUR word.
  [ "$SYNC_DOC" = 1 ] && sed -i "s/$CQ_SENTINEL/$ADOMWORD/g" "$A"
  exit $rc
}

# Never run text substitutions on binary content (a file is binary if stripping
# NUL bytes changes it). SYNC_DOC is still 0 here, so do_merge leaves it alone.
is_binary() { ! LC_ALL=C tr -d '\000' < "$1" | cmp -s - "$1"; }
if is_binary "$A" || is_binary "$B" || is_binary "$O"; then
  do_merge
fi

# ---- derive OUR (%A) value for each token class ---------------------------

sync_tokens_read "$A" "$P"

# OUR prevailing prover word: whichever of the standalone words dominates on our
# side (a branch may mix both -- "Rocq master" alongside "versions of Coq").
# Either count may legitimately be zero, so absorb grep's no-match status: under
# `pipefail` it would otherwise fail the assignment and `set -e` would abort the
# driver before it merges anything, which git reports as a marker-less conflict.
if [ "$SYNC_DOC" = 1 ]; then
  arocq="$( { grep -oE '\bRocq\b' "$A" || true; } | wc -l)"
  acoq="$( { grep -oE '\bCoq\b' "$A" || true; } | wc -l)"
  [ "$acoq" -gt "$arocq" ] && ADOMWORD='Coq' || ADOMWORD='Rocq'
fi

# Rewrite $1 in place to match the values read from OUR side.
normalize() {
  sync_tokens_apply "$1"
  #   9. prose prover name (Markdown only): the standalone words "Coq" and
  #      "Rocq" -- e.g. "other versions of Coq" vs "... of Rocq". Both sides
  #      collapse to one sentinel so this file (base/theirs) matches regardless
  #      of which word it used; OUR side is left untouched, so lines that differ
  #      only in this word resolve to OUR wording. Runs last so the earlier,
  #      more specific rules still see the real words. "CoqHammer"/"coqc"/... are
  #      untouched (no word boundary / lowercase).
  [ "$SYNC_DOC" = 1 ] && sed -i -E "s/\b(Coq|Rocq)\b/$CQ_SENTINEL/g" "$1"
  return 0  # never let an unmatched trailing guard trip `set -e` in the caller
}

normalize "$O"
normalize "$B"

# git merge-file writes the merged result into %A in place and exits with the
# number of remaining conflicts; propagate that as our status.
do_merge
