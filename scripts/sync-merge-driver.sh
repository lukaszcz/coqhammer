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
# edits to those same lines still merge cleanly. Every rule derives its value
# from the file being merged and is a no-op on files that lack the token, so
# the driver is safe to attach to all files. The exit status of
# `git merge-file` (0 = clean, >0 = number of conflicts) is propagated so real
# conflicts still surface for manual resolution.

set -euo pipefail

O="$1"; A="$2"; B="$3"; L="${4:-7}"; P="${5:-}"

# Sentinel that stands in for the standalone prover-name word ("Coq"/"Rocq")
# while merging Markdown; see rule 9. Chosen so it cannot occur in real text.
CQ_SENTINEL='@@RocqOrCoq@@'

# Documentation files get the prose Coq<->Rocq rule (9); left 0 for the early
# binary-file merge below, set for real once we know the file is text.
DOC=0
# OUR side's prevailing prover word, used only to turn back any sentinel that
# survives into genuinely-new text taken from theirs (computed below).
ADOMWORD='Rocq'

do_merge() {
  set +e
  git merge-file --marker-size="$L" "$A" "$O" "$B"
  local rc=$?
  # Restore any sentinel that reached the output (only possible on lines that
  # came verbatim from theirs, or inside an unresolved conflict) to OUR word.
  [ "$DOC" = 1 ] && sed -i "s/$CQ_SENTINEL/$ADOMWORD/g" "$A"
  exit $rc
}

# Never run text substitutions on binary content (a file is binary if stripping
# NUL bytes changes it).
is_binary() { ! LC_ALL=C tr -d '\000' < "$1" | cmp -s - "$1"; }
if is_binary "$A" || is_binary "$B" || is_binary "$O"; then
  do_merge
fi

# The prose Coq<->Rocq rule (9) applies to Markdown only: standalone "Coq" and
# "Rocq" pervade source and .v files (module paths, "From Coq Require", ...)
# where a blanket rewrite would silently absorb genuine code differences.
case "$P" in
  *.md|*.markdown) DOC=1 ;;
esac
# OUR prevailing prover word: whichever of the standalone words dominates on our
# side (master mixes both -- "Rocq master" but "versions of Coq").
if [ "$DOC" = 1 ]; then
  arocq="$(grep -oE '\bRocq\b' "$A" | wc -l)"
  acoq="$(grep -oE '\bCoq\b' "$A" | wc -l)"
  [ "$acoq" -gt "$arocq" ] && ADOMWORD='Coq' || ADOMWORD='Rocq'
fi

# ---- derive OUR (%A) value for each token class ---------------------------
#
# Each value is read from the file currently being merged, so the rules are
# self-scoping: build-metadata files yield the metadata tokens, README/CI
# files yield the documentation/CI tokens, and every other file yields none.

# Build metadata (*.opam, dune, META.*):
#   1. runtime library prefix: coq-core.* (release Rocq) vs rocq-runtime.*
#      (unstable Rocq); only the prefix differs, the suffix is identical.
if grep -q 'rocq-runtime' "$A"; then
  PREFIX='rocq-runtime'
elif grep -q 'coq-core' "$A"; then
  PREFIX='coq-core'
else
  PREFIX=''
fi
#   2. opam version + maintainer: pure per-branch identity metadata (dev branch
#      "<X.Y>.dev"/dev-maintainer vs release branch "<CVER>+<X.Y>"/release-
#      maintainer), so OUR value always wins.
AVER="$(sed -n 's/^version: "\(.*\)"/\1/p' "$A" | head -n1)"
AMAINT="$(sed -n 's/^maintainer: "\(.*\)"/\1/p' "$A" | head -n1)"
#   3. Rocq stdlib/core dependency line: '"coq" {>= "9.1" & < "9.2~"}' vs
#      '"rocq-stdlib" {= "dev"}'; also pure per-branch metadata, OUR line wins.
ADEP="$(grep -m1 -E '^[[:space:]]*"(rocq-stdlib|coq)"[[:space:]]*\{' "$A" || true)"

# Documentation / CI (README.md, .github/workflows/*, ...):
#   4. workflow-status badge branch:  ...badge.svg?branch=<name>
ABADGE="$(sed -n -E 's/.*[?&]branch=([A-Za-z0-9._-]+).*/\1/p' "$A" | head -n1)"
#   5. docker image tag:  rocq/rocq-prover:<tag>   (tag is "dev" on master)
ATAG="$(sed -n -E 's#.*rocq/rocq-prover:([A-Za-z0-9._-]+).*#\1#p' "$A" | head -n1)"
#   6. prose / link label:  "<Rocq|Coq> <label>" where label is "master" or
#      "X.Y". Both spellings are matched so an old, pre-rename merge base (which
#      still says "Coq X.Y") is normalized to OUR flavor too, not just theirs.
ALABEL="$(sed -n -E 's/.*\b(Rocq|Coq) (master|[0-9]+\.[0-9]+).*/\2/p' "$A" | head -n1)"
#   7. Rocq homepage URL, coupled to the label: rocq-prover.org for a release,
#      github.com/rocq-prover/rocq for master -- taken from "[<Rocq|Coq> ...](URL)"
#      (again matching the old "Coq" spelling so an old base's URL is rewritten).
AURL="$(sed -n -E 's#.*\[(Rocq|Coq) [^]]*\]\(([^)]*)\).*#\2#p' "$A" | head -n1)"

# Source:
#   8. the plugin version banner in g_hammer.mlg, e.g.
#        let hammer_version_string = "CoqHammer (dev) for Rocq 9.1"
#      ("Rocq 9.1" on a dev branch, "Coq master" on master); a whole per-branch
#      identity string, so OUR line wins verbatim.
AVSTRING="$(sed -n -E 's/^let hammer_version_string = "(.*)"/\1/p' "$A" | head -n1)"

# Rewrite $1 in place to match the values read from OUR side.
normalize() {
  local f="$1"
  [ -n "$PREFIX" ] && sed -i -E "s/\b(coq-core|rocq-runtime)\b/$PREFIX/g" "$f"
  [ -n "$AVER" ]   && sed -i -E "s/^version: \".*\"/version: \"$AVER\"/" "$f"
  [ -n "$AMAINT" ] && sed -i -E "s/^maintainer: \".*\"/maintainer: \"$AMAINT\"/" "$f"
  if [ -n "$ADEP" ]; then
    awk -v dep="$ADEP" '
      /^[[:space:]]*"(rocq-stdlib|coq)"[[:space:]]*\{/ && !seen { print dep; seen = 1; next }
      { print }
    ' "$f" > "$f.sync" && mv "$f.sync" "$f"
  fi
  [ -n "$ABADGE" ] && sed -i -E "s/([?&]branch=)[A-Za-z0-9._-]+/\1$ABADGE/g" "$f"
  [ -n "$ATAG" ]   && sed -i -E "s#(rocq/rocq-prover:)[A-Za-z0-9._-]+#\1$ATAG#g" "$f"
  [ -n "$ALABEL" ] && sed -i -E "s/\b(Rocq|Coq) (master|[0-9]+\.[0-9]+)/Rocq $ALABEL/g" "$f"
  [ -n "$AURL" ]   && sed -i -E "s#(\[(Rocq|Coq) [^]]*\]\()[^)]*#\1$AURL#g" "$f"
  [ -n "$AVSTRING" ] && sed -i -E "s#^(let hammer_version_string = ).*#\1\"$AVSTRING\"#" "$f"
  #   9. prose prover name (Markdown only): the standalone words "Coq" and
  #      "Rocq" -- e.g. "other versions of Coq" vs "... of Rocq". Both sides
  #      collapse to one sentinel so this file (base/theirs) matches regardless
  #      of which word it used; OUR side is left untouched, so lines that differ
  #      only in this word resolve to OUR wording. Runs last so the earlier,
  #      more specific rules still see the real words. "CoqHammer"/"coqc"/... are
  #      untouched (no word boundary / lowercase).
  [ "$DOC" = 1 ] && sed -i -E "s/\b(Coq|Rocq)\b/$CQ_SENTINEL/g" "$f"
  return 0  # never let an unmatched trailing guard trip `set -e` in the caller
}

normalize "$O"
normalize "$B"

# git merge-file writes the merged result into %A in place and exits with the
# number of remaining conflicts; propagate that as our status.
do_merge
