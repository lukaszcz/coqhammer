#!/usr/bin/env bash
#
# sync-merge-driver.sh %O %A %B %L %P
#
# Custom git merge driver used by `just sync` (see sync-branch.sh).
#
# It is registered locally (in .git/config + .git/info/attributes) for the
# build-metadata files that carry Rocq-version-flavored tokens -- the *.opam,
# dune and META.* files. Its job is to make the *trivial* per-branch
# differences in those files disappear from the 3-way merge so that only
# genuine changes remain (and genuinely conflict).
#
# git invokes a merge driver with:
#   %O  path to a temp file holding the merge-base version
#   %A  path to a temp file holding *our* version -- the branch being merged
#       INTO (the branch you are on) -- also the output file
#   %B  path to a temp file holding *their* version -- the branch being merged
#   %L  conflict marker size
#   %P  the real pathname of the file being merged
#
# The driver is direction-agnostic: it reads the token flavor from OUR side
# (%A, the current branch) and rewrites the base (%O) and theirs (%B) to that
# same flavor before handing off to `git merge-file`. Because the flavored
# lines then match on all three sides they never conflict, while real edits to
# those same lines still merge cleanly. The exit status of `git merge-file`
# (0 = clean, >0 = number of conflicts) is propagated so real conflicts still
# surface for manual resolution.

set -euo pipefail

O="$1"; A="$2"; B="$3"; L="${4:-7}"

# ---- derive OUR (%A) flavor for each token class --------------------------

# 1. Runtime library prefix: "coq-core.*" (release Rocq) vs "rocq-runtime.*"
#    (unstable Rocq). Only the prefix differs; the suffix (.plugins.ltac,
#    .vernac, ...) is identical, so normalizing the prefix is enough.
if grep -q 'rocq-runtime' "$A"; then
  PREFIX='rocq-runtime'
elif grep -q 'coq-core' "$A"; then
  PREFIX='coq-core'
else
  PREFIX=''
fi

# 2. opam dev-version placeholder: version: "dev" vs "9.1.dev" vs "9.0.dev" ...
#    This line is pure per-branch metadata, so OUR value always wins.
AVER="$(sed -n 's/^version: "\(.*\)"/\1/p' "$A" | head -n1)"

# 3. Rocq stdlib/core dependency line: '"coq" {>= "9.1" & < "9.2~"}' vs
#    '"rocq-stdlib" {= "dev"}'. Also pure per-branch metadata; OUR line wins.
ADEP="$(grep -m1 -E '^[[:space:]]*"(rocq-stdlib|coq)"[[:space:]]*\{' "$A" || true)"

# Rewrite $1 in place to match the flavor read from OUR side.
normalize() {
  local f="$1"
  [ -n "$PREFIX" ] && sed -i -E "s/\b(coq-core|rocq-runtime)\b/$PREFIX/g" "$f"
  [ -n "$AVER" ]   && sed -i -E "s/^version: \".*\"/version: \"$AVER\"/" "$f"
  if [ -n "$ADEP" ]; then
    awk -v dep="$ADEP" '
      /^[[:space:]]*"(rocq-stdlib|coq)"[[:space:]]*\{/ && !seen { print dep; seen = 1; next }
      { print }
    ' "$f" > "$f.sync" && mv "$f.sync" "$f"
  fi
}

normalize "$O"
normalize "$B"

# git merge-file writes the merged result into %A in place and exits with the
# number of remaining conflicts; propagate that as our status.
set +e
git merge-file --marker-size="$L" "$A" "$O" "$B"
exit $?
