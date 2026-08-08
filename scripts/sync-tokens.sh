#!/usr/bin/env bash
#
# sync-tokens.sh -- the per-Rocq-version "flavor" tokens that distinguish one
# CoqHammer branch from another, and how to read and re-impose them.
#
# Sourced (never executed) by both halves of `just sync`:
#
#   * scripts/sync-merge-driver.sh cancels the tokens out of a 3-way merge, by
#     rewriting the base and their side to OUR values so only genuine changes
#     can conflict.
#   * scripts/sync-branch.sh re-imposes them on the merge result, for the paths
#     git resolved *without* ever calling the merge driver (see the comment on
#     SYNC_FLAVORED_PATHS below).
#
# Every rule derives its value from the file being merged, so the rules are
# self-scoping: build-metadata files yield the metadata tokens, README/CI files
# yield the documentation/CI tokens, and every other file yields none. A token
# class absent from the reference file yields an empty value and is a no-op.

# The files that carry branch-identity tokens: exactly the set migrate.sh
# rewrites when it flavors a freshly branched rocq-<X.Y>, plus the build
# metadata that names the Rocq runtime library. This list exists because
# re-imposing a token *one-sidedly* (as sync-branch.sh does after the merge) is
# only safe where every match really is branch identity. It must stay a closed
# list: CHANGES.md, for one, is full of version numbers that are history rather
# than flavor and must never be rewritten.
SYNC_FLAVORED_PATHS=(
  coq-hammer.opam
  coq-hammer-tactics.opam
  README.md
  .github/workflows/docker-action.yml
  src/plugin/g_hammer.mlg
  src/lib/dune
  src/plugin/dune
  src/tactics/dune
  src/plugin/META.coq-hammer
  src/tactics/META.coq-hammer-tactics
)

# Set by sync_tokens_read; consumed by sync_tokens_apply.
SYNC_DOC=0            # 1 when the path is Markdown (see rules 6, 7 and 9)
SYNC_PREFIX=''
SYNC_VER=''
SYNC_MAINT=''
SYNC_DEPS=''
SYNC_BADGE=''
SYNC_TAG=''
SYNC_LABEL=''
SYNC_URL=''
SYNC_VSTRING=''

# Matches every Rocq/Coq dependency line in an opam `depends` block.
SYNC_DEP_RE='^[[:space:]]*"(rocq-core|rocq-runtime|rocq-stdlib|coq)"[[:space:]]*[{]'

# sync_tokens_read <file> <path>: read the flavored token values from <file>, a
# copy of <path> carrying the flavor that must win.
sync_tokens_read() {
  local a="$1" path="${2:-}"

  # Rules 6, 7 and 9 rewrite prose, and are restricted to Markdown: the prover
  # name and "<Rocq|Coq> <version>" both occur in source and .v files (module
  # paths, "From Coq Require", comments citing a Rocq version) where rewriting
  # them would silently absorb -- or invent -- genuine code differences.
  SYNC_DOC=0
  case "$path" in
    *.md|*.markdown) SYNC_DOC=1 ;;
  esac

  # Build metadata (*.opam, dune, META.*):
  #   1. runtime library prefix: coq-core.* (release Rocq) vs rocq-runtime.*
  #      (unstable Rocq); only the prefix differs, the suffix is identical.
  if grep -q 'rocq-runtime' "$a"; then
    SYNC_PREFIX='rocq-runtime'
  elif grep -q 'coq-core' "$a"; then
    SYNC_PREFIX='coq-core'
  else
    SYNC_PREFIX=''
  fi
  #   2. opam version + maintainer: pure per-branch identity metadata (dev branch
  #      "<X.Y>.dev"/dev-maintainer vs release branch "<CVER>+<X.Y>"/release-
  #      maintainer), so OUR value always wins.
  SYNC_VER="$(sed -n 's/^version: "\(.*\)"/\1/p' "$a" | head -n1)"
  SYNC_MAINT="$(sed -n 's/^maintainer: "\(.*\)"/\1/p' "$a" | head -n1)"
  #   3. Rocq dependency line(s): the ported rocq-* branches carry a
  #      '"rocq-core" {...}' + '"rocq-runtime" {...}' + '"rocq-stdlib" {...}'
  #      block, master a single '"rocq-stdlib" {= "dev"}', an older branch a
  #      single '"coq" {>= ...}'; all pure per-branch metadata, so OUR whole
  #      block wins. Capture every Rocq dependency line (they are adjacent in
  #      `depends`) so the full block, not just the first line, is substituted.
  SYNC_DEPS="$(grep -E "$SYNC_DEP_RE" "$a" || true)"
  [ -n "$SYNC_DEPS" ] && SYNC_DEPS="$SYNC_DEPS"$'\n'

  # Documentation / CI (README.md, .github/workflows/*, ...):
  #   4. workflow-status badge branch:  ...badge.svg?branch=<name>
  SYNC_BADGE="$(sed -n -E 's/.*[?&]branch=([A-Za-z0-9._-]+).*/\1/p' "$a" | head -n1)"
  #   5. docker image tag:  rocq/rocq-prover:<tag>   (tag is "dev" on master)
  SYNC_TAG="$(sed -n -E 's#.*rocq/rocq-prover:([A-Za-z0-9._-]+).*#\1#p' "$a" | head -n1)"
  #   6. prose / link label:  "<Rocq|Coq> <label>" where label is "master" or
  #      "X.Y". Both spellings are matched so an old, pre-rename merge base
  #      (which still says "Coq X.Y") is normalized to OUR flavor too.
  #   7. Rocq homepage URL, coupled to the label: rocq-prover.org for a release,
  #      github.com/rocq-prover/rocq for master -- taken from "[<Rocq|Coq> ...](URL)".
  SYNC_LABEL=''
  SYNC_URL=''
  if [ "$SYNC_DOC" = 1 ]; then
    SYNC_LABEL="$(sed -n -E 's/.*\b(Rocq|Coq) (master|[0-9]+\.[0-9]+).*/\2/p' "$a" | head -n1)"
    SYNC_URL="$(sed -n -E 's#.*\[(Rocq|Coq) [^]]*\]\(([^)]*)\).*#\2#p' "$a" | head -n1)"
  fi

  # Source:
  #   8. the plugin version banner in g_hammer.mlg, e.g.
  #        let hammer_version_string = "CoqHammer (dev) for Rocq 9.1"
  #      ("Rocq 9.1" on a dev branch, "Rocq master" on master); a whole
  #      per-branch identity string, so OUR line wins verbatim.
  SYNC_VSTRING="$(sed -n -E 's/^let hammer_version_string = "(.*)"/\1/p' "$a" | head -n1)"
}

# sync_tokens_apply <file>: rewrite <file> in place so that every token class
# read by the last sync_tokens_read matches OUR value.
sync_tokens_apply() {
  local f="$1"
  [ -n "$SYNC_PREFIX" ] && sed -i -E "s/\b(coq-core|rocq-runtime)\b/$SYNC_PREFIX/g" "$f"
  [ -n "$SYNC_VER" ]    && sed -i -E "s/^version: \".*\"/version: \"$SYNC_VER\"/" "$f"
  [ -n "$SYNC_MAINT" ]  && sed -i -E "s/^maintainer: \".*\"/maintainer: \"$SYNC_MAINT\"/" "$f"
  if [ -n "$SYNC_DEPS" ]; then
    awk -v deps="$SYNC_DEPS" -v re="$SYNC_DEP_RE" '
      $0 ~ re {
        if (!seen) { printf "%s", deps; seen = 1 }
        next
      }
      { print }
    ' "$f" > "$f.sync" && mv "$f.sync" "$f"
  fi
  [ -n "$SYNC_BADGE" ] && sed -i -E "s/([?&]branch=)[A-Za-z0-9._-]+/\1$SYNC_BADGE/g" "$f"
  [ -n "$SYNC_TAG" ]   && sed -i -E "s#(rocq/rocq-prover:)[A-Za-z0-9._-]+#\1$SYNC_TAG#g" "$f"
  [ -n "$SYNC_LABEL" ] && sed -i -E "s/\b(Rocq|Coq) (master|[0-9]+\.[0-9]+)/Rocq $SYNC_LABEL/g" "$f"
  [ -n "$SYNC_URL" ]   && sed -i -E "s#(\[(Rocq|Coq) [^]]*\]\()[^)]*#\1$SYNC_URL#g" "$f"
  [ -n "$SYNC_VSTRING" ] \
    && sed -i -E "s#^(let hammer_version_string = ).*#\1\"$SYNC_VSTRING\"#" "$f"
  return 0  # never let an unmatched trailing guard trip `set -e` in the caller
}
