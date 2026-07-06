#!/usr/bin/env bash
#
# sync-branch.sh <source-branch>
#
# Merge <source-branch> into the CURRENT branch, automatically absorbing the
# recurring, mechanical per-branch differences between CoqHammer branches --
# the Rocq-version-flavored tokens in the *.opam / dune / META.* build-metadata
# files. Run it while checked out on the branch you are merging INTO.
#
#   git checkout master        # the branch that tracks unstable Rocq
#   just sync rocq-9.1         # pull the rocq-9.1 development into it
#
# (Any two branches work, in either direction: on rocq-9.1 you can likewise
# `just sync master` to pull Rocq-API updates back, keeping rocq-9.1's flavor.)
#
# It uses a direction-agnostic, token-normalizing merge driver
# (scripts/sync-merge-driver.sh) that is registered *locally* only for the
# duration of the merge: nothing is committed to any branch's tracked state,
# and unrelated merges are unaffected. `git rerere` is also enabled so that any
# genuine conflict you resolve once is reapplied automatically on the next sync.
#
# On success the merge is left committed on the current branch for you to
# review and push. If real (non-trivial) conflicts remain, the merge is left in
# progress on the current branch for you to resolve and commit by hand --
# exactly as a plain `git merge` would.

set -euo pipefail

# Self-contained on purpose: this script runs on the branch being merged INTO,
# which may not (yet) carry the rest of the scripts/ tooling, so it does not
# source release-lib.sh.
die()  { echo "error: $*" >&2; exit 1; }
info() { echo ">> $*" >&2; }
current_branch() { git rev-parse --abbrev-ref HEAD; }
require_clean_worktree() {
  git diff --quiet && git diff --cached --quiet \
    || die "working tree is dirty; commit or stash first"
}

REPO_ROOT="$(git rev-parse --show-toplevel)"
cd "$REPO_ROOT"

SOURCE="${1:-}"
[ -n "$SOURCE" ] || die "usage: sync-branch.sh <source-branch>"

git rev-parse --verify --quiet "${SOURCE}^{commit}" >/dev/null \
  || die "branch '$SOURCE' does not exist"

TARGET="$(current_branch)"
[ "$TARGET" != "HEAD" ] || die "detached HEAD; check out the target branch first"
[ "$SOURCE" != "$TARGET" ] || die "source and target are the same branch ('$TARGET')"

require_clean_worktree

GIT_DIR="$(git rev-parse --git-dir)"
INFO_ATTR="$GIT_DIR/info/attributes"
DRIVER="$REPO_ROOT/scripts/sync-merge-driver.sh"
[ -x "$DRIVER" ] || die "merge driver not executable: $DRIVER"

# ---- set up the local, temporary merge driver -----------------------------

ATTR_BACKUP=""
cleanup() {
  # Restore .git/info/attributes and drop the temporary driver config,
  # regardless of how the merge ended (clean, conflicted, or aborted).
  if [ -n "$ATTR_BACKUP" ]; then
    mv -f "$ATTR_BACKUP" "$INFO_ATTR"
  else
    rm -f "$INFO_ATTR"
  fi
  git config --unset-all merge.rocqsync.name 2>/dev/null || true
  git config --unset-all merge.rocqsync.driver 2>/dev/null || true
}
trap cleanup EXIT

if [ -e "$INFO_ATTR" ]; then
  ATTR_BACKUP="$(mktemp "${INFO_ATTR}.bak.XXXXXX")"
  cp "$INFO_ATTR" "$ATTR_BACKUP"
fi
mkdir -p "$(dirname "$INFO_ATTR")"
cat > "$INFO_ATTR" <<'ATTRS'
# Temporary: installed by scripts/sync-branch.sh, removed on exit.
# The driver derives every substitution from OUR side and is a no-op on files
# with no version tokens (and on binary files), so it is safe for all files.
* merge=rocqsync
ATTRS

git config merge.rocqsync.name   "CoqHammer version-token aware merge"
git config merge.rocqsync.driver "$DRIVER %O %A %B %L %P"

# rerere makes any genuine resolution reusable on the next sync.
git config rerere.enabled true

# ---- do the merge ---------------------------------------------------------

info "merging '$SOURCE' into current branch '$TARGET'"

set +e
git merge --no-edit -m "Merge ${SOURCE} into ${TARGET}" "$SOURCE"
MERGE_RC=$?
set -e

if [ "$MERGE_RC" -eq 0 ]; then
  info "merge completed cleanly on '$TARGET'."
  info "review it (git show / git log) and push when satisfied:"
  info "    git push origin $TARGET"
  exit 0
fi

# Non-trivial conflicts remain: leave the merge in progress on the current
# branch for the user.
echo >&2
info "the version-token differences were resolved automatically, but real"
info "conflicts remain on '$TARGET'. Resolve them, then commit the merge:"
echo >&2
git diff --name-only --diff-filter=U | sed 's/^/    /' >&2
echo >&2
info "    git add <files> && git commit --no-edit"
info "or abort with:  git merge --abort   (leaves you on '$TARGET')"
exit "$MERGE_RC"
