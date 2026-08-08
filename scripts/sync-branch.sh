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
# and unrelated merges are unaffected. Afterwards it re-imposes the current
# branch's own version tokens on the merge result, because git bypasses the
# driver entirely for paths it can resolve without a content merge (see
# reflavor_merge_result below). `git rerere` is also enabled so that any genuine
# conflict you resolve once is reapplied automatically on the next sync.
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

# Locate the companion merge driver next to THIS script, not via the repo root:
# `just sync` may run on a branch that has not yet received the scripts/ tooling
# (e.g. the first sync onto master), where $REPO_ROOT/scripts/ would be empty.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# shellcheck source=scripts/sync-tokens.sh
source "$SCRIPT_DIR/sync-tokens.sh"

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

# Use the COMMON git dir, not `--git-dir`: in a linked worktree the latter is
# the per-worktree gitdir (.git/worktrees/<name>), but git reads info/attributes
# only from the shared .git, so a driver mapping written to the per-worktree dir
# would be silently ignored and the merge would fall back to the default driver.
GIT_COMMON_DIR="$(cd "$(git rev-parse --git-common-dir)" && pwd)"
INFO_ATTR="$GIT_COMMON_DIR/info/attributes"
DRIVER="$SCRIPT_DIR/sync-merge-driver.sh"
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

# rerere makes any genuine resolution reusable on the next sync. It must be on
# *during* the merge to capture the conflict preimages, so enable it now, but
# remember its previous state: if the merge turns out clean there is nothing to
# record and we restore rerere to how we found it (see below). Only when real
# conflicts remain -- which you resolve by hand after this script exits, while
# rerere records the resolution -- does it need to stay on, and there we tell
# you it was enabled and how to switch it off.
RERERE_WAS="$(git config --get rerere.enabled 2>/dev/null || true)"
git config rerere.enabled true

restore_rerere() {
  # Put rerere.enabled back the way we found it (clean-merge path only).
  if [ "$RERERE_WAS" = "true" ]; then
    :                                              # was already on; leave it
  elif [ -n "$RERERE_WAS" ]; then
    git config rerere.enabled "$RERERE_WAS"        # restore an explicit value
  else
    git config --unset rerere.enabled 2>/dev/null || true   # was unset; unset
  fi
}

# ---- re-impose OUR flavor where the merge driver was bypassed -------------
#
# git runs a merge driver only where it needs a real 3-way *content* merge. A
# path whose OUR side is byte-identical to the merge base is resolved by taking
# THEIRS wholesale, and the driver never sees it -- so the source branch's
# flavored tokens arrive unnormalized. That happens in two ways:
#
#   * this branch simply never touched the file (dune, justfile, AGENTS.md, ...);
#   * there is more than one merge base, so the ort strategy first builds a
#     *virtual* merge base by merging the real ones -- through this very driver,
#     which normalizes the result to OUR flavor. The virtual base then matches
#     our side exactly, and the outer merge takes theirs wholesale. The driver's
#     own normalization is what erases the difference it needs to act on.
#
# Neither case can be fixed from inside the driver, so re-impose our tokens on
# the merge result afterwards. Only the closed SYNC_FLAVORED_PATHS list is
# touched: unlike the driver, which rewrites base and theirs by the same rule so
# the rewrites cancel, this pass is one-sided and would corrupt a file whose
# version numbers are history rather than flavor.
REFLAVORED=0
reflavor_merge_result() {
  local ours="$1" path ref merged
  ref="$(mktemp)"; merged="$(mktemp)"
  for path in "${SYNC_FLAVORED_PATHS[@]}"; do
    git cat-file -e "${ours}:${path}" 2>/dev/null || continue   # not on our side
    [ -f "$path" ] || continue
    git show "${ours}:${path}" > "$ref"
    cp -- "$path" "$merged"
    sync_tokens_read "$ref" "$path"
    sync_tokens_apply "$merged"
    cmp -s "$merged" "$path" && continue
    cp -- "$merged" "$path"
    # Leave a conflicted path unstaged: the user still has to resolve it, and
    # it is now correctly flavored on both sides of the markers.
    if [ -z "$(git ls-files -u -- "$path")" ]; then
      git add -- "$path"
    fi
    REFLAVORED=$((REFLAVORED + 1))
    info "  restored '$TARGET' version tokens in $path"
  done
  rm -f "$ref" "$merged"
}

# ---- do the merge ---------------------------------------------------------

info "merging '$SOURCE' into current branch '$TARGET'"

OURS_BEFORE="$(git rev-parse HEAD)"

# --no-ff on purpose. A sync that fast-forwards would make this branch *become*
# the source branch, flavor and all, and would leave HEAD pointing at a commit
# the source branch owns -- which the token-restoring commit below must never
# rewrite. Always recording a merge commit keeps the two branches' identities,
# and their flavors, distinct.
set +e
git merge --no-edit --no-ff -m "Merge ${SOURCE} into ${TARGET}" "$SOURCE"
MERGE_RC=$?
set -e

reflavor_merge_result "$OURS_BEFORE"

if [ "$MERGE_RC" -eq 0 ]; then
  # The merge is already committed; fold the restored tokens into it so the
  # branch is never left with the wrong flavor in its history. Amend only a
  # two-parent commit built on OUR pre-merge tip -- i.e. the merge commit this
  # run just created. Anything else belongs to another branch's history and gets
  # a follow-up commit instead of being rewritten.
  if [ "$REFLAVORED" -gt 0 ]; then
    if [ "$(git rev-parse --verify --quiet 'HEAD^1' || true)" = "$OURS_BEFORE" ] \
       && git rev-parse --verify --quiet 'HEAD^2' >/dev/null; then
      git commit --amend --no-edit --quiet
      info "amended the merge commit with the restored version tokens"
    else
      git commit --quiet -m "Restore ${TARGET} version tokens after merging ${SOURCE}"
      info "committed the restored version tokens on top of the merge"
    fi
  fi
  # Clean merge: no conflicts were recorded, so there is no reason to leave
  # rerere enabled repo-wide -- put it back the way we found it.
  restore_rerere
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
echo >&2
info "rerere will remember how you resolve these and reapply it on the next"
info "sync. Because conflicts remain it is left enabled, and (if it was not"
info "already on) it now applies to ALL merges in this repository. Switch off"
info "once you no longer want that:"
info "    git config --unset rerere.enabled       # cached resolutions kept"
info "    git rerere clear                         # also drop what it learned"
exit "$MERGE_RC"
