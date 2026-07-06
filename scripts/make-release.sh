#!/usr/bin/env bash
#
# make-release.sh <patch|minor|major|none> [--trivial]
#
# Cuts a CoqHammer release from the current development branch and
# publishes it on GitHub (branch + tag + GitHub release).
#
#   patch|minor|major   bump the CoqHammer version and release it for the
#                       current branch's Rocq version.
#   none                release the *current* CoqHammer version for the
#                       current branch's Rocq version (used when porting an
#                       existing release to a new Rocq: check out the new
#                       rocq-<X.Y> dev branch first, then run this).
#
# With `none` the script scans the commits that are new relative to the
# previous release of the same CoqHammer version and asks you to confirm
# they are trivial (Rocq-API / doc / style only). If they are not, a version
# bump is required -- re-run with patch|minor|major.
#
#   --trivial   skip the interactive triviality confirmation (assume yes).
#
# Everything after the (optional) confirmation runs unattended, including
# pushing the branch and tag and creating the GitHub release.

set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/release-lib.sh"

LEVEL="${1:-}"
[ -n "$LEVEL" ] || die "usage: make-release.sh <patch|minor|major|none> [--trivial]"
ASSUME_TRIVIAL=0
[ "${2:-}" = "--trivial" ] && ASSUME_TRIVIAL=1

cd "$REPO_ROOT"
command -v gh >/dev/null || die "the GitHub CLI 'gh' is required"
require_clean_worktree

DEV_BRANCH="$(current_branch)"
case "$DEV_BRANCH" in
  rocq-*) ;;
  *) die "not on a rocq-<X.Y> development branch (on '$DEV_BRANCH')" ;;
esac

ROCQ="$(rocq_version_from_opam)"
OLD_CVER="$(current_cver)"
CVER="$(bump_cver "$OLD_CVER" "$LEVEL")"

REL_BRANCH="v${CVER}-rocq${ROCQ}"
TAG="v${CVER}+${ROCQ}"

info "dev branch:      $DEV_BRANCH"
info "Rocq version:    $ROCQ"
info "CoqHammer:       $OLD_CVER -> $CVER  (bump: $LEVEL)"
info "release branch:  $REL_BRANCH"
info "release tag:     $TAG"

git show-ref --verify --quiet "refs/heads/$REL_BRANCH" \
  && die "branch $REL_BRANCH already exists"
git rev-parse -q --verify "refs/tags/$TAG" >/dev/null \
  && die "tag $TAG already exists"

# --- Triviality gate for the "port existing release to new Rocq" case ------
if [ "$LEVEL" = none ]; then
  # Previous release of the same CoqHammer version, on any other Rocq line.
  PREV_TAG="$(git tag --list "v${CVER}+*" | grep -vx "$TAG" | sort -V | tail -1 || true)"
  if [ -z "$PREV_TAG" ]; then
    info "no previous v${CVER}+* release found to compare against"
  else
    echo >&2
    info "changes on $DEV_BRANCH not in $PREV_TAG:"
    git --no-pager log --oneline "$PREV_TAG..HEAD" >&2 || true
    echo >&2
    git --no-pager diff --stat "$PREV_TAG..HEAD" >&2 || true
    echo >&2
  fi
  if [ "$ASSUME_TRIVIAL" -ne 1 ]; then
    read -r -p "Are these changes trivial (Rocq-port / doc / style only)? [y/N] " ans
    case "$ans" in
      y | Y | yes | YES) ;;
      *) die "non-trivial changes: a version bump is required (run: just release patch|minor|major)" ;;
    esac
  fi
fi

# --- Create the release branch and apply the deterministic edits -----------
info "creating release branch $REL_BRANCH"
git checkout -q -b "$REL_BRANCH"

for f in coq-hammer.opam coq-hammer-tactics.opam; do
  sed -i \
    -e "s|^version: \"${ROCQ}\.dev\"|version: \"${CVER}+${ROCQ}\"|" \
    -e "s|^maintainer: \".*\"|maintainer: \"${RELEASE_MAINTAINER}\"|" \
    "$f"
done

# README.md: title line + Docker CI badge branch reference.
sed -i \
  -e "1s|.*|CoqHammer ${CVER} for Rocq ${ROCQ}|" \
  -e "s|branch=rocq-${ROCQ}|branch=${REL_BRANCH}|g" \
  README.md

git add coq-hammer.opam coq-hammer-tactics.opam README.md
git commit -q -m "Release CoqHammer ${CVER} for Rocq ${ROCQ}"
git tag -a "$TAG" -m "CoqHammer ${CVER} for Rocq ${ROCQ}"

# --- Publish on GitHub -----------------------------------------------------
info "pushing $REL_BRANCH and $TAG to origin"
git push -q origin "$REL_BRANCH"
git push -q origin "refs/tags/$TAG"

notes="$(changes_section "$CVER")"
info "creating GitHub release $TAG"
if [ -n "$notes" ]; then
  gh release create "$TAG" --repo "$GH_REPO" \
    --title "CoqHammer ${CVER} for Rocq ${ROCQ}" --notes "$notes"
else
  gh release create "$TAG" --repo "$GH_REPO" \
    --title "CoqHammer ${CVER} for Rocq ${ROCQ}" --generate-notes
fi

git checkout -q "$DEV_BRANCH"

info "done. Published tag $TAG."
info "Next: publish on opam with  just publish-opam ${CVER}+${ROCQ}"
