#!/usr/bin/env bash
#
# publish-opam.sh <opam-version>
#
#   <opam-version>   a published CoqHammer opam version, i.e. <CVER>+<ROCQ>
#                    e.g. 1.3.2+9.1  (must match a pushed GitHub tag v<...>).
#
# Adds coq-hammer and coq-hammer-tactics opam packages for the given release
# to a local checkout of the fork
#
#     git@github.com:lukaszcz/opam-coq-archive.git
#
# on a fresh branch. The fork's master is first synced with upstream
# (coq/opam-coq-archive). Each new opam file is derived from the most recent
# existing entry of the same package by updating exactly four things:
#
#   * the Rocq/Coq dependency            (rocq-core/rocq-runtime >= <ROCQ> &
#                                         rocq-stdlib >= <ROCQ-or-newest-published>
#                                         for Rocq >= 9.0, or legacy coq for older
#                                         branches, all < <next>~)
#   * the "date:" tag                    (today)
#   * the release tarball URL            (.../tags/v<CVER>+<ROCQ>.tar.gz)
#   * the sha512 checksum                (computed from that tarball)
#
# The branch is pushed to the fork. No pull request is opened.
#
# Env:
#   OPAM_ARCHIVE_DIR   where to keep the fork checkout
#                      (default: $HOME/.cache/coqhammer/opam-coq-archive)
#   OPAM_PUSH=0        do everything locally, do not push the branch

set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/release-lib.sh"

VERSTR="${1:-}"
[ -n "$VERSTR" ] || die "usage: publish-opam.sh <CVER>+<ROCQ>   (e.g. 1.3.2+9.1)"
case "$VERSTR" in
  *+*) ;;
  *) die "version must be of the form <CVER>+<ROCQ>, e.g. 1.3.2+9.1" ;;
esac
CVER="${VERSTR%%+*}"
ROCQ="${VERSTR##*+}"
ROCQ_NEXT="$(next_rocq "$ROCQ")"
ROCQ_MAJOR="${ROCQ%%.*}"
TAG="v${VERSTR}"
TODAY="$(date +%F)"

# Lower bound for the rocq-stdlib dependency on Rocq >= 9.0: normally <ROCQ>,
# but rocq-stdlib usually lags rocq-core on opam. Older Coq releases keep the
# legacy `coq` dependency and do not mention the split Rocq packages.
STDLIB_LB="$ROCQ"
if [ "$ROCQ_MAJOR" -ge 9 ] 2>/dev/null && command -v opam >/dev/null 2>&1; then
  _stdlib_all="$(opam show rocq-stdlib -f all-versions 2>/dev/null | tr ' ,' '\n\n' | grep -E '^[0-9]' || true)"
  if ! printf '%s\n' "$_stdlib_all" | grep -qE "^${ROCQ//./\\.}(\.|$)"; then
    _stdlib_newest="$(printf '%s\n' "$_stdlib_all" | sort -V | tail -1)"
    [ -n "$_stdlib_newest" ] && STDLIB_LB="$(printf '%s\n' "$_stdlib_newest" | grep -oE '^[0-9]+\.[0-9]+')"
  fi
fi
ARCHIVE_DIR="${OPAM_ARCHIVE_DIR:-$HOME/.cache/coqhammer/opam-coq-archive}"
BRANCH="release-coq-hammer-${VERSTR}"

command -v git >/dev/null || die "git is required"
command -v curl >/dev/null || die "curl is required"
command -v sha512sum >/dev/null || die "sha512sum is required"

# --- Obtain / sync the fork ------------------------------------------------
if [ ! -d "$ARCHIVE_DIR/.git" ]; then
  info "cloning fork into $ARCHIVE_DIR"
  mkdir -p "$(dirname "$ARCHIVE_DIR")"
  git clone "$OPAM_FORK_URL" "$ARCHIVE_DIR"
fi
cd "$ARCHIVE_DIR"

git remote get-url upstream >/dev/null 2>&1 || git remote add upstream "$OPAM_UPSTREAM_URL"

info "syncing fork master with upstream"
git fetch -q upstream
git fetch -q origin
git checkout -q master 2>/dev/null || git checkout -q -b master origin/master
git reset --hard upstream/master
if [ "${OPAM_PUSH:-1}" = 1 ]; then
  git push -q --force-with-lease origin master
fi

git show-ref --verify --quiet "refs/heads/$BRANCH" && git branch -q -D "$BRANCH"
info "creating branch $BRANCH"
git checkout -q -b "$BRANCH"

# --- Compute the tarball checksum ------------------------------------------
TARBALL_URL="https://github.com/${GH_REPO}/archive/refs/tags/${TAG}.tar.gz"
info "downloading $TARBALL_URL"
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
curl -fsSL "$TARBALL_URL" -o "$tmp" || die "could not download $TARBALL_URL (is the tag pushed?)"
SHA512="$(sha512sum "$tmp" | cut -d' ' -f1)"
info "sha512 = $SHA512"

# --- Create the two package entries ----------------------------------------
add_package() {
  local pkg="$1"
  local dir="released/packages/$pkg"
  local newdir="$dir/$pkg.$VERSTR"
  local template

  # Prefer the most recent entry of the same CoqHammer version; otherwise the
  # most recent entry of the package overall.
  template="$(ls -d "$dir/$pkg.$CVER+"* 2>/dev/null | sort -V | tail -1 || true)"
  [ -n "$template" ] || template="$(ls -d "$dir/$pkg."* 2>/dev/null | sort -V | tail -1 || true)"
  [ -n "$template" ] || die "no existing $pkg entry to use as a template"

  [ -e "$newdir" ] && die "$newdir already exists"
  info "$pkg: templating from $(basename "$template")"
  mkdir -p "$newdir"
  cp "$template/opam" "$newdir/opam"

  # Replace whatever Rocq/Coq dependency line(s) the template carries -- an old
  # entry's single "coq" line or a newer entry's "rocq-core"/"rocq-runtime"/
  # "rocq-stdlib" form -- with the canonical dependency block for this release.
  # Rocq >= 9 uses the split packages; older Coq branches keep `coq`.
  # (`nxt`, not `next`, since `next` is an awk statement.)
  awk -v v="$ROCQ" -v nxt="$ROCQ_NEXT" -v slb="$STDLIB_LB" -v major="$ROCQ_MAJOR" '
    /^[[:space:]]*"(rocq-core|rocq-runtime|rocq-stdlib|coq)"[[:space:]]*[{]/ {
      if (!done) {
        if (major >= 9) {
          print "  \"rocq-core\" {>= \"" v "\" & < \"" nxt "~\"}"
          print "  \"rocq-runtime\" {>= \"" v "\" & < \"" nxt "~\"}"
          print "  \"rocq-stdlib\" {>= \"" slb "\" & < \"" nxt "~\"}"
        } else {
          print "  \"coq\" {>= \"" v "\" & < \"" nxt "~\"}"
        }
        done = 1
      }
      next
    }
    { print }
  ' "$newdir/opam" > "$newdir/opam.pub" && mv "$newdir/opam.pub" "$newdir/opam"

  sed -i \
    -e "s|\"date:[0-9-]*\"|\"date:${TODAY}\"|" \
    -e "s|archive/refs/tags/v[^\"]*|archive/refs/tags/${TAG}.tar.gz|" \
    -e "s|checksum: \"sha512=[0-9a-fA-F]*\"|checksum: \"sha512=${SHA512}\"|" \
    "$newdir/opam"

  git add "$newdir/opam"
}

add_package coq-hammer
add_package coq-hammer-tactics

git commit -q -m "Add coq-hammer(-tactics) ${VERSTR}"

if [ "${OPAM_PUSH:-1}" = 1 ]; then
  info "pushing branch $BRANCH to fork"
  git push -q -u origin "$BRANCH"
  info "done. Branch pushed to the fork; open a PR to coq/opam-coq-archive manually."
else
  info "done. Branch $BRANCH created locally in $ARCHIVE_DIR (not pushed)."
fi
