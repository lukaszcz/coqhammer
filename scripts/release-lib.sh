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
# The most recent released CoqHammer version, read from the GitHub
# releases -- the authoritative record of what has actually shipped.
# Release tags are v<CVER>+<ROCQ> (older ones v<CVER>+coq<ROCQ>); the
# CoqHammer version is the leading v<X.Y[.Z]> component, maximised over
# all Rocq lines.
current_cver() {
  local v
  v="$(gh api "repos/${GH_REPO}/releases" --paginate --jq '.[].tag_name' 2>/dev/null \
        | grep -oE '^v[0-9]+(\.[0-9]+){1,2}' | sed 's/^v//' | sort -V | tail -1)"
  [ -n "$v" ] || die "could not read the latest release version from GitHub (${GH_REPO})"
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

# rocq_core_pkg <X.Y>: the opam core/meta package name for Rocq <X.Y>. Since
# the Rocq rename (Rocq >= 9.0) it is rocq-core; the deprecated `coq`
# meta-package is used only for the older Coq (< 9.0) branches.
rocq_core_pkg() {
  [ "${1%%.*}" -ge 9 ] 2>/dev/null && echo rocq-core || echo coq
}

# opam_pkg_versions <pkg>: all released opam versions of <pkg>, one per line.
opam_pkg_versions() {
  command -v opam >/dev/null || return 1
  opam show "$1" -f all-versions 2>/dev/null | tr ' ,' '\n\n' | grep -E '^[0-9]'
}

# opam_newest_matching <pkg> <X.Y>: newest opam version of <pkg> in the <X.Y>
# line (e.g. 9.2.1 for rocq-core 9.2); empty if none.
opam_newest_matching() {
  opam_pkg_versions "$1" | grep -E "^${2//./\\.}(\.|$)" | sort -V | tail -1
}

# opam_newest <pkg>: newest opam version of <pkg> overall; empty if none.
opam_newest() {
  opam_pkg_versions "$1" | sort -V | tail -1
}

# opam_newest_below <pkg> <X.Y>: newest opam version of <pkg> whose major.minor
# line is strictly older than <X.Y> (e.g. 9.1.0 for bound 9.2); empty if none.
opam_newest_below() {
  opam_pkg_versions "$1" \
    | awk -v b="$2" '
        { split($0, ver, "."); split(b, bnd, ".")
          if (ver[1] + 0 < bnd[1] + 0 ||
              (ver[1] + 0 == bnd[1] + 0 && ver[2] + 0 < bnd[2] + 0)) print }' \
    | sort -V | tail -1
}

# stdlib_lower_bound <rocq>: lower bound for the rocq-stdlib opam-file
# dependency targeting Rocq <rocq>. Normally <rocq> itself, but rocq-stdlib
# usually lags rocq-core on opam; if <rocq> is not yet published for
# rocq-stdlib, fall back to the newest available stdlib major.minor line below
# the release's own upper bound so the constraint stays satisfiable. The bound
# matters because releases are not always made for the newest Rocq line: when a
# stdlib line >= <next-rocq> is already published, taking the newest line
# overall would emit an empty range (e.g. >= 9.3 & < 9.3~). Echoes <rocq>
# unchanged for pre-9 Coq branches (which keep the legacy `coq` dependency
# instead) or when opam is unavailable.
stdlib_lower_bound() {
  local v="$1" newest
  if [ "$(rocq_core_pkg "$v")" = "rocq-core" ] \
     && [ -z "$(opam_newest_matching rocq-stdlib "$v" || true)" ]; then
    newest="$(opam_newest_below rocq-stdlib "$(next_rocq "$v")" || true)"
    if [ -n "$newest" ]; then
      printf '%s\n' "$newest" | grep -oE '^[0-9]+\.[0-9]+'
      return 0
    fi
  fi
  echo "$v"
}

# rewrite_opam_deps <opam-file> <rocq> <next-rocq> <stdlib-lb>
# Replaces whatever Rocq/Coq dependency line(s) <opam-file> carries -- an old
# entry's single "coq" line, a dev branch's single "rocq-stdlib" line, or the
# current "rocq-core"/"rocq-runtime"/"rocq-stdlib" form -- with the canonical
# dependency block for <rocq>: the split packages (>= <rocq>, rocq-stdlib >=
# <stdlib-lb>, all < <next-rocq>~) for Rocq >= 9, or legacy `coq` for older
# Coq branches. (`nxt`, not `next`, since `next` is an awk statement.)
rewrite_opam_deps() {
  local file="$1" v="$2" nxt="$3" slb="$4" core
  core="$(rocq_core_pkg "$v")"
  awk -v v="$v" -v nxt="$nxt" -v slb="$slb" -v core="$core" '
    /^[[:space:]]*"(rocq-core|rocq-runtime|rocq-stdlib|coq)"[[:space:]]*[{]/ {
      if (!done) {
        if (core == "rocq-core") {
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
  ' "$file" > "$file.tmp" && mv "$file.tmp" "$file"
}

# changes_section <cver> <rocq>
# Prints the GitHub release notes for the given version: a plain
# "CoqHammer v. <CVER> for Rocq <ROCQ>" line followed by the bullet list
# from the "Overview of changes" subsection of that version's CHANGES.md
# entry (empty if the entry is absent). CHANGES.md is read only to source
# the release notes -- never to determine the version (that comes from the
# GitHub releases; see current_cver).
changes_section() {
  local cver="$1" rocq="$2" body
  body="$(awk -v v="$cver" '
    $0 ~ "^CoqHammer v\\. " v "([^0-9]|$)" { insec = 1; next }
    insec && /^CoqHammer v\. / { exit }
    insec && !grab && /^Overview of changes/ { getline; grab = 1; next }
    grab {
      if ($0 ~ /^(-{3,}|={3,})$/) { have = 0; exit }   # underline of the next heading
      if (have) print buf
      buf = $0; have = 1
    }
    END { if (have && buf !~ /^[[:space:]]*$/) print buf }
  ' "$REPO_ROOT/CHANGES.md")"
  [ -n "$body" ] || return 0
  printf 'CoqHammer v. %s for Rocq %s\n\n%s\n' "$cver" "$rocq" "$body"
}
