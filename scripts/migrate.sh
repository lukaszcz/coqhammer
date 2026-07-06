#!/usr/bin/env bash
#
# migrate.sh <X.Y>
#
# Migrate CoqHammer to a new Rocq version. Run it on the branch you want to
# branch FROM -- typically `master` (which tracks unstable Rocq):
#
#   git checkout master
#   just migrate 9.2
#
# It performs three local, side-effect-contained steps and NOTHING ELSE (no
# network writes, no worktrees, no `agm` invocations, no builds):
#
#   1. Creates a new local branch `rocq-<X.Y>` off the current branch, WITHOUT
#      touching the working tree (the commit is built with git plumbing, so the
#      branch you are on is left exactly as it was and no worktree is created).
#
#   2. On that branch, rewrites the per-Rocq-version tokens that distinguish a
#      `rocq-<X.Y>` development branch from `master` -- the same tokens the
#      sync merge driver (scripts/sync-merge-driver.sh) normalizes, so a later
#      `just sync` is a no-op on them:
#        * the two *.opam files: version "<X.Y>.dev" and the Rocq dependency
#          line `"coq" {>= "<X.Y>" & < "<next>~"}`;
#        * the README title line, the CI-badge branch, and the requirement
#          label + homepage URL;
#        * the docker image tag in the Docker CI workflow, plus the `rocq-*` /
#          `coq*` push triggers so the new branch is actually built by CI;
#        * the `hammer_version_string` banner in src/plugin/g_hammer.mlg.
#
#   3. If the AGM project config tree exists ($PROJ_DIR/config), adds a
#      workspace config `$PROJ_DIR/config/rocq-<X.Y>/env.sh` selecting the Rocq
#      toolchain for the new branch: the opam `coq` package when Rocq <X.Y> is
#      available on opam, otherwise a from-source build pinned to a git ref
#      resolved from the official Rocq repository (latest release tag, else the
#      version branch). The config change is committed in the config repo.
#
# Everything is local: review the new branch (and the config commit) and push
# when satisfied. To build it, open a workspace for `rocq-<X.Y>` yourself.

set -euo pipefail
source "$(dirname "${BASH_SOURCE[0]}")/release-lib.sh"

ROCQ_SOURCE_REPO="https://github.com/rocq-prover/rocq.git"
STDLIB_SOURCE_REPO="https://github.com/rocq-prover/stdlib.git"

V="${1:-}"
[ -n "$V" ] || die "usage: migrate.sh <X.Y>   (e.g. migrate.sh 9.2)"
case "$V" in
  [0-9]*.[0-9]*) ;;
  *) die "version must be of the form <X.Y>, e.g. 9.2 (got '$V')" ;;
esac
[[ "$V" =~ ^[0-9]+\.[0-9]+$ ]] || die "version must be exactly major.minor, e.g. 9.2 (got '$V')"

NEXT="$(next_rocq "$V")"          # 9.2 -> 9.3, 8.20 -> 8.21
NEW_BRANCH="rocq-${V}"
# For matching version numbers inside regexes.
VRE="${V//./\\.}"

cd "$REPO_ROOT"
command -v git >/dev/null || die "git is required"
require_clean_worktree

SOURCE="$(current_branch)"
[ "$SOURCE" != "HEAD" ] || die "detached HEAD; check out the branch to migrate FROM first"
[ "$SOURCE" != "$NEW_BRANCH" ] || die "already on '$NEW_BRANCH'"
git show-ref --verify --quiet "refs/heads/$NEW_BRANCH" \
  && die "branch '$NEW_BRANCH' already exists"

info "migrating to Rocq $V"
info "source branch:   $SOURCE"
info "new branch:      $NEW_BRANCH"

# ---------------------------------------------------------------------------
# 1. Resolve the toolchain for the new branch: opam package vs from-source.
# ---------------------------------------------------------------------------

# opam_has_rocq <X.Y>: true if the opam `coq` package has a release <X.Y>.*
opam_has_rocq() {
  command -v opam >/dev/null || return 1
  opam show coq -f all-versions 2>/dev/null \
    | tr ' ,' '\n\n' | grep -qE "^${VRE}(\.|$)"
}

# resolve_source_ref <repo-url>: print a git ref for a source build of <X.Y>,
# preferring the latest stable release tag V<X.Y>.<z>, then the version branch
# v<X.Y>, then the latest pre-release tag V<X.Y>+<...>. Non-zero if none found.
resolve_source_ref() {
  local url="$1" refs t
  refs="$(git ls-remote --heads --tags "$url" 2>/dev/null)" || return 1
  [ -n "$refs" ] || return 1
  t="$(printf '%s\n' "$refs" \
        | sed -nE "s#.*refs/tags/(V${VRE}\.[0-9]+)\$#\1#p" | sort -V | tail -1)"
  if [ -n "$t" ]; then printf '%s\n' "$t"; return 0; fi
  if printf '%s\n' "$refs" | grep -qE "refs/heads/v${VRE}\$"; then
    printf 'v%s\n' "$V"; return 0
  fi
  t="$(printf '%s\n' "$refs" \
        | sed -nE "s#.*refs/tags/(V${VRE}\+[A-Za-z0-9.]+)\$#\1#p" | sort -V | tail -1)"
  if [ -n "$t" ]; then printf '%s\n' "$t"; return 0; fi
  return 1
}

TOOLCHAIN=""        # "opam" or "source"
ROCQ_REF=""
STDLIB_REF=""
STDLIB_GUESSED=0
if opam_has_rocq; then
  TOOLCHAIN="opam"
  info "toolchain:       opam package coq.$V*"
else
  TOOLCHAIN="source"
  ROCQ_REF="$(resolve_source_ref "$ROCQ_SOURCE_REPO")" \
    || die "Rocq $V is not on opam and no matching branch/tag found on $ROCQ_SOURCE_REPO"
  # Match the stdlib ref independently (since Rocq 9.0 it is a separate repo and
  # its refs do not always mirror Rocq's, e.g. patch tags may be missing).
  if STDLIB_REF="$(resolve_source_ref "$STDLIB_SOURCE_REPO")"; then :; else
    STDLIB_REF="$ROCQ_REF"
    STDLIB_GUESSED=1
  fi
  info "toolchain:       source build, Rocq ref '$ROCQ_REF', stdlib ref '$STDLIB_REF'"
fi

# ---------------------------------------------------------------------------
# 2. Build the new branch by rewriting the version tokens, without a worktree.
#    Each file is read from $SOURCE, transformed in a temp file, hashed into a
#    blob, and staged in a scratch index; the resulting tree becomes one commit
#    whose parent is $SOURCE. The current working tree is never touched.
# ---------------------------------------------------------------------------

TMPDIR_MIG="$(mktemp -d)"
trap 'rm -rf "$TMPDIR_MIG"' EXIT
IDX="$TMPDIR_MIG/index"
export GIT_INDEX_FILE="$IDX"
git read-tree "$SOURCE"

# The transforms are flavor-agnostic: they map either the `master` flavor
# ("dev" / "Coq master" / rocq-stdlib) or an existing `rocq-<N>` flavor to the
# target Rocq <X.Y>, so migrate works from any branch.

transform_opam() {
  sed -i -E \
    -e "s#^version: \".*\"#version: \"${V}.dev\"#" \
    -e "s#^([[:space:]]*)\"(rocq-stdlib|coq)\"[[:space:]]*\{[^}]*\}#\1\"coq\" {>= \"${V}\" \& < \"${NEXT}~\"}#" \
    "$1"
}

transform_readme() {
  sed -i -E \
    -e "1s#.*#CoqHammer (dev) for Rocq ${V} (use other branches for other versions of Rocq)#" \
    -e "s#([?&]branch=)[A-Za-z0-9._-]+#\1${NEW_BRANCH}#g" \
    -e "s#\[(Rocq|Coq) [^]]*\]\([^)]*\)#[Rocq ${V}](https://rocq-prover.org/)#g" \
    "$1"
}

transform_docker() {
  sed -i -E "s#(rocq/rocq-prover:)[A-Za-z0-9._-]+#\1${V}#g" "$1"
  # Ensure the new branch (and any rocq-*/coq* branch) triggers Docker CI.
  if ! grep -qE "rocq-\*" "$1"; then
    awk '
      /^      - master$/ && !done {
        print
        print "      - " "\047rocq-*\047"
        print "      - " "\047coq*\047"
        done = 1
        next
      }
      { print }
    ' "$1" > "$1.mig" && mv "$1.mig" "$1"
  fi
}

transform_mlg() {
  sed -i -E \
    "s#^let hammer_version_string = \".*\"#let hammer_version_string = \"CoqHammer (dev) for Rocq ${V}\"#" \
    "$1"
}

# stage <path> <transform-fn>: transform $SOURCE:<path> and stage the result.
stage() {
  local path="$1" fn="$2" mode blob work
  git cat-file -e "$SOURCE:$path" 2>/dev/null \
    || { info "  skip (absent on $SOURCE): $path"; return 0; }
  work="$TMPDIR_MIG/work"
  git show "$SOURCE:$path" > "$work"
  "$fn" "$work"
  mode="$(git ls-tree "$SOURCE" -- "$path" | awk '{print $1}')"
  blob="$(git hash-object -w "$work")"
  git update-index --cacheinfo "${mode},${blob},${path}"
}

info "rewriting version tokens on $NEW_BRANCH:"
stage coq-hammer.opam                     transform_opam
stage coq-hammer-tactics.opam             transform_opam
stage README.md                           transform_readme
stage .github/workflows/docker-action.yml transform_docker
stage src/plugin/g_hammer.mlg             transform_mlg

NEW_TREE="$(git write-tree)"
SOURCE_TREE="$(git rev-parse "${SOURCE}^{tree}")"
if [ "$NEW_TREE" = "$SOURCE_TREE" ]; then
  die "no version tokens changed -- is '$SOURCE' already flavored for Rocq $V?"
fi
NEW_COMMIT="$(git commit-tree "$NEW_TREE" -p "$SOURCE" \
  -m "Set up ${NEW_BRANCH} development branch (Rocq ${V})")"
git branch "$NEW_BRANCH" "$NEW_COMMIT"
unset GIT_INDEX_FILE
info "created branch $NEW_BRANCH at $(git rev-parse --short "$NEW_COMMIT")"

# ---------------------------------------------------------------------------
# 3. Add the AGM workspace config for the new branch, if the config tree is
#    present. This lives in a separate git repo ($PROJ_DIR/config); commit the
#    new branch config there.
# ---------------------------------------------------------------------------

proj="${PROJ_DIR:-}"
if [ -z "$proj" ]; then
  # Fall back to the AGM split layout: repo/ (or worktrees/<b>/) under $proj.
  case "$REPO_ROOT" in
    */worktrees/*) proj="${REPO_ROOT%/worktrees/*}" ;;
    */repo)        proj="${REPO_ROOT%/repo}" ;;
  esac
fi
CFG_DIR="${proj:+$proj/config}"

if [ -n "$CFG_DIR" ] && [ -d "$CFG_DIR" ]; then
  branch_cfg="$CFG_DIR/$NEW_BRANCH"
  env_file="$branch_cfg/env.sh"
  mkdir -p "$branch_cfg"
  if [ "$TOOLCHAIN" = "opam" ]; then
    cat > "$env_file" <<EOF
#!/usr/bin/env bash
#
# Workspace config for the $NEW_BRANCH development branch (Rocq $V).
#
# Rocq $V is available as an opam package, so setup.sh installs it from the
# opam constraints in this branch's coq-hammer*.opam files. No version override
# is needed; the package name is pinned for clarity.

export COQHAMMER_ROCQ_PACKAGE=coq
EOF
  else
    {
      cat <<EOF
#!/usr/bin/env bash
#
# Workspace config for the $NEW_BRANCH development branch (Rocq $V).
#
# Rocq $V is not available as an opam package, so build it (and, since Rocq 9.0,
# the standard library) from source. See \$PROJ_DIR/config/README.md.

export COQHAMMER_ROCQ_SOURCE_REF=$ROCQ_REF
EOF
      if [ "$STDLIB_GUESSED" -eq 1 ]; then
        cat <<EOF
# NOTE: no matching stdlib ref was found on the stdlib repository; the Rocq ref
# is used as a best guess. If the source build fails to find the standard
# library, set COQHAMMER_STDLIB_SOURCE_REF to the correct stdlib branch/tag.
EOF
      fi
      echo "export COQHAMMER_STDLIB_SOURCE_REF=$STDLIB_REF"
    } > "$env_file"
  fi

  if git -C "$CFG_DIR" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    git -C "$CFG_DIR" add -- "$NEW_BRANCH"
    if git -C "$CFG_DIR" diff --cached --quiet -- "$NEW_BRANCH"; then
      info "config for $NEW_BRANCH already up to date in $CFG_DIR"
    else
      git -C "$CFG_DIR" commit -q -m "Add config for $NEW_BRANCH (Rocq $V)" \
        -- "$NEW_BRANCH"
      info "committed workspace config: $env_file"
    fi
  else
    info "wrote workspace config (not a git repo, left uncommitted): $env_file"
  fi
  if [ "$STDLIB_GUESSED" -eq 1 ]; then
    info "WARNING: stdlib source ref guessed as '$STDLIB_REF'; verify $env_file"
  fi
else
  info "no AGM config tree at \${PROJ_DIR}/config -- skipping workspace config"
fi

# ---------------------------------------------------------------------------

echo >&2
info "done. Review and push when satisfied:"
info "    git log -p $NEW_BRANCH -1"
info "    git push origin $NEW_BRANCH"
if [ -n "$CFG_DIR" ] && [ -d "$CFG_DIR" ]; then
  info "    git -C $CFG_DIR push"
fi
