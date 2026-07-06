# CoqHammer release automation.
#
# See scripts/release-lib.sh for the naming conventions and
# scripts/make-release.sh / scripts/publish-opam.sh for details.
#
#   just release minor            # bump 1.3.2 -> 1.4.0 and release for the
#                                 # current branch's Rocq version
#   just release patch            # 1.3.2 -> 1.3.3
#   just release major            # 1.3.2 -> 2.0.0
#   just release-rocq             # release the current version for a new Rocq
#                                 # (check out the rocq-<X.Y> dev branch first)
#   just publish-opam 1.3.2+9.1   # publish a released version on opam (fork)
#   just migrate 9.2              # branch rocq-9.2 off the current branch and
#                                 # retarget its version strings / opam files

_default:
    @just --list

# Install both packages, then run the quick smoke-test suite.
check:
    make install
    make quicktest

# Bump the CoqHammer version (patch|minor|major) and publish a GitHub release.
release level:
    ./scripts/make-release.sh {{level}}

# Release the current CoqHammer version for the currently checked-out Rocq
# dev branch (porting an existing release to a new Rocq). Scans the new
# commits and asks you to confirm they are trivial before proceeding.
# Pass "--trivial" to skip the confirmation.
release-rocq *args:
    ./scripts/make-release.sh none {{args}}

# Add opam packages for a published release to the opam-coq-archive fork.
publish-opam version:
    ./scripts/publish-opam.sh {{version}}

# Merge <source> into the CURRENT branch, automatically absorbing the trivial
# per-branch version-token differences in the *.opam / dune / META.* files.
# Run it on the branch you are merging INTO; any real conflicts are left in
# progress on it for you to resolve and commit. E.g. on `master` (which tracks
# unstable Rocq): `just sync rocq-9.1`.
sync source:
    ./scripts/sync-branch.sh {{source}}

# Migrate the project to a new Rocq version. Run it on the branch to migrate
# FROM (typically `master`): creates a new local branch `rocq-<VERSION>`,
# rewrites the per-Rocq version strings and *.opam files on it, and -- when the
# AGM project config tree is present -- adds a `config/rocq-<VERSION>` workspace
# config selecting the toolchain (opam package, or a from-source build when the
# version is not yet on opam). Branch only: no worktree is created and no build
# is run; review and push the branch (and the config commit) yourself.
# E.g. on master:  just migrate 9.2
migrate version:
    ./scripts/migrate.sh {{version}}
