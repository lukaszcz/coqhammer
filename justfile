# CoqHammer release automation.
#
# See scripts/release-lib.sh for the naming conventions and
# scripts/make-release.sh / scripts/publish-opam.sh for details.
#
#   just release minor            # bump 1.3.2 -> 1.4.0 and release for the
#                                 # current branch's Rocq version
#   just release patch            # 1.3.2 -> 1.3.3
#   just release major            # 1.3.2 -> 2.0.0
#   just release none             # release the current version unchanged for a
#                                 # new Rocq (check out the rocq-<X.Y> branch first)
#   just release none --trivial   # ... skipping the triviality confirmation
#   just publish-opam 1.3.2+9.1   # publish a released version on opam (fork)
#   just migrate 9.2              # branch rocq-9.2 off the current branch and
#                                 # retarget its version strings / opam files

_default:
    @just --list

# Build and install both packages, then run the quick plugin and tactics tests
# followed by the translation-shape assertions.  quicktest is the prover-free
# subset CI runs; it reaches the assertion files that prove no goal, but not
# extraction_matches, extraction_deptypes, case_prop_transl or
# extraction_transl, so a change to the translation can leave the assertions
# those four carry stale without any target here going red.  They discharge
# their goals through the ATPs, so test-extraction -- and hence `just check` as
# a whole, unlike quicktest -- needs the provers a development machine has.
check:
    make install
    make quicktest
    make test-extraction

# Run the complete plugin suite and consistency canaries once via isolated Dune.
check-extra:
    make clean
    make dune-test-plugin

# Bump the CoqHammer version (patch|minor|major, or none to keep it) and publish
# a GitHub release for this branch's Rocq. `none` ports the current release to a
# newly checked-out rocq-<X.Y> dev branch: it scans the new commits and asks you
# to confirm they are trivial before proceeding. Extra args after <level> are
# forwarded to make-release.sh (e.g. --trivial to skip that confirmation).
[doc('Cut a GitHub release (level: patch|minor|major|none); extra args forwarded')]
release level *args:
    ./scripts/make-release.sh {{level}} {{args}}

# Add opam packages for a published release to the opam-coq-archive fork.
publish-opam version:
    ./scripts/publish-opam.sh {{version}}

# Merge <source> into the CURRENT branch, automatically absorbing the trivial
# per-branch version-token differences in the *.opam / dune / META.* files.
# Run it on the branch you are merging INTO; any real conflicts are left in
# progress on it for you to resolve and commit. E.g. on `master` (which tracks
# unstable Rocq): `just sync rocq-9.1`.
[doc('Merge <source> into the current branch, absorbing per-branch version tokens')]
sync source:
    ./scripts/sync-branch.sh {{source}}

# Migrate the project to a new Rocq version. Run it on the release branch to
# migrate FROM (typically the latest stable `rocq-<X.Y>` branch, never `master`):
# creates a new local branch `rocq-<VERSION>`, rewrites the per-Rocq version
# strings and *.opam files on it, and -- when the AGM project config tree is
# present -- adds a `config/rocq-<VERSION>` workspace config selecting the
# toolchain (opam package, or a from-source build when the version is not yet on
# opam). Branch only: no worktree is created and no build is run; review and push
# the branch (and the config commit) yourself.
# E.g. on rocq-9.1:  just migrate 9.2
[doc('Branch rocq-<version> off the current branch and retarget its version tokens')]
migrate version:
    ./scripts/migrate.sh {{version}}
