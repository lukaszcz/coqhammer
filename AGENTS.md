## Overview

CoqHammer is an automated reasoning tool for Rocq (Coq), written mostly in OCaml. It consists of two separately packaged components:

1. **coq-hammer-tactics** — the `sauto` general proof search tactic and friends (`hauto`, `qauto`, `sfirstorder`, ...). Sources: `src/lib/`, `src/tactics/`, `theories/Tactics/`.
2. **coq-hammer** — the `hammer` tool: premise selection by machine learning, translation of goals to FOL, invocation of external ATPs (Vampire, CVC4, Eprover, Z3), and proof reconstruction with `sauto`. Sources: `src/plugin/`, `theories/Plugin/`. Depends on coq-hammer-tactics being **installed**.

Each git branch targets one Rocq/Coq version. Never branch from or merge with `master` for release work — `master` tracks unstable Rocq development.

## Build commands

Two build systems are maintained in parallel: coq_makefile (primary, via `Makefile`) and dune.

```bash
make                  # build tactics, install them, then build the plugin
make tactics          # build coq-hammer-tactics only
make plugin           # build coq-hammer plugin (requires tactics installed)
make install          # install both
make dune             # dune build of both packages
make dune-install
make clean
```

The plugin build cannot proceed without an installed coq-hammer-tactics (see `Makefile.coq.plugin.local`, which links against the `coq-hammer-tactics.lib` findlib package) — hence `make` interleaves `install-tactics` between the two builds.

Two small standalone binaries are built alongside the plugin and installed into the Rocq bin directory: `predict` (C++, machine-learning premise selection: kNN, naive Bayes, random forest — `src/predict/`) and `htimeout` (C, `src/htimeout/`).

## Tests

Tests are `.v` files compiled with the **installed** plugin (`rocq c` with no `-Q`/`-R` flags), so install before testing.

```bash
make tests            # full test suite (tests/plugin + tests/tactics)
make quicktest        # just plugin_test.vo and tactics_test.vo
make test-plugin
make test-tactics
```

Run a single test file directly:

```bash
cd tests/plugin && rocq c bugs.v      # or basic.v, arith.v, lists.v, ...
cd tests/tactics && rocq c tactics_test.v
```

`tests/plugin/*.v` require external ATPs to be installed since they actually run `hammer`.

## Automation (`just`)

The `justfile` wraps the build/release/branch workflow (run `just` with no
argument to list everything). The most useful recipes:

```bash
just check                    # install both packages + run quicktest (the
                              # verification gate; run this when finished)
just release <patch|minor|major|none> [args...]   # cut a GitHub release for
                              # this branch's Rocq; patch/minor/major bump the
                              # CoqHammer version, none keeps it (Rocq port).
                              # Extra args are forwarded to make-release.sh,
                              # e.g. just release none --trivial
just release-rocq [--trivial]   # alias for `just release none [--trivial]`
                              # (run on a newly checked-out rocq-<X.Y> branch)
just publish-opam <ver>       # add a released version to the opam-coq-archive
                              # fork, e.g. just publish-opam 1.3.2+9.1
just sync <source>            # merge <source> into the current branch,
                              # auto-absorbing the per-branch version tokens
                              # in *.opam / dune / META.* (e.g. just sync master)
just migrate <X.Y>            # branch rocq-<X.Y> off the current branch and
                              # retarget its version strings / opam files
```

Release conventions and the underlying scripts live in `scripts/` (see
`scripts/release-lib.sh` for branch/tag/version naming). Never run release work
from `master` — it tracks unstable Rocq (see Overview).

## Architecture

The `hammer` pipeline (entry point `src/plugin/hammer_main.ml`, vernacular/tactic syntax in `src/plugin/g_hammer.mlg`):

1. **Premise selection** — `features.ml` extracts features from the goal and accessible lemmas; the external `predict` binary ranks the most relevant premises.
2. **Translation** — Coq terms are converted to an intermediate `hh_term` representation (`hh_term.ml`, `coqterms.ml`, `coq_convert.ml`), then translated to untyped first-order logic (`coq_transl.ml`, driven by options in `coq_transl_opts.ml`) and emitted as TPTP (`tptp_out.ml`).
3. **ATP invocation** — `provers.ml` runs the external provers in parallel (`parallel.ml`, `timeout.ml`) and parses back the list of premises used in the found proof.
4. **Reconstruction** — the goal is re-proved inside Coq from the returned premises using `sauto`-based tactics (`src/tactics/tacbest.ml` searches over tactic/option combinations).

`sauto` itself (`src/tactics/sauto.ml`, ~1400 lines, the core of the tactics package) is a general proof search procedure for CIC, heavily configurable via `s_opts` (`sauto.mli`); option parsing from tactic syntax lives in `tacopts.ml`, and the tactic grammar in `g_hammer_tactics.mlg`.

`src/lib/` is shared OCaml infrastructure exposed as its own findlib library (`coq-hammer-tactics.lib`): `hhutils.ml` (wrappers around Rocq APIs), `hhlib.ml` (generic utilities), `hhlpo.ml` (lexicographic path order), `hammer_errors.ml`, `hhpartac.ml` (parallel tactic execution).

File conventions: `.mlg` files are Rocq grammar extensions (VERNAC/TACTIC EXTEND) preprocessed by coqpp; `.mlpack` files list the modules packed into each plugin. Adding an OCaml file requires updating both the relevant `_CoqProject.*` file and the dune setup.

`eval/` contains the benchmark harness for evaluating hammer performance on Coq libraries (see `eval/README.md`).

## Style (from CONTRIBUTING.md)

- No TABs, ever — spaces only.
- Follow the existing indentation and formatting style.
- Remove dead code instead of commenting it out.
- Keep commits focused; avoid unrelated or behavior-neutral changes unless the commit is explicitly a refactor.

## Instructions

- When finished, verify with `just check`
