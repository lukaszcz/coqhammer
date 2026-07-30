## Overview

CoqHammer is an automated reasoning tool for Rocq (Coq), written mostly in OCaml. It consists of two separately packaged components:

1. **coq-hammer-tactics** — the `sauto` general proof search tactic and friends (`hauto`, `qauto`, `sfirstorder`, ...). Sources: `src/lib/`, `src/tactics/`, `theories/Tactics/`.
2. **coq-hammer** — the `hammer` tool: premise selection by machine learning, translation of goals to FOL, invocation of external ATPs (Vampire, CVC4, Eprover, Z3), and proof reconstruction with `sauto`. Sources: `src/plugin/`, `theories/Plugin/`. Depends on coq-hammer-tactics being **installed**.

## Branch naming conventions

- **`master`** — the development branch that tracks the unstable upstream Rocq
  `master` branch.
- **`rocq-X.Y`** — the CoqHammer development branch targeting Rocq version
  `X.Y` (for example, `rocq-9.2`). These branches are normally created by
  migrating from `master`; they are not release branches.
- **`vX.Y.Z-rocqA.B`** — a release branch for CoqHammer version `X.Y.Z`
  targeting Rocq version `A.B` (for example, `v1.3.0-rocq9.2`). Release work
  must start from the corresponding `rocq-A.B` development branch, not from
  `master`.

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

`make install` is the expected workflow: it builds both packages and installs
them into the active workspace-local opam switch under `_opam/`. The plugin
build cannot proceed without an installed coq-hammer-tactics (see
`Makefile.coq.plugin.local`, which links against the
`coq-hammer-tactics.lib` findlib package) — hence `make` interleaves
`install-tactics` between the two builds.

Two small standalone binaries are built alongside the plugin and installed into the Rocq bin directory: `predict` (C++, machine-learning premise selection: kNN, naive Bayes, random forest — `src/predict/`) and `htimeout` (C, `src/htimeout/`).

## Workspace-local opam switch

Each AGM workspace uses its own temporary opam switch. The setup
script creates the switch when it is missing and installs the branch's OCaml,
Rocq, and CoqHammer dependencies.

By default, the switch is tied to the current checkout:

```text
COQHAMMER_OPAM_SWITCH=$REPO_DIR
opam prefix:              $REPO_DIR/_opam
```

The `_opam/` directory is ignored by Git and must remain available for normal
builds, installs, and tests.

Do not install CoqHammer into the default/global opam switch as a substitute;
the plugin and tactics packages are expected to be installed into this
workspace's `_opam` prefix.

## Tests

Tests are `.v` files compiled with the **installed** plugin (`rocq c` with no `-Q`/`-R` flags), so install before testing.

```bash
make tests             # all tests except the deprecated legacy tactics ones
make tests-plugin      # complete plugin suite and ATP consistency canaries
make tests-tactics     # complete tactics suite
make quicktest         # the fast prover-free check: unit, plugin and tactics
make test-unit         # OCaml unit tests only (no install, no ATP needed)
make test-plugin       # plugin tests needing no external ATP -- what CI runs
make test-tactics      # compile only tactics_test.v
make test-extraction   # extraction tests and ATP consistency canaries
make dune-test-plugin  # complete plugin suite via Dune
make -C tests/tactics legacy-tests   # deprecated Reconstr tactics, opt-in
just check             # install both packages and run quicktest
just check-extra       # clean, then run the complete Dune plugin suite
```

The Make test targets depend on `make install`; when running a single test file
directly, run `make install` first. The Make and Dune test commands use the
installed Rocq and CoqHammer packages from the workspace's `_opam/` switch;
they do not create a separate test installation.
`make dune-test-plugin` performs `make install` first for the same reason.

Run a single test file directly:

```bash
cd tests/plugin && rocq c bugs.v      # or basic.v, arith.v, lists.v, ...
cd tests/tactics && rocq c tactics_test.v
```

`tests/plugin/*.v` require external ATPs to be installed since they actually run `hammer`.

## Automation (`just`)

The `justfile` wraps the build/release/branch workflow. Run `just` with no
arguments to list all recipes.

Release conventions and the underlying scripts live in `scripts/` (see
`scripts/release-lib.sh` for branch/tag/version naming).

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
- Avoid code duplication. Abstract common logic into shared helper functions.
- Keep commits focused; avoid unrelated or behavior-neutral changes unless the commit is explicitly a refactor.

## Instructions

- Do not edit CHANGES.md
- NEVER run `git clean`, never remove `.agent-files` or `_opam`
- Do not include session links or coding agent attribution in commit messages
- When finished, verify with `just check`
