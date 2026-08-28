# CoqHammer evaluation

This directory evaluates the current CoqHammer checkout. The main entry point
is `evaluate.sh`; it builds the source tree containing `eval/` and installs it
in `eval/_installs/current` before running an evaluation.

## Quick start

Run all commands from this directory. `N` is the number of parallel jobs.

```bash
# Smoke test one committed corpus
./evaluate.sh sample --corpus stdlib-regression -j N

# Evaluate a prepared library in problems/
./evaluate.sh library N [your.mail@mail.com]

# Explore extraction configurations
./evaluate.sh screening -j 4 --tim 5

# Run the complete extraction evaluation for the current configuration
./evaluate.sh confirmation -j 4 --tim 10
```

Use `./evaluate.sh --help` for the unified interface. The screening and
confirmation modes also accept the options printed by their individual help
commands. They create resumable checkpoints under `results/` and write
summaries and provenance under `artifacts/` after a complete run.

The confirmation grid runs all seven full corpora (`stdlib-regression`,
`dependent-stdlib`, `stdpp`, `color-vector`, `dependent-slice`,
`equations-examples`, `external-equations`); run `./install-external-libs.sh`
first to install the libraries and build the Coq-Equations checkout that some
of them need.

The standard evaluation uses the prepared source files in `problems/`. The
full extraction confirmation evaluates seven corpora:

- `stdlib-regression`: built from the installed Rocq standard library. The
  installed library ships a `.glob` beside every `.v`, which is all `coqnames`
  needs to place the `hammer_hook` calls, so this needs no stdlib rebuild.
  The default slice is `Arith Bool Vectors Lists NArith`, about 1200 goals
  across 40 files; change it with `--stdlib-modules` or `STDLIB_CORPUS_MODULES`;
- `dependent-stdlib`: dependent modules from the installed Rocq standard
  library;
- `stdpp`: built from the installed `rocq-stdpp` library;
- `color-vector`: built from the installed CoLoR vector modules;
- `dependent-slice`: committed dependent elimination, finite map, and
  well-founded recursion fixtures;
- `equations-examples`: built from the configured Coq-Equations checkout;
- `external-equations`: built from the installed `rocq-equations` library, or
  from a checkout passed with `--external-source /path/to/Coq-Equations`. See
  `corpora/external-equations/CANDIDATES.md` for how it was chosen.

The extraction screening grid intentionally uses only the three committed
sample corpora `stdlib-regression`, `dependent-slice`, and
`external-equations`; it is an option sweep, not the seven-corpus confirmation.

Generating the corpora from the installed libraries keeps them in step with the
Rocq the evaluation actually runs against, instead of committing a snapshot
that silently drifts. Pass `--sample-corpus` to use the small committed smoke
wrappers instead; those are for dry runs in minimal images, not for evidence.

Jobs default to a pool sized from the core count and capped so the concurrent
ATP processes fit in available memory. `EVAL_JOBS` pins it, and
`EVAL_MEMORY_PER_JOB_MB` / `EVAL_RESERVE_MB` tune the memory model; `-j`
overrides all of them.

## Preparing a library

If the library is not already prepared, use these steps before
`./evaluate.sh library N`:

1. Place its sources, including all `*.v` files, in `problems/`.
2. Build the helper tools:

   ```bash
   (cd tools && make)
   ```

3. Fix logical prefixes from the `problems/` directory:

   ```bash
   ../tools/fixreqs.sh prefix
   ```

   Replace `prefix` with the library's Coq logical prefix. The command updates
   `Require`, `Require Import`, and `Require Export` statements for files found
   in `problems/`.

4. Compile the library and create its `.glob` files:

   ```bash
   make -j N init
   ```

   Fix any source files that do not compile.

5. Insert `hammer_hook` calls:

   ```bash
   (cd problems && ../tools/mkhooks.sh)
   ```

   Inspect and adjust the generated sources if necessary.

6. Check the hooked files:

   ```bash
   ./check.sh N
   ```

   Errors are recorded in `check.log`.

`make clean-problems` removes generated files when the preparation needs to be
repeated. The lower-level commands used by `evaluate.sh library` are
`gen-atp.sh`, `atp/run-provers.sh`, `run-reconstr.sh`, and `gen-stats.sh`.

## Extraction configurations

`rebuild-config.sh` is an implementation helper used by the grid commands.
`current` builds exactly the option values committed in
`src/plugin/coq_transl_opts.ml`. The other names are controlled configuration
variants used to understand the current translator:

- `all-off` and `all-on`;
- `loo-erasure-guards`;
- `loo-indexed-families`.

Configuration builds restore `coq_transl_opts.ml` after installation.
Each build wipes its install prefix first, so `--prefix` is accepted only for a
dedicated install directory: outside the checkout or under `eval/_installs`,
and, if it already exists, carrying the `.coqhammer-eval-prefix` marker an
earlier `rebuild-config.sh` run wrote for that path. A prefix built before the
marker existed, or one that was moved or copied, is refused; remove it by hand
(`rm -rf PREFIX`) and rebuild it.
To inspect the available names:

```bash
./rebuild-config.sh --list
```

The screening run evaluates `current` together with these variants. The
confirmation run evaluates only `current`, including ATP generation,
reconstruction, and consistency checks across all standard premise-selector
and prover combinations.

Every complete grid writes `provenance.env` beside its summary. Checkpoints
are reused only when their source commit, installed package, configuration,
corpus content, scripts, and applicable timeout settings still match. Each
per-file Rocq phase (`init`, `check`, ATP generation, and confirmation
reconstruction) is supervised with `--compile-timeout SEC` (600 by default).
On expiry the supervisor sends TERM to the compilation process group, waits the
fixed `--compile-timeout-grace SEC` (10 by default), then sends KILL and reports
the source file and phase with exit status 124. Generation checkpoints from
before compile supervision are rejected. Regeneration retains downstream ATP
results, but reuses each only when its recorded input hash still matches the
newly generated problems.

Of everything a run produces, only the artifacts of a grid whose numbers the
branch actually claims are tracked: `summary.tsv`, `analysis.md`,
`provenance.env`, and the README beside them. The rest — `results/`,
`problems/`, `logs/`, `_external/` — is ignored. The line is not source versus
output but reproducible versus not. Checkpoints and generated problems come
back by rerunning; a summary does not, since it depends on four external ATPs,
pinned external libraries, and timeout-bound prover runs that never repeat
exactly. A summary is therefore evidence about one commit rather than build
output, and it is committed so that `provenance.env`'s `repository_commit` and
the numbers it vouches for share a single history — checkpoints are keyed by
label, so once a grid is rerun that history is the only surviving record of the
previous one.

The tracked grid artifacts are the ones cited by branch claims.
`artifacts/extraction-confirmation` carries the full-grid consistency and
reconstruction measurements. `artifacts/extraction-screening` carries the
indexed-families extraction-option sweep, and `artifacts/premise-screening`
carries the premise-selection definitional-slot sweep and its non-standard
measurement policy. `artifacts/indexed-families-comparison` is a compact,
cross-commit report derived from workspace-local baseline/candidate snapshots;
it retains their digests and common-key statistics without committing the
large attempt tables. `artifacts/indexed-families-ablation` compactly records
the two corrected option-off screening cells rerun after the
ablation-boundary fix. Screening or
comparison output not cited by the branch is rerun rather than tracked.
`summary.tsv` and `analysis.md` are marked `linguist-generated` in
`.gitattributes` so review collapses them; regenerate grid output through the
harness rather than editing it.

The confirmation run also checks that the translated axioms stay consistent: it
replaces each conjecture with `$false` and expects no refutation. Those axioms
include the goal's own hypotheses, so a vacuously true lemma is refutable no
matter how faithful the translation is — stdlib's `Nat.testbit_neg_r`, proved
by `inversion H` from `n < 0`, is one. The check therefore runs against the
curated list in `corpora/<corpus>/consistency-lemmas.txt`, whose entries are
known to have satisfiable hypotheses; the list is a sample across the corpus
modules, not an enumeration of it. A corpus with no such file is skipped with a
warning and left unchecked rather than reported as passing.

`tools/curate-consistency-lemmas.sh PROBLEM_DIR OUT` regenerates such a list
from a corpus's generated problems. It runs both provers at a longer timeout
than the check uses, so a lemma whose refutation is merely slow cannot pass
curation and then fire during a run. Use it when adding a corpus or after a
library update changes which goals exist.

## Other tools

- `diff-transl-configs.sh CONFIG_A CONFIG_B [CONSTANT]` compares translation
  output for two current-tree configurations;
- `atp/run-provers.sh` runs the configured external ATPs directly;
- `tools/stat` computes ATP statistics from the generated output.

External ATPs must be installed for screening, confirmation, and library runs.
