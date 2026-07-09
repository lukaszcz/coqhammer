How to evaluate a new Coq library?
----------------------------------

Let `N` be the number of parallel jobs to execute. Unless otherwise
stated, execute all commands in the `eval/` directory.

Some libraries prepared for evaluation are available at
https://github.com/lukaszcz/coqhammer-eval.git. If the library to
evaluate is already prepared (according to steps 1-6 below), then put
it in the `problems/` subdirectory and do:

```bash
./run-eval.sh N [your.mail@mail.com]
```

Otherwise follow all steps below. You may find `make clean-problems`
useful when you want to redo some steps.

1. Place the library sources in the `problems/` directory (possibly
   with subdirectories). The sources should contain the `*.v` files.

2. `cd tools && make`

3. Run `tools/fixreqs.sh prefix` in the `problems/` directory to fix
   the `Require` statements. This script expects one parameter -- the
   Coq logical prefix for the library. All `Require file` (also
   `Require Import` and `Require Export`) statements for files which
   are found in the `problems/` directory are changed to `From prefix
   Require file`.

4. `make -j N init`

   This will compile the problems, creating the necessary `*.glob`
   files. If some files do not compile then you need to fix this
   manually.

5. `cd problems && ../tools/mkhooks.sh`

   This script may be used to insert calls to `hammer_hook` in the
   library source files (it requires the corresponding `*.glob` files
   to be present). Run it in the `problems/` directory. After running
   `tools/mkhooks.sh` you may need to edit some files manually to make
   them compile with `coqc`.

6. `./check.sh N`

   This checks if the problems compile with `coqc` after running
   `tools/mkhooks.sh`. It may fail for some files, which must be then
   edited manually to make them compile with `coqc`. The errors may be
   viewed in the `check.log` file.

7. `./gen-atp.sh N [your.mail@mail.com]`

   After running this command the generated ATP problems are in the
   `atp/problems/` directory.

8. `cd atp && ./run-provers.sh N [your.mail@mail.com]`

   The script `atp/run-provers.sh` should be edited when adding or
   changing the (versions of) ATP provers used in the evaluation. When
   adding new ATPs also the `hammer_hook` code in
   [`src/plugin/hammer_main.ml`](../src/plugin/hammer_main.ml) should be edited.

9. `./run-reconstr.sh N [your.mail@mail.com]`

After executing these steps, the reconstruction results are in the
`out/` directory. The ATP results are in the `atp/o/` directory.

10. `./gen-stats.sh`

   This computes the statistics (including the greedy sequence), using
   the `stat` program (see below).

Steps 7-10 may be run using the script `./run-eval.sh [-v] N [your.mail@mail.com]`.
The optional flag -v enables the verbose mode (more emails about the progress are sent).

Tools
-----

* `stat`: compute ATP statistics. Run in the `atp/` directory (or
    `eval/` with the `-r` option). Reads the `o/*/*.p` files
    (`out/*/*.out` with the `-r` option).

  Example: `tools/stat , y,p , , false`

Extraction evaluation workflow
------------------------------

The extraction-factored translator is evaluated by alternating installed plugin
prefixes rather than by runtime options. The helper scripts below keep each build
switchable and leave the source constants in `src/plugin/coq_transl_opts.ml`
restored after a configuration build.

1. Build the pre-refactor baseline at the branch fork point:

   ```bash
   ./build-baseline.sh --label baseline-merge-base
   ```

2. Build a refactored configuration:

   ```bash
   ./rebuild-config.sh --list
   ./rebuild-config.sh all-on --label refactor-all-on
   ```

   Named configurations are `all-off`, `all-on`, and the five leave-one-out
   ablations `loo-split-case-axioms`, `loo-prop-case-erasure`,
   `loo-erasure-guards`, `loo-refinement-types`, and
   `loo-wf-recursion-eqs`. Append `-decl-skips` to any of them to enable
   declaration-level refinement skips for the rebuild.

3. Prepare one corpus in `eval/problems`:

   ```bash
   ./prepare-corpus.sh stdlib-regression --sample
   ./prepare-corpus.sh dependent-slice --sample
   ./prepare-corpus.sh external-equations --sample
   ```

   `stdlib-regression` is the standard stdlib regression axis (the full prepared
   stdlib problem set can still be dropped directly into `problems/` as described
   above). `dependent-slice` contains Vector/Fin, FMapAVL/MSetAVL, Eqdep_dec,
   Program/WF, and extraction_deptypes-style fixtures. `external-equations` is
   the selected external Program/Equations-heavy development; see
   `corpora/external-equations/CANDIDATES.md` for candidates and rationale. For
   a full external run, pass `--source /path/to/Coq-Equations`.

4. Dry-run a small sample end-to-end (one prover, one premise-count directory):

   ```bash
   ./run-dry-sample.sh --label baseline-merge-base --corpus stdlib-regression \
     --prover eprover --premise knn-32
   ./run-dry-sample.sh --label refactor-all-on --corpus external-equations \
     --prover eprover --premise knn-32
   ```

   Summaries are written under `results/<label>/<corpus>/summary.txt`; the
   generated ATP and reconstruction result lists next to each summary are the
   quick parse check for harness regressions.

5. Run the confirmation grid (baseline versus the selected screening configuration,
   all standard `hammer_hook` premise-selector/count directories and all four
   provers):

   ```bash
   ./run-confirmation-grid.sh -j 4 --tim 10 --consistency-tim 2
   ```

   The script writes resumable raw checkpoints under `results/confirmation/` and the
   committed summary artifacts under `artifacts/extraction-confirmation/`.

6. To verify that scripted configuration rebuilding changes translation output
   and restores the tree, run for example:

   ```bash
   ./diff-transl-configs.sh all-off all-on Nat.add
   git diff --exit-code -- src/plugin/coq_transl_opts.ml
   ```

`stat` takes 5 (optionally 6) space-separated arguments: the `-r`
option (optional), 4 lists (comma-separated values; empty list is
represented by a single comma) and a boolean

```
stat -r [labels] [sorting specification] [which fields to merge]
     [greedy sequence fixed start]
     (should different versions of the greedy sequence be computed?)
```

- `y` - the number of proved theorems
- `n` - the number of countersatisfiable problems
- `p` - the prover
