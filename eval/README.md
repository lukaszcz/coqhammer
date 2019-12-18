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
