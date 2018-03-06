How to evaluate a new Coq library?
----------------------------------

Let `N` be the number of parallel jobs to execute. Unless otherwise
stated, execute all commands in the `eval/` directory.

Steps 1-5 may be skipped if the library to evaluate is one of the
libraries already prepared in the `libs/` directory. Then just do:

```bash
ln -s libs/library problems
```

Otherwise follow all steps.

1. Place the library sources in the `problems/` directory (possibly
   with subdirectories). The sources should contain the `*.v` files.

2. `make -k -j N init`

   This will compile the problems, creating the necessary `*.glob`
   files.

3. `cd tools && make`

4. `cd problems && ../tools/mkhooks.sh`

   This script may be used to insert calls to `hammer_hook` in the
   library source files (it requires the corresponding `*.glob` files
   to be present). Run it in the `problems/` directory. After running
   `tools/mkhooks.sh` you may need to edit some files manually to make
   them compile with `coqc`.

5. `./check.sh N`

   This checks if the problems compile with `coqc` after running
   `tools/mkhooks.sh`. It may fail for some files, which must be then
   edited manually to make them compile with `coqc`. The errors may be
   viewed in the `check.log` file.

6. `./gen-atp.sh N`

7. `cd atp && ./run-provers.sh N [your.mail@mail.com]`

   The script `atp/run-provers.sh` should be edited when adding or
   changing the (versions of) ATP provers used in the evaluation. When
   adding new ATPs also the `hammer_hook` code in [`src/hammer.ml4`](../src/hammer.ml4)
   should be edited.

8. `./run-reconstr.sh N`

After executing these steps, the reconstruction results are in the
`out/` directory. The ATP results are in the `atp/o/` directory.

Tools
-----

* `stat`: compute ATP statistics. Run in the atp/ directory. Reads the
  `o/*/*.p` files.

  Example: `tools/stat , y,p , , false`

`stat` takes 5 space-separated arguments: 4 lists (comma-separated
values; empty list is represented by a single comma) and a boolean

```
stat [labels] [sorting specification] [which fields to merge]
     [greedy sequence fixed start]
     (should different versions of the greedy sequence be computed?)
```

- `y` - the number of proved theorems
- `n` - the number of countersatisfiable problems
- `p` - the prover
