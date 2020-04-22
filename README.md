CoqHammer (dev) for Coq master (use other branches for other versions of Coq)

[![Travis](https://travis-ci.org/lukaszcz/coqhammer.svg?branch=master)](https://travis-ci.org/lukaszcz/coqhammer/builds)

CoqHammer is a general-purpose automated reasoning hammer tool for
Coq. It combines learning from previous proofs with the translation of
problems to the logics of automated systems and the reconstruction of
successfully found proofs. A typical use is to prove relatively simple
goals using available lemmas. The problem is to find appropriate
lemmas in a large collection of all accessible lemmas and combine them
to prove the goal. The advantage of a hammer is that it is a general
system not depending on any domain-specific knowledge and not
requiring configuration by the user. The hammer plugin may use all
currently accessible lemmas, including those proven earlier in a given
formalization, not only the lemmas from predefined libraries or hint
databases. At present, however, best results are achieved for statements
"close to" first-order logic and lemmas from the standard library or
similar.

Since version 1.2 the CoqHammer distribution includes automated
reasoning tactics based on a proof search procedure for the Calculus
of Inductive Constructions. These tactics are used in CoqHammer's
reconstruction backend, but they may also be installed and used
separately. See the "Tactics" section below.

Requirements
------------
- [Coq master](https://github.com/coq/coq)
- automated provers ([Vampire](https://vprover.github.io/download.html), [CVC4](http://cvc4.cs.stanford.edu/downloads/), [Eprover](http://www.eprover.org), and/or [Z3](https://github.com/Z3Prover/z3/releases))

Installation
------------

The latest release of CoqHammer is most easily installed via
[OPAM](https://opam.ocaml.org/):
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hammer
```

To instead build and install CoqHammer manually, run `make` followed
by `make install`. Then optionally run `make tests` to check if
everything works. Some of the tests may fail if your machine is not
fast enough or you do not have all provers installed. More information
about provers is provided below.

If you are only interested in the CoqHammer's reconstruction tactics,
they can be installed standalone (without the hammer plugin) via OPAM
after adding the `coq-released` repository as above:
```
opam install coq-hammer-tactics
```
To instead build and install the tactics manually, use `make tactics`
followed by `make install-tactics`.

The plugin has been tested on Linux and Mac OS X.

The command `make install` will try to install the `predict` and
`htimeout` programs into the directory specified by the `COQBIN`
environment variable. If this variable is not set then a binary
directory is guessed basing on the Coq library directory.

Note that some old versions of Proof General encounter problems with
the plugin. If you use Proof General you might need the most recent
version obtained directly from https://proofgeneral.github.io.

Usage
-----

In `coqtop` or `coqide`, first load the hammer plugin:

```coq
From Hammer Require Import Hammer.
```

Then, the available commands are as follows:

command                          | description
-------------------------------- | ------------------------------------
`hammer`                         |  Runs the hammer tactic.
`predict n`                      |  Prints n dependencies for the current goal predicted by the machine-learning premise selection.
`Hammer_version`                 |  Prints the version of CoqHammer.
`Hammer_cleanup`                 |  Resets the hammer cache.

Some examples are given in the [`examples`](examples) directory.

The intended use of the `hammer` tactic is to replace it upon success
with the reconstruction tactic shown in the response window. This
reconstruction tactic has no time limits and makes no calls to
external ATPs. The success of the `hammer` tactic itself is not
guaranteed to be reproducible.

Installation of first-order provers
-----------------------------------

To use the plugin you need at least one of the following ATPs
available in the path (under the command name in brackets): Vampire
(`vampire`), CVC4 (`cvc4`), Eprover (`eprover`), Z3 (`z3_tptp`). It is
recommended to have all four ATPs, or at least Vampire and CVC4.

The websites for the provers are:
- Vampire: https://vprover.github.io.
- CVC4: http://cvc4.cs.stanford.edu. CVC4 needs to be version 1.6 or
later. Earlier versions do not fully support the TPTP format. It is
recommended to have the better-performing GPL version of CVC4 instead
of the BSD version.
- Eprover: http://www.eprover.org.
- Z3: https://github.com/Z3Prover/z3/releases. Note that the default
version of Z3 does not support the TPTP format. You need to compile
the TPTP frontend located in `examples/tptp` in the Z3 source package.

Tactics
-------

The `Tactics` module contains the reconstruction tactics which may
also be used directly in your proof scripts. In contrast to the
`hammer` tactic they do not invoke external ATPs and they do not use
any lemmas except explicitly provided ones.

The most useful tactics are:

* `sauto`

  A "super" version of `auto`. In addition to applying hypotheses, it
  tries applying constructors, inverting the hypotheses, ordered
  rewriting, heuristic rewriting, rewriting with hints from the
  `shints` database, arithmetic solving with `lia`, case splitting,
  intelligent unfolding, forward reasoning and hypotheses
  simplification.

  The underlying proof search procedure of `sauto` is based on a
  fairly general inhabitation procedure for the Calculus of Inductive
  Constructions. While it is in theory complete only for a
  "first-order" fragment of CIC, in practice it can handle a much
  larger part of the Coq logic.

* `hauto`

  The same as `sauto` but by default does not use constructors of or
  do inversion on inductive types other than logical connectives and
  equality. Also does not use the hints from the `shints`
  database. This tactic is faster than `sauto` if you can provide
  precise dependencies, and it is thus used most often as the
  reconstruction tactic suggested by `hammer`.

* `ssimpl`

  A goal simplification tactic. It does not perform much of actual
  proof search (beyond what `intuition` and `auto` already do). It is
  designed in such a way as to terminate in a short time in most
  circumstances. It uses the rewrite hints from the `shints` database.

  **WARNING**: This tactic may change the proof state unpredictably and
  introduce randomly named hypotheses into the context.

  It is nonetheless useful to sometimes use `ssimpl` before a call to
  `hammer`. Examples of this are provided in
  [`examples/imp.v`](examples/imp.v) and
  [`examples/combs.v`](examples/combs.v).

* `strivial`

  A simple and quick goal solving tactic. Usually a bit stronger than
  `auto`. Incorporates `lia` and `congruence`.

* `scrush`

  The definition of `scrush` is: `try strivial; ssimpl; sauto`.

* `qsimpl`

  A more conservative version of `ssimpl`. Useful when `ssimpl`
  performs too much simplification or takes too much time.

* `sintuition`

  An even more conservative and quicker simplification tactic.

* `simp_hyps`

  A basic hypotheses simplification tactic. Used as a component of
  most other tactics.

* `use (lem1, ..., lemN)`

  Adds lemmas `lem1`, ..., `lemN` to the context and simplifies them.

* `sprover`

  Performs iterative deepening proof search with a depth-bounded
  version of `sauto`.

Tactic options
--------------

* `tactic n`

  Limit the cost of the entire proof tree by `n`. The default
  is 1000. Note that this does not directly limit the depth of proof
  search, but only the cost of the whole proof tree, according to the
  cost model built into `sauto`. Example: `sauto 200`, `hauto 2000`.

* `using (lem1,...,lemn)`

  Add lemmas to the hypotheses.

* `unfolding (def1,...,defn)`

  Unfold given definitions. Use `logic` for all logical constants.

* `inverting (ind1,...,indn)`

  Invert values of given inductive types. Use `logic` for all
  inductive types representing logical connectives and quantifiers.

Example: `sauto 500 using Nat.add_1_r unfolding (Nat.Even, Nat.Odd) inverting List.Forall`

Papers about CoqHammer
----------------------

1. Ł. Czajka, C. Kaliszyk, [Hammer for Coq: Automation for Dependent Type Theory](https://link.springer.com/article/10.1007/s10817-018-9458-4)

   This paper is the main reference for CoqHammer. It describes the
   first version of the system.

2. Ł. Czajka, [A Shallow Embedding of Pure Type Systems into First-order Logic](http://drops.dagstuhl.de/opus/volltexte/2018/9853/)

   This paper proves soundness of a core version of the embedding used
   by CoqHammer.

3. Ł. Czajka, [Practical proof search for Coq by type inhabitation](http://www.mimuw.edu.pl/~lukaszcz/sauto.pdf)

   This paper describes a general proof search procedure for the
   Calculus of Inductive Constructions which is used in CoqHammer's
   reconstruction backend since version 1.2.

4. Ł. Czajka, B. Ekici, C. Kaliszyk, [Concrete Semantics with Coq and CoqHammer](https://arxiv.org/abs/1808.06413)

Further CoqHammer options
-------------------------

```coq
Set/Unset Hammer Debug.
Set Hammer GSMode n.
(* The hammer may operate in one of two modes: gs-mode or the ordinary
   mode. If GSMode is set to n > 0 then n best strategies (combination
   of prover, prediction method and number of predictions) are run in
   parallel. Otherwise, if n = 0, then the ordinary mode is active and
   the number of machine-learning dependency predictions, the
   prediction method and whether to run the ATPs in parallel are
   determined by the options below (Hammer Predictions, Hammer
   PredictMethod and Hammer Parallel). It is advisable to set GSMode
   to the number of cores your machine has, plus/minus one. Default: 8 *)
Set Hammer Predictions n.
(* number of predictions for machine-learning dependency prediction;
   irrelevant if GSMode > 0; default: 1024 *)
Set Hammer PredictMethod "knn"/"nbayes".
(* irrelevant if GSMode > 0; default: "knn" *)
Set/Unset Hammer Parallel.
(* run ATPs in parallel; irrelevant if GSMode > 0; default: on *)
Set Hammer ATPLimit n.
(* ATP time limit in seconds, default: 10s *)
Set Hammer ReconstrLimit n.
(* time limit for proof reconstruction, default: 10s *)
Set Hammer CrushLimit n.
(* before invoking external ATPs the hammer first tries to solve the
   goal using the scrush tactic with a time limit of n seconds; default: 1s *)
Set/Unset Hammer Vampire/CVC4/Eprover/Z3.
Set Hammer PredictPath "/path/to/predict". (* default: "predict" *)
Set/Unset Hammer FilterProgram.
(* ignore dependencies from Coq.Program.*, default: on *)
Set/Unset Hammer FilterClasses.
(* ignore dependencies from Coq.Classes.*, default: on *)
Set/Unset Hammer FilterHurkens.
(* ignore dependencies from Coq.Logic.Hurkens.*, default: on *)
Set Hammer MinimizationThreshold n.
(* the minimum number of dependencies returned by an ATP for which minimization is performed, default: 6 *)
Set/Unset Hammer SearchBlacklist.
(* ignore dependencies blacklisted with the Search Blacklist
   vernacular command, default: on *)
Set/Unset Hammer ClosureGuards.
(* should guards be generated for types of free variables? setting
   this to "on" will typically harm the hammer success rate, but it
   may help with functional extensionality; set this to "on" if you
   use functional extensionality and get many unreconstructible
   proofs; default: off *)
```

Debugging
---------

The following commands are useful for debugging.

command                          | description
-------------------------------- | ---------------------------------------------------------
`Hammer_print "name"`            |  Prints object `name` in hhterm format.
`Hammer_transl "name"`           |  Prints all axioms resulting from the translation of `name` in the intermediate coqterm format accepted by the [`tptp_out.ml`](src/plugin/tptp_out.ml) module.
`hammer_transl`                  |  Prints all axioms resulting from the translation of the current goal.
`Hammer_features "name"`         |  Prints the features of `name`, bypassing the cache.
`Hammer_features_cached "name"`  |  Prints the features of `name`, using and possibly modifying the cache.
`hammer_features`                |  Prints the features of the current goal.
`Hammer_objects`                 |  Prints the number of accessible objects.

Copyright and license
---------------------

Copyright (c) 2017-2020, Lukasz Czajka, TU Dortmund University, and
Cezary Kaliszyk, University of Innsbruck. Distributed under the terms
of LGPL 2.1, see the file [LICENSE](LICENSE).
