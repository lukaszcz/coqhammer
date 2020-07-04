CoqHammer (dev) for Coq 8.10

[![Travis](https://travis-ci.org/lukaszcz/coqhammer.svg?branch=coq8.10)](https://travis-ci.org/lukaszcz/coqhammer/builds)

Since version 1.3, the CoqHammer system consists of two major separate
components.

1. The `sauto` general proof search tactic for the Calculus of
   Inductive Construction.

   A "super" version of `auto`. The underlying proof search procedure
   is based on a fairly general inhabitation procedure for the
   Calculus of Inductive Constructions. While it is in theory complete
   only for a "first-order" fragment of CIC, in practice it can handle
   a much larger part of the Coq logic. In contrast to the `hammer`
   tactic, `sauto` uses only explicitly provided lemmas. For effective
   use, `sauto` typically needs some configuration by means of
   available options.

   See the [Super Auto](#Super Auto) section below.

2. The `hammer` automated reasoning tool which combines learning from
   previous proofs with the translation of problems to the logics of
   external automated systems and the reconstruction of successfully
   found proofs with the `sauto` procedure.

   A typical use is to prove relatively simple goals using available
   lemmas. The problem is to find appropriate lemmas in a large
   collection of all accessible lemmas and combine them to prove the
   goal. The advantage of a hammer is that it is general tool not
   depending on any domain-specific knowledge and not requiring
   configuration by the user. The `hammer` tactic may use all
   currently accessible lemmas, including those proven earlier in a
   given formalization, not only the lemmas from predefined libraries
   or hint databases. At present, however, best results are achieved
   for statements "close to" first-order logic and lemmas from the
   standard library or similar. In comparison to `sauto`, the current
   main limitation of `hammer` is its poor effectiveness on
   non-first-order problems.

   See the [Hammer](#Hammer) section below.

Requirements
------------
- [Coq 8.10](https://github.com/coq/coq)
- for `hammer`: automated provers ([Vampire](https://vprover.github.io/download.html), [CVC4](http://cvc4.cs.stanford.edu/downloads/), [Eprover](http://www.eprover.org), and/or [Z3](https://github.com/Z3Prover/z3/releases))

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
about provers is [provided below](#installation-of-first-order-provers).

If you are only interested in `sauto` and related tactics, they
can be installed standalone (without the hammer plugin) via OPAM after
adding the `coq-released` repository as above:
```
opam install coq-hammer-tactics
```
To instead build and install the tactics manually, use `make tactics`
followed by `make install-tactics`. The tactics may be tested with
`make test-tactics`.

CoqHammer has been tested on Linux and Mac OS X.

The command `make install` will try to install the `predict` and
`htimeout` programs into the directory specified by the `COQBIN`
environment variable. If this variable is not set then a binary
directory is guessed basing on the Coq library directory.

Note that some old versions of Proof General encounter problems with
the plugin. If you use Proof General you might need the most recent
version obtained directly from https://proofgeneral.github.io.

Super Auto
----------

The `Tactics` module contains `sauto` and related tactics. These
tactics are used by the `hammer` tool for proof reconstruction. To use
them directly in your proof scripts first include:

```coq
From Hammer Require Import Tactics.
```

The module provides "solvers" which either solve the goal or fail, and
"simplifiers" which simplify the goal but do not perform backtracking
proof search. The "simplifiers" never fail. The "solvers" are based on
variants of the `sauto` tactic. The "simplifiers" are based on
variants of the heuristics and simplifications performed by `sauto`
upon context change.

Solvers in the order of increasing strength and decreasing speed:
`strivial`, `qauto`, `hauto`, `sauto`.

Simplifiers in the order of increasing strength and decreasing speed:
`simp_hyps`, `sintuition`, `qsimpl`, `ssimpl`.

Additional variants of the "solvers" are used in the reconstruction
backend of the `hammer` tactic. The "solvers" listed here are the ones
most suited for standalone use.

Some examples are given in the [`examples`](examples) directory.

Super Auto options
------------------

The options take arguments specified by:
```
<bopt> ::= on | off
<db> ::= <hintDb> | <rewDb>
<X-list> ::= <X>, .., <X> | - | *
```
Additionaly, `<number>` denotes a natural number, `<term>` a
Coq term, `<const>` a Coq constant, `<ind>` an inductive type,
`<hintDb>` a hint database, `<rewDb>` a rewriting hint
database, `<tactic>` a tactic. For a list, `-` denotes the empty
list, `*` denotes the list of all available object of a given type
(e.g., `*` for `<ind-list>` denotes the list of all inductive types).

Below is a list of options for `sauto` and its variants. The defaults
are for `sauto`.

* `use: <term-list>`

  Add the given lemmas at the top of the context. Default: `use: -`.

* `inv: <ind-list>`

  Try performing inversion (case reasoning) on values of the given
  inductive types. Default: `inv: *`.

  This does not affect inversion for the inductive types representing
  logical connectives. Use `inv: never` to prevent inversion for
  logical connectives.

* `ctrs: <ind-list>`

  Try using constructors of given inductive types. Default: `ctrs: *`.

  This does not affect constructors of the inductive types
  representing logical connectives. Use `ctrs: never` to prevent using
  constructors of logical connectives.

* `unfold: <const-list>`

  Try unfolding the given definitions based on heuristic criteria. Default: `unfold: -`.

  This does not affect `iff` and `not` which are treated specially and
  always unfolded. Use `unfold: never` to prevent this behaviour.

* `unfold!: <const-list>`

  Always unfold the given definitions. Default: `unfold!: -`.

* `db: <db-list>`

  Use the given hint databases (accepts both `auto` and `autorewrite`
  hint databases). Default: `db: -`.

* `hint:db: <db-list>`

  Use the given `auto` hint databases. Default: `hint:db: -`.

* `rew:db: <db-list>`

  Use the given `autorewrite` hint databases. Default: `rew:db: -`.

* `cases: <ind-list>`

  Eliminate discriminees in case expression when the discriminee has
  one of the given inductive types. If `ecases: on` then elimination
  of match disciminees is performed eagerly, otherwise with
  backtracking. Default: `cases: *`, `ecases: on`.

* `split: <sind-list>`

  Eagerly apply constructors of the given "simple" inductive types. An
  inductive type is "simple" if it is non-recursive with one
  constructor whose application does not introduce new existential
  metavariables. Default: `split: *`.

* `limit: <number>`

  Limit the cost of the entire proof tree. Note that this does not
  directly limit the depth of proof search, but only the cost of the
  whole proof tree, according to the cost model built into
  `sauto`. Default: `limit: 1000`.

* `depth: <number>`

  Directly limit the depth of proof search. Cancels the `limit:`
  option.

* `finish: <tactic>`

  Use the given tactic at the leaves of the proof search
  tree. Default: `finish: sfinal trysolve`.

* `final: <tactic>`

  Shorthand for `finish: sfinal <tactic>`.

* `simp: <tactic>`

  Set a tactic for additional simplification after changing the
  context. This is for *additional* simplification -- it has no impact
  on other simplifications performed by `sauto`. The default `simp:`
  tactic does not actually simplify by tries to fully solve the
  goal. Default: `simp: sfinal trysolve`.

* `simp+: <tactic>`

  Add the given tactic for additional simplification after changing
  the context, keeping all previously registered `simp:` tactics.

* `ssimp: <tactic>`

  Set a tactic for additional strong simplification in `ssimpl` and
  `qsimpl`. Default: `ssimp: ssolve`.

* `ssimp+: <tactic>`

  Add the given tactic for additional strong simplification in
  `ssimpl` and `qsimpl`, keeping all previously registered `ssimp:`
  tactics.

* `solve: <tactic>`

  Set a solver tactic to run at each node of the proof search
  tree. For instance, for goals involving real numbers one might use
  `solve: lra`. Default: `solve: -`.

* `solve+: <tactic>`

  Add a solver tactic to run at each node of the proof search tree,
  keeping all previously registered `solve:` tactics.

* `fwd: <bopt>`

  Controls whether to perform limited forward reasoning. Default:
  `fwd: on`.

* `ecases: <bopt>`

  Controls whether elimination of discriminees in case expressions is
  performed eagerly. Default: `ecases: on`.

* `sinv: <bopt>`

  Controls whether to use the "simple inverting" heuristic. This
  heuristic eagerly invert all hypotheses `H : I` with `I` inductive
  when the number of subgoals generated by the inversion is at most
  one. Default: `sinv: on`.

* `einv: <bopt>`

  Controls whether to use the "eager simple elimination restriction",
  i.e., eagerly invert all hypotheses with non-recursive inductive
  types with at most two constructors. Default: `einv: on`.

* `ered: <bopt>`

  Controls whether reduction (with `simpl`) is performed eagerly. Default:
  `ered: on`.

* `red: <bopt>`

  Controls whether to perform reduction with `simpl`. When `red: on`, it
  depends on the `ered:` option if reduction is performed eagerly or
  with backtracking. Default: `red: on`.

* `erew: <bopt>`

  Controls whether directed rewriting is performed eagerly. Directed
  rewriting means rewriting with hypotheses orientable with
  LPO. If `erew: off` but `rew: on`, directed rewriting is still
  performed but with backtracking. Default: `erew: on`.

* `urew: <bopt>`

  Controls whether to perform undirected rewriting. Default: `urew: on`.

* `rew: <bopt>`

  Controls whether to perform rewriting (both directed and
  undirected). Setting `rew: off` implies `urew: off`. Default: `rew: on`.

* `brefl: <bopt>`

  Controls whether to perform boolean reflection, i.e., convert
  elements of `bool` into statements in `Prop`. Default: `brefl: off`.

* `sapp: <bopt>`

  Controls whether to use the `sapply` tactic for application. The
  `sapply` tactic performs applications modulo simple equational
  reasoning. This increases the success rate, but decreases
  speed. Default: `sapp: on`.

* `exh: <bopt>`

  Controls whether to perform backtracking on instantiations of
  existential metavariables. Default: `exh: off`.

* `sig: <bopt>`

  Controls whether to (eagerly) perform simplifications for
  sigma-types (using the `destruct_sigma` and `invert_sigma`
  tactics). Default: `sig: on`.

* `lia: <bopt>`

  Controls whether to try the `lia` tactic for arithmetic
  subgoals. Default: `on`.

* `dep: <bopt>`

  Enhanced support for dependent types. When `on`, the `depelim`
  tactic from the `Program` module is used for inversion. This may
  negatively impact speed and introduce dependencies on some axioms
  equivalent to Uniqueness of Identity Proofs. Default: `dep: off`.

Hammer
------

In your Coq file editor or toplevel (e.g., `coqide` or `coqtop`),
first load the hammer plugin:

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
guaranteed to be reproducible. If all uses of `hammer` in a file have
been replaced with reconstruction tactics, it is recommended to ensure
that only the `Tactics` module is loaded and not the hammer plugin.

Installation of first-order provers
-----------------------------------

To use the `hammer` tactic you need at least one of the following ATPs
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

Papers about CoqHammer
----------------------

1. Ł. Czajka, C. Kaliszyk, [Hammer for Coq: Automation for Dependent Type Theory](https://link.springer.com/article/10.1007/s10817-018-9458-4), Journal of Automated Reasoning, 2018

   This paper is the main reference for the `hammer` tactic. It
   describes the first version of the `hammer` tool.

2. Ł. Czajka, [Practical proof search for Coq by type inhabitation](http://www.mimuw.edu.pl/~lukaszcz/sauto.pdf), IJCAR 2020

   This paper is the main reference for the `sauto` tactic.

3. Ł. Czajka, [A Shallow Embedding of Pure Type Systems into First-order Logic](http://drops.dagstuhl.de/opus/volltexte/2018/9853/), TYPES 2016

   This paper proves soundness of a core version of the translation
   used by the `hammer` tactic.

4. Ł. Czajka, B. Ekici, C. Kaliszyk, [Concrete Semantics with Coq and CoqHammer](https://arxiv.org/abs/1808.06413), CICM 2018

Archival CoqHammer versions
---------------------------

CoqHammer versions before 1.0.6 are available from: http://cl-informatik.uibk.ac.at/cek/coqhammer.

Hammer options
--------------

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
Set Hammer SAutoLimit n.
(* before invoking external ATPs the hammer first tries to solve the
   goal using the sauto tactic with a time limit of n seconds; default: 1s *)
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

See [CREDITS](CREDITS.md) for a full list of contributors.
