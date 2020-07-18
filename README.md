CoqHammer (dev) for Coq 8.11

[![Travis](https://travis-ci.org/lukaszcz/coqhammer.svg?branch=coq8.11)](https://travis-ci.org/lukaszcz/coqhammer/builds)

Since version 1.3, the CoqHammer system consists of two major separate
components.

1. The `sauto` general proof search tactic for the Calculus of
   Inductive Construction.

   A "super" version of `auto`. The underlying proof search procedure
   is based on a fairly general inhabitation procedure for the
   Calculus of Inductive Constructions. While it is in theory complete
   only for a "first-order" fragment of CIC, in practice it can handle
   a much larger part of Coq's logic. In contrast to the `hammer`
   tactic, `sauto` can use only explicitly provided lemmas and it does
   not invoke any external ATPs. For effective use, `sauto` typically
   needs some configuration by providing appropriate options.

   See the [Sauto](#Sauto) section below.

2. The `hammer` automated reasoning tool which combines learning from
   previous proofs with the translation of problems to the logics of
   external automated systems and the reconstruction of successfully
   found proofs with the `sauto` procedure.

   A typical use is to prove relatively simple goals using available
   lemmas. The problem is to find appropriate lemmas in a large
   collection of all accessible lemmas and combine them to prove the
   goal. The advantage of a hammer is that it is a general tool not
   depending on any domain-specific knowledge and not requiring
   configuration by the user. The `hammer` tactic may use all
   currently accessible lemmas, including those proven earlier in a
   given formalization, not only the lemmas from predefined libraries
   or hint databases. At present, however, best results are achieved
   for statements "close to" first-order logic and lemmas from the
   standard library or similar. In comparison to `sauto`, the current
   main limitation of `hammer` is its poor effectiveness on problems
   heavily dependent on non-first-order features of Coq's logic
   (e.g. higher-order functions, boolean reflection or sophisticated
   uses of dependent types).

   See the [Hammer](#Hammer) section below.

Requirements
------------
- [Coq 8.11](https://github.com/coq/coq)
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

Sauto
-----

The `Tactics` module contains `sauto` and related tactics. These
tactics are used by the `hammer` tool for proof reconstruction. To use
them directly in your proof scripts first include:

```coq
From Hammer Require Import Tactics.
```

The module provides "solvers" which either solve the goal or fail, and
"simplifiers" which simplify the goal but do not perform backtracking
proof search. The simplifiers never fail. The solvers are based on
variants of the `sauto` tactic or its sub-components. The simplifiers
are based on variants of the heuristics and simplifications performed
by `sauto` upon context change.

Below we list the solvers and the simplifiers in the order of
increasing strength and decreasing speed:
* solvers: `sdone`, `strivial`, `qauto`, `hauto`, `sauto`;
* simplifiers: `simp_hyps`, `sintuition`, `qsimpl`, `ssimpl`.

The `hauto` tactic is just `sauto inv: - ctrs: -`. The `qauto` tactic
is just `hauto quick: on limit: 100 finish: (eauto; congruence 400)`.

See the [Options for sauto](#options-for-sauto) section for an
explanation of these options.

The `sdone` tactic is used by `sauto` as the final tactic at the
leaves of the proof search tree (see the `final:` and `finish:`
options). The `strivial` tactic is just `srun (sfinal sdone)`. The
`srun` and `sfinal` tactics are described in the next section.

Additional variants of the solvers are used in the reconstruction
backend of the `hammer` tactic. The solvers listed here are the ones
most suited for standalone use.

The are some examples in the [`examples`](examples) directory.

Other tactics from the Tactics module
-------------------------------------

In addition to the solvers and the simplifiers listed in the previous
section, the `Tactics` module contains a number of handy tactics which
are used internally by `sauto`.

* `sdestruct t`

  Destruct `t` in the "right" way, introducing appropriate hypotheses
  into the context and handling boolean terms correctly (automatically
  performing boolean reflection).

* `dep_destruct t`

  Dependent destruction of `t`. A simple wrapper around the `dependent
  destruction` tactic from the Program module.

* `sinvert t`

  Inversion of the conclusion of `t`. The term `t` may be quantified -
  then new existential variables are introduced or new subgoals are
  generated for the arguments.

* `sdepinvert t`

  Dependent inversion of the conclusion of `t`. The same as `sinvert
  t` but may use the `depelim` tactic for inversion.

* `sapply t`

  Apply `t` modulo simple heuristic equational reasoning. See the
  `sapp:` option.

* `bool_reflect`

  Boolean reflection in the goal and in all hypotheses. See the
  [Boolean reflection](#boolean-reflection) section.

* `use lem1, .., lemn`

  Add the listed lemmas at the top of the context and simplify them.

* `srun tac <sauto-options>`

  The `srun` tactical first interprets sauto options (see
  [Options for sauto](#options-for-sauto)) and performs `sauto`
  initialisation, then runs `unshelve solve [ tac ]`, and then tries
  to solve the unshelved subgoals with `auto`, `easy` and `do 10
  constructor`.

  Only the following options are interpreted by `srun`: `use:`,
  `unfold:`, `unfold!:`, `brefl:`, `brefl!:`, `red:`, `ered:`,
  `sig:`. Other options have no effect.

  The `sauto` initialisation performed by `srun` executes the actions
  corresponding to the options listed here. The default values of the
  options are like for `sauto`.

* `sfinal tac`

  Perform "final" simplifications of the goal (simplifying hypotheses,
  eliminating universally quantified disjunctions and existentials)
  and solve all the resulting subgoals with `tac`. The `sfinal tac`
  tactic invocation fails if `tac` does not solve some of the
  resulting subgoals.

* `forwarding`

  Limited forward reasoning corresponding to the `fwd:` option.

* `forward_reasoning n`

  Repeated forward reasoning with repetition limit `n`. This is
  similar to but not exactly the same as `do n forwarding`.

* `simpl_sigma`

  Simplifications for sigma-types. Composed of two tactics:
  `destruct_sigma` which eagerly destructs all elements of subset
  types occurring as arguments to the first projection, and
  `invert_sigma` which is a faster but weaker version of
  `inversion_sigma` from the standard library. The `simpl_sigma`
  tactic corresponds to the `sig:` option.

* `generalize proofs`
* `generalize proofs in H`
* `generalize proofs in *`

  Generalizes by proof terms occurring in the goal and/or a
  hypothesis. Corresponds to the `prf:` option.

* `srewriting`

  Directed rewriting with the hypotheses which may be oriented using
  LPO. Corresponds to the `erew:` option.

* `simple_inverting`
* `simple_inverting_dep`

  Perform "simple inversion" corresponding to the `sinv:` option. The
  `_dep` version may use the `depelim` tactic.

* `eager_inverting`
* `eager_inverting_dep`

  Perform "eager simple elimination" corresponding to the `einv:`
  option. The `_dep` version may use the `depelim` tactic.

* `case_split`
* `case_split_dep`

  Eliminate one discriminee of a match expression occurring in the
  goal or in a hypothesis. The `_dep` version may use the `depelim`
  tactic.

* `case_splitting`
* `case_splitting_dep`

  Eagerly eliminate all discriminees of match expressions occurring in
  the goal or in a hypothesis. This corresponds to the action enabled by
  setting `cases: *` and `ecases: on`. The `_dep` version may use the
  `depelim` tactic.

* `simple_splitting`

  Eagerly apply constructors of "simple" inductive types -
  non-recursive inductive types with exactly one constructor such that
  application of the constructor does not introduce new existential
  variables. This corresponds to `split: *`.

* `simple_splitting logic`

  Simple splitting for logical connectives only.

* `ssolve`

  The `ssolve` tactic is just
  ```coq
  solve [ (intuition auto); try sfinal sdone; try congruence 24;
           try easy; try solve [ econstructor; sfinal sdone ] ].
  ```

Options for sauto
-----------------

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
list, `*` denotes the list of all available objects of a given type
(e.g., `*` for `<ind-list>` denotes the list of all inductive types).

Below is a list of options for `sauto` and its variants. The defaults
are for `sauto`.

* `use: <term-list>`

  Add the listed lemmas at the top of the context. Default: `use: -`.

* `inv: <ind-list>`

  Try performing inversion (case reasoning) on values of the listed
  inductive types. Default: `inv: *`.

  This does not affect inversion for the inductive types representing
  logical connectives. Use `inv: never` to prevent inversion for
  logical connectives.

* `ctrs: <ind-list>`

  Try using constructors of listed inductive types. Default: `ctrs: *`.

  This does not affect constructors of the inductive types
  representing logical connectives. Use `ctrs: never` to prevent using
  constructors of logical connectives.

* `unfold: <const-list>`

  Try unfolding the listed definitions based on heuristic criteria. Default: `unfold: -`.

  This does not affect `iff` and `not` which are treated specially and
  always unfolded. Use `unfold: never` to prevent this behaviour.

* `unfold!: <const-list>`

  Always unfold the listed definitions. A primitive version of
  `unfold:` without heuristics. Default: `unfold!: -`.

* `db: <db-list>`

  Use the listed hint databases (accepts both `auto` and `autorewrite`
  hint databases). Default: `db: -`.

* `hint:db: <db-list>`

  Use the listed `auto` hint databases. Default: `hint:db: -`.

* `rew:db: <db-list>`

  Use the listed `autorewrite` hint databases. Default: `rew:db: -`.

* `cases: <ind-list>`

  Eliminate discriminees in case expressions when the discriminee has
  one of the listed inductive types. If `ecases: on` then elimination
  of match disciminees is performed eagerly, otherwise with
  backtracking. Default: `cases: *`, `ecases: on`.

* `split: <sind-list>`

  Eagerly apply constructors of the listed "simple" inductive
  types. An inductive type is "simple" if it is non-recursive with
  exactly one constructor, and such that the application of the
  constructor does not introduce new existential variables. Default:
  `split: -`.

  This does not affect inductive types representing logical
  connectives. Use `split: never` to prevent eager applications of
  constructors of "simple" inductive types representing logical
  connectives (i.e., conjunction and existential quantification).

* `limit: <number>`

  Limit the cost of the entire proof tree. Note that this does not
  directly limit the depth of proof search, but only the cost of the
  whole proof tree, according to the cost model built into
  `sauto`. Default: `limit: 1000`.

* `depth: <number>`

  Directly limit the depth of proof search. Cancels the `limit:`
  option.

* `finish: <tactic>`

  Set a tactic to use at the leaves of the proof search
  tree. Default: `finish: (sfinal sdone)`.

* `final: <tactic>`

  Shorthand for `finish: (sfinal <tactic>)`. Default: `final: sdone`.

* `simp: <tactic>`

  Set a tactic for additional simplification after context
  change. This option is for *additional* simplification - it has no
  impact on other simplifications performed by `sauto`. The default
  `simp:` tactic does not actually simplify but tries to fully solve
  the goal. Default: `simp: (sfinal sdone)`.

* `simp+: <tactic>`

  Add a tactic for additional simplification after context change,
  keeping all previously registered `simp:` tactics.

* `ssimp: <tactic>`

  Set a tactic for additional strong simplification in `ssimpl` and
  `qsimpl`. Default: `ssimp: ssolve`.

* `ssimp+: <tactic>`

  Add a tactic for additional strong simplification in `ssimpl` and
  `qsimpl`, keeping all previously registered `ssimp:` tactics.

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
  heuristic eagerly inverts all hypotheses `H : I` with `I` inductive
  when the number of subgoals generated by the inversion is at most
  one. Default: `sinv: on`.

* `einv: <bopt>`

  Controls whether to use the "eager simple elimination restriction",
  i.e., eagerly invert all hypotheses which have a non-recursive
  inductive type with at most two constructors. Default: `einv: on`.

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
  elements of `bool` applied to `is_true` into statements in
  `Prop`. Setting `brefl: on` implies `ecases: off` - use `brefl!:` to
  prevent this behaviour. You may also re-enable `ecases:` by
  providing `ecases: on` *after* `brefl: on`. Default: `brefl: off`.

  See also the [Boolean reflection](#boolean-reflection) section.

* `brefl!: <bopt>`

  A primitive version of `brefl:` which when enabled does not
  automatically disable `ecases:`.

* `sapp: <bopt>`

  Controls whether to use the `sapply` tactic for application. The
  `sapply` tactic performs application modulo simple equational
  reasoning. This increases the success rate, but decreases
  speed. Default: `sapp: on`.

* `exh: <bopt>`

  Controls whether to perform backtracking on instantiations of
  existential variables. Default: `exh: off`.

* `lia: <bopt>`

  Controls whether to try the `lia` tactic for arithmetic
  subgoals. Default: `lia: on`.

  Note that invoking `lia` is done via the default `simp:` and
  `finish:` tactics - if these tactics are changed then `lia:` has no
  effect. To re-enable `lia` use `solve: lia` or `solve+: lia`.

* `sig: <bopt>`

  Controls whether to (eagerly) perform simplifications for
  sigma-types (using the `simpl_sigma` tactic). Default: `sig: on`.

* `prf: <bopt>`

  Controls whether to (eagerly) generalize proof terms occurring in
  the goal or in one of the hypotheses. Default: `prf: off`.

* `dep: <bopt>`

  Enhanced support for dependent types. When `on`, the `depelim`
  tactic from the Program module is used for inversion. This may
  negatively impact speed and introduce dependencies on some axioms
  equivalent to Uniqueness of Identity Proofs. Setting `dep: on`
  implies `prf: on`, `einv: off` and `sinv: off` - use `dep!:` to
  prevent this behaviour. You can also change the `prf:`, `einv:` and
  `sinv:` options separately by setting them *after* `dep:
  on`. Default: `dep: off`.

* `dep!: <bopt>`

  A primitive version of `dep:` which when enabled does not affect
  `prf:`, `einv:` or `sinv:`.

* `eager: <bopt>`
* `e: <bopt>`

  This is a compound option which controls multiple other options:
  `ered`, `erew`, `ecases`, `einv`, `sinv`, `sig`. Setting `eager: on`
  (or `e: on`) has the effect of enabling all these options. Setting
  `eager: off` disables all of the listed options.

* `lazy: <bopt>`
* `l: <bopt>`

  The exact opposite of `eager:`, i.e., `lazy: on` is just `eager:
  off`, and `lazy: off` is just `eager: on`.

* `quick: <bopt>`
* `q: <bopt>`

  Setting `quick: on` (or `q: on`) has the same effect as setting:
  ```
  sapp: off simp: idtac finish: sdone lia: off
  ```
  Setting `quick: off` has no effect.

* `lq: <bopt>`

  Settting `lq: on` has the same effect as setting `lazy: on` and
  `quick: on`. Setting `lq: off` has no effect.

Boolean reflection
------------------

Importing the Reflect module with
```coq
From Hammer Require Import Reflect.
```
declares `is_true` as a coercion and makes available the following tactics
related to boolean reflection.

* `breflect`
* `breflect in H`
* `breflect in *`

  Perform boolean reflection - convert boolean statements (arguments
  of `is_true`) into propositions in `Prop`, and boolean comparisons
  (on basic types from the standard library) into the corresponding
  inductive types.

  The `breflect` tactic just performs generalised top-down rewriting
  (also under binders) with the `brefl` rewrite hint
  database. This allows for easy customisation of boolean reflection
  by adding lemmas expressing reflection of user-defined boolean
  predicates. For instance, suppose you have a boolean predicate
  ```coq
  sortedb : list nat -> bool
  ```
  and a corresponding inductive predicate
  ```coq
  sorted : list nat -> Prop
  ```
  and a lemma
  ```coq
  sortedb_sorted_iff : forall l : list nat, is_true (sortedb l) <-> sorted l
  ```
  Then adding the rewrite hint
  ```coq
  Hint Rewrite -> sortedb_sorted_iff : brefl.
  ```
  will result in `breflect` automatically converting `is_true (sortedb l)` to
  `sorted l`. This will then also be done by `bool_reflect` and by
  `sauto` with `brefl: on`, because these tactics internally use
  `breflect`.

* `breify`
* `breify in H`
* `breify in *`

  The reverse of `breflect`. Uses the `breif` rewrite hint
  database.

* `bsimpl`
* `bsimpl in H`
* `bsimpl in *`

  Simplify boolean expressions. This is just generalised top-down
  rewriting with the `bsimpl` database.

* `bdestruct t`
* `bdestruct t as H`

  Destruct a boolean term `t` in the "right" way, introducing an
  appropriate hypothesis into the context and automatically performing
  boolean reflection on it. The second form of the tactic provides an
  explicit name for the introduced hypothesis. A successful run of
  `bdestruct` always results in two subgoals with one new hypothesis
  in each.

* `blia`

  Perform boolean reflection and then run `lia`.

Hammer
------

In your Coq file editor or toplevel (e.g., `coqide` or `coqtop`),
first load the hammer plugin:

```coq
From Hammer Require Import Hammer.
```

The available commands are:

command                          | description
-------------------------------- | ------------------------------------
`hammer`                         |  Runs the hammer tactic.
`predict n`                      |  Prints n dependencies for the current goal predicted by the machine-learning premise selection.
`Hammer_version`                 |  Prints the version of CoqHammer.
`Hammer_cleanup`                 |  Resets the hammer cache.

There are some examples in the [`examples`](examples) directory.

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

   This paper is the main reference for the `hammer` tactic.

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
(* ATP time limit in seconds, default: 20s *)
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

Copyright (c) 2017-2020, Lukasz Czajka, TU Dortmund University.\
Copyright (c) 2017-2018, Cezary Kaliszyk, University of Innsbruck.

Distributed under the terms of LGPL 2.1, see the file
[LICENSE](LICENSE).

See [CREDITS](CREDITS.md) for a full list of contributors.
