CoqHammer (dev) for Rocq 9.2 (use other branches for other versions of Rocq)

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/lukaszcz/coqhammer/actions/workflows/docker-action.yml/badge.svg?branch=rocq-9.2
[docker-action-link]: https://github.com/lukaszcz/coqhammer/actions?query=workflow:"Docker%20CI"

CoqHammer video tutorial:
[part 1 (sauto)](https://www.youtube.com/watch?v=0c_utk9bVgU&list=PLXXF_svQE_b-9A5p2OKU7Tjz-NcE7H2xg),
[part 2 (hammer)](https://www.youtube.com/watch?v=EEmpVCSqShA&list=PLXXF_svQE_b_vja6TWFbGNB266Et8m5yC).

Since version 1.3, the CoqHammer system consists of two major separate components.

1. The `sauto` general proof search tactic for the Calculus of
   Inductive Construction.

2. The `hammer` automated reasoning tool which combines learning from
   previous proofs with the translation of problems to the logics of
   external automated systems and the reconstruction of successfully
   found proofs with the `sauto` procedure.

See the [CoqHammer webpage](https://coqhammer.github.io) for
documentation and installation instructions.

Premise selection options
-------------------------
- `Set Hammer DefinitionPremises K.` reserves bounded slots within each
  predictor premise budget for accessible definitions referenced by the goal
  or hypotheses (including grouped inductives and constructors). Candidates
  are ordered by rarity, then size and name. At most `K` and one eighth of the
  budget (rounded up) are reserved; the predictor fills the remaining slots,
  so these definitions do not increase the budget. The default is `32`;
  `0` disables reserved definition premises.
- `Set Hammer DefinitionFeatures G.` expands the predictor query with the
  plain constant dependencies taken from definitions of rare seed constants
  mentioned by the goal or hypotheses. A seed constant is expanded when at
  most `G` accessible definitions refer to it. The default is `16`; `0`
  disables definition-feature expansion.

`Unset Hammer DefinitionPremises.` and `Unset Hammer DefinitionFeatures.`
restore their respective defaults.

Requirements
------------
- [Rocq 9.2](https://rocq-prover.org/)
- for `hammer`: automated provers
  ([Vampire](https://vprover.github.io/download.html),
  [CVC4](http://cvc4.cs.stanford.edu/downloads/),
  [Eprover](http://www.eprover.org), and/or
  [Z3](https://github.com/Z3Prover/z3/releases))

Copyright and license
---------------------

Copyright (c) 2017-2026, Lukasz Czajka.\
Copyright (c) 2017-2018, Cezary Kaliszyk, University of Innsbruck.

Distributed under the terms of LGPL 2.1, see the file
[LICENSE](LICENSE).

See [CREDITS](CREDITS.md) for a full list of contributors.
