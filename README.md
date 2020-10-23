CoqHammer (dev) for Coq 8.11

[![Travis](https://travis-ci.org/lukaszcz/coqhammer.svg?branch=coq8.11)](https://travis-ci.org/lukaszcz/coqhammer/builds)

CoqHammer video tutorial:
[part 1 (sauto)](https://www.youtube.com/watch?v=0c_utk9bVgU&list=PLXXF_svQE_b-9A5p2OKU7Tjz-NcE7H2xg),
[part 2 (hammer)](https://www.youtube.com/watch?v=EEmpVCSqShA&list=PLXXF_svQE_b_vja6TWFbGNB266Et8m5yC).

Since version 1.3, the CoqHammer system consists of two major separate
components.

1. The `sauto` general proof search tactic for the Calculus of
   Inductive Construction.

2. The `hammer` automated reasoning tool which combines learning from
   previous proofs with the translation of problems to the logics of
   external automated systems and the reconstruction of successfully
   found proofs with the `sauto` procedure.

See the [CoqHammer webpage](https://coqhammer.github.io) for
documentation and installation instructions.

Requirements
------------
- [Coq 8.11](https://github.com/coq/coq)
- for `hammer`: automated provers
  ([Vampire](https://vprover.github.io/download.html),
  [CVC4](http://cvc4.cs.stanford.edu/downloads/),
  [Eprover](http://www.eprover.org), and/or
  [Z3](https://github.com/Z3Prover/z3/releases))

Related projects
----------------

- [SMTCoq](https://smtcoq.github.io) connects Coq with external SAT
  and SMT solvers. In contrast, CoqHammer's target external tools are
  general automated theorem provers (ATPs). CoqHammer never uses the
  "modulo theory" facilities of the SMT solvers it supports (CVC4 and
  Z3), effectively treating them as if they were general ATPs. If what
  you need is predominantly SMT theory reasoning (e.g. reasoning about
  linear arithemtic, bit vectors, arrays) then you might want to try
  SMTCoq.

- [Tactician](https://coq-tactician.github.io) is a tactic learner and
  prover for Coq. It uses machine learning methods to synthesise
  tactic scripts. In contrast, CoqHammer searches for proof terms
  directly at the level of Coq's logic. A limitation of CoqHammer (in
  particular of the `hammer` tactic which relies on first-order ATPs)
  is that it might perform poorly with some features of Coq's
  logic. An approach based on tactic script synthesis is not directly
  limited in this way.

  In particular, by design CoqHammer will never perform induction. If
  you are interested in automatically finding inductive proofs or in
  interactive tactic recommendation, then you might want to try
  Tactician. On the other hand, we expect CoqHammer to be generally
  stronger on the parts of Coq logic it can handle well
  (non-inductive, "close to" first-order, goal-directed proofs).

Copyright and license
---------------------

Copyright (c) 2017-2020, Lukasz Czajka, TU Dortmund University.\
Copyright (c) 2017-2018, Cezary Kaliszyk, University of Innsbruck.

Distributed under the terms of LGPL 2.1, see the file
[LICENSE](LICENSE).

See [CREDITS](CREDITS.md) for a full list of contributors.
