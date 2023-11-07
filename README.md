CoqHammer (dev) for Coq master (use other branches for other versions of Coq)

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/lukaszcz/coqhammer/workflows/Docker%20CI/badge.svg?branch=master
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

Requirements
------------
- [Coq master](https://github.com/coq/coq)
- for `hammer`: automated provers
  ([Vampire](https://vprover.github.io/download.html),
  [CVC4](http://cvc4.cs.stanford.edu/downloads/),
  [Eprover](http://www.eprover.org), and/or
  [Z3](https://github.com/Z3Prover/z3/releases))

Copyright and license
---------------------

Copyright (c) 2017-2022, Lukasz Czajka, TU Dortmund University.\
Copyright (c) 2017-2018, Cezary Kaliszyk, University of Innsbruck.

Distributed under the terms of LGPL 2.1, see the file
[LICENSE](LICENSE).

See [CREDITS](CREDITS.md) for a full list of contributors.
