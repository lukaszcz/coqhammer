(* Hook-only entry point for the evaluation harness.  The grammar an ML module
   declares is import-scoped, so a bare Require of Hammer.Tactics.Tactics
   loads the sauto machinery without putting a single sauto tactic in the
   client's grammar: importing Tactics instead activates rules such as csimpl,
   which then capture identically named tactics of the library under
   evaluation.  hammer_hook's reconstruction modes still reach that machinery,
   because they drive sauto from OCaml and resolve the few Ltac names they
   need through the nametab, neither of which goes through tactic syntax.
   Importing this module activates the coq-hammer plugin's own grammar, and
   only that.

   What the bare Require does not isolate are hints: the global hints of
   everything Tactics.v requires -- Eqdep, Program.Equality, List, ... -- reach
   the client at Require time (about fifteen extra heads in core), and Import
   adds none beyond them.  Keeping that transitive Require set small is the
   only lever here; see Reflect.v, which dropped ssreflect for exactly this
   reason. *)
From Hammer Require Tactics.
Declare ML Module "coq-hammer.plugin".
