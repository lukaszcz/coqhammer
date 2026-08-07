(* Hook-only entry point for the evaluation harness.  Requiring the tactics
   without importing them loads the sauto machinery needed by hammer_hook's
   reconstruction modes, while leaving the client's tactic grammar and hint
   environment untouched: importing Hammer.Tactics.Tactics would activate
   grammar rules such as csimpl that capture identically named tactics of the
   library under evaluation.  Importing this module activates only the
   hammer/hammer_hook grammar. *)
From Hammer Require Tactics.
Declare ML Module "coq-hammer.plugin".
