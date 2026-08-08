(* Stub replacement for src/lib/hammer_errors.ml.

   The real module is built against Rocq (Feedback, Pp, CErrors, Proofview),
   which the standalone unit tests cannot link.  The plugin modules under test
   here use nothing from it but the HammerError exception, so the stub declares
   exactly the exceptions and nothing else. *)

exception HammerError of string
exception HammerFailure of string
exception HammerTacticError of string
