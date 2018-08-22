(* Translation from Coq to FOL *)

open Hh_term
open Coqterms

val reinit : hhdef list -> unit
val translate : string (* name *) -> (string (* name *) * coqterm (* formula *)) list (* axioms *)
val retranslate : string list (* names *) -> unit
val get_axioms : string list (* definition names *) ->
  (string (* name *) * coqterm (* formula *)) list (* axioms *)
val remove_def : string (* name *) -> unit
val cleanup : unit -> unit
val write_problem : string (* file name *) -> string (* conjecture name *) ->
  string list (* dependency names  *) -> unit
