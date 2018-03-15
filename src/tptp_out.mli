
open Coqterms

(* write an already translated problem to FOF TPTP format *)
val write_fol_problem : (string -> unit) (* output function *) ->
  (string (* name *) * coqterm (* formula *)) list (* axioms *) ->
  (string (* name *) * coqterm (* formula *)) ->
  unit
