(* Typing and type destruction *)

open Coqterms

type coqvalue

val eval : coqterm -> coqvalue
val reify : coqvalue -> coqterm

(* Constructorhood is answered from the definitions hash and cached, so the
   cache belongs to the same lifetime as the hash. *)
val clear_constructor_hash : unit -> unit

val check_prop : coqcontext -> coqterm -> bool
val check_proof_var : coqcontext -> string (* variable name *) -> bool
val check_type_target_is_prop : coqterm (* type *) -> bool
val check_type_target_is_type : coqterm (* type *) -> bool

(* In e.g. Pi x : alpha. Pi y : beta . c x y: args = [(x, alpha); (y, beta)]; target = c x y;
   app target = c; targs = [x; y] *)
val destruct_type : coqterm (* type *) -> coqterm (* target *) * (string * coqterm) list (* args *)
val destruct_type_app : coqterm (* type *) ->
  coqterm (* app target *) * coqterm list (* targs *) * (string * coqterm) list (* args *)

val get_type_args : coqterm (* type *) -> (string * coqterm) list
val get_type_target : coqterm (* type *) -> coqterm
val get_type_app_target : coqterm (* type *) -> coqterm
