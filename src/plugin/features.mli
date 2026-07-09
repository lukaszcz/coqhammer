
open Hh_term

val get_def_features : hhdef (* def *) -> string list
val get_def_features_cached : hhdef (* def *) -> string list
val get_goal_features : hhdef list (* hyps *) -> hhdef (* goal *) -> string list (* features *)

(* `extract` extracts the features and dependencies into temporary
   files (to be used by the `predict` command) *)
val extract : hhdef list (* hyps *) -> hhdef list (* defs *) -> hhdef (* goal *) ->
  string (* (temporary) file name *)

(* `choose_given_lemmas` selects the premises for the ATPs based on
   the given lemmas: the lemmas themselves plus the definitions
   directly referenced by the goal, the hypotheses or the lemmas.
   Callers that accept arbitrary user lemmas should append lemmas missing from
   the search results to the defs list before calling this function. *)
val choose_given_lemmas : hhdef list (* hyps *) -> hhdef list (* defs *) ->
  hhdef list (* lemmas *) -> hhdef (* goal *) ->
  hhdef list (* premises *)

val run_predict : string (* file name (from `extract`) *) -> hhdef list (* defs *) ->
  int (* pred_num *) -> string (* pred_method *) ->
  hhdef list (* predictions *)

(* Always keep definitions directly mentioned by the goal/hypotheses alongside
   ML predictions. *)
val add_direct_goal_dependencies : hhdef list (* hyps *) -> hhdef list (* defs *) ->
  hhdef (* goal *) -> hhdef list (* predictions *) -> hhdef list

(* `clean` removes the temporary files created by `extract` *)
val clean : string (* file name  *) -> unit

(* `predict` is essentially: extract + run_predict + clean *)
val predict : hhdef list (* hyps *) -> hhdef list (* defs *) -> hhdef (* goal *) ->
  hhdef list (* predictions  *)

(* `cleanup` resets the feature and dependency cache *)
val cleanup : unit -> unit
