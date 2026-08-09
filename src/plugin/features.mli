
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

(* Predictions are returned in the predictor's ranking order, best first;
   the list length is at most [pred_num]. *)
val run_predict : string (* file name (from `extract`) *) -> hhdef list (* defs *) ->
  int (* pred_num *) -> string (* pred_method *) ->
  hhdef list (* predictions *)

(* Add a few (capped) definitions directly mentioned by the goal or the
   hypotheses to the ML predictions. *)
val add_direct_goal_dependencies : hhdef list (* hyps *) -> hhdef list (* defs *) ->
  hhdef (* goal *) -> hhdef list (* predictions *) -> hhdef list

(* `clean` removes the temporary files created by `extract` *)
val clean : string (* file name  *) -> unit

(* `predict` is essentially: extract + run_predict + clean *)
val predict : hhdef list (* hyps *) -> hhdef list (* defs *) -> hhdef (* goal *) ->
  hhdef list (* predictions  *)

(* `cleanup` resets the feature and dependency cache *)
val cleanup : unit -> unit
