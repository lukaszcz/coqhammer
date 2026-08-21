
open Hh_term

val get_def_features : hhdef (* def *) -> string list
val get_def_features_cached : hhdef (* def *) -> string list
val get_goal_features : hhdef list (* hyps *) -> hhdef (* goal *) -> string list (* features *)

type selection_ctx

type selection_metadata = {
  def_candidates : int;
  seed_min_occ : int option;
  seed_median_occ : int option;
  forced_slots : int;
}

(* Build the per-invocation selection context, including the filtered
   definition lookup table used by extraction and prediction. The goal seed,
   occurrence table and ranked definitional candidates remain lazy. *)
val make_selection_ctx : hhdef list (* hyps *) -> hhdef list (* defs *) ->
  hhdef (* goal *) -> selection_ctx

(* Eagerly prepare enabled definitional slots. Every caller that goes on to
   call [extract] must call this first: [extract] releases the converted
   type/body trees that ranking the definitional candidates reads, so a
   [merge_def_slots] or [selection_metadata] forcing the ranking afterwards
   would convert every candidate whose size is not cached yet a second time.
   GS mode also calls this in the parent process so every candidate and
   reconstruction retry shares the work. This does not force the lazy fields
   when [DefinitionPremises] is zero. *)
val prepare_def_slots : selection_ctx -> unit

(* Derive eval metadata from the same seed, occurrence table and ranked
   definitional candidates used by selection. Seed statistics include only
   accessible, nontrivial seed constants. An empty such seed has [None] for
   both occurrence fields. For an even-sized seed, [seed_median_occ] is the
   lower of the two middle values after sorting. [forced_slots] is exactly the
   merge's [min(|D|, DefinitionPremises, ceil(n / 8))]; it is zero when [n] or
   [DefinitionPremises] is non-positive, and its ceiling calculation cannot
   overflow. *)
val selection_metadata : selection_ctx -> int (* premise budget *) ->
  selection_metadata

(* Construct the predictor's conjecture features. Positive
   [DefinitionFeatures] values add the plain dependencies of seed definitions
   whose occurrence count is at most the configured value. At zero this is
   exactly [get_goal_features] and does not force lazy context fields. *)
val get_query_features : selection_ctx -> hhdef list (* hyps *) ->
  hhdef (* goal *) -> string list (* features *)

(* `extract` extracts the features and dependencies into temporary
   files (to be used by the `predict` command). *)
val extract : selection_ctx -> hhdef list (* hyps *) -> hhdef (* goal *) ->
  string (* (temporary) file name *)

(* `choose_given_lemmas` selects the premises for the ATPs based on
   the given lemmas: the lemmas themselves plus the definitions
   directly referenced by the goal, the hypotheses or the lemmas.
   Callers that accept arbitrary user lemmas should append lemmas missing from
   the search results to the defs list before calling this function. *)
val choose_given_lemmas : hhdef list (* hyps *) -> hhdef list (* defs *) ->
  hhdef list (* lemmas *) -> hhdef (* goal *) ->
  hhdef list (* premises *)

(* Look up the predictor's output in the context's filtered definition table.
   Predictions are returned in the predictor's ranking order, best first;
   unknown names are dropped and the list length is at most [pred_num]. *)
val run_predict : selection_ctx -> string (* file name (from `extract`) *) ->
  int (* pred_num *) -> string (* pred_method *) ->
  hhdef list (* predictions *)

(* Reserve up to [DefinitionPremises], [ceil(n / 8)] definitional slots
   inside the premise budget [n]. Non-forced predictions are deduplicated by
   name without changing rank order before truncation. For positive [n], a
   zero option returns predictions exactly unchanged without forcing lazy
   context fields; non-positive [n] returns the empty list without forcing
   them. *)
val merge_def_slots : selection_ctx -> int (* premise budget *) ->
  hhdef list (* ranked predictions *) -> hhdef list

(* `clean` removes the temporary files created by `extract` *)
val clean : string (* file name  *) -> unit

(* [predict] is extract + run_predict + merge + clean over one context. Like
   any other path that reaches [extract], its caller must have run
   [prepare_def_slots] on the context first. *)
val predict : selection_ctx -> hhdef list (* hyps *) -> hhdef (* goal *) ->
  hhdef list (* predictions *)

(* `cleanup` resets the feature, dependency and term-size caches *)
val cleanup : unit -> unit
