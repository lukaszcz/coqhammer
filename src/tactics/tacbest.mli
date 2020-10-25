open Tacopts

val best_tactics : sopt_t list -> (unit Proofview.tactic * string) list list
val hbest_tactics : sopt_t list -> (unit Proofview.tactic * string) list list
val sbest_tactics : sopt_t list -> (unit Proofview.tactic * string) list list

val hammer_pretactics : unit -> (unit Proofview.tactic * string) list

val run_best :
  int (* time limit *) ->
  (unit Proofview.tactic * string) list (* tactic list *) ->
  sopt_t list (* sauto options *) ->
  (string -> unit Proofview.tactic -> unit Proofview.tactic) (* success continuation *) ->
  (unit -> unit Proofview.tactic) (* failure continuation *) ->
  unit Proofview.tactic

val find_best_tactic :
  (unit Proofview.tactic * string) list list -> (* tactic batches to try *)
  sopt_t list -> (* sauto options *)
  string -> (* tactic name ("best", "hammer", ...) *)
  unit Proofview.tactic
