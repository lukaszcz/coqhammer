(* sauto -- interface *)

type sauto_opts = {
  exhaustive : bool;
  leaf_tac : unit Proofview.tactic;
  inversions : string list;
}

val default_sauto_opts : sauto_opts

(* sauto opts depth_limit *)
val sauto : sauto_opts -> int -> unit Proofview.tactic
