(* sauto -- interface *)

type sauto_opts = {
  inversions : string list;
}

val sauto : sauto_opts -> unit Proofview.tactic
