(* sauto -- interface *)

type 'a soption = SNone | SAll | SSome of 'a

type s_opts = {
  s_exhaustive : bool;
  s_leaf_tac : unit Proofview.tactic;
  s_inversions : string list soption;
  s_simple_inverting : bool;
  s_forwarding : bool;
}

val default_s_opts : s_opts

(* sauto opts depth_limit *)
val sauto : s_opts -> int -> unit Proofview.tactic
