(* sauto -- interface *)

open Names

type 'a soption = SNone | SAll | SSome of 'a | SNoHints of 'a

type s_opts = {
  s_exhaustive : bool;
  s_leaf_tac : unit Proofview.tactic;
  s_simpl_tac : unit Proofview.tactic;
  s_unfolding : Constant.t list soption;
  s_constructors : inductive list soption;
  s_simple_splits : inductive list soption;
  s_case_splits : inductive list soption;
  s_inversions : inductive list soption;
  s_rew_bases : string list;
  s_bnat_reflect : bool;
  s_case_splitting : bool;
  s_simple_inverting : bool;
  s_forwarding : bool;
}

val default_s_opts : s_opts

(* sauto opts depth_limit *)
val sauto : s_opts -> int -> unit Proofview.tactic

val ssimpl : s_opts -> unit Proofview.tactic
