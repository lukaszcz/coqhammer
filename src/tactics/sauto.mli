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
  s_eager_reducing : bool;
  s_eager_rewriting : bool;
  s_eager_inverting : bool;
  s_simple_inverting : bool;
  s_forwarding : bool;
  s_reducing : bool;
  s_rewriting : bool;
  s_heuristic_rewriting : bool;
  s_aggressive_unfolding : bool;
  s_presimplify : bool;
  s_depth_cost_model : bool;
}

val default_s_opts : s_opts

val simple_splitting : s_opts -> unit Proofview.tactic
val eager_inverting : s_opts -> unit Proofview.tactic

val sunfold : bool (* aggressive? *) -> Constant.t -> unit Proofview.tactic
val sunfolding : bool (* aggressive? *) -> unit Proofview.tactic

(* sauto opts cost_limit *)
val sauto : s_opts -> int -> unit Proofview.tactic
val sintuition : s_opts -> unit Proofview.tactic
val ssimpl : s_opts -> unit Proofview.tactic
val qsimpl : s_opts -> unit Proofview.tactic

val logic_constants : Constant.t list
val logic_inductives : inductive list

val add_unfold_hint : Constant.t -> unit
val add_ctrs_hint : inductive -> unit
val add_simple_split_hint : inductive -> unit
val add_case_split_hint : inductive -> unit
val add_inversion_hint : inductive -> unit

val print_actions : s_opts -> unit Proofview.tactic
