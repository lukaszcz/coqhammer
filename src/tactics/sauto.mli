(* sauto -- interface *)

open Names

type 'a soption = SNone | SAll | SSome of 'a

type s_opts = {
  s_exhaustive : bool;
  s_hints : bool;
  s_leaf_tac : unit Proofview.tactic;
  s_leaf_nolia_tac : unit Proofview.tactic;
  s_solve_tac : unit Proofview.tactic;
  s_simpl_tac : unit Proofview.tactic;
  s_simpl_nolia_tac : unit Proofview.tactic;
  s_ssimpl_tac : unit Proofview.tactic;
  s_ssimpl_nolia_tac : unit Proofview.tactic;
  s_unfolding : Constant.t list soption;
  s_constructors : inductive list soption;
  s_simple_splits : inductive list soption;
  s_case_splits : inductive list soption;
  s_inversions : inductive list soption;
  s_rew_bases : string list;
  s_hint_bases : Hints.hint_db list;
  s_reflect : bool;
  s_eager_case_splitting : bool;
  s_eager_reducing : bool;
  s_eager_rewriting : bool;
  s_eager_inverting : bool;
  s_simple_inverting : bool;
  s_forwarding : bool;
  s_reducing : bool;
  s_rewriting : bool;
  s_heuristic_rewriting : bool;
  s_aggressive_unfolding : bool;
  s_sapply : bool;
  s_depth_cost_model : bool;
  s_limit : int;
  s_prerun : bool;
  s_destruct_proj1_sigs : bool;
  s_lia : bool;
}

val default_s_opts : unit -> s_opts
val hauto_s_opts : unit -> s_opts
val qauto_s_opts : unit -> s_opts

val simple_splitting : s_opts -> unit Proofview.tactic
val eager_inverting : s_opts -> unit Proofview.tactic

val sunfold : bool (* aggressive? *) -> Constant.t -> unit Proofview.tactic
val sunfolding : bool (* aggressive? *) -> unit Proofview.tactic

val sauto : s_opts -> unit Proofview.tactic
val sintuition : s_opts -> unit Proofview.tactic
val ssimpl : s_opts -> unit Proofview.tactic
val qsimpl : s_opts -> unit Proofview.tactic
val scrush : s_opts -> unit Proofview.tactic
val fcrush : s_opts -> unit Proofview.tactic
val ecrush : s_opts -> unit Proofview.tactic
val sblast : s_opts -> unit Proofview.tactic
val qblast : s_opts -> unit Proofview.tactic

val logic_constants : Constant.t list
val logic_inductives : inductive list

val add_unfold_hint : Constant.t -> unit
val add_ctrs_hint : inductive -> unit
val add_simple_split_hint : inductive -> unit
val add_case_split_hint : inductive -> unit
val add_inversion_hint : inductive -> unit

val print_actions : s_opts -> unit Proofview.tactic

val unshelve : 'a Proofview.tactic -> unit Proofview.tactic
val usolve : 'a Proofview.tactic -> unit Proofview.tactic
