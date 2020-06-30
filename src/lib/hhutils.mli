open Names
open Ltac_plugin

val intern_constr : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr ->
  Evd.evar_map * EConstr.t

val exists_global : string -> bool

val get_constr : string -> EConstr.t

val get_global : string -> GlobRef.t

val get_global_from_id : Id.t -> GlobRef.t

val get_inductive : string -> inductive

val get_inductive_from_id : Id.t -> inductive

val get_inductive_from_qualid : Libnames.qualid -> inductive

val get_const : string -> Constant.t

val get_const_from_id : Id.t -> Constant.t

val get_const_from_qualid : Libnames.qualid -> Constant.t

val get_ind_name : inductive -> string

val get_ind_nparams : inductive -> int

val get_ind_constrs : inductive -> Constr.t list

val get_ind_nconstrs : inductive -> int

val is_indexed_ind : inductive -> bool

val close : (Name.t * 'a * 'a -> 'a) -> (Name.t * 'a) list -> 'a -> 'a

val get_tactic : string -> Tacexpr.ltac_constant

val get_tacexpr : string -> Tacexpr.glob_tactic_arg list -> Tacexpr.glob_tactic_expr

val ltac_apply : string -> Tacexpr.glob_tactic_arg list -> unit Proofview.tactic

val ltac_eval : string -> Tacinterp.Value.t list -> unit Proofview.tactic

val get_hyps : Proofview.Goal.t -> (Id.t * EConstr.t) list

val drop_lambdas : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val take_lambdas : Evd.evar_map -> int -> EConstr.t -> (Name.t Context.binder_annot * EConstr.t) list

val drop_prods : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val take_prods : Evd.evar_map -> int -> EConstr.t -> (Name.t Context.binder_annot * EConstr.t) list

val drop_all_lambdas : Evd.evar_map -> EConstr.t -> EConstr.t

val take_all_lambdas : Evd.evar_map -> EConstr.t -> (Name.t Context.binder_annot * EConstr.t) list

val drop_all_prods : Evd.evar_map -> EConstr.t -> EConstr.t

val take_all_prods : Evd.evar_map -> EConstr.t -> (Name.t Context.binder_annot * EConstr.t) list

val destruct_app : Evd.evar_map -> EConstr.t -> EConstr.t (* head *) * EConstr.t list (* args *)

val destruct_app_red : Evd.evar_map -> EConstr.t -> EConstr.t (* head *) * EConstr.t (* head after red *) * EConstr.t list (* args after red *)

val destruct_prod : Evd.evar_map -> EConstr.t ->
  (Name.t Context.binder_annot * EConstr.t) list (* prods *) * EConstr.t (* head *) * EConstr.t list (* args *)

val destruct_prod_red : Evd.evar_map -> EConstr.t ->
  (Name.t Context.binder_annot * EConstr.t) list (* prods *) * EConstr.t (* head *) * EConstr.t (* head after red *) * EConstr.t list (* args after red *)

val map_fold_constr : (int -> 'a -> EConstr.t -> 'a * EConstr.t) ->
                      'a -> Evd.evar_map -> EConstr.t ->
                      'a * EConstr.t

val map_constr : (int -> EConstr.t -> EConstr.t) -> Evd.evar_map -> EConstr.t -> EConstr.t

val fold_constr : (int -> 'a -> EConstr.t -> 'a) -> 'a -> Evd.evar_map -> EConstr.t -> 'a

val fold_constr_shallow : ('a -> EConstr.t -> 'a) -> 'a -> Evd.evar_map -> EConstr.t -> 'a

val map_fold_constr_ker : (int -> 'a -> Constr.t -> 'a * Constr.t) ->
                          'a -> Constr.t ->
                          'a * Constr.t

val map_constr_ker : (int -> Constr.t -> Constr.t) -> Constr.t -> Constr.t

val fold_constr_ker : (int -> 'a -> Constr.t -> 'a) -> 'a -> Constr.t -> 'a

(* De Bruijn indices in Rel are 1-based *)
val rel_occurs : Evd.evar_map -> EConstr.t -> int list -> bool

val shift_binders_down : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val shift_binders_up : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val is_False : Evd.evar_map -> EConstr.t -> bool

val is_atom : Evd.evar_map -> EConstr.t -> bool

val is_ind_atom : Evd.evar_map -> EConstr.t -> bool

val is_product : Evd.evar_map -> EConstr.t -> bool

val get_app_head : Evd.evar_map -> EConstr.t -> EConstr.t

val get_head : Evd.evar_map -> EConstr.t -> EConstr.t

val get_app_head_red : Evd.evar_map -> EConstr.t -> EConstr.t

val get_head_red : Evd.evar_map -> EConstr.t -> EConstr.t

val print_constr : Evd.evar_map -> EConstr.t -> unit

val constr_to_string : Evd.evar_map -> EConstr.t -> string

type hint

val hint_priority : hint -> int
val hint_tactic : hint -> EConstr.t -> unit Proofview.tactic
val hint_to_string : hint -> string
val find_hints : Hints.hint_db -> Id.Pred.t -> Evd.evar_map -> EConstr.t -> hint list
