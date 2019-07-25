open Names
open Ltac_plugin

val intern_constr : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr ->
  Evd.evar_map * EConstr.t

val exists_global : string -> bool

val get_constr : string -> EConstr.t

val get_inductive : string -> inductive

val get_ind_name : inductive -> string

val get_ind_nparams : inductive -> int

val close : (Name.t * 'a * 'a -> 'a) -> (Name.t * 'a) list -> 'a -> 'a

val get_tactic : string -> Tacexpr.ltac_constant

val get_tacexpr : string -> Tacexpr.glob_tactic_arg list -> Tacexpr.glob_tactic_expr

val ltac_apply : string -> Tacexpr.glob_tactic_arg list -> unit Proofview.tactic

val ltac_eval : string -> Tacinterp.Value.t list -> unit Proofview.tactic

val get_hyps : Proofview.Goal.t -> (Id.t * EConstr.t) list

val drop_lambdas : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val take_lambdas : Evd.evar_map -> int -> EConstr.t -> (Name.t * EConstr.t) list

val drop_prods : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val take_prods : Evd.evar_map -> int -> EConstr.t -> (Name.t * EConstr.t) list

val drop_all_lambdas : Evd.evar_map -> EConstr.t -> EConstr.t

val take_all_lambdas : Evd.evar_map -> EConstr.t -> (Name.t * EConstr.t) list

val drop_all_prods : Evd.evar_map -> EConstr.t -> EConstr.t

val take_all_prods : Evd.evar_map -> EConstr.t -> (Name.t * EConstr.t) list

val map_fold_constr : (int -> 'a -> EConstr.t -> 'a * EConstr.t) ->
                      'a -> Evd.evar_map -> EConstr.t ->
                      'a * EConstr.t

val map_constr : (int -> EConstr.t -> EConstr.t) -> Evd.evar_map -> EConstr.t -> EConstr.t

val fold_constr : (int -> 'a -> EConstr.t -> 'a) -> 'a -> Evd.evar_map -> EConstr.t -> 'a

val map_fold_constr_ker : (int -> 'a -> Constr.t -> 'a * Constr.t) ->
                          'a -> Constr.t ->
                          'a * Constr.t

val map_constr_ker : (int -> Constr.t -> Constr.t) -> Constr.t -> Constr.t

val fold_constr_ker : (int -> 'a -> Constr.t -> 'a) -> 'a -> Constr.t -> 'a

val rel_occurs : Evd.evar_map -> EConstr.t -> int list -> bool

val shift_binders_down : Evd.evar_map -> int -> EConstr.t -> EConstr.t

val shift_binders_up : Evd.evar_map -> int -> EConstr.t -> EConstr.t
