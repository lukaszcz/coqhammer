(* Lexicographic path order on terms *)

open Names

val gt : (Constant.t -> Constant.t -> bool) -> Evd.evar_map -> EConstr.t -> EConstr.t -> bool

val const_gt : Constant.t -> Constant.t -> bool

val lpo : Evd.evar_map -> EConstr.t -> EConstr.t -> bool

val clear_cache : unit -> unit
