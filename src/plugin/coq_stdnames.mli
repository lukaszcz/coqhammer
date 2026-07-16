(** Recognition of canonical Rocq stdlib constants under their historical
    root prefixes (Corelib / Coq / Stdlib). *)

val is_canonical_constant : string list -> string -> string -> bool
(** [is_canonical_constant prefixes basename name] holds when [name] is
    [prefix ^ "." ^ basename] for some listed [prefix]. *)

val is_init_logic : string -> string -> bool
val is_init_datatypes : string -> string -> bool
val is_init_wf : string -> string -> bool
val is_init_specif : string -> string -> bool
val is_jmeq : string -> string -> bool
val is_program_wf : string -> string -> bool
