(* Classification of the premise names an ATP reports back.  The names are the
   ones tptp_out emitted, so recovering the Coq constant behind one is a matter
   of stripping the axiom-kind prefix and the suffix that a split axiom carries.
   This module holds the part of that decoding which needs nothing from Rocq, so
   that it can be exercised by a plain OCaml unit test (tests/unit). *)

val is_good_dep : string -> bool

val remove_duplicates : string list -> string list

(* Drop the suffix a split axiom carries: $_def_c$conj -> c *)
val strip_dollar_suffix : string -> string

(* The type a case axiom is about, with any number of $_case_ prefixes peeled
   off, or "$none" when the name carries no subject. *)
val case_name_subject : string -> string

val get_deps : string list -> string list
val get_defs : string list -> string list
val get_typings : string list -> string list
val get_cases : string list -> string list
val get_inversions : string list -> string list
val get_injections : string list -> string list
val get_discrims : string list -> (string * string) list
