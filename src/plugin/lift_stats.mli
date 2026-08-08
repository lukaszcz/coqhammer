(* Diagnostic counters for lifted symbols; see lift_stats.ml.  Every entry
   point is a no-op unless COQHAMMER_LIFT_STATS names a directory. *)

val enabled : unit -> bool

val count : string -> unit
val add : string -> int -> unit

(* Registers a supplier of counters owned by another module.  The suppliers are
   consulted when the accumulated counters are written out. *)
val add_source : (unit -> (string * int) list) -> unit
