
open Hh_term

val extract_eprover_data : string (* file name *) -> string list (* deps *) * string list (* defs *)
val extract_vampire_data : string (* file name *) -> string list (* deps *) * string list (* defs *)
val extract_z3_data : string (* file name *) -> string list (* deps *) * string list (* defs *)

val write_atp_file : string (* file name *) -> hhdef list (* filtered defs *) ->
  hhdef list (* hyps *) -> hhdef list (* all defs *) -> hhdef (* goal *) -> unit

val predict : hhdef list (* filtered defs *) -> hhdef list (* hyps *) ->
  hhdef list (* all defs *) -> hhdef (* goal *) ->
  string list (* deps *) * string list (* defs *)
