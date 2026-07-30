open Hh_term

(* info about what the ATP used in the proof *)
type atp_info = {
  deps : string list; (* dependencies: lemmas, theorems *)
  defs : string list; (* definitions (non-propositional) *)
  typings : string list;
  cases : string list;
  inversions : string list;
  injections : string list;
  discrims : (string * string) list;
  types : string list; (* (co)inductive types *)
}

val prn_atp_info : atp_info -> string

val extract_eprover_data : string (* file name *) -> atp_info
val extract_vampire_data : string (* file name *) -> atp_info
val extract_z3_data : string (* file name *) -> atp_info
val extract_cvc4_data : string (* file name *) -> atp_info

val write_atp_file : string (* file name *) -> hhdef list (* filtered deps *) ->
  hhdef list (* hyps *) -> hhdef list (* all deps *) -> hhdef (* goal *) -> unit

val minimize : atp_info ->
  hhdef list (* hyps *) -> hhdef list (* all deps *) -> hhdef (* goal *) ->
  atp_info

(* Runs the enabled ATPs and returns the name of the one that succeeded
   together with what it used.  Reporting is left to the caller: the greedy
   schedule runs each prover in a forked child, so only the parent knows which
   result was actually taken. *)
val predict : hhdef list (* filtered deps *) -> hhdef list (* hyps *) ->
  hhdef list (* all deps *) -> hhdef (* goal *) ->
  string (* prover that succeeded *) * atp_info

(* Detect ATPs and set the hammer options in opt.ml (?_enabled)
   accordingly. Returns true if at least one prover found, false
   otherwise. *)
val detect : unit -> bool
