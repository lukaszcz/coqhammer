open Ltac_plugin
open Proofview.Notations
open Hammer_lib
open Hammer_errors
open Sauto
open Tacopts

module Utils = Hhutils

let try_usolve (opts : s_opts) (lst : sopt_t list) (ret : s_opts -> unit Proofview.tactic)
      (msg : string) : unit Proofview.tactic =
  try_tactic begin fun () ->
    usolve @@
      interp_opts opts lst
        begin fun opts ->
          Proofview.tclORELSE (ret opts)
            (fun _ -> Tacticals.New.tclZEROMSG (Pp.str msg))
        end
  end

let use_lemmas lst =
  let use_tac t =
    Utils.ltac_eval "Tactics.use_tac" [Tacinterp.Value.of_constr t]
  in
  List.fold_left (fun tac t -> tac <*> use_tac t) Tacticals.New.tclIDTAC lst
