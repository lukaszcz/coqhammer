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

let with_delayed_uconstrs ist cs tac =
  let flags = {
    Pretyping.use_typeclasses = Pretyping.UseTC;
    solve_unification_constraints = true;
    fail_evar = false;
    expand_evars = true;
    program_mode = false;
    polymorphic = false;
  } in
  let cs = List.map (Tacinterp.type_uconstr ~flags ist) cs in
  Tacticals.New.tclMAPDELAYEDWITHHOLES true cs tac

let use_lemmas ist lst =
  let use_tac t =
    Tactics.generalize [t] <*>
      Utils.ltac_eval "Tactics.use_tac" []
  in
  with_delayed_uconstrs ist lst use_tac
