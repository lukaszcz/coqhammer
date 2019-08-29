DECLARE PLUGIN "hammer_tactics"

open Names
open Ltac_plugin
open Stdarg
open Tacarg
open Sauto

module Utils = Hhutils

let default_sauto_depth = 5

let get_opt opt def = match opt with Some x -> x | None -> def

let get_s_opts unfoldings =
  let get_unfoldings opts =
    match unfoldings with
    | [h] when Id.to_string h = "default" -> opts
    | [h] when Id.to_string h = "none" -> { opts with s_unfolding = SNone }
    | _ ->
       let b_nohints = List.mem "nohints" (List.map Id.to_string unfoldings) in
       let unfoldings = List.filter (fun x -> Id.to_string x <> "nohints") unfoldings in
       let lst = List.map (fun x -> Utils.get_const (Id.to_string x)) unfoldings in
       { opts with s_unfolding = if b_nohints then SNoHints lst else SSome lst }
  in
  get_unfoldings default_s_opts

TACTIC EXTEND Hammer_simple_splitting
| [ "simple_splitting" ] -> [ simple_splitting default_s_opts ]
END

TACTIC EXTEND Hammer_sauto_gen_1
| [ "sauto_gen" int_or_var_opt(n) ] -> [ sauto default_s_opts (get_opt n default_sauto_depth) ]
END

TACTIC EXTEND Hammer_ssimpl_gen
| [ "ssimpl_gen" ] -> [
  ssimpl { default_s_opts with s_simpl_tac = Utils.ltac_apply "Tactics.ssolve" [] }
]
END

TACTIC EXTEND Hammer_sauto_gen_2
| [ "sauto_gen" int_or_var_opt(n) "using" ne_constr_list_sep(lemmas, ",") "unfolding" ne_ident_list_sep(unfoldings,",") ] -> [
  if lemmas = [Utils.get_constr "Tactics.default"] then
    sauto (get_s_opts unfoldings) (get_opt n default_sauto_depth)
  else
    Proofview.tclTHEN
      (Tactics.generalize lemmas)
      (sauto (get_s_opts unfoldings) (get_opt n default_sauto_depth))
]
END
