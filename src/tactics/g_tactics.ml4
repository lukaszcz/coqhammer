DECLARE PLUGIN "hammer_tactics"

open Ltac_plugin
open Stdarg
open Tacarg
open Sauto

module Utils = Hhutils

let default_sauto_depth = 5

let get_opt opt def = match opt with Some x -> x | None -> def

let rec destruct_constr t =
  let open Constr in
  let open EConstr in
  match kind Evd.empty t with
  | App(i, args) ->
     begin
       match kind Evd.empty i with
       | Ind(ind, _) when ind = Utils.get_inductive "pair" ->
          begin
            match Array.to_list args with
            | [_; _; t1; t2] ->
               destruct_constr t1 @ destruct_constr t2
            | _ -> [t]
          end
       | _ -> [t]
     end
  | _ -> [t]

let get_s_opts unfoldings =
  let cdefault = Utils.get_constr "Tactics.default" in
  let chints = Utils.get_constr "Tactics.hints" in
  let cnone = Utils.get_constr "Tactics.none" in
  let cnohints = Utils.get_constr "Tactics.nohints" in
  let to_const t =
    let open Constr in
    let open EConstr in
    match kind Evd.empty t with
    | Const(c, _) -> c
    | _ -> failwith "sauto: unfolding: not a constant"
  in
  let unfoldings = destruct_constr unfoldings in
  let get_unfoldings opts =
    match unfoldings with
    | [h] when h = cdefault -> opts
    | [h] when h = chints -> { opts with s_unfolding = SSome [] }
    | [h] when h = cnone -> { opts with s_unfolding = SNone }
    | _ ->
       let b_nohints = List.mem cnohints unfoldings in
       let lst = List.map to_const unfoldings in
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
| [ "sauto_gen" int_or_var_opt(n) "using" constr(lemmas) "unfolding" constr(unfoldings) ] -> [
  if lemmas = Utils.get_constr "Tactics.default" then
    sauto (get_s_opts unfoldings) (get_opt n default_sauto_depth)
  else
    Proofview.tclTHEN
      (Tactics.generalize (destruct_constr lemmas))
      (sauto (get_s_opts unfoldings) (get_opt n default_sauto_depth))
]
END
