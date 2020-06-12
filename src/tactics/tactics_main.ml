open Proofview.Notations
open Hammer_errors
open Sauto

module Utils = Hhutils

type sopt_t =
  SONop
| SOUse of Constrexpr.constr_expr list
| SOGen of Constrexpr.constr_expr list
| SOUnfold of Libnames.qualid list
| SOUnfoldAll
| SOUnfoldNone
| SOInv of Libnames.qualid list
| SOInvAll
| SOInvNone
| SOCtrs of Libnames.qualid list
| SOCtrsAll
| SOCtrsNone
| SOCaseSplit of Libnames.qualid list
| SOCaseSplitAll
| SOCaseSplitNone
| SOSimpleSplit of Libnames.qualid list
| SOSimpleSplitAll
| SOSimpleSplitNone
| SORewBases of string list
| SORewBasesAll
| SORewBasesNone
| SOForward of bool
| SOEagerCaseSplit of bool
| SOSimpleInvert of bool
| SOEagerInvert of bool
| SOEagerReduce of bool
| SOEagerRewrite of bool
| SOHeuristicRewrite of bool
| SORewrite of bool
| SOReflect of bool
| SOReduce of bool
| SOSapply of bool
| SOLimit of int
| SODepth of int
| SOExhaustive of bool
| SOAlwaysApply of bool

let const_of_qualid q =
  catch_errors (fun () -> Utils.get_const_from_qualid q)
    (fun _ ->
      raise (HammerTacticError ("not a constant: " ^ Libnames.string_of_qualid q)))

let inductive_of_qualid q =
  catch_errors (fun () -> Utils.get_inductive_from_qualid q)
    (fun _ ->
      raise (HammerTacticError ("not an inductive type: " ^ Libnames.string_of_qualid q)))

let sopt_append sc lst2 =
  match sc with
  | SSome lst1 -> SSome (lst1 @ lst2)
  | _ -> SSome lst2

let use_constrs lems =
  Tactics.generalize lems <*>
    Tacticals.New.tclDO (List.length lems)
      (Proofview.tclORELSE
         (Tactics.intro_move None Logic.MoveFirst)
         (fun _ -> Tactics.intro))

let gen_constrs lems =
  Tactics.generalize lems

let interp_use use ret opts lst env sigma =
  let (sigma, lst) =
    List.fold_left
      begin fun (sigma, acc) t ->
        let (sigma', t') = Utils.intern_constr env sigma t in
        (sigma', t' :: acc)
      end
      (sigma, [])
      lst
  in
  let (lems, ctrs) =
    List.fold_left
      begin fun (lems, ctrs) t ->
        let open Constr in
        let open EConstr in
        match kind sigma t with
        | Ind(ind, _) -> (lems, ind :: ctrs)
        | _ -> (t :: lems, ctrs)
      end
      ([], [])
      lst
  in
  let opts =
    if ctrs <> [] then
      { opts with
        s_constructors = sopt_append opts.s_constructors ctrs }
    else
      opts
  in
  use lems <*> ret opts

let interp_opt ret opt opts =
  match opt with
  | SONop -> ret opts
  | SOUse lst ->
     Proofview.Goal.enter begin fun gl ->
       let sigma = Proofview.Goal.sigma gl in
       let env = Proofview.Goal.env gl in
       interp_use use_constrs ret opts lst env sigma
     end
  | SOGen lst ->
     Proofview.Goal.enter begin fun gl ->
       let sigma = Proofview.Goal.sigma gl in
       let env = Proofview.Goal.env gl in
       interp_use gen_constrs ret opts lst env sigma
     end
  | SOUnfold lst ->
     let lst = List.map const_of_qualid lst in
     ret { opts with s_unfolding = sopt_append opts.s_unfolding lst }
  | SOUnfoldAll ->
     ret { opts with s_unfolding = SAll }
  | SOUnfoldNone ->
     ret { opts with s_unfolding = SNone }
  | SOInv lst ->
     let lst = List.map inductive_of_qualid lst in
     ret { opts with s_inversions = sopt_append opts.s_inversions lst }
  | SOInvAll ->
     ret { opts with s_inversions = SAll }
  | SOInvNone ->
     ret { opts with s_inversions = SNone }
  | SOCtrs lst ->
     let lst = List.map inductive_of_qualid lst in
     ret { opts with s_constructors = sopt_append opts.s_constructors lst }
  | SOCtrsAll ->
     ret { opts with s_constructors = SAll }
  | SOCtrsNone ->
     ret { opts with s_constructors = SNone }
  | SOCaseSplit lst ->
     let lst = List.map inductive_of_qualid lst in
     ret { opts with s_case_splits = sopt_append opts.s_case_splits lst }
  | SOCaseSplitAll ->
     ret { opts with s_case_splits = SAll }
  | SOCaseSplitNone ->
     ret { opts with s_case_splits = SNone }
  | SOSimpleSplit lst ->
     let lst = List.map inductive_of_qualid lst in
     ret { opts with s_simple_splits = sopt_append opts.s_simple_splits lst }
  | SOSimpleSplitAll ->
     ret { opts with s_simple_splits = SAll }
  | SOSimpleSplitNone ->
     ret { opts with s_simple_splits = SNone }
  | SORewBases lst ->
     ret { opts with s_rew_bases = opts.s_rew_bases @ lst }
  | SORewBasesAll -> (* TODO *)
     ret { opts with s_rew_bases = [] }
  | SORewBasesNone ->
     ret { opts with s_rew_bases = ["nohints"] }
  | SOForward b ->
     ret { opts with s_forwarding = b }
  | SOEagerCaseSplit b ->
     ret { opts with s_eager_case_splitting = b }
  | SOSimpleInvert b ->
     ret { opts with s_simple_inverting = b }
  | SOEagerInvert b ->
     ret { opts with s_eager_inverting = b }
  | SOEagerReduce b ->
     ret { opts with s_eager_reducing = b }
  | SOEagerRewrite b ->
     ret { opts with s_eager_rewriting = b }
  | SOHeuristicRewrite b ->
     ret { opts with s_heuristic_rewriting = b }
  | SORewrite b ->
     if b then
       ret { opts with s_rewriting = true }
     else
       ret { opts with s_rewriting = false;
                       s_eager_rewriting = false;
                       s_heuristic_rewriting = false }
  | SOReflect b ->
     ret { opts with s_reflect = true }
  | SOReduce b ->
     if b then
       ret { opts with s_reducing = true }
     else
       ret { opts with s_reducing = false; s_eager_reducing = false }
  | SOSapply b ->
     ret { opts with s_sapply = true }
  | SOLimit n ->
     ret { opts with s_limit = n; s_depth_cost_model = false }
  | SODepth n ->
     ret { opts with s_limit = n; s_depth_cost_model = true }
  | SOExhaustive b ->
     ret { opts with s_exhaustive = b }
  | SOAlwaysApply b ->
     ret { opts with s_always_apply = b }

let interp_opts (opts : s_opts) (lst : sopt_t list) (ret : s_opts -> unit Proofview.tactic)
    : unit Proofview.tactic =
  let rec interp lst (opts : s_opts) : unit Proofview.tactic =
    match lst with
    | [] -> ret opts
    | opt :: lst' ->
       let ret opts =
         Proofview.tclUNIT opts >>= try_bind_tactic (interp lst')
       in
       interp_opt ret opt opts
  in
  interp lst opts
