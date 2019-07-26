(* sauto -- implementation *)

open Names
open Proofview.Notations
open Ltac_plugin

module Utils = Hhutils

type sauto_opts = {
  exhaustive : bool;
  leaf_tac : unit Proofview.tactic;
  inversions : string list;
}

let default_sauto_opts =
  { exhaustive = false;
    leaf_tac = Tacticals.New.tclIDTAC;
    inversions = [] }

type action =
    ActApply of Id.t | ActRewriteLR of Id.t | ActRewriteRL of Id.t |
    ActInvert of Id.t |  ActInst of Id.t |  ActOrInst of Id.t |
    ActExFalso | ActConstructor

let mk_tac_arg_id id = Tacexpr.Reference (Locus.ArgVar CAst.(make id))

let simp_hyps_tac = Utils.ltac_apply "Tactics.simp_hyps" []
let simp_hyp_tac id = Utils.ltac_apply "Tactics.simp_hyp" [mk_tac_arg_id id]
let fail_tac = Proofview.tclZERO (Failure "sauto")
let rewrite_lr_tac tac id = Equality.rewriteLR ~tac:(tac, Equality.AllMatches) (EConstr.mkVar id)
let rewrite_rl_tac tac id = Equality.rewriteRL ~tac:(tac, Equality.AllMatches) (EConstr.mkVar id)
let einst_tac id = Utils.ltac_apply "Tactics.einst" [mk_tac_arg_id id]
let exfalso_tac = Utils.ltac_apply "exfalso" []

let eval_hyp evd (id, hyp) =
  let (prods, head, args) as dh = Utils.destruct_prod evd hyp in
  let n = List.length prods in
  let num_subgoals = List.length (List.filter (fun (name, _) -> name = Name.Anonymous) prods) in
  (id, hyp, n + num_subgoals * 10, dh)

let create_hyp_actions evd ghead (id, hyp, cost, (prods, head, args)) =
  if head = ghead then
    [(cost, ActApply id)]
  else
    let open Constr in
    let open EConstr in
    match kind evd head with
    | Rel _ ->
       [(cost + 40, ActApply id)]
    | Ind _ ->
       if prods = [] && args <> [] then
         [(100, ActInvert id)] (* TODO: inversion cost estimation *)
       else if prods <> [] then
         [(cost + 40, ActInst id)]
       else
         []
    | _ ->
       []

let create_actions evd goal hyps =
  let open Constr in
  let open EConstr in
  let ghead =
    match kind evd goal with
    | App (h, _) -> h
    | _ -> goal
  in
  let actions =
    List.concat (List.map (create_hyp_actions evd ghead) hyps)
  in
  let actions =
    let open Constr in
    let open EConstr in
    match kind evd ghead with
    | Ind _ ->
       (50, ActConstructor) :: actions
    | _ ->
       actions
  in
  List.map snd
    (List.sort (fun x y -> Pervasives.compare (fst x) (fst y)) actions)

let repeat2 tac1 tac2 =
  Tacticals.New.tclTHEN tac1
    (Tacticals.New.tclREPEAT
       (Tacticals.New.tclTHEN (Tacticals.New.tclPROGRESS tac2) tac1))

let (<~>) = repeat2

let rec search opts n hyps visited =
  if n = 0 then
    opts.leaf_tac
  else
    Proofview.Goal.nf_enter begin fun gl ->
      let goal = Proofview.Goal.concl gl in
      if List.mem goal visited then
        fail_tac
      else
        let evd = Proofview.Goal.sigma gl in
        let hyps =
          if hyps = [] then
            List.map (eval_hyp evd) (Utils.get_hyps gl)
          else
            hyps
        in
        let actions = create_actions evd goal hyps in
        if actions = [] then
          opts.leaf_tac
        else
          apply_actions opts n actions hyps (goal :: visited)
    end

and apply_actions opts n actions hyps visited =
  let cont branch tac acts =
    branch
      (tac <*> search opts (n - 1) hyps visited)
      (fun _ -> apply_actions opts n acts hyps visited)
  in
  let branch =
    if opts.exhaustive then Proofview.tclOR else Proofview.tclORELSE
  in
  let continue = cont branch in
  match actions with
  | ActApply id :: acts ->
     continue (Tactics.Simple.eapply (EConstr.mkVar id)) acts
  | ActRewriteLR id :: acts ->
     continue (rewrite_lr_tac opts.leaf_tac id) acts
  | ActRewriteRL id :: acts ->
     continue (rewrite_rl_tac opts.leaf_tac id) acts
  | ActInvert id :: acts ->
     continue (Inv.inv_clear_tac id) acts
  | ActInst id :: acts ->
     continue (einst_tac id) acts
  | ActExFalso :: acts ->
     continue exfalso_tac acts
  | ActConstructor :: acts ->
     branch
       (Tactics.any_constructor true
          (Some (Tactics.simpl_in_concl <*> search opts (n - 1) hyps visited)))
       (fun _ -> apply_actions opts n acts hyps visited)
  | [] ->
     fail_tac

and simplify opts =
  simp_hyps_tac

and intros opts n =
  Tactics.simpl_in_concl <*>
  Tactics.intros <*>
    simplify opts <*>
    search opts n [] []

let sauto opts n = intros opts n
