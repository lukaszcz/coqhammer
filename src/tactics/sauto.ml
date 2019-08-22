(* sauto -- implementation *)

open Names
open Proofview.Notations
open Ltac_plugin

module Utils = Hhutils

type 'a soption = SNone | SAll | SSome of 'a

type s_opts = {
  s_exhaustive : bool;
  s_leaf_tac : unit Proofview.tactic;
  s_inversions : string list soption;
  s_simple_inverting : bool;
  s_forwarding : bool;
}

let default_s_opts = {
  s_exhaustive = false;
  s_leaf_tac = Tacticals.New.tclIDTAC;
  s_inversions = SAll;
  s_simple_inverting = true;
  s_forwarding = true;
}

(*****************************************************************************************)

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
let yintros_tac = Utils.ltac_apply "Tactics.yintros" []
let generalizing_tac = Utils.ltac_apply "Tactics.generalizing" []
let simple_inverting_tac = Utils.ltac_apply "Tactics.simple_inverting" []

(*****************************************************************************************)

let repeat2 tac1 tac2 =
  Tacticals.New.tclTHEN tac1
    (Tacticals.New.tclREPEAT
       (Tacticals.New.tclTHEN (Tacticals.New.tclPROGRESS tac2) tac1))

let (<~>) = repeat2

let opt b tac = if b then tac else Tacticals.New.tclIDTAC

let forward_resolve evd id t =
  Tacticals.New.tclIDTAC

let forward_rewrite evd id t = Tacticals.New.tclIDTAC (* TODO *)

let simplify opts = simp_hyps_tac (* TODO *)

(*****************************************************************************************)

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

let rec search opts n hyps hyp_ids visited =
  if n = 0 then
    opts.s_leaf_tac
  else
    Proofview.Goal.nf_enter begin fun gl ->
      let goal = Proofview.Goal.concl gl in
      if List.mem goal visited then
        fail_tac
      else
        let evd = Proofview.Goal.sigma gl in
        let (hyps, hyp_ids) =
          if hyps = [] then
            let rhyps = Utils.get_hyps gl in
            (List.map (eval_hyp evd) rhyps, Id.Set.of_list (List.map fst rhyps))
          else
            (hyps, hyp_ids)
        in
        let actions = create_actions evd goal hyps in
        if actions = [] then
          opts.s_leaf_tac
        else
          apply_actions opts n actions hyps hyp_ids (goal :: visited)
    end

and apply_actions opts n actions hyps hyp_ids visited =
  let branch =
    if opts.s_exhaustive then Proofview.tclOR else Proofview.tclORELSE
  in
  let cont tac acts =
    branch tac (fun _ -> apply_actions opts n acts hyps hyp_ids visited)
  in
  let continue tac acts =
    cont (tac <*> search opts (n - 1) hyps hyp_ids visited) acts
  in
  match actions with
  | ActApply id :: acts ->
     continue (Tactics.Simple.eapply (EConstr.mkVar id)) acts
  | ActRewriteLR id :: acts ->
     continue (rewrite_lr_tac opts.s_leaf_tac id) acts
  | ActRewriteRL id :: acts ->
     continue (rewrite_rl_tac opts.s_leaf_tac id) acts
  | ActInvert id :: acts ->
     cont
       (Inv.inv_clear_tac id <*> Tactics.simpl_in_concl <*>
          start_search opts (n - 1) (Id.Set.remove id hyp_ids))
       acts
  | ActInst id :: acts ->
     continue (einst_tac id) acts
  | ActExFalso :: acts ->
     continue exfalso_tac acts
  | ActConstructor :: acts ->
     cont
       (Tactics.any_constructor true
          (Some (Tactics.simpl_in_concl <*> search opts (n - 1) hyps hyp_ids visited)))
       acts
  | [] ->
     fail_tac

and forward_reasoning opts hyp_ids =
  let rec go n hyp_ids =
    if n = 0 then
      Tacticals.New.tclIDTAC
    else
      Proofview.Goal.nf_enter begin fun gl ->
        let rhyps =
          List.filter (fun (id, _) -> not (Id.Set.mem id hyp_ids)) (Utils.get_hyps gl)
        in
        if rhyps = [] then
          Tacticals.New.tclIDTAC
        else
          List.fold_left
            begin fun tac (id, hyp) ->
              if Id.Set.mem id hyp_ids then
                tac
              else
                let evd = Proofview.Goal.sigma gl in
                tac <*> forward_resolve evd id hyp
            end
            Tacticals.New.tclIDTAC
            rhyps
          <*>
            let hyp_ids = Id.Set.of_list (List.map fst rhyps) in
            go (n - 1) hyp_ids
      end
  in
  go 5 hyp_ids

and start_search opts n hyp_ids =
  forward_reasoning opts hyp_ids <*>
    search opts n [] Id.Set.empty []

and intros opts n hyp_ids =
  Tactics.simpl_in_concl <*>
    yintros_tac <*>
    opt opts.s_simple_inverting simple_inverting_tac <*>
    start_search opts n hyp_ids

(*****************************************************************************************)

let sauto opts n = generalizing_tac <*> intros opts n Id.Set.empty
