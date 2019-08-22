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

let rec search opts n hyps visited =
  if n = 0 then
    opts.s_leaf_tac
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
          opts.s_leaf_tac
        else
          apply_actions opts n actions hyps (goal :: visited)
    end

and apply_actions opts n actions hyps visited =
  let branch =
    if opts.s_exhaustive then Proofview.tclOR else Proofview.tclORELSE
  in
  let cont tac acts =
    branch tac (fun _ -> apply_actions opts n acts hyps visited)
  in
  let continue tac acts =
    cont (tac <*> search opts (n - 1) hyps visited) acts
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
       (Inv.inv_clear_tac id <*> Tactics.simpl_in_concl <*> start_search opts (n - 1))
       acts
  | ActInst id :: acts ->
     continue (einst_tac id) acts
  | ActExFalso :: acts ->
     continue exfalso_tac acts
  | ActConstructor :: acts ->
     cont
       (Tactics.any_constructor true
          (Some (Tactics.simpl_in_concl <*> search opts (n - 1) hyps visited)))
       acts
  | [] ->
     fail_tac

and start_search opts n =
  simplify opts <*> search opts n [] []

and intros opts n =
  Tactics.simpl_in_concl <*>
    yintros_tac <*>
    opt opts.s_simple_inverting simple_inverting_tac <*>
    start_search opts n

(*****************************************************************************************)

let sauto opts n = generalizing_tac <*> intros opts n
