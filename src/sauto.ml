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
    ActApply of Id.t | ActRewriteLR of Id.t | ActRewriteRL of Id.t | ActInst of Id.t |
        ActOrInst of Id.t | ActOrSplit | ActExists | ActExFalso | ActConstructor

let mk_tac_arg id = Tacexpr.Reference (Locus.ArgVar CAst.(make id))

let simp_hyps_tac = Utils.ltac_apply "Tactics.simp_hyps" []
let fail_tac = Proofview.tclZERO (Failure "sauto")
let rewrite_lr_tac tac id = Equality.rewriteLR ~tac:(tac, Equality.AllMatches) (EConstr.mkVar id)
let rewrite_rl_tac tac id = Equality.rewriteRL ~tac:(tac, Equality.AllMatches) (EConstr.mkVar id)
let einst_tac id = Utils.ltac_apply "Tactics.einst" [mk_tac_arg id]
let orinst_tac id = Utils.ltac_apply "Tactics.orinst" [mk_tac_arg id]
let exists_tac = Utils.ltac_apply "eexists" []
let exfalso_tac = Utils.ltac_apply "exfalso" []

let rec goal_cost evd goal = 10
and hyp_cost evd hyp = 10

let eval_hyp evd (id, hyp) = (id, hyp)

let create_action evd goal (id, hyp) = (10, ActApply id)

let create_actions evd goal hyps =
  let actions =
    List.map (create_action evd goal) hyps
  in
  let actions =
    actions
  in
  List.map snd
    (List.sort (fun x y -> compare (fst x) (fst y)) actions)

let repeat2 tac1 tac2 =
  Tacticals.New.tclTHEN tac1
    (Tacticals.New.tclREPEAT
       (Tacticals.New.tclTHEN (Tacticals.New.tclPROGRESS tac2) tac1))

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
  | ActInst id :: acts ->
     continue (einst_tac id) acts
  | ActOrInst id :: acts ->
     continue (orinst_tac id) acts
  | ActExists :: acts ->
     continue exists_tac acts
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
  Tactics.intros <*>
    simplify opts <*>
    search opts n [] []

let sauto opts n = intros opts n
