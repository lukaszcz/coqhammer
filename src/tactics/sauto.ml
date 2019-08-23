(* sauto -- implementation *)

open Names
open Tactypes
open Proofview.Notations
open Ltac_plugin

module Utils = Hhutils

type 'a soption = SNone | SAll | SSome of 'a | SHints

type s_opts = {
  s_exhaustive : bool;
  s_leaf_tac : unit Proofview.tactic;
  s_simpl_tac : unit Proofview.tactic;
  s_splits : string list soption;
  s_inversions : string list soption;
  s_bnat_reflect : bool;
  s_case_splitting : bool;
  s_simple_inverting : bool;
  s_forwarding : bool;
}

let default_s_opts = {
  s_exhaustive = false;
  s_leaf_tac = Tacticals.New.tclSOLVE [ Utils.ltac_apply "Tactics.isolve" [] ];
  s_simpl_tac = Tacticals.New.tclIDTAC;
  s_splits = SAll;
  s_inversions = SAll;
  s_bnat_reflect = true;
  s_case_splitting = true;
  s_simple_inverting = true;
  s_forwarding = true;
}

(*****************************************************************************************)

type action =
    ActApply of Id.t | ActRewriteLR of Id.t | ActRewriteRL of Id.t | ActInvert of Id.t |
        ActConstructor

let mk_tac_arg_id id = Tacexpr.Reference (Locus.ArgVar CAst.(make id))

let simp_hyps_tac = Utils.ltac_apply "Tactics.simp_hyps" []
let simp_hyp_tac id = Utils.ltac_apply "Tactics.simp_hyp" [mk_tac_arg_id id]
let fail_tac = Tacticals.New.tclFAIL 0 Pp.(str "sauto")
let rewrite_lr_tac tac id = Equality.rewriteLR ~tac:(tac, Equality.AllMatches) (EConstr.mkVar id)
let rewrite_rl_tac tac id = Equality.rewriteRL ~tac:(tac, Equality.AllMatches) (EConstr.mkVar id)
let einvert_tac id = Utils.ltac_apply "Tactics.einvert" [mk_tac_arg_id id]
let subst_simpl_tac = Utils.ltac_apply "Tactics.subst_simpl" []
let intros_until_atom_tac = Utils.ltac_apply "Tactics.intros_until_atom" []
let simple_inverting_tac = Utils.ltac_apply "Tactics.simple_inverting" []
let case_splitting_tac = Utils.ltac_apply "Tactics.simple_splitting" []
let forwarding_tac = Utils.ltac_apply "Tactics.forwarding" []
let bnat_reflect_tac = Utils.ltac_apply "Tactics.bnat_reflect" []

(*****************************************************************************************)

let is_simple_split opts evd t = false
let is_inversion opts evd t = false

(*****************************************************************************************)

let repeat2 tac1 tac2 =
  Tacticals.New.tclTHEN tac1
    (Tacticals.New.tclREPEAT
       (Tacticals.New.tclTHEN (Tacticals.New.tclPROGRESS tac2) tac1))

let (<~>) = repeat2

let opt b tac = if b then tac else Tacticals.New.tclIDTAC

let autorewriting opts = Tacticals.New.tclIDTAC

let rec simple_splitting opts =
  Proofview.Goal.nf_enter begin fun gl ->
    let goal = Proofview.Goal.concl gl in
    let evd = Proofview.Goal.sigma gl in
    if is_simple_split opts evd goal then
      Tactics.constructor_tac true None 1 NoBindings <*>
        Tactics.simpl_in_concl <*> simple_splitting opts
    else
      Tacticals.New.tclIDTAC
  end

let simplify opts =
  simp_hyps_tac <~>
    (opt opts.s_bnat_reflect bnat_reflect_tac <*> simple_splitting opts <*>
       intros_until_atom_tac <*> subst_simpl_tac) <~>
    opts.s_simpl_tac <~>
    autorewriting opts <~>
    opt opts.s_case_splitting case_splitting_tac <~>
    opt opts.s_simple_inverting simple_inverting_tac <~>
    opt opts.s_forwarding forwarding_tac

(*****************************************************************************************)

let eval_hyp evd (id, hyp) =
  let (prods, head, args) as dh = Utils.destruct_prod evd hyp in
  let n = List.length prods in
  let num_subgoals = List.length (List.filter (fun (name, _) -> name = Name.Anonymous) prods) in
  (id, hyp, n + num_subgoals * 10, dh)

let create_hyp_actions evd ghead (id, hyp, cost, (prods, head, args)) =
  if Utils.is_False evd head && prods = [] then
    [(0, ActInvert id)]
  else if head = ghead then
    [(cost, ActApply id)]
  else
    let open Constr in
    let open EConstr in
    match kind evd head with
    | Rel _ ->
       [(cost + 40, ActApply id)]
    | _ ->
       []

let create_actions evd goal hyps =
  let open Constr in
  let open EConstr in
  let ghead = Utils.get_head evd goal in
  let actions =
    List.concat (List.map (create_hyp_actions evd ghead) hyps)
  in
  let actions =
    let open Constr in
    let open EConstr in
    match kind evd ghead with
    | Ind _ ->
       (50, ActConstructor) :: actions (* TODO: constructor cost estimation *)
    | _ ->
       actions
  in
  List.map snd
    (List.sort (fun x y -> Pervasives.compare (fst x) (fst y)) actions)

let create_extra_hyp_actions evd (id, hyp, cost, (prods, head, args)) =
  let open Constr in
  let open EConstr in
  match kind evd head with
  | Ind _ ->
     [(cost, ActInvert id)]
  | _ ->
     []

let create_extra_actions evd goal hyps =
  let actions =
    List.concat (List.map (create_extra_hyp_actions evd) hyps)
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
        let open Constr in
        let open EConstr in
        match kind evd goal with
        | Prod (_, h, f) when not (Utils.is_atom evd h) || not (Utils.is_False evd f) ->
           intros opts n
        | _ ->
           if is_simple_split opts evd goal then
             simple_splitting opts <*> search opts n hyps (goal :: visited)
           else
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
     cont (einvert_tac id <*> start_search opts (n - 1)) acts
  | ActConstructor :: acts ->
     cont
       (Tactics.any_constructor true
          (Some (Tactics.simpl_in_concl <*> search opts (n - 1) hyps visited)))
       acts
  | [] ->
     fail_tac

and extra_search opts n =
  Proofview.Goal.nf_enter begin fun gl ->
    let goal = Proofview.Goal.concl gl in
    let evd = Proofview.Goal.sigma gl in
    let hyps = List.map (eval_hyp evd) (Utils.get_hyps gl) in
    let actions = create_extra_actions evd goal hyps in
    apply_actions opts n actions [] []
  end

and start_search opts n =
  simplify opts <*> Proofview.tclORELSE (search opts n [] []) (fun _ -> extra_search opts n)

and intros opts n =
  Tactics.simpl_in_concl <*>
    intros_until_atom_tac <*>
    start_search opts n

(*****************************************************************************************)

let sauto opts n = subst_simpl_tac <*> intros opts n

let ssimpl opts = Tactics.intros <*> subst_simpl_tac <*> (simplify opts <~> Tactics.intros)
