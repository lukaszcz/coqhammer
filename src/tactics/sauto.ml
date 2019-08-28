(* sauto -- implementation *)

open Names
open Tactypes
open Locus
open Proofview.Notations
open Ltac_plugin

module Utils = Hhutils

type 'a soption = SNone | SAll | SSome of 'a | SNoHints of 'a

type s_opts = {
  s_exhaustive : bool;
  s_leaf_tac : unit Proofview.tactic;
  s_simpl_tac : unit Proofview.tactic;
  s_unfolding : Constant.t list soption;
  s_constructors : inductive list soption;
  s_simple_splits : inductive list soption;
  s_case_splits : inductive list soption;
  s_inversions : inductive list soption;
  s_rew_bases : string list;
  s_bnat_reflect : bool;
  s_case_splitting : bool;
  s_simple_inverting : bool;
  s_forwarding : bool;
}

let default_s_opts = {
  s_exhaustive = false;
  s_leaf_tac = Utils.ltac_apply "Tactics.leaf_solve" [];
  s_simpl_tac = Utils.ltac_apply "Tactics.simpl_solve" [];
  s_unfolding = SSome [];
  s_constructors = SAll;
  s_simple_splits = SSome [];
  s_case_splits = SAll;
  s_inversions = SAll;
  s_rew_bases = [];
  s_bnat_reflect = true;
  s_case_splitting = true;
  s_simple_inverting = true;
  s_forwarding = true;
}

(*****************************************************************************************)

let unfolding_hints = ref [ Utils.get_const "iff"; Utils.get_const "not" ]
let constructor_hints = ref []
let simple_split_hints = ref [ Utils.get_inductive "and"; Utils.get_inductive "ex";
                               Utils.get_inductive "prod"; Utils.get_inductive "sig";
                               Utils.get_inductive "sigT" ]
let case_split_hints = ref []
let inversion_hints = ref []

(*****************************************************************************************)

type action =
    ActApply of Id.t | ActRewriteLR of Id.t | ActRewriteRL of Id.t | ActInvert of Id.t |
        ActUnfold of Constant.t | ActConstructor

let mk_tac_arg_id id = Tacexpr.Reference (Locus.ArgVar CAst.(make id))
let mk_tac_arg_constr t = Tacexpr.ConstrMayEval (Genredexpr.ConstrTerm t)

let simp_hyps_tac = Utils.ltac_apply "Tactics.simp_hyps" []
let fail_tac = Utils.ltac_apply "fail" []
let rewrite_lr_tac tac id = Tacticals.New.tclPROGRESS (Equality.rewriteLR ~tac:(tac, Equality.AllMatches) (EConstr.mkVar id))
let rewrite_rl_tac tac id = Tacticals.New.tclPROGRESS (Equality.rewriteRL ~tac:(tac, Equality.AllMatches) (EConstr.mkVar id))
let einvert_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.einvert" [mk_tac_arg_id id])
let subst_simpl_tac = Utils.ltac_apply "Tactics.subst_simpl" []
let intros_until_atom_tac = Utils.ltac_apply "Tactics.intros_until_atom" []
let simple_inverting_tac = Utils.ltac_apply "Tactics.simple_inverting" []
let case_splitting_tac = Utils.ltac_apply "Tactics.case_splitting" []
let forwarding_tac = Utils.ltac_apply "Tactics.forwarding" []
let bnat_reflect_tac = Utils.ltac_apply "Tactics.bnat_reflect" []
let tryunfold_tac t = Utils.ltac_apply "Tactics.tryunfold" [mk_tac_arg_constr t]

let autorewrite bases =
  let bases =
    if List.mem "nohints" bases then
      List.filter (fun s -> s <> "nohints") bases
    else
      ["shints"; "list"] @ bases
  in
  Autorewrite.auto_multi_rewrite
    bases
    { onhyps = None; concl_occs = AllOccurrences }

let unfold c = Tactics.unfold_constr (GlobRef.ConstRef c) <*> Tactics.simpl_in_concl

let unfolding opts =
  let do_unfolding lst =
    Tacticals.New.tclREPEAT
      (List.fold_left
         (fun acc c -> tryunfold_tac (DAst.make (Glob_term.GRef (GlobRef.ConstRef c, None)), None) <*> acc)
         Tacticals.New.tclIDTAC
         lst)
  in
  match opts.s_unfolding with
  | SSome lst -> do_unfolding (!unfolding_hints @ lst)
  | SNoHints lst -> do_unfolding lst
  | _ -> Tacticals.New.tclIDTAC

(*****************************************************************************************)

let in_sopt_list hints x opt =
  match opt with
  | SAll -> true
  | SSome lst when (List.mem x lst || List.mem x hints) -> true
  | SNoHints lst when List.mem x lst -> true
  | _ -> false

let is_simple_ind ind = Utils.get_ind_nconstrs ind = 1

let is_simple_split opts evd t =
  let open Constr in
  let open EConstr in
  let head = Utils.get_head evd t in
  match kind evd head with
  | Ind (ind, _) when is_simple_ind ind ->
     in_sopt_list !simple_split_hints ind opts.s_simple_splits
  | _ -> false

let is_case_split opts evd t =
  if opts.s_case_splits = SNone then
    false
  else
    try
      Utils.fold_constr begin fun n acc t ->
        let open Constr in
        let open EConstr in
        match kind evd t with
        | Case (ci, _, _, _) when in_sopt_list !case_split_hints ci.ci_ind opts.s_case_splits -> raise Exit
        | _ -> acc
      end false evd t
    with Exit ->
      true

let is_inversion opts evd ind = in_sopt_list !inversion_hints ind opts.s_inversions

(*****************************************************************************************)

let repeat2 tac1 tac2 =
  Tacticals.New.tclTHEN tac1
    (Tacticals.New.tclREPEAT
       (Tacticals.New.tclTHEN (Tacticals.New.tclPROGRESS tac2) tac1))

let (<~>) = repeat2

let opt b tac = if b then tac else Tacticals.New.tclIDTAC

let autorewriting opts = autorewrite opts.s_rew_bases

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

let case_splitting opts =
  match opts.s_case_splits with
  | SAll -> case_splitting_tac
  | SSome lst ->
     let introp =
       Some (CAst.make (IntroAndPattern [CAst.make (IntroAction IntroWildcard)]))
     in
     Proofview.Goal.nf_enter begin fun gl ->
       let evd = Proofview.Goal.sigma gl in
       Utils.fold_constr begin fun n acc t ->
         let open Constr in
         let open EConstr in
         match kind evd t with
         | Case (ci, _, _, _) when in_sopt_list !case_split_hints ci.ci_ind opts.s_case_splits ->
            Proofview.tclTHEN (Tactics.destruct false None t introp None) acc
         | _ -> acc
       end (Proofview.tclUNIT ())
         (Proofview.Goal.sigma gl)
         (Proofview.Goal.concl gl)
     end
  | _ -> Tacticals.New.tclIDTAC

let simplify opts =
  simp_hyps_tac <~>
    opt opts.s_bnat_reflect bnat_reflect_tac <~>
    opts.s_simpl_tac <~>
    (simple_splitting opts <*>
       intros_until_atom_tac <*> subst_simpl_tac) <~>
    autorewriting opts <~>
    opt (opts.s_case_splits = SAll) case_splitting_tac <~>
    opt opts.s_simple_inverting simple_inverting_tac <~>
    opt opts.s_forwarding forwarding_tac

(*****************************************************************************************)

let eval_hyp evd (id, hyp) =
  let (prods, head, args) = Utils.destruct_prod evd hyp in
  let num_subgoals = List.length (List.filter (fun (name, _) -> name = Name.Anonymous) prods) in
  let n = List.length prods in
  (id, hyp, n + num_subgoals * 10, (prods, head, args))

let hyp_cost evd hyp =
  match eval_hyp evd (None, hyp) with
  | (_, _, cost, _) -> cost

let constrs_cost ind =
  let evd = Evd.empty in
  let cstrs = Utils.get_ind_constrs ind in
  List.fold_left (fun acc x -> acc + hyp_cost evd (EConstr.of_constr x)) 0 cstrs

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

let create_actions opts evd goal hyps =
  let ghead = Utils.get_head evd goal in
  let actions =
    List.concat (List.map (create_hyp_actions evd ghead) hyps)
  in
  let actions =
    let open Constr in
    let open EConstr in
    match kind evd ghead with
    | Ind (ind, _) when in_sopt_list !constructor_hints ind opts.s_constructors ->
       (constrs_cost ind, ActConstructor) :: actions
    | Const (c, _) when in_sopt_list !unfolding_hints c opts.s_unfolding ->
       (60, ActUnfold c) :: actions
    | _ ->
       actions
  in
  List.map snd
    (List.sort (fun x y -> Pervasives.compare (fst x) (fst y)) actions)

let create_extra_hyp_actions opts evd (id, hyp, cost, (prods, head, args)) =
  let open Constr in
  let open EConstr in
  match kind evd head with
  | Ind (ind, _) when is_inversion opts evd ind ->
     [(cost, ActInvert id)]
  | _ ->
     []

let create_extra_actions opts evd goal hyps =
  let actions =
    List.concat (List.map (create_extra_hyp_actions opts evd) hyps)
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
        (* Feedback.msg_notice (Printer.pr_constr (EConstr.to_constr evd goal)); *)
        let open Constr in
        let open EConstr in
        match kind evd goal with
        | Prod (_, h, f) when not (Utils.is_atom evd h) || not (Utils.is_False evd f) ->
           intros opts n
        | _ ->
           if is_simple_split opts evd goal then
             simple_splitting opts <*> search opts n hyps (goal :: visited)
           else if is_case_split opts evd goal then
             case_splitting opts <*> start_search opts n
           else
             let hyps =
               if hyps = [] then
                 List.map (eval_hyp evd) (Utils.get_hyps gl)
               else
                 hyps
             in
             let actions = create_actions opts evd goal hyps in
             let tac =
               if actions = [] then
                 opts.s_leaf_tac
               else
                 apply_actions opts n actions hyps (goal :: visited)
             in
             match kind evd goal with
             | Prod _ -> Proofview.tclORELSE tac (fun _ -> Tactics.intros <*> start_search opts n)
             | _ -> tac
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
  | ActUnfold c :: acts ->
     continue (unfold c) acts
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
    let actions = create_extra_actions opts evd goal hyps in
    apply_actions opts n actions [] []
  end

and start_search opts n =
  unfolding opts <*> simplify opts <*>
    Proofview.tclORELSE (search opts n [] []) (fun _ -> extra_search opts n)

and intros opts n =
  Tactics.simpl_in_concl <*>
    intros_until_atom_tac <*>
    start_search opts n

(*****************************************************************************************)

let sauto opts n = unfolding opts <*> subst_simpl_tac <*> intros opts n

let ssimpl opts =
  Tactics.intros <*> unfolding opts <*>
    (simplify opts <~> (Tactics.intros <*> unfolding opts))