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
  s_simple_inverting = true;
  s_forwarding = true;
}

(*****************************************************************************************)

let logic_constants = [ Utils.get_const "iff"; Utils.get_const "not" ]
let logic_inductives = [ Utils.get_inductive "and"; Utils.get_inductive "or"; Utils.get_inductive "ex";
                         Utils.get_inductive "prod"; Utils.get_inductive "sumbool"; Utils.get_inductive "sig";
                         Utils.get_inductive "sum"; Utils.get_inductive "sigT" ]

let unfolding_hints = ref logic_constants
let constructor_hints = ref logic_inductives
let simple_split_hints = ref [ Utils.get_inductive "and"; Utils.get_inductive "ex";
                               Utils.get_inductive "prod"; Utils.get_inductive "sig";
                               Utils.get_inductive "sigT" ]
let case_split_hints = ref []
let inversion_hints = ref logic_inductives

let add_unfold_hint c = unfolding_hints := c :: !unfolding_hints
let add_ctrs_hint c = constructor_hints := c :: !constructor_hints
let add_simple_split_hint c = simple_split_hints := c :: !simple_split_hints
let add_case_split_hint c = case_split_hints := c :: !case_split_hints
let add_inversion_hint c = inversion_hints := c :: !inversion_hints

(*****************************************************************************************)

type action =
    ActApply of Id.t | ActInvert of Id.t | ActUnfold of Constant.t | ActCaseUnfold of Constant.t |
        ActConstructor | ActIntro

let action_to_string act =
  match act with
  | ActApply id -> "apply " ^ Id.to_string id
  | ActInvert id -> "invert " ^ Id.to_string id
  | ActUnfold c -> "unfold " ^ Constant.to_string c
  | ActCaseUnfold c -> "case-unfold " ^ Constant.to_string c
  | ActConstructor -> "constructor"
  | ActIntro -> "intro"

let print_search_actions n actions =
  print_int n; print_newline ();
  Hhlib.oiter print_string (fun (cost, br, act) ->
    print_string "("; print_int cost; print_string ", ";
    print_int br; print_string ", "; print_string (action_to_string act); print_string ")") "; " actions;
  print_newline ()

(*****************************************************************************************)

let mk_tac_arg_id id = Tacexpr.Reference (Locus.ArgVar CAst.(make id))
let mk_tac_arg_constr t = Tacexpr.ConstrMayEval (Genredexpr.ConstrTerm t)

let simp_hyps_tac = Utils.ltac_apply "Tactics.simp_hyps" []
let fail_tac = Utils.ltac_apply "fail" []
let sinvert_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.sinvert" [mk_tac_arg_id id])
let subst_simpl_tac = Utils.ltac_apply "Tactics.subst_simpl" []
let intros_until_atom_tac = Utils.ltac_apply "Tactics.intros_until_atom" []
let simple_inverting_tac = Utils.ltac_apply "Tactics.simple_inverting" []
let case_splitting_tac = Utils.ltac_apply "Tactics.case_splitting" []
let forwarding_tac = Utils.ltac_apply "Tactics.forwarding" []
let bnat_reflect_tac = Utils.ltac_apply "Tactics.bnat_reflect" []
let fullunfold_tac t = Utils.ltac_apply "Tactics.fullunfold" [mk_tac_arg_constr t]

(*****************************************************************************************)

let autorewrite bases =
  let bases =
    if List.mem "nohints" bases then
      List.filter (fun s -> s <> "nohints") bases
    else
      ["shints"; "list"] @ (List.filter (fun s -> s <> "shints" && s <> "list") bases)
  in
  Autorewrite.auto_multi_rewrite
    bases
    { onhyps = None; concl_occs = AllOccurrences }

(*****************************************************************************************)

let is_simple_unfold c =
  match Global.body_of_constant c with
  | Some (b, _) ->
     begin
       let t = EConstr.of_constr b in
       let body = Utils.drop_all_lambdas Evd.empty t in
       let open Constr in
       let open EConstr in
       match kind Evd.empty body with
       | Prod _  | App _ | Const _ | Ind _ | Sort _ | Var _ | Rel _ -> true
       | _ -> false
     end
  | None -> false

(* -1 if not a case unfold *)
let case_unfold_cost c =
  match Global.body_of_constant c with
  | Some (b, _) ->
     begin
       let t = EConstr.of_constr b in
       let lambdas = Utils.take_all_lambdas Evd.empty t in
       let body = Utils.drop_all_lambdas Evd.empty t in
       let open Constr in
       let open EConstr in
       match kind Evd.empty body with
       | Case _ -> List.length lambdas * 10 + 10
       | _ -> -1
     end
  | None -> -1

let unfold c = Tactics.unfold_constr (GlobRef.ConstRef c) <*> Tactics.simpl_in_concl

let fullunfold c = fullunfold_tac (DAst.make (Glob_term.GRef (GlobRef.ConstRef c, None)), None)

let tryunfold c =
  if is_simple_unfold c then
    fullunfold c
  else
    Tacticals.New.tclIDTAC

let unfolding opts =
  let do_unfolding lst =
    Tacticals.New.tclREPEAT
      (List.fold_left
         (fun acc c -> tryunfold c <*> acc)
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

(* check if the inductive type is non-recursive with exactly one
   constructor *)
let is_simple_ind ind =
  let cstrs = Utils.get_ind_constrs ind in
  match cstrs with
  | [ t ] ->
     let (prods, _, _) = Utils.destruct_prod Evd.empty (EConstr.of_constr t) in
     let t2 =
       List.fold_right (fun (name, types) acc -> EConstr.mkLambda (name, types, acc))
         prods (EConstr.mkRel 0)
     in
     Utils.fold_constr
       begin fun k acc x ->
         let open Constr in
         let open EConstr in
         match kind Evd.empty x with
         | Ind (ind2, _) when ind2 = ind -> false
         | Rel n when n > k -> false
         | _ -> acc
       end
       true
       Evd.empty
       t2
  | _ -> false

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
    Tactics.simpl_in_concl <~>
    (Tacticals.New.tclPROGRESS intros_until_atom_tac <*> subst_simpl_tac) <~>
    simple_splitting opts <~>
    autorewriting opts <~>
    opt (opts.s_case_splits = SAll) case_splitting_tac <~>
    opt opts.s_simple_inverting simple_inverting_tac <~>
    opt opts.s_forwarding forwarding_tac

(*****************************************************************************************)

let eval_hyp evd (id, hyp) =
  let (prods, head, args) = Utils.destruct_prod evd hyp in
  let num_subgoals = List.length (List.filter (fun (name, _) -> name = Name.Anonymous) prods) in
  let n = List.length prods in
  (id, hyp, n + num_subgoals * 10, num_subgoals, (prods, head, args))

let hyp_cost evd hyp =
  match eval_hyp evd (None, hyp) with
  | (_, _, cost, _, _) -> cost

let hyp_nsubgoals evd hyp =
  match eval_hyp evd (None, hyp) with
  | (_, _, _, num_subgoals, _) -> num_subgoals

let constrs_cost ind =
  let evd = Evd.empty in
  let cstrs = Utils.get_ind_constrs ind in
  if cstrs = [] then
    10
  else
    10 + (List.fold_left (fun acc x -> acc + (hyp_cost evd (EConstr.of_constr x))) 0 cstrs) / List.length cstrs

let constrs_nsubgoals ind =
  let evd = Evd.empty in
  let cstrs = Utils.get_ind_constrs ind in
  List.fold_left (fun acc x -> max acc (hyp_nsubgoals evd (EConstr.of_constr x))) 0 cstrs

let create_hyp_actions evd ghead (id, hyp, cost, num_subgoals, (prods, head, args)) =
  if Utils.is_False evd head && prods = [] then
    [(0, 1, ActInvert id)]
  else if head = ghead then
    [(cost, num_subgoals, ActApply id)]
  else
    let open Constr in
    let open EConstr in
    match kind evd head with
    | Rel _ ->
       [(cost + 40, num_subgoals, ActApply id)]
    | _ ->
       []

let create_extra_hyp_actions opts evd (id, hyp, cost, num_subgoals, (prods, head, args)) =
  let open Constr in
  let open EConstr in
  let rec has_arg_dep lst =
    match lst with
    | [] -> false
    | h :: t ->
       begin
         match kind evd h with
         | App _ | Const _ | Construct _ -> true
         | _ -> has_arg_dep t
       end
  in
  (* TODO: count in (recursive) constructors with no non-trivial argument dependencies? *)
  match kind evd head with
  | Ind (ind, _) when is_inversion opts evd ind ->
     let num_ctrs = Utils.get_ind_nconstrs ind in
     let b_arg_dep = has_arg_dep args in
     [(cost + if b_arg_dep then 40 else num_ctrs * 10 + 120),
      (if b_arg_dep then num_subgoals + 1 else num_subgoals + num_ctrs),
      ActInvert id]
  | _ ->
     []

let create_case_unfolding_actions opts evd goal hyps =
  let create lst =
    List.fold_left begin fun acc c ->
      let cost = case_unfold_cost c in
      if cost >= 0 then
        (cost, 1, ActCaseUnfold c) :: acc
      else
        acc
    end [] lst
  in
  let get_consts lst =
    Hhlib.sort_uniq Pervasives.compare
      (List.concat
         (List.map
            begin fun t ->
              Utils.fold_constr begin fun n acc t ->
                let open Constr in
                let open EConstr in
                match kind evd t with
                | Const (c, _) -> c :: acc
                | _ -> acc
              end [] evd t
            end
            lst))
  in
  match opts.s_unfolding with
  | SSome lst -> create (!unfolding_hints @ lst)
  | SNoHints lst -> create lst
  | SAll -> create (get_consts (goal :: List.map (fun (_, x, _, _, _) -> x) hyps))
  | SNone -> []

let create_extra_actions opts evd goal hyps =
  let actions =
    List.concat (List.map (create_extra_hyp_actions opts evd) hyps)
  in
  let actions =
    create_case_unfolding_actions opts evd goal hyps @ actions
  in
  actions

let create_actions extra opts evd goal hyps =
  let actions =
    if extra then create_extra_actions opts evd goal hyps else []
  in
  let actions =
    let open Constr in
    let open EConstr in
    match kind evd goal with
    | Prod _ -> (30, 1, ActIntro) :: actions
    | _ -> actions
  in
  let ghead = Utils.get_head evd goal in
  let actions =
    let open Constr in
    let open EConstr in
    match kind evd ghead with
    | Ind (ind, _) when in_sopt_list !constructor_hints ind opts.s_constructors ->
       (constrs_cost ind, constrs_nsubgoals ind, ActConstructor) :: actions
    | Const (c, _) when in_sopt_list !unfolding_hints c opts.s_unfolding ->
       (60, 1, ActUnfold c) :: actions
    | _ ->
       actions
  in
  let actions =
    List.concat (List.map (create_hyp_actions evd ghead) hyps) @ actions
  in
  List.stable_sort (fun (x, _, _) (y, _, _) -> Pervasives.compare x y) actions

let rec search extra opts n hyps visited =
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
             simple_splitting opts <*> search extra opts n hyps (goal :: visited)
           else if is_case_split opts evd goal then
             case_splitting opts <*> start_search opts n
           else
             let hyps =
               if hyps = [] then
                 List.map (eval_hyp evd) (Utils.get_hyps gl)
               else
                 hyps
             in
             let actions = create_actions extra opts evd goal hyps in
             match actions with
             | [] -> opts.s_leaf_tac
             | (cost, _, _) :: _ when cost > n -> opts.s_leaf_tac
             | _ -> apply_actions opts n actions hyps (goal :: visited)
    end

and start_search opts n =
  unfolding opts <*> simplify opts <*> search true opts n [] []

and intros opts n =
  Tactics.simpl_in_concl <*>
    intros_until_atom_tac <*>
    start_search opts n

and apply_actions opts n actions hyps visited =
  let branch =
    if opts.s_exhaustive then Proofview.tclOR else Proofview.tclORELSE
  in
  let cont tac acts =
    branch tac (fun _ -> apply_actions opts n acts hyps visited)
  in
  let continue n tac acts =
    cont (tac <*> search false opts n hyps visited) acts
  in
  match actions with
  | (cost, branching, act) :: acts ->
     if cost > n then
       fail_tac
     else
       begin
         let n' = (n - cost) / max branching 1 in
         match act with
         | ActApply id ->
            continue n' (Tactics.Simple.eapply (EConstr.mkVar id)) acts
         | ActInvert id ->
            cont (sinvert_tac id <*> start_search opts n') acts
         | ActUnfold c ->
            continue n' (unfold c) acts
         | ActCaseUnfold c ->
            cont (Tacticals.New.tclPROGRESS (fullunfold c) <*> start_search opts n') acts
         | ActConstructor ->
            cont
              (Tactics.any_constructor true
                 (Some (Tactics.simpl_in_concl <*> search false opts n' hyps visited)))
              acts
         | ActIntro ->
            cont (Tactics.intros <*> subst_simpl_tac <*> start_search opts n') acts
       end
  | [] ->
     fail_tac

(*****************************************************************************************)

let sauto opts n = unfolding opts <*> subst_simpl_tac <*> intros opts n

let ssimpl opts =
  Tactics.intros <*> unfolding opts <*> subst_simpl_tac <*>
    (simplify opts <~> (Tactics.intros <*> unfolding opts))
