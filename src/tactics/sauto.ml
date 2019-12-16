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
  s_eager_reducing : bool;
  s_eager_rewriting : bool;
  s_eager_inverting : bool;
  s_simple_inverting : bool;
  s_forwarding : bool;
  s_reducing : bool;
  s_rewriting : bool;
  s_heuristic_rewriting : bool;
  s_aggressive_unfolding : bool;
  s_presimplify : bool;
  s_depth_cost_model : bool;
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
  s_eager_reducing = true;
  s_eager_rewriting = true;
  s_eager_inverting = true;
  s_simple_inverting = true;
  s_forwarding = true;
  s_reducing = true;
  s_rewriting = true;
  s_heuristic_rewriting = true;
  s_aggressive_unfolding = false;
  s_presimplify = false;
  s_depth_cost_model = false;
}

(*****************************************************************************************)

let logic_constants = [ Utils.get_const "Init.Logic.iff"; Utils.get_const "Init.Logic.not" ]
let logic_inductives = [ Utils.get_inductive "Init.Logic.and"; Utils.get_inductive "Init.Logic.or";
                         Utils.get_inductive "Init.Logic.ex"; Utils.get_inductive "Init.Datatypes.prod";
                         Utils.get_inductive "Init.Specif.sumbool"; Utils.get_inductive "Init.Specif.sig";
                         Utils.get_inductive "Init.Datatypes.sum"; Utils.get_inductive "Init.Specif.sigT";
                         Utils.get_inductive "Init.Logic.False" ]

let unfolding_hints = ref logic_constants
let constructor_hints = ref logic_inductives
let simple_split_hints = ref [ Utils.get_inductive "Init.Logic.and";
                               Utils.get_inductive "Init.Logic.ex";
                               Utils.get_inductive "Init.Datatypes.prod";
                               Utils.get_inductive "Init.Specif.sig";
                               Utils.get_inductive "Init.Specif.sigT" ]
let case_split_hints = ref []
let inversion_hints = ref logic_inductives

let add_unfold_hint c = unfolding_hints := c :: !unfolding_hints
let add_ctrs_hint c = constructor_hints := c :: !constructor_hints
let add_simple_split_hint c = simple_split_hints := c :: !simple_split_hints
let add_case_split_hint c = case_split_hints := c :: !case_split_hints
let add_inversion_hint c = inversion_hints := c :: !inversion_hints

(*****************************************************************************************)

type action =
    ActApply of Id.t | ActRewriteLR of Id.t | ActRewriteRL of Id.t | ActRewrite of Id.t |
        ActInvert of Id.t | ActUnfold of Constant.t | ActCaseUnfold of Constant.t |
            ActConstructor | ActIntro | ActReduce

let action_to_string act =
  match act with
  | ActApply id -> "apply " ^ Id.to_string id
  | ActRewriteLR id -> "rewrite -> " ^ Id.to_string id
  | ActRewriteRL id -> "rewrite <- " ^ Id.to_string id
  | ActRewrite id -> "srewrite " ^ Id.to_string id
  | ActInvert id -> "invert " ^ Id.to_string id
  | ActUnfold c -> "unfold " ^ Constant.to_string c
  | ActCaseUnfold c -> "case-unfold " ^ Constant.to_string c
  | ActConstructor -> "constructor"
  | ActIntro -> "intro"
  | ActReduce -> "reduce"

let print_search_actions actions =
  Hhlib.oiter print_string (fun (cost, br, act) ->
    print_string "("; print_int cost; print_string ", ";
    print_int br; print_string ", "; print_string (action_to_string act); print_string ")") "; " actions;
  print_newline ()

(*****************************************************************************************)

let mk_tac_arg_id id = Tacexpr.Reference (Locus.ArgVar CAst.(make id))
let mk_tac_arg_constr t = Tacexpr.ConstrMayEval (Genredexpr.ConstrTerm t)

let erewrite b_all l2r id =
  Equality.general_rewrite_clause l2r true (EConstr.mkVar id, NoBindings)
    Locus.({onhyps = if b_all then None else Some []; concl_occs = AllOccurrences})

let simp_hyps_tac = Utils.ltac_apply "Tactics.simp_hyps" []
let fail_tac = Utils.ltac_apply "fail" []
let sinvert_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.sinvert" [mk_tac_arg_id id])
let seinvert_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.seinvert" [mk_tac_arg_id id])
let ssubst_tac = Utils.ltac_apply "Tactics.ssubst" []
let subst_simpl_tac = Utils.ltac_apply "Tactics.subst_simpl" []
let srewrite_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.srewrite" [mk_tac_arg_id id])
let intros_until_atom_tac = Utils.ltac_apply "Tactics.intros_until_atom" []
let simple_inverting_tac = Utils.ltac_apply "Tactics.simple_inverting" []
let simple_inverting_nocbn_tac = Utils.ltac_apply "Tactics.simple_inverting_nocbn" []
let simple_invert_tac id = Utils.ltac_apply "Tactics.simple_invert" [mk_tac_arg_id id]
let simple_invert_nocbn_tac id = Utils.ltac_apply "Tactics.simple_invert_nocbn" [mk_tac_arg_id id]
let case_splitting_tac = Utils.ltac_apply "Tactics.case_splitting" []
let case_splitting_nocbn_tac = Utils.ltac_apply "Tactics.case_splitting_nocbn" []
let case_splitting_concl_tac = Utils.ltac_apply "Tactics.case_splitting_concl" []
let case_splitting_concl_nocbn_tac = Utils.ltac_apply "Tactics.case_splitting_concl_nocbn" []
let forwarding_tac = Utils.ltac_apply "Tactics.forwarding" []
let forwarding_nocbn_tac = Utils.ltac_apply "Tactics.forwarding_nocbn" []
let srewriting_tac = Utils.ltac_apply "Tactics.srewriting" []
let bnat_reflect_tac = Utils.ltac_apply "Tactics.bnat_reflect" []
let fullunfold_tac t = Utils.ltac_apply "Tactics.fullunfold" [mk_tac_arg_constr t]
let cbn_in_concl_tac = Utils.ltac_apply "Tactics.cbn_in_concl" []
let cbn_in_all_tac = Utils.ltac_apply "Tactics.cbn_in_all" []

(*****************************************************************************************)

let autorewrite b_all bases =
  let bases =
    if List.mem "nohints" bases then
      List.filter (fun s -> s <> "nohints") bases
    else
      ["shints"; "list"] @ (List.filter (fun s -> s <> "shints" && s <> "list") bases)
  in
  if bases = [] then
    Proofview.tclUNIT ()
  else
    Autorewrite.auto_multi_rewrite
      bases
      { onhyps = if b_all then None else Some []; concl_occs = AllOccurrences }

let subst_simpl opts =
  if opts.s_eager_reducing && opts.s_reducing then
    subst_simpl_tac
  else
    ssubst_tac

let sinvert opts id =
  if opts.s_exhaustive then
    seinvert_tac id <*> subst_simpl opts
  else
    sinvert_tac id <*> subst_simpl opts

let reduce_concl opts =
  if opts.s_eager_reducing && opts.s_reducing then
    cbn_in_concl_tac
  else
    Proofview.tclUNIT ()

(*****************************************************************************************)

let get_consts evd lst =
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

let is_simple_unfold b_aggressive c =
  match Global.body_of_constant c with
  | Some (b, _) ->
     begin
       let t = EConstr.of_constr b in
       let body = Utils.drop_all_lambdas Evd.empty t in
       let open Constr in
       let open EConstr in
       match kind Evd.empty body with
       | Prod _  | App _ | Const _ | Ind _ | Sort _ | Var _ | Rel _ | Construct _ | Int _ -> true
       | Case _ | LetIn _ | Cast _ -> b_aggressive
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

let unfold c = Tactics.unfold_constr (GlobRef.ConstRef c)

let fullunfold c = fullunfold_tac (DAst.make (Glob_term.GRef (GlobRef.ConstRef c, None)), None)

let sunfold b_aggressive c =
  if is_simple_unfold b_aggressive c then
    fullunfold c
  else
    Tacticals.New.tclIDTAC

let unfolding opts =
  let do_unfolding lst =
    Tacticals.New.tclREPEAT
      (List.fold_left
         (fun acc c -> sunfold opts.s_aggressive_unfolding c <*> acc)
         Tacticals.New.tclIDTAC
         lst)
  in
  match opts.s_unfolding with
  | SSome lst -> do_unfolding (!unfolding_hints @ lst)
  | SNoHints lst -> do_unfolding lst
  | SAll ->
     Proofview.Goal.enter begin fun gl ->
       do_unfolding
         (get_consts (Proofview.Goal.sigma gl)
            (Proofview.Goal.concl gl :: List.map snd (Utils.get_hyps gl)))
     end
  | SNone -> Tacticals.New.tclIDTAC

let sunfolding b_aggressive =
  unfolding { default_s_opts with s_unfolding = SAll; s_aggressive_unfolding = b_aggressive }

(*****************************************************************************************)

let in_sopt_list hints x opt =
  match opt with
  | SAll -> true
  | SSome lst when (List.mem x lst || List.mem x hints) -> true
  | SNoHints lst when List.mem x lst -> true
  | _ -> false

let in_sopt_list_explicitly hints x opt =
  match opt with
  | SAll -> false
  | SSome lst when (List.mem x lst || List.mem x hints) -> true
  | SNoHints lst when List.mem x lst -> true
  | _ -> false

let is_constr_non_recursive ind t =
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

let has_dangling_evars evd t =
  let (prods, head, args) = Utils.destruct_prod evd t in
  let app = EConstr.mkApp (head, Array.of_list args) in
  let rec go t k =
    let open Constr in
    let open EConstr in
    match kind evd t with
    | Prod (na, ty, body) ->
       if not (Utils.rel_occurs evd body [1]) then
         go body (k - 1)
       else if Utils.rel_occurs evd app [k] then
         go body (k - 1)
       else
         true
    | _ ->
       false
  in
  go t (List.length prods)

(* check if the inductive type is non-recursive with at most two
   constructors *)
let is_eager_ind ind =
  let cstrs = Utils.get_ind_constrs ind in
  match cstrs with
  | [] -> true
  | [ t ] -> is_constr_non_recursive ind t
  | [ t1; t2 ] -> is_constr_non_recursive ind t1 && is_constr_non_recursive ind t2
  | _ -> false

(* check if the inductive type is non-recursive with exactly one
   constructor and no dangling evars *)
let is_simple_ind ind =
  let cstrs = Utils.get_ind_constrs ind in
  match cstrs with
  | [ t ] -> is_constr_non_recursive ind t && not (has_dangling_evars Evd.empty (EConstr.of_constr t))
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
      Utils.fold_constr_shallow begin fun acc t ->
        let open Constr in
        let open EConstr in
        match kind evd t with
        | Case (ci, _, _, _) when in_sopt_list !case_split_hints ci.ci_ind opts.s_case_splits -> raise Exit
        | _ -> acc
      end false evd t
    with Exit ->
      true

let is_inversion opts evd ind args =
  in_sopt_list !inversion_hints ind opts.s_inversions &&
    if ind = Utils.get_inductive "Init.Logic.eq" then
      match args with
      | [_; t1; t2] ->
         begin
           let open Constr in
           let open EConstr in
           match (kind evd (Utils.get_app_head evd t1), kind evd (Utils.get_app_head evd t2)) with
           | (Construct _, Construct _) -> true
           | _ -> false
         end
      | _ -> false
    else
      true

let is_eager_inversion opts evd t =
  let open Constr in
  let open EConstr in
  let (head, args) = Utils.destruct_app evd t in
  match kind evd head with
  | Ind (ind, _) when is_eager_ind ind ->
     is_inversion opts evd ind args
  | _ -> false

(*****************************************************************************************)

let is_equality evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Ind(ind, _) when ind = Utils.get_inductive "eq" -> true
  | _ -> false

(*****************************************************************************************)

let rec brepeat n t =
  if n = 0 then
    Proofview.tclUNIT ()
  else
    Proofview.tclINDEPENDENT begin
      Proofview.tclIFCATCH t
        (fun () -> Proofview.tclCHECKINTERRUPT <*> brepeat (n - 1) t)
        (fun e -> Tacticals.New.catch_failerror e <*> Proofview.tclUNIT ())
    end

let repeat t =
  brepeat 8 (Tacticals.New.tclPROGRESS t)

let repeat2 tac1 tac2 =
  Tacticals.New.tclTHEN tac1
    (repeat
       (Tacticals.New.tclTHEN (Tacticals.New.tclPROGRESS tac2) tac1))

let (<~>) = repeat2

let rec repeat_when p f =
  Proofview.Goal.enter begin fun gl ->
    let evd = Proofview.Goal.sigma gl in
    let rec go hyps =
      match hyps with
      | [] -> Tacticals.New.tclIDTAC
      | (id, hyp) :: hyps' ->
         if p evd hyp then
           f id <*> repeat_when p f
         else
           go hyps'
    in
    go (Utils.get_hyps gl)
  end

let rec do_when p f forbidden_ids =
  Proofview.Goal.enter begin fun gl ->
    let evd = Proofview.Goal.sigma gl in
    let rec go hyps =
      match hyps with
      | [] -> Tacticals.New.tclIDTAC
      | (id, hyp) :: hyps' ->
         if not (List.mem id forbidden_ids) && p evd hyp then
           f id <*> do_when p f (id :: forbidden_ids)
         else
           go hyps'
    in
    go (Utils.get_hyps gl)
  end

let do_when p f = do_when p f []

let opt b tac = if b then tac else Tacticals.New.tclIDTAC

let with_reduction opts tac1 tac2 =
  if opts.s_eager_reducing && opts.s_reducing then tac1 else tac2

let autorewriting b_all opts = autorewrite b_all opts.s_rew_bases

let rec simple_splitting opts =
  if opts.s_simple_splits = SNone then
    Proofview.tclUNIT ()
  else
    Proofview.Goal.enter begin fun gl ->
      let goal = Proofview.Goal.concl gl in
      let evd = Proofview.Goal.sigma gl in
      if is_simple_split opts evd goal then
        Tactics.constructor_tac true None 1 NoBindings <*>
          reduce_concl opts <*> simple_splitting opts
      else
        Tacticals.New.tclIDTAC
  end

let case_splitting b_all opts =
  match opts.s_case_splits with
  | SAll ->
     if b_all then
       with_reduction opts case_splitting_tac case_splitting_nocbn_tac
     else
       with_reduction opts case_splitting_concl_tac case_splitting_concl_nocbn_tac
  | SNone -> Tacticals.New.tclIDTAC
  | _ ->
     let introp =
       Some (CAst.make (IntroAndPattern [CAst.make (IntroAction IntroWildcard)]))
     in
     Proofview.Goal.enter begin fun gl ->
       let evd = Proofview.Goal.sigma gl in
       Utils.fold_constr_shallow begin fun acc t ->
         let open Constr in
         let open EConstr in
         match kind evd t with
         | Case (ci, _, c, _) when in_sopt_list !case_split_hints ci.ci_ind opts.s_case_splits ->
            Proofview.tclTHEN (Tactics.destruct false None c introp None <*> subst_simpl opts) acc
         | _ -> acc
       end (Proofview.tclUNIT ())
         (Proofview.Goal.sigma gl)
         (Proofview.Goal.concl gl)
     end

let eager_inverting opts =
  match opts.s_inversions with
  | SNone -> Tacticals.New.tclIDTAC
  | _ ->
     do_when
       begin fun evd hyp ->
         let (head, args) = Utils.destruct_app evd hyp in
         let open Constr in
         let open EConstr in
         match kind evd head with
         | Ind(ind, _) when is_eager_inversion opts evd hyp -> true
         | _ -> false
       end
       (fun id -> sinvert opts id <*> subst_simpl opts)

let simple_inverting opts =
  match opts.s_inversions with
  | SAll -> with_reduction opts simple_inverting_tac simple_inverting_nocbn_tac
  | SNone -> Tacticals.New.tclIDTAC
  | _ ->
     repeat_when
       begin fun evd hyp ->
         let (head, args) = Utils.destruct_app evd hyp in
         let open Constr in
         let open EConstr in
         match kind evd head with
         | Ind(ind, _) when is_inversion opts evd ind args -> true
         | _ -> false
       end
       (with_reduction opts simple_invert_tac simple_invert_nocbn_tac)

let simplify opts =
  let simpl1 =
    simp_hyps_tac <~>
      opt opts.s_bnat_reflect bnat_reflect_tac <~>
      opts.s_simpl_tac <~>
      reduce_concl opts <~>
      (Tacticals.New.tclPROGRESS intros_until_atom_tac <*> subst_simpl opts) <~>
      simple_splitting opts <~>
      autorewriting true opts <~>
      opt opts.s_eager_rewriting srewriting_tac <~>
      case_splitting true opts <~>
      opt opts.s_eager_inverting (eager_inverting opts) <~>
      opt opts.s_simple_inverting (simple_inverting opts)
  in
  if opts.s_forwarding then
    simpl1 <*>
      (Tacticals.New.tclTRY
         (Tacticals.New.tclPROGRESS (with_reduction opts forwarding_tac forwarding_nocbn_tac) <*>
            simpl1))
  else
    simpl1

let simplify_concl opts =
  (reduce_concl opts <~> autorewriting false opts) <*>
    Tacticals.New.tclTRY (Tacticals.New.tclPROGRESS (case_splitting false opts) <*> simplify opts)

(*****************************************************************************************)

let eval_hyp evd (id, hyp) =
  let (prods, head, args) = Utils.destruct_prod evd hyp in
  let app = EConstr.mkApp (head, Array.of_list args) in
  let n = List.length prods in
  let rec go t m m' k =
    let open Constr in
    let open EConstr in
    match kind evd t with
    | Prod (na, ty, body) ->
       if not (Utils.rel_occurs evd body [1]) then
         go body (m + 1) m' (k - 1)
       else
         if Utils.rel_occurs evd app [k] then
           go body m m' (k - 1)
         else
           go body m (m' + 1) (k - 1)
    | _ -> (m, m')
  in
  let (num_subgoals, num_dangling_evars) = go hyp 0 0 n in
  (id, hyp, n + num_subgoals * 10 + num_dangling_evars * 10, num_subgoals, (prods, head, args))

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

let create_hyp_actions opts evd ghead (id, hyp, cost, num_subgoals, (prods, head, args)) =
  let acts =
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
  in
  if opts.s_rewriting && is_equality evd head then
    begin
      match Hhlib.drop (List.length args - 2) args with
      | [t1; t2] ->
         if Lpo.lpo evd t1 t2 then
           (cost + 5, num_subgoals, ActRewriteLR id) :: acts
         else if Lpo.lpo evd t2 t1 then
           (cost + 5, num_subgoals, ActRewriteRL id) :: acts
         else if opts.s_heuristic_rewriting then
           (cost - num_subgoals * 5, 1, ActRewrite id) :: acts
         else
           acts
      | _ ->
         acts
    end
  else
    acts

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
  match kind evd head with
  | Ind (ind, _) when is_inversion opts evd ind args ->
     let ctrs = Utils.get_ind_constrs ind in
     let num_ctrs = List.length ctrs in
     let b_arg_dep = num_ctrs <= 1 || has_arg_dep args in
     if b_arg_dep || in_sopt_list_explicitly !inversion_hints ind opts.s_inversions then
       let deps =
         List.length (List.filter
                        begin fun t ->
                          match Utils.destruct_prod evd (EConstr.of_constr t) with
                          | (_, _, args) -> not (has_arg_dep args)
                        end
                        ctrs)
       in
       let deps = if deps = num_ctrs then deps - 1 else deps in
       [(cost + 40 + if b_arg_dep then deps * 10 else num_ctrs * 10),
        (if b_arg_dep then num_subgoals + max deps 1 else num_subgoals + num_ctrs),
        ActInvert id]
     else
       []
  | _ ->
     []

let create_case_unfolding_actions opts evd goal hyps =
  if opts.s_aggressive_unfolding then
    []
  else
    let create lst =
      List.fold_left begin fun acc c ->
        let cost = case_unfold_cost c in
        if cost >= 0 then
          (cost, 1, ActCaseUnfold c) :: acc
        else
          acc
      end [] lst
    in
    match opts.s_unfolding with
    | SSome lst -> create (!unfolding_hints @ lst)
    | SNoHints lst -> create lst
    | SAll -> create (get_consts evd (goal :: List.map (fun (_, x, _, _, _) -> x) hyps))
    | SNone -> []

let create_extra_actions opts evd goal hyps =
  let actions =
    List.concat (List.map (create_extra_hyp_actions opts evd) hyps)
  in
  let actions =
    create_case_unfolding_actions opts evd goal hyps @ actions
  in
  let actions =
    if opts.s_eager_reducing || not opts.s_reducing then
      actions
    else
      (80, 1, ActReduce) :: actions
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
    List.concat (List.map (create_hyp_actions opts evd ghead) hyps) @ actions
  in
  List.stable_sort (fun (x, _, _) (y, _, _) -> Pervasives.compare x y) actions

(*****************************************************************************************)

type tactics = {
  t_simplify : unit Proofview.tactic;
  t_simplify_concl : unit Proofview.tactic;
  t_simple_splitting : unit Proofview.tactic;
  t_case_splitting : unit Proofview.tactic;
  t_unfolding : unit Proofview.tactic;
  t_reduce_concl : unit Proofview.tactic;
  t_subst_simpl : unit Proofview.tactic;
}

let create_tactics opts = {
  t_simplify = simplify opts;
  t_simplify_concl = simplify_concl opts;
  t_simple_splitting = simple_splitting opts;
  t_case_splitting = case_splitting false opts;
  t_unfolding = unfolding opts;
  t_reduce_concl = reduce_concl opts;
  t_subst_simpl = subst_simpl opts;
}

(*****************************************************************************************)

let rec search extra tacs opts n rtrace visited =
  if n = 0 then
    opts.s_leaf_tac
  else
    Proofview.Goal.enter begin fun gl ->
      let goal = Proofview.Goal.concl gl in
      if List.mem goal visited then
        fail_tac
      else
        let evd = Proofview.Goal.sigma gl in
        let open Constr in
        let open EConstr in
        match kind evd goal with
        | Prod (_, h, f) when not (Utils.is_atom evd h) || not (Utils.is_False evd f) ->
           intros tacs opts n
        | _ ->
           if is_simple_split opts evd goal then
             tacs.t_simple_splitting <*> search extra tacs opts n rtrace (goal :: visited)
           else if is_case_split opts evd goal then
             tacs.t_case_splitting <*> start_search tacs opts n
           else
             let hyps = List.map (eval_hyp evd) (Utils.get_hyps gl) in
             let actions = create_actions extra opts evd goal hyps in
             match actions with
             | [] -> opts.s_leaf_tac
             | (cost, _, _) :: _ when not opts.s_depth_cost_model && cost > n -> opts.s_leaf_tac
             | _ -> apply_actions tacs opts n actions rtrace (goal :: visited)
    end

and start_search tacs opts n =
  tacs.t_unfolding <*> tacs.t_simplify <*> search true tacs opts n [] []

and intros tacs opts n =
  tacs.t_reduce_concl <*>
    intros_until_atom_tac <*>
    start_search tacs opts n

and apply_actions tacs opts n actions rtrace visited =
  let branch =
    if opts.s_exhaustive then Proofview.tclOR else Proofview.tclORELSE
  in
  let cont tac acts =
    branch tac (fun _ -> apply_actions tacs opts n acts rtrace visited)
  in
  let continue n tac acts =
    cont (Proofview.tclBIND tac (fun _ -> search false tacs opts n rtrace visited)) acts
  in
  match actions with
  | (cost, branching, act) :: acts ->
     if not opts.s_depth_cost_model && cost > n then
       fail_tac (* should replace this with leaf_tac? *)
     else
       begin
         let n' =
           if opts.s_depth_cost_model then
             n - 1
           else
             (n - cost) / max branching 1
         in
         match act with
         | ActApply id ->
            continue n' (Tactics.Simple.eapply (EConstr.mkVar id)) acts
         | ActRewriteLR id ->
            continue n' (erewrite (not opts.s_eager_rewriting) true id <*> tacs.t_simplify_concl) acts
         | ActRewriteRL id ->
            continue n' (erewrite (not opts.s_eager_rewriting) false id <*> tacs.t_simplify_concl) acts
         | ActRewrite id ->
            if List.memq id rtrace then
              apply_actions tacs opts n acts rtrace visited
            else
              cont (Proofview.tclBIND (srewrite_tac id)
                      (fun _ ->
                        tacs.t_simplify_concl <*> search false tacs opts n (id :: rtrace) visited))
                acts
         | ActInvert id ->
            cont (sinvert opts id <*> start_search tacs opts n') acts
         | ActUnfold c ->
            continue n' (Tacticals.New.tclPROGRESS (unfold c) <*> tacs.t_simplify_concl) acts
         | ActCaseUnfold c ->
            cont (Proofview.tclBIND
                    (Tacticals.New.tclPROGRESS (fullunfold c))
                    (fun _ -> start_search tacs opts n')) acts
         | ActConstructor ->
            cont
              (Tactics.any_constructor true
                 (Some (tacs.t_simplify_concl <*> search false tacs opts n' rtrace visited)))
              acts
         | ActIntro ->
            cont (Tactics.intros <*> tacs.t_subst_simpl <*> start_search tacs opts n') acts
         | ActReduce ->
            cont (Proofview.tclBIND
                    (Tacticals.New.tclPROGRESS cbn_in_all_tac)
                    (fun _ -> start_search tacs opts n')) acts
       end
  | [] ->
     fail_tac

(*****************************************************************************************)

let sintuition opts =
  Tactics.intros <*> simp_hyps_tac <*> ssubst_tac <*> Tacticals.New.tclTRY opts.s_simpl_tac <*>
    Tacticals.New.tclREPEAT (Tacticals.New.tclPROGRESS
                               (Tactics.intros <*> simp_hyps_tac <*> ssubst_tac) <*>
                               Tacticals.New.tclTRY opts.s_simpl_tac)

let ssimpl opts =
  let tac1 =
    Tactics.intros <*> unfolding opts <*> sintuition opts <*> subst_simpl opts <*>
      simp_hyps_tac <*> with_reduction opts forwarding_tac forwarding_nocbn_tac <*>
      subst_simpl opts
  and tac2 =
    Tactics.intros <*> unfolding opts <*>
      opt opts.s_forwarding (with_reduction opts forwarding_tac forwarding_nocbn_tac) <*>
      subst_simpl opts
  in
  tac1 <*> (simplify opts <~> tac2)

let qsimpl opts =
  let tac =
    (sintuition opts <*> subst_simpl opts) <~>
      opt opts.s_bnat_reflect bnat_reflect_tac <~>
      autorewriting true opts <~>
      (simple_splitting opts <*> case_splitting true opts) <~>
      opt opts.s_simple_inverting (simple_inverting opts)
  in
  Tactics.intros <*> unfolding opts <*> tac

let sauto opts n =
  let simp =
    if opts.s_presimplify then
      ssimpl opts
    else
      Proofview.tclUNIT ()
  in
  simp <*> unfolding opts <*> subst_simpl opts <*>
    intros (create_tactics opts) opts n

let print_actions opts =
  Proofview.Goal.enter begin fun gl ->
    let goal = Proofview.Goal.concl gl in
    let evd = Proofview.Goal.sigma gl in
    let hyps = List.map (eval_hyp evd) (Utils.get_hyps gl) in
    let actions = create_actions true opts evd goal hyps in
    print_search_actions actions;
    Tacticals.New.tclIDTAC
  end
