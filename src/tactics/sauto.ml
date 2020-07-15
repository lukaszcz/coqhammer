(* sauto -- implementation *)

open Names
open Tactypes
open Locus
open Proofview.Notations
open Ltac_plugin

module Utils = Hhutils
module Lpo = Hhlpo

type 'a soption = SNone | SAll | SSome of 'a

type s_opts = {
  s_exhaustive : bool;
  s_hints : bool;
  s_leaf_tac : unit Proofview.tactic;
  s_leaf_nolia_tac : unit Proofview.tactic;
  s_solve_tac : unit Proofview.tactic;
  s_simpl_tac : unit Proofview.tactic;
  s_simpl_nolia_tac : unit Proofview.tactic;
  s_ssimpl_tac : unit Proofview.tactic;
  s_ssimpl_nolia_tac : unit Proofview.tactic;
  s_unfolding : Constant.t list soption;
  s_always_unfold : Constant.t list soption;
  s_constructors : inductive list soption;
  s_simple_splits : inductive list soption;
  s_case_splits : inductive list soption;
  s_inversions : inductive list soption;
  s_rew_bases : string list;
  s_hint_bases : Hints.hint_db list;
  s_reflect : bool;
  s_eager_case_splitting : bool;
  s_eager_reducing : bool;
  s_eager_rewriting : bool;
  s_eager_inverting : bool;
  s_simple_inverting : bool;
  s_forwarding : bool;
  s_reducing : bool;
  s_rewriting : bool;
  s_heuristic_rewriting : bool;
  s_aggressive_unfolding : bool;
  s_sapply : bool;
  s_depth_cost_model : bool;
  s_limit : int;
  s_prerun : bool;
  s_simpl_sigma : bool;
  s_lia : bool;
  s_dep : bool;
  s_genproofs : bool;
}

let default_s_opts () = {
  s_exhaustive = false;
  s_hints = true;
  s_leaf_tac = Utils.ltac_apply "Tactics.leaf_solve" [];
  s_leaf_nolia_tac = Utils.ltac_apply "Tactics.leaf_solve_nolia" [];
  s_solve_tac = Utils.ltac_apply "fail" [];
  s_simpl_tac = Tacticals.New.tclTRY (Utils.ltac_apply "Tactics.simpl_solve" []);
  s_simpl_nolia_tac = Tacticals.New.tclTRY (Utils.ltac_apply "Tactics.simpl_solve_nolia" []);
  s_ssimpl_tac = Tacticals.New.tclTRY (Utils.ltac_apply "Tactics.ssolve" []);
  s_ssimpl_nolia_tac = Tacticals.New.tclTRY (Utils.ltac_apply "Tactics.ssolve_nolia" []);
  s_unfolding = SSome [];
  s_always_unfold = SNone;
  s_constructors = SAll;
  s_simple_splits = SSome [];
  s_case_splits = SAll;
  s_inversions = SAll;
  s_rew_bases = [];
  s_hint_bases = [];
  s_reflect = false;
  s_eager_case_splitting = true;
  s_eager_reducing = true;
  s_eager_rewriting = true;
  s_eager_inverting = true;
  s_simple_inverting = true;
  s_forwarding = true;
  s_reducing = true;
  s_rewriting = true;
  s_heuristic_rewriting = true;
  s_aggressive_unfolding = false;
  s_sapply = true;
  s_depth_cost_model = false;
  s_limit = 1000;
  s_prerun = false; (* "true" slows things down *)
  s_simpl_sigma = true;
  s_lia = true;
  s_dep = false;
  s_genproofs = false;
}

let hauto_s_opts () =
  { (default_s_opts ()) with s_inversions = SSome [];
                             s_constructors = SSome [] }

let eauto_tac = Eauto.gen_eauto (Eauto.make_dimension None None) [] (Some [])
let congr_tac () = Utils.ltac_apply "Tactics.congr_tac" []
let lia_tac () = Utils.ltac_apply "Tactics.lia_tac" []

let qauto_s_opts () =
  { (hauto_s_opts ()) with s_simpl_tac = Tacticals.New.tclIDTAC;
                           s_simpl_nolia_tac = Tacticals.New.tclIDTAC;
                           s_leaf_tac = (eauto_tac <*>
                                           Tacticals.New.tclTRY (congr_tac ()) <*>
                                           lia_tac ());
                           s_leaf_nolia_tac = (eauto_tac <*> congr_tac ());
                           s_sapply = false;
                           s_limit = 100;
                           s_prerun = true;
                           s_lia = false }

let set_dep_opts b opts =
  if b then
    { opts with s_dep = true;
                s_genproofs = true;
                s_eager_inverting = false;
                s_simple_inverting = false }
  else
    { opts with s_dep = false }

let set_eager_opts b opts =
  { opts with s_eager_reducing = b;
              s_eager_rewriting = b;
              s_eager_case_splitting = b;
              s_eager_inverting = b;
              s_simple_inverting = b;
              s_simpl_sigma = b }

let set_quick_opts b opts =
  if b then
    { opts with s_inversions = SSome [];
                s_constructors = SSome [];
                s_simpl_tac = Tacticals.New.tclIDTAC;
                s_simpl_nolia_tac = Tacticals.New.tclIDTAC;
                s_leaf_tac = Utils.ltac_apply "Tactics.sdone_tac" [];
                s_leaf_nolia_tac = Utils.ltac_apply "Tactics.sdone_nolia_tac" [];
                s_sapply = false;
                s_lia = false }
  else
    opts

let with_reduction opts tac1 tac2 =
  if opts.s_eager_reducing && opts.s_reducing then tac1 else tac2

(*****************************************************************************************)

let coq_equality = Utils.get_inductive "Init.Logic.eq"
let logic_constants = [ Utils.get_const "Init.Logic.iff"; Utils.get_const "Init.Logic.not" ]
let logic_inductives = [ Utils.get_inductive "Init.Logic.and"; Utils.get_inductive "Init.Logic.or";
                         Utils.get_inductive "Init.Logic.ex"; Utils.get_inductive "Init.Datatypes.prod";
                         Utils.get_inductive "Init.Specif.sumbool"; Utils.get_inductive "Init.Specif.sig";
                         Utils.get_inductive "Init.Datatypes.sum"; Utils.get_inductive "Init.Specif.sigT";
                         Utils.get_inductive "Init.Logic.False"; Utils.get_inductive "Init.Logic.eq" ]

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
        ActDestruct of EConstr.t | ActHint of Utils.hint |
        ActConstructor | ActIntro | ActReduce | ActFEqual

let action_to_string act =
  match act with
  | ActApply id -> "apply " ^ Id.to_string id
  | ActRewriteLR id -> "rewrite -> " ^ Id.to_string id
  | ActRewriteRL id -> "rewrite <- " ^ Id.to_string id
  | ActRewrite id -> "srewrite " ^ Id.to_string id
  | ActInvert id -> "invert " ^ Id.to_string id
  | ActUnfold c -> "unfold " ^ Constant.to_string c
  | ActCaseUnfold c -> "case-unfold " ^ Constant.to_string c
  | ActDestruct t -> "destruct " ^ Utils.constr_to_string Evd.empty t
  | ActHint h -> Utils.hint_to_string h
  | ActConstructor -> "constructor"
  | ActIntro -> "intro"
  | ActReduce -> "reduce"
  | ActFEqual -> "f_equal"

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

let simp_hyps_tac () = Utils.ltac_apply "Tactics.simp_hyps" []
let esimp_hyps_tac () = Utils.ltac_apply "Tactics.esimp_hyps" []
let fail_tac = Utils.ltac_apply "fail" []
let sinvert_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.sinvert" [mk_tac_arg_id id])
let seinvert_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.seinvert" [mk_tac_arg_id id])
let sdepinvert_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.sdepinvert" [mk_tac_arg_id id])
let sedepinvert_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.sedepinvert" [mk_tac_arg_id id])
let ssubst_tac () = Utils.ltac_apply "Tactics.ssubst" []
let subst_simpl_tac () = Utils.ltac_apply "Tactics.subst_simpl" []
let srewrite_tac id = Tacticals.New.tclPROGRESS (Utils.ltac_apply "Tactics.srewrite" [mk_tac_arg_id id])
let intros_until_atom_tac () = Utils.ltac_apply "Tactics.intros_until_atom" []
let simple_inverting_tac opts =
  Utils.ltac_apply
    (if opts.s_dep then
       with_reduction opts
         "Tactics.simple_inverting_dep"
         "Tactics.simple_inverting_dep_nored"
     else
       with_reduction opts
         "Tactics.simple_inverting"
         "Tactics.simple_inverting_nored")
    []
let simple_invert_tac opts id =
  Utils.ltac_apply
    (if opts.s_dep then
       with_reduction opts
         "Tactics.simple_invert_dep"
         "Tactics.simple_invert_dep_nored"
     else
       with_reduction opts
         "Tactics.simple_invert"
         "Tactics.simple_invert_nored")
    [mk_tac_arg_id id]
let sapply_tac id = Utils.ltac_apply "Tactics.sapply" [mk_tac_arg_id id]
let case_splitting_tac opts =
  Utils.ltac_apply
    (if opts.s_dep then
       with_reduction opts
         "Tactics.case_splitting_dep"
         "Tactics.case_splitting_dep_nored"
     else
       with_reduction opts
         "Tactics.case_splitting"
         "Tactics.case_splitting_nored")
    []
let case_splitting_concl_tac opts =
  Utils.ltac_apply
    (if opts.s_dep then
       with_reduction opts
         "Tactics.case_splitting_concl_dep"
         "Tactics.case_splitting_concl_dep_nored"
     else
       with_reduction opts
         "Tactics.case_splitting_concl"
         "Tactics.case_splitting_concl_nored")
    []
let case_splitting_on_tac opts ind =
  Utils.ltac_eval
    (if opts.s_dep then
       with_reduction opts
         "Tactics.case_splitting_on_dep"
         "Tactics.case_splitting_on_dep_nored"
     else
       with_reduction opts
         "Tactics.case_splitting_on"
         "Tactics.case_splitting_on_nored")
    [Tacinterp.Value.of_constr (EConstr.mkInd ind)]
let case_splitting_concl_on_tac opts ind =
  Utils.ltac_eval
    (if opts.s_dep then
       with_reduction opts
         "Tactics.case_splitting_concl_on_dep"
         "Tactics.case_splitting_concl_on_dep_nored"
     else
       with_reduction opts
         "Tactics.case_splitting_concl_on"
         "Tactics.case_splitting_concl_on_nored")
    [Tacinterp.Value.of_constr (EConstr.mkInd ind)]
let forwarding_tac () = Utils.ltac_apply "Tactics.forwarding" []
let forwarding_nored_tac () = Utils.ltac_apply "Tactics.forwarding_nored" []
let srewriting_tac () = Utils.ltac_apply "Tactics.srewriting" []
let bnat_reflect_tac () = Utils.ltac_apply "Tactics.bnat_reflect" []
let bool_reflect_tac () = Utils.ltac_apply "Tactics.bool_reflect" []
let fullunfold_tac t = Utils.ltac_apply "Tactics.fullunfold" [mk_tac_arg_constr t]
let red_in_concl_tac () = Utils.ltac_apply "Tactics.red_in_concl" []
let red_in_all_tac () = Utils.ltac_apply "Tactics.red_in_all" []
let dsolve_tac () = Utils.ltac_apply "Tactics.dsolve" []
let qforwarding_tac () = Utils.ltac_apply "Tactics.qforwarding" []
let instering_tac () = Utils.ltac_apply "Tactics.instering" []
let einstering_tac () = Utils.ltac_apply "Tactics.einstering" []
let f_equal_tac () = Utils.ltac_apply "Tactics.f_equal_tac" []
let simpl_sigma_tac () = Utils.ltac_apply "Tactics.simpl_sigma" []
let generalize_proofs_tac () = Utils.ltac_apply "Tactics.generalize_proofs" []
let unfold_local_defs_tac () = Utils.ltac_apply "Tactics.unfold_local_defs" []

(*****************************************************************************************)

let eq_ind (mi1, i1) (mi2, i2) = i1 = i2 && MutInd.equal mi1 mi2

let rec mem_constr evd x lst =
  match lst with
  | [] -> false
  | h :: t -> if EConstr.eq_constr evd x h then true else mem_constr evd x t

let rec mem_ind ind lst =
  match lst with
  | [] -> false
  | h :: t -> if eq_ind ind h then true else mem_ind ind t

let rec mem_const c lst =
  match lst with
  | [] -> false
  | h :: t -> if Constant.equal c h then true else mem_const c t

(*****************************************************************************************)

module IndHash =
  struct
    type t = inductive
    let equal = eq_ind
    let hash (mi, _) = MutInd.hash mi
  end

module IndMemo = Hhlib.MakeMemo(IndHash)

let memoize_ind = IndMemo.memoize

(*****************************************************************************************)

let opt b tac = if b then tac else Tacticals.New.tclIDTAC

let autorewrite b_all bases =
  if bases = [] then
    Proofview.tclUNIT ()
  else
    Autorewrite.auto_multi_rewrite
      bases
      { onhyps = if b_all then None else Some []; concl_occs = AllOccurrences }

let subst_simpl opts =
  opt opts.s_simpl_sigma (simpl_sigma_tac ()) <*>
    if opts.s_eager_reducing && opts.s_reducing then
      subst_simpl_tac ()
    else
      ssubst_tac ()

let sinvert opts id =
  let sinv =
    if opts.s_exhaustive then
      if opts.s_dep then
        sedepinvert_tac id
      else
        seinvert_tac id
    else
      if opts.s_dep then
        sdepinvert_tac id
      else
        sinvert_tac id
  in
  sinv <*> subst_simpl opts

let reduce_concl opts =
  if opts.s_eager_reducing && opts.s_reducing then
    red_in_concl_tac ()
  else
    Proofview.tclUNIT ()

(*****************************************************************************************)

let leaf_tac opts = if opts.s_lia then opts.s_leaf_tac else opts.s_leaf_nolia_tac
let simpl_tac opts = if opts.s_lia then opts.s_simpl_tac else opts.s_simpl_nolia_tac
let ssimpl_tac opts = if opts.s_lia then opts.s_ssimpl_tac else opts.s_ssimpl_nolia_tac

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
  match Global.body_of_constant Library.indirect_accessor c with
  | Some (b, _, _) ->
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
  match Global.body_of_constant Library.indirect_accessor c with
  | Some (b, _, _) ->
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

let fullunfolding opts =
  match opts.s_always_unfold with
  | SSome lst ->
     List.fold_left (fun tac c -> tac <*> fullunfold c) Tacticals.New.tclIDTAC lst
  | SNone -> Tacticals.New.tclIDTAC
  | SAll -> Utils.ltac_apply "Tactics.fullunfold_all" []

let sunfold b_aggressive c =
  if is_simple_unfold b_aggressive c then
    fullunfold c
  else
    Tacticals.New.tclIDTAC

let sdestruct opts t =
  if opts.s_dep then
    Utils.ltac_eval "Tactics.sdepdestruct" [Tacinterp.Value.of_constr t]
  else
    Utils.ltac_eval "Tactics.sdestruct" [Tacinterp.Value.of_constr t]

(* TODO: port gunfolding from Reconstr.v *)
let unfolding opts =
  let do_unfolding lst =
    Tacticals.New.tclREPEAT
      (List.fold_left
         (fun acc c -> sunfold opts.s_aggressive_unfolding c <*> acc)
         Tacticals.New.tclIDTAC
         lst)
  in
  match opts.s_unfolding with
  | SSome lst ->
     if opts.s_hints then
       do_unfolding (!unfolding_hints @ lst)
     else
       do_unfolding lst
  | SAll ->
     Proofview.Goal.enter begin fun gl ->
       do_unfolding
         (get_consts (Proofview.Goal.sigma gl)
            (Proofview.Goal.concl gl :: List.map snd (Utils.get_hyps gl)))
     end
  | SNone -> Tacticals.New.tclIDTAC

let sunfolding b_aggressive =
  unfolding { (default_s_opts ()) with
      s_unfolding = SAll; s_aggressive_unfolding = b_aggressive }

(*****************************************************************************************)

let in_sopt_list mem b_hints hints x opt =
  match opt with
  | SAll -> true
  | SSome lst when mem x lst || (b_hints && mem x hints) -> true
  | _ -> false

let in_sopt_list_ind = in_sopt_list mem_ind
let in_sopt_list_const = in_sopt_list mem_const

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
      | Ind (ind2, _) when eq_ind ind2 ind -> false
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
let is_eager_ind =
  memoize_ind begin fun ind ->
    let cstrs = Utils.get_ind_constrs ind in
    match cstrs with
    | [] -> true
    | [ t ] -> is_constr_non_recursive ind t
    | [ t1; t2 ] -> is_constr_non_recursive ind t1 && is_constr_non_recursive ind t2
    | _ -> false
  end

(* check if the inductive type is (non-indexed?) non-recursive with
   exactly one constructor and no dangling evars *)
let is_simple_ind =
  memoize_ind begin fun ind ->
    let cstrs = Utils.get_ind_constrs ind in
    match cstrs with
    | [ t ] -> is_constr_non_recursive ind t && not (has_dangling_evars Evd.empty (EConstr.of_constr t))
    | _ -> false
  end

let is_simple_split opts evd t =
  let open Constr in
  let open EConstr in
  let head = Utils.get_head_red evd t in
  match kind evd head with
  | Ind (ind, _) when is_simple_ind ind ->
     in_sopt_list_ind opts.s_hints !simple_split_hints ind opts.s_simple_splits
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
        | Case (ci, _, _, _, _) when
               in_sopt_list_ind opts.s_hints !case_split_hints ci.ci_ind opts.s_case_splits ->
           raise Exit
        | _ -> acc
      end false evd t
    with Exit ->
      true

let is_inversion opts evd ind args =
  in_sopt_list_ind opts.s_hints !inversion_hints ind opts.s_inversions &&
    if eq_ind ind coq_equality then
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
  let (_, head, args) = Utils.destruct_app_red evd t in
  match kind evd head with
  | Ind (ind, _) when is_eager_ind ind ->
     is_inversion opts evd ind args
  | _ -> false

(*****************************************************************************************)

let is_equality evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Ind(ind, _) when eq_ind ind coq_equality -> true
  | _ -> false

let with_equality evd head args default f =
  if is_equality evd head then
    match Hhlib.drop (List.length args - 2) args with
    | [t1; t2] -> f t1 t2
    | _ -> default
  else
    default

let is_unorientable_equality evd head args =
  with_equality evd head args false
    begin fun t1 t2 ->
      not (Lpo.lpo evd t1 t2 || Lpo.lpo evd t2 t1)
    end

(*****************************************************************************************)

let is_true_const = Utils.get_const "Init.Datatypes.is_true"

let is_coercion evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Const(c, _) when Constant.equal c is_true_const -> true
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
         if not (List.memq id forbidden_ids) && p evd hyp then
           f id <*> do_when p f (id :: forbidden_ids)
         else
           go hyps'
    in
    go (Utils.get_hyps gl)
  end

let do_when p f = do_when p f []

let autorewriting b_all opts =
  if opts.s_rewriting then
    autorewrite b_all opts.s_rew_bases
  else
    Proofview.tclUNIT ()

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
       case_splitting_tac opts
     else
       case_splitting_concl_tac opts
  | SNone -> Tacticals.New.tclIDTAC
  | SSome lst ->
     let csplit =
       if b_all then
         case_splitting_on_tac opts
       else
         case_splitting_concl_on_tac opts
     in
     List.fold_left (fun tac ind -> tac <*> csplit ind) Tacticals.New.tclIDTAC
       (!case_split_hints @ lst)

let eager_inverting opts =
  match opts.s_inversions with
  | SNone -> Tacticals.New.tclIDTAC
  | _ ->
     do_when
       begin fun evd hyp ->
         let (_, head, args) = Utils.destruct_app_red evd hyp in
         let open Constr in
         let open EConstr in
         match kind evd head with
         | Ind(ind, _) when is_eager_inversion opts evd hyp -> true
         | _ -> false
       end
       (fun id -> sinvert opts id <*> subst_simpl opts)

let simple_inverting opts =
  match opts.s_inversions with
  | SAll -> simple_inverting_tac opts
  | SNone -> Tacticals.New.tclIDTAC
  | _ ->
     repeat_when
       begin fun evd hyp ->
         let (_, head, args) = Utils.destruct_app_red evd hyp in
         let open Constr in
         let open EConstr in
         match kind evd head with
         | Ind(ind, _) when is_inversion opts evd ind args -> true
         | _ -> false
       end
       (simple_invert_tac opts)

let simplify opts =
  let simpl1 =
    simp_hyps_tac () <~>
      opt opts.s_reflect (bnat_reflect_tac ()) <~>
      opt opts.s_eager_case_splitting (case_splitting true opts) <~>
      simpl_tac opts <~>
      reduce_concl opts <~>
      (Tacticals.New.tclPROGRESS
         begin
           opt opts.s_genproofs (generalize_proofs_tac ()) <*>
             intros_until_atom_tac ()
         end <*> subst_simpl opts) <~>
      simple_splitting opts <~>
      autorewriting true opts <~>
      opt opts.s_eager_rewriting (srewriting_tac ()) <~>
      opt opts.s_eager_inverting (eager_inverting opts) <~>
      opt opts.s_simple_inverting (simple_inverting opts)
  in
  fullunfolding opts <*>
    opt opts.s_reflect (bool_reflect_tac ()) <*>
    (if opts.s_forwarding then
       simpl1 <*>
         (Tacticals.New.tclTRY
            (Tacticals.New.tclPROGRESS (with_reduction opts (forwarding_tac ()) (forwarding_nored_tac ())) <*> simpl1))
     else
       simpl1)
  <*> Tacticals.New.tclTRY opts.s_solve_tac

let simplify_concl opts =
  (reduce_concl opts <~> autorewriting false opts) <*>
    if opts.s_eager_case_splitting then
      Tacticals.New.tclTRY (Tacticals.New.tclPROGRESS (case_splitting false opts) <*> simplify opts)
    else
      Proofview.tclUNIT ()

(*****************************************************************************************)

let eval_hyp evd (id, hyp) =
  let (prods, head0, head, args) = Utils.destruct_prod_red evd hyp in
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
  (id, hyp, n + num_subgoals * 10 + num_dangling_evars * 10, num_subgoals, (prods, head0, head, args))

let hyp_cost evd hyp =
  match eval_hyp evd (None, hyp) with
  | (_, _, cost, _, _) -> cost

let hyp_nsubgoals evd hyp =
  match eval_hyp evd (None, hyp) with
  | (_, _, _, num_subgoals, _) -> num_subgoals

let constrs_cost =
  memoize_ind begin fun ind ->
    let evd = Evd.empty in
    let cstrs = Utils.get_ind_constrs ind in
    if cstrs = [] then
      10
    else
      10 + (List.fold_left (fun acc x -> acc + (hyp_cost evd (EConstr.of_constr x))) 0 cstrs) / List.length cstrs
  end

let constrs_nsubgoals =
  memoize_ind begin fun ind ->
    let evd = Evd.empty in
    let cstrs = Utils.get_ind_constrs ind in
    List.fold_left (fun acc x -> max acc (hyp_nsubgoals evd (EConstr.of_constr x))) 0 cstrs
  end

let rec has_arg_dep evd lst =
  let open Constr in
  let open EConstr in
  match lst with
  | [] -> false
  | h :: t ->
     begin
       match kind evd h with
       | App _ | Const _ | Construct _ -> true
       | _ -> has_arg_dep evd t
     end

let eval_ind_inversion =
  memoize_ind begin fun ind ->
    let evd = Evd.empty in
    let ctrs = Utils.get_ind_constrs ind in
    let num_ctrs = List.length ctrs in
    let num_deps =
      List.length (List.filter
                     begin fun t ->
                       match Utils.destruct_prod evd (EConstr.of_constr t) with
                       | (_, _, args) -> not (has_arg_dep evd args)
                     end
                     ctrs)
    in
    let num_deps = if num_deps = num_ctrs then num_deps - 1 else num_deps in
    (num_ctrs, num_deps)
  end

let create_case_actions opts evd t acc =
  Utils.fold_constr_shallow begin fun acc t ->
    let open Constr in
    let open EConstr in
    match kind evd t with
    | Case (ci, _, _, c, _) when
           in_sopt_list_ind opts.s_hints !case_split_hints ci.ci_ind opts.s_case_splits ->
       let num_ctrs = Utils.get_ind_nconstrs ci.ci_ind in
       (40 + num_ctrs * 5, num_ctrs, ActDestruct c) :: acc
    | _ -> acc
  end acc evd t

let create_hyp_actions opts evd ghead0 ghead
      (id, hyp, cost, num_subgoals, (prods, head0, head, args)) =
  let acts =
    if Utils.is_False evd head && prods = [] then
      [(0, 1, ActInvert id)]
    else if EConstr.eq_constr evd head ghead ||
              EConstr.eq_constr evd head0 ghead0 ||
                EConstr.eq_constr evd head0 ghead then
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
  if opts.s_rewriting && is_equality evd head && not (is_coercion evd head0) then
    (* using "with_equality" here slows things down considerably *)
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
    | _ -> acts
  else
    acts

let create_extra_hyp_actions opts evd (id, hyp, cost, num_subgoals, (prods, head0, head, args)) =
  let acts =
    let open Constr in
    let open EConstr in
    match kind evd head with
    | Ind (ind, _) when is_inversion opts evd ind args ->
       let (num_ctrs, num_deps) = eval_ind_inversion ind in
       let b_arg_dep = num_ctrs <= 1 || has_arg_dep evd args in
       [(cost + 40 + if b_arg_dep then num_deps * 10 else num_ctrs * 10),
        (if b_arg_dep then num_subgoals + max num_deps 1 else num_subgoals + num_ctrs),
        ActInvert id]
    | _ ->
       []
  in
  if not opts.s_eager_case_splitting && opts.s_case_splits <> SNone then
    create_case_actions opts evd hyp acts
  else
    acts

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
    | SSome lst ->
       if opts.s_hints then
         create (!unfolding_hints @ lst)
       else
         create lst
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
    if not opts.s_eager_case_splitting && opts.s_case_splits <> SNone then
      create_case_actions opts evd goal actions
    else
      actions
  in
  let actions =
    if opts.s_eager_reducing || not opts.s_reducing then
      actions
    else
      (80, 1, ActReduce) :: actions
  in
  actions

let create_hint_actions bases evd goal gl =
  let secvars = Auto.compute_secvars gl in
  let hints =
    List.concat (List.map (fun db -> Utils.find_hints db secvars evd goal) bases)
  in
  List.map begin fun h ->
    let p = Utils.hint_priority h in
    (p * 10 + 10, p, ActHint h)
  end hints

(* result: (cost, num_subgoals, action) list *)
let create_actions extra opts evd goal hyps gl =
  let actions =
    if extra then create_extra_actions opts evd goal hyps else []
  in
  let actions =
    if opts.s_hint_bases <> [] then
      create_hint_actions opts.s_hint_bases evd goal gl @ actions
    else
      actions
  in
  let actions =
    let open Constr in
    let open EConstr in
    match kind evd goal with
    | Prod _ -> (30, 1, ActIntro) :: actions
    | _ -> actions
  in
  let (_, ghead0, ghead, gargs) = Utils.destruct_prod_red evd goal in
  let actions =
    let open Constr in
    let open EConstr in
    match kind evd ghead with
    | Ind (ind, _) when
           in_sopt_list_ind opts.s_hints !constructor_hints ind opts.s_constructors ->
       (constrs_cost ind, constrs_nsubgoals ind, ActConstructor) :: actions
    | _ ->
       actions
  in
  let actions =
    with_equality evd ghead0 gargs actions
      begin fun t1 t2 ->
        let open Constr in
        let open EConstr in
        match kind evd t1, kind evd t2 with
        | (App (head1, args1), App (head2, args2))
             when eq_constr evd head1 head2 && Array.length args1 = Array.length args2 ->
           let len = Array.length args1 in
           (len * 10, len, ActFEqual) :: actions
        | _ ->
           actions
      end
  in
  let actions =
    let open Constr in
    let open EConstr in
    match kind evd ghead0 with
    | Const (c, _) when
           in_sopt_list_const opts.s_hints !unfolding_hints c opts.s_unfolding ->
       (60, 1, ActUnfold c) :: actions
    | _ ->
       actions
  in
  let actions =
    List.concat (List.map (create_hyp_actions opts evd ghead0 ghead) hyps) @ actions
  in
  List.stable_sort (fun (x, _, _) (y, _, _) -> Pervasives.compare x y) actions

(*****************************************************************************************)

type tactics = {
  t_finish : unit Proofview.tactic;
  t_simplify : unit Proofview.tactic;
  t_simplify_concl : unit Proofview.tactic;
  t_simple_splitting : unit Proofview.tactic;
  t_case_splitting : unit Proofview.tactic;
  t_unfolding : unit Proofview.tactic;
  t_reduce_concl : unit Proofview.tactic;
  t_subst_simpl : unit Proofview.tactic;
  b_sapply_initialised : bool;
}

let create_tactics opts = {
  t_finish = Tacticals.New.tclSOLVE [ leaf_tac opts; opts.s_solve_tac ];
  t_simplify = simplify opts;
  t_simplify_concl = simplify_concl opts;
  t_simple_splitting = simple_splitting opts;
  t_case_splitting = case_splitting false opts;
  t_unfolding = unfolding opts;
  t_reduce_concl = reduce_concl opts;
  t_subst_simpl = subst_simpl opts;
  b_sapply_initialised = false;
}

(*****************************************************************************************)

let rec search extra tacs opts n rtrace visited =
  if n = 0 then
    tacs.t_finish
  else
    Proofview.Goal.enter begin fun gl ->
      let goal = Proofview.Goal.concl gl in
      let evd = Proofview.Goal.sigma gl in
      let open Constr in
      let open EConstr in
      if mem_constr evd goal visited then
        fail_tac
      else
        match kind evd goal with
        | Prod (_, h, f) when not (Utils.is_atom evd h) || not (Utils.is_False evd f) ->
           intros tacs opts n
        | _ ->
           if is_simple_split opts evd goal then
             tacs.t_simple_splitting <*> search extra tacs opts n rtrace (goal :: visited)
           else if opts.s_eager_case_splitting && is_case_split opts evd goal then
             Tacticals.New.tclIFCATCH (Tacticals.New.tclPROGRESS tacs.t_case_splitting)
               (fun () -> start_search tacs opts n)
               (fun () -> run_actions extra tacs opts n rtrace visited evd goal gl)
           else
             run_actions extra tacs opts n rtrace visited evd goal gl
    end

and start_search tacs opts n =
  tacs.t_unfolding <*> tacs.t_simplify <*>
    if opts.s_sapply && not tacs.b_sapply_initialised then
      Proofview.Goal.enter begin fun gl ->
        let evd = Proofview.Goal.sigma gl in
        let sapp =
          List.exists
            begin fun (_, hyp) ->
              let (_, head, args) = Utils.destruct_prod evd hyp in
              is_unorientable_equality evd head args
            end
            (Utils.get_hyps gl)
        in
        search true tacs { opts with s_sapply = sapp } n [] []
      end
    else
      search true tacs opts n [] []

and intros tacs opts n =
  tacs.t_reduce_concl <*>
    intros_until_atom_tac () <*>
    opt opts.s_simpl_sigma (simpl_sigma_tac ()) <*>
    start_search tacs opts n

and run_actions extra tacs opts n rtrace visited evd goal gl =
  let hyps = List.map (eval_hyp evd) (Utils.get_hyps gl) in
  let actions = create_actions extra opts evd goal hyps gl in
  match actions with
  | [] -> tacs.t_finish
  | (cost, _, _) :: _ when not opts.s_depth_cost_model && cost > n -> tacs.t_finish
  | _ -> apply_actions tacs opts n actions rtrace (goal :: visited)

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
  let final_tac =
    if not opts.s_depth_cost_model && n < 25 then
      tacs.t_finish
    else
      opts.s_solve_tac
  in
  let apply id =
    if opts.s_sapply then
      sapply_tac id
    else
      Tactics.Simple.eapply (EConstr.mkVar id)
  in
  match actions with
  | (cost, branching, act) :: acts ->
     if not opts.s_depth_cost_model && cost > n then
       final_tac
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
            continue n' (apply id) acts
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
         | ActDestruct t ->
            cont (sdestruct opts t <*> start_search tacs opts n') acts
         | ActHint h ->
            continue n' (Tacticals.New.tclPROGRESS
                           (Utils.hint_tactic h (List.hd visited))
                         <*> tacs.t_simplify_concl) acts
         | ActConstructor ->
            cont
              (Tactics.any_constructor true
                 (Some (tacs.t_simplify_concl <*> search false tacs opts n' rtrace visited)))
              acts
         | ActIntro ->
            cont (Tactics.intros <*> tacs.t_subst_simpl <*> start_search tacs opts n') acts
         | ActReduce ->
            cont (Proofview.tclBIND
                    (Tacticals.New.tclPROGRESS (red_in_all_tac ()))
                    (fun _ -> start_search tacs opts n')) acts
         | ActFEqual ->
            continue n' (f_equal_tac ()) acts
       end
  | [] ->
     final_tac

(*****************************************************************************************)

let sinit opts =
  unfold_local_defs_tac () <*>
    opt opts.s_reflect (bool_reflect_tac ()) <*>
    fullunfolding opts <*>
    unfolding opts <*> subst_simpl opts

let sintuition opts =
  unfold_local_defs_tac () <*>
  fullunfolding opts <*>
    Tactics.intros <*>
    opt opts.s_reflect (bool_reflect_tac ()) <*>
    simp_hyps_tac () <*> subst_simpl opts <*> ssimpl_tac opts <*>
    Tacticals.New.tclREPEAT (Tacticals.New.tclPROGRESS
                               (Tactics.intros <*> simp_hyps_tac () <*> subst_simpl opts) <*>
                               ssimpl_tac opts)

let ssimpl opts =
  let tac1 =
    Tactics.intros <*> unfolding opts <*> sintuition opts <*> subst_simpl opts <*>
      simp_hyps_tac () <*>
      opt opts.s_forwarding (with_reduction opts
                               (forwarding_tac ()) (forwarding_nored_tac ())) <*>
      subst_simpl opts
  and tac2 =
    Tactics.intros <*> unfolding opts <*>
      opt opts.s_forwarding (with_reduction opts
                               (forwarding_tac ()) (forwarding_nored_tac ())) <*>
      subst_simpl opts
  in
  let opts2 =
    { opts with s_simpl_tac = opts.s_ssimpl_tac;
                s_simpl_nolia_tac = opts.s_ssimpl_nolia_tac }
  in
  unfold_local_defs_tac () <*>
  fullunfolding opts <*>
  opt opts.s_reflect (bool_reflect_tac ()) <*>
  tac1 <*> (simplify opts2 <~> tac2)

let qsimpl opts =
  let tac =
    sintuition opts <~>
      (opt opts.s_reflect (bnat_reflect_tac ()) <*>
         opt opts.s_reflect (bool_reflect_tac ())) <~>
      autorewriting true opts <~>
      (simple_splitting opts <*>
         opt opts.s_eager_case_splitting (case_splitting true opts)) <~>
      opt opts.s_simpl_sigma (simpl_sigma_tac ()) <~>
      opt opts.s_simple_inverting (simple_inverting opts)
  in
  Tactics.intros <*>
    unfold_local_defs_tac () <*>
    fullunfolding opts <*>
    opt opts.s_reflect (bool_reflect_tac ()) <*>
    unfolding opts <*> tac

let sauto opts =
  sinit opts <*>
    Tacticals.New.tclTRY (opts.s_solve_tac) <*>
    intros (create_tactics opts) opts opts.s_limit

let scrush opts =
  sinit opts <*> ssimpl opts <*> sauto opts

let fcrush opts =
  sinit opts <*>
    qsimpl opts <*> qforwarding_tac () <*> qsimpl opts <*> instering_tac () <*>
    qsimpl opts <*> sauto opts

let ecrush opts =
  sinit opts <*>
    qsimpl opts <*> qforwarding_tac () <*> einstering_tac () <*> esimp_hyps_tac () <*>
    qsimpl opts <*> sauto opts

let sblast opts =
  sinit opts <*>
    Tacticals.New.tclSOLVE [Tacticals.New.tclREPEAT (ssimpl opts <*> instering_tac ())]

let qblast opts =
  sinit opts <*>
    Tacticals.New.tclSOLVE [Tacticals.New.tclREPEAT
                              (qsimpl opts <*> qforwarding_tac () <*> instering_tac ())]

let scongruence opts =
  sinit opts <*> Tactics.intros <*> congr_tac ()

let sfirstorder opts =
  sinit opts <*>
    if opts.s_lia then
      Utils.ltac_apply "Tactics.firstorder_tac" []
    else
      Utils.ltac_apply "Tactics.firstorder_nolia_tac" []

let strivial opts =
  sinit opts <*>
    if opts.s_lia then
      Utils.ltac_apply "Tactics.isolve" []
    else
      Utils.ltac_apply "Tactics.isolve_nolia" []

let print_actions opts =
  Proofview.Goal.enter begin fun gl ->
    let goal = Proofview.Goal.concl gl in
    let evd = Proofview.Goal.sigma gl in
    let hyps = List.map (eval_hyp evd) (Utils.get_hyps gl) in
    let actions = create_actions true opts evd goal hyps gl in
    print_search_actions actions;
    Tacticals.New.tclIDTAC
  end

let unshelve tac =
  Proofview.with_shelf tac >>=
    begin fun (shelf, _) ->
      Proofview.Unsafe.tclNEWGOALS (List.map Proofview.with_empty_state shelf)
    end

let usolve tac =
  unshelve tac <*> dsolve_tac ()
