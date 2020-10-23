open Ltac_plugin
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
| SOAlwaysUnfold of Libnames.qualid list
| SOAlwaysUnfoldAll
| SOAlwaysUnfoldNone
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
| SOBases of string list
| SOBasesAdd of string list
| SOBasesAll
| SORewBases of string list
| SORewBasesAdd of string list
| SOHintBases of string list
| SOHintBasesAdd of string list
| SOHintBasesAll
| SOFinish of Tacexpr.raw_tactic_expr
| SOFinal of Tacexpr.raw_tactic_expr
| SOSolve of Tacexpr.raw_tactic_expr
| SOSimp of Tacexpr.raw_tactic_expr
| SOSSimp of Tacexpr.raw_tactic_expr
| SOSolveAdd of Tacexpr.raw_tactic_expr
| SOSimpAdd of Tacexpr.raw_tactic_expr
| SOSSimpAdd of Tacexpr.raw_tactic_expr
| SOForward of bool
| SOEagerCaseSplit of bool
| SOSimpleInvert of bool
| SOEagerInvert of bool
| SOEagerReduce of bool
| SOEagerRewrite of bool
| SODirectedRewrite of bool
| SOUndirectedRewrite of bool
| SORewrite of bool
| SOReflect of bool
| SOReflectRaw of bool
| SOReduce of bool
| SOSapply of bool
| SOLimit of int
| SODepth of int
| SOExhaustive of bool
| SOLia of bool
| SOSig of bool
| SOPrf of bool
| SODep of bool
| SODepRaw of bool
| SOEager of bool
| SOQuick of bool

let string_of_bopt b =
  if b then "on" else "off"

let string_of_strlist lst =
  match lst with
  | [] -> "-"
  | _ -> Hhlib.sfold (fun x -> x) ", " lst

let string_of_qualid_list lst =
  match lst with
  | [] -> "-"
  | _ -> Hhlib.sfold (fun q -> Pp.string_of_ppcmds (Libnames.pr_qualid q)) ", " lst

let string_of_tactic evd tac =
  Pp.string_of_ppcmds (Pptactic.pr_raw_tactic (Global.env ()) evd tac)

let string_of_sopt evd opt =
  match opt with
  | SONop -> ""
  | SOUse lst -> "use: " ^ Hhlib.sfold (Hhutils.constr_expr_to_string evd) ", " lst
  | SOGen lst -> "gen: " ^ Hhlib.sfold (Hhutils.constr_expr_to_string evd) ", " lst
  | SOUnfold lst -> "unfold: " ^ string_of_qualid_list lst
  | SOUnfoldAll -> "unfold: *"
  | SOUnfoldNone -> "unfold: -"
  | SOAlwaysUnfold lst -> "unfold!: " ^ string_of_qualid_list lst
  | SOAlwaysUnfoldAll -> "unfold!: *"
  | SOAlwaysUnfoldNone -> "unfold!: -"
  | SOInv lst -> "inv: " ^ string_of_qualid_list lst
  | SOInvAll -> "inv: *"
  | SOInvNone -> "inv: never"
  | SOCtrs lst -> "ctrs: " ^ string_of_qualid_list lst
  | SOCtrsAll -> "ctrs: *"
  | SOCtrsNone -> "ctrs: never"
  | SOCaseSplit lst -> "cases: " ^ string_of_qualid_list lst
  | SOCaseSplitAll -> "cases: *"
  | SOCaseSplitNone -> "cases: never"
  | SOSimpleSplit lst -> "split: " ^ string_of_qualid_list lst
  | SOSimpleSplitAll -> "split: *"
  | SOSimpleSplitNone -> "split: never"
  | SOBases lst -> "db: " ^ string_of_strlist lst
  | SOBasesAdd lst -> "db+: " ^ string_of_strlist lst
  | SOBasesAll -> "db: *"
  | SORewBases lst -> "rew:db: " ^ string_of_strlist lst
  | SORewBasesAdd lst -> "rew:db+: " ^ string_of_strlist lst
  | SOHintBases lst -> "hint:db: " ^ string_of_strlist lst
  | SOHintBasesAdd lst -> "hint:db+: " ^ string_of_strlist lst
  | SOHintBasesAll -> "hint:db: *"
  | SOFinish tac -> "finish: " ^ string_of_tactic evd tac
  | SOFinal tac -> "final: " ^ string_of_tactic evd tac
  | SOSolve tac -> "solve: " ^ string_of_tactic evd tac
  | SOSimp tac -> "simp: " ^ string_of_tactic evd tac
  | SOSSimp tac -> "ssimp: " ^ string_of_tactic evd tac
  | SOSolveAdd tac -> "solve+: " ^ string_of_tactic evd tac
  | SOSimpAdd tac -> "simp+: " ^ string_of_tactic evd tac
  | SOSSimpAdd tac -> "ssimp+: " ^ string_of_tactic evd tac
  | SOForward b -> "fwd: " ^ string_of_bopt b
  | SOEagerCaseSplit b -> "ecases: " ^ string_of_bopt b
  | SOSimpleInvert b -> "sinv: " ^ string_of_bopt b
  | SOEagerInvert b -> "einv: " ^ string_of_bopt b
  | SOEagerReduce b -> "ered: " ^ string_of_bopt b
  | SOEagerRewrite b -> "erew: " ^ string_of_bopt b
  | SODirectedRewrite b -> "drew: " ^ string_of_bopt b
  | SOUndirectedRewrite b -> "urew: " ^ string_of_bopt b
  | SORewrite b -> "rew: " ^ string_of_bopt b
  | SOReflect b -> "brefl: " ^ string_of_bopt b
  | SOReflectRaw b -> "brefl!:" ^ string_of_bopt b
  | SOReduce b -> "red: " ^ string_of_bopt b
  | SOSapply b -> "sapp: " ^ string_of_bopt b
  | SOLimit n -> "limit: " ^ string_of_int n
  | SODepth d -> "depth: " ^ string_of_int d
  | SOExhaustive b -> "exh: " ^ string_of_bopt b
  | SOLia b -> "lia: " ^ string_of_bopt b
  | SOSig b -> "sig: " ^ string_of_bopt b
  | SOPrf b -> "prf: " ^ string_of_bopt b
  | SODep b -> "dep: " ^ string_of_bopt b
  | SODepRaw b -> "dep!: " ^ string_of_bopt b
  | SOEager b -> "l: " ^ string_of_bopt (not b)
  | SOQuick b -> "q: " ^ string_of_bopt b

let string_of_sopt_list evd lst =
  List.map (string_of_sopt evd) (List.filter (fun x -> x <> SONop) lst)

let const_of_qualid q =
  catch_errors (fun () -> Utils.get_const_from_qualid q)
    (fun _ ->
      raise (HammerTacticError ("not a constant: " ^ Libnames.string_of_qualid q)))

let inductive_of_qualid q =
  catch_errors (fun () -> Utils.get_inductive_from_qualid q)
    (fun _ ->
      raise (HammerTacticError ("not an inductive type: " ^ Libnames.string_of_qualid q)))

let exists_rew_db s =
  catch_errors (fun () -> ignore (Autorewrite.find_rewrites s); true)
    (fun _ -> false)

let exists_hint_db s =
  catch_errors (fun () -> ignore (Hints.searchtable_map s); true)
    (fun _ -> false)

let partition_hint_bases bases =
  let (lst1, lst2) = List.partition exists_rew_db bases in
  (lst1, Hints.make_db_list (List.filter exists_hint_db lst1 @ lst2))

let check_rew_bases =
  List.iter begin fun s ->
    if not (exists_rew_db s) then
      raise (HammerTacticError ("Rewriting base " ^ s ^ " does not exist"))
  end

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

let mk_final tac =
  let sfinal =
    Libnames.qualid_of_string "Tactics.sfinal"
  in
  Tacexpr.TacArg(CAst.make
                   Tacexpr.(TacCall(CAst.make
                                      (sfinal, [Tacexpr.Tacexp tac]))))

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
  | SOAlwaysUnfold lst ->
     let lst = List.map const_of_qualid lst in
     ret { opts with s_always_unfold = sopt_append opts.s_always_unfold lst }
  | SOAlwaysUnfoldAll ->
     ret { opts with s_always_unfold = SAll }
  | SOAlwaysUnfoldNone ->
     ret { opts with s_always_unfold = SNone }
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
  | SOBases lst ->
     let (lst1, lst2) = partition_hint_bases lst in
     ret { opts with s_rew_bases = lst1; s_hint_bases = lst2 }
  | SOBasesAdd lst ->
     let (lst1, lst2) = partition_hint_bases lst in
     ret { opts with s_rew_bases = opts.s_rew_bases @ lst1;
                     s_hint_bases = opts.s_hint_bases @ lst2 }
  | SOBasesAll ->
     ret { opts with s_hint_bases = Hints.current_pure_db () }
  | SORewBases lst ->
     check_rew_bases lst;
     ret { opts with s_rew_bases = lst }
  | SORewBasesAdd lst ->
     check_rew_bases lst;
     ret { opts with s_rew_bases = opts.s_rew_bases @ lst }
  | SOHintBases lst ->
     let hints = Hints.make_db_list lst in
     ret { opts with s_hint_bases = hints }
  | SOHintBasesAdd lst ->
     let hints = Hints.make_db_list lst in
     ret { opts with s_hint_bases = opts.s_hint_bases @ hints }
  | SOHintBasesAll ->
     ret { opts with s_hint_bases = Hints.current_pure_db () }
  | SOFinish tac ->
     let tac = Tacticals.New.tclSOLVE [Tacinterp.interp tac] in
     ret { opts with s_leaf_tac = tac; s_leaf_nolia_tac = tac }
  | SOFinal tac ->
     let tac = Tacticals.New.tclSOLVE [Tacinterp.interp (mk_final tac)] in
     ret { opts with s_leaf_tac = tac; s_leaf_nolia_tac = tac }
  | SOSolve tac ->
     ret { opts with s_solve_tac = Tacticals.New.tclSOLVE [Tacinterp.interp tac] }
  | SOSimp tac ->
     let tac = Tacinterp.interp tac in
     ret { opts with s_simpl_tac = tac; s_simpl_nolia_tac = tac }
  | SOSSimp tac ->
     let tac = Tacinterp.interp tac in
     ret { opts with s_ssimpl_tac = tac; s_ssimpl_nolia_tac = tac }
  | SOSolveAdd tac ->
     ret { opts with s_solve_tac =
                       Tacticals.New.tclSOLVE [opts.s_leaf_tac; Tacinterp.interp tac] }
  | SOSimpAdd tac ->
     let tac = Tacticals.New.tclTRY (Tacinterp.interp tac) in
     ret { opts with s_simpl_tac = opts.s_simpl_tac <*> tac;
                     s_simpl_nolia_tac = opts.s_simpl_nolia_tac <*> tac }
  | SOSSimpAdd tac ->
     let tac = Tacticals.New.tclTRY (Tacinterp.interp tac) in
     ret { opts with s_ssimpl_tac = opts.s_ssimpl_tac <*> tac;
                     s_ssimpl_nolia_tac = opts.s_ssimpl_nolia_tac <*> tac }
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
  | SODirectedRewrite b ->
     ret { opts with s_directed_rewriting = b }
  | SOUndirectedRewrite b ->
     ret { opts with s_undirected_rewriting = b }
  | SORewrite b ->
     ret (set_rew_opts b opts)
  | SOReflect b ->
     ret (set_brefl_opts b opts)
  | SOReflectRaw b ->
     ret { opts with s_reflect = b }
  | SOReduce b ->
     ret { opts with s_reducing = b }
  | SOSapply b ->
     ret { opts with s_sapply = b }
  | SOLimit n ->
     ret { opts with s_limit = n; s_depth_cost_model = false }
  | SODepth n ->
     ret { opts with s_limit = n; s_depth_cost_model = true }
  | SOExhaustive b ->
     ret { opts with s_exhaustive = b }
  | SOLia b ->
     ret { opts with s_lia = b }
  | SOSig b ->
     ret { opts with s_simpl_sigma = b }
  | SOPrf b ->
     ret { opts with s_genproofs = b }
  | SODep b ->
     ret (set_dep_opts b opts)
  | SODepRaw b ->
     ret { opts with s_dep = b }
  | SOEager b ->
     ret (set_eager_opts b opts)
  | SOQuick b ->
     ret (set_quick_opts b opts)

let interp_opts (opts : s_opts) (lst : sopt_t list) (ret : s_opts -> unit Proofview.tactic)
    : unit Proofview.tactic =
  let rec interp lst (opts : s_opts) : unit Proofview.tactic =
    match lst with
    | [] -> ret opts
    | opt :: lst' ->
       let ret opts =
         Proofview.tclUNIT opts >>= fun opts ->
           try_tactic begin fun () ->
             interp lst' opts
           end
       in
       interp_opt ret opt opts
  in
  interp lst opts

let try_usolve (opts : s_opts) (lst : sopt_t list) (ret : s_opts -> unit Proofview.tactic)
      (msg : string) : unit Proofview.tactic =
  try_tactic begin fun () ->
    usolve @@
      interp_opts opts lst
        begin fun opts ->
          Proofview.tclORELSE (ret opts)
            (fun _ -> Tacticals.New.tclZEROMSG (Pp.str msg))
        end
  end

let use_lemmas lst =
  let use_tac t =
    Utils.ltac_eval "Tactics.use_tac" [Tacinterp.Value.of_constr t]
  in
  List.fold_left (fun tac t -> tac <*> use_tac t) Tacticals.New.tclIDTAC lst
