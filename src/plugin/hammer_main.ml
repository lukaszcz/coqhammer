open Hammer_lib
open Hammer_tactics
open Hammer_errors
open Sauto

open Util
open Names
open Term
open Constr
open Context
open Proofview.Notations

open Ltac_plugin

module Utils = Hhutils

(***************************************************************************************)

let mk_id x = Hh_term.Id x
let mk_app x y = Hh_term.Comb(x, y)
let mk_comb (x, y) = mk_app x y

let tuple (l : Hh_term.hhterm list) =
  match l with
  | [] -> failwith "tuple: empty list"
  | [h] -> h
  | h :: t ->
    List.fold_left mk_app h t

let hhterm_of_global glob =
  mk_id (Libnames.string_of_path (Nametab.path_of_global (Globnames.canonical_gr glob)))

let hhterm_of_sort s = match Sorts.family s with
  | InSProp -> mk_id "$Prop"
  | InProp -> mk_id "$Prop"
  | InSet  -> mk_id "$Set"
  | InType -> mk_id "$Type"

let hhterm_of_constant c =
  tuple [mk_id "$Const"; hhterm_of_global (Names.GlobRef.ConstRef c)]

let hhterm_of_inductive i =
  tuple [mk_id "$Ind"; hhterm_of_global (Names.GlobRef.IndRef i);
         mk_id (string_of_int (Inductiveops.inductive_nparams (Global.env()) i))]

let hhterm_of_construct cstr =
  tuple [mk_id "$Construct"; hhterm_of_inductive (fst cstr);
         hhterm_of_global (Names.GlobRef.ConstructRef cstr)]

let hhterm_of_var v =
  tuple [mk_id "$Var"; hhterm_of_global (Names.GlobRef.VarRef v)]

let hhterm_of_intarray a =
  tuple ((mk_id "$IntArray") :: (List.map mk_id (List.map string_of_int (Array.to_list a))))

let hhterm_of_caseinfo ci =
  let {ci_ind = ci_ind; ci_npar = ci_npar; ci_cstr_ndecls = ci_cstr_ndecls;
       ci_cstr_nargs = ci_cstr_nargs; ci_pp_info = ci_pp_info} = ci
  in
  tuple [mk_id "$CaseInfo"; hhterm_of_inductive ci_ind;
         mk_id (string_of_int ci_npar);
         hhterm_of_intarray ci_cstr_ndecls;
         hhterm_of_intarray ci_cstr_nargs]

(* Unsafe *)
let hhterm_of_name name = match name.binder_name with
  | Name.Name id -> tuple [mk_id "$Name"; mk_id (Id.to_string id)]
  | Name.Anonymous  -> tuple [mk_id "$Name"; mk_id "$Anonymous"]

let hhterm_of_namearray a =
  tuple ((mk_id "$NameArray") :: (List.map hhterm_of_name (Array.to_list a)))

let hhterm_of_bool b =
  if b then mk_app (mk_id "$Bool") (mk_id "$True")
  else mk_app (mk_id "$Bool") (mk_id "$False")

let rec hhterm_of (t : Constr.t) : Hh_term.hhterm =
  match Constr.kind t with
  | Rel n -> tuple [mk_id "$Rel"; mk_id (string_of_int n)]
  | Meta n -> raise (HammerError "Metavariables not supported.")
  | Var v -> hhterm_of_var v
  | Sort s -> tuple [mk_id "$Sort"; hhterm_of_sort s]
  | Cast (ty1,ck,ty2) -> tuple [mk_id "$Cast"; hhterm_of ty1; hhterm_of ty2]
  | Prod (na,ty,c)    ->
     tuple [mk_id "$Prod"; hhterm_of_name na; hhterm_of ty; hhterm_of c]
  | Lambda (na,ty,c)  ->
     tuple [mk_id "$Lambda"; hhterm_of_name na; hhterm_of ty; hhterm_of c]
  | LetIn (na,b,ty,c) ->
     tuple [mk_id "$LetIn"; hhterm_of_name na; hhterm_of b; hhterm_of ty; hhterm_of c]
  | App (f,args)      ->
     tuple [mk_id "$App"; hhterm_of f; hhterm_of_constrarray args]
  | Const (c,u)       -> hhterm_of_constant c
  | Proj (p,c)        -> tuple [mk_id "$Proj";
                                hhterm_of_constant (Projection.constant p);
                                hhterm_of_bool (Projection.unfolded p);
                                hhterm_of c]
  | Evar (evk,cl)     -> raise (HammerError "Existential variables not supported.")
  | Ind (ind,u)       -> hhterm_of_inductive ind
  | Construct (ctr,u) -> hhterm_of_construct ctr
  | Case (ci,p,c,bl)  ->
      tuple ([mk_id "$Case"; hhterm_of_caseinfo ci ; hhterm_of p;
        hhterm_of c; hhterm_of_constrarray bl])
  | Fix (nvn,recdef) -> tuple [mk_id "$Fix";
                               hhterm_of_intarray (fst nvn);
                               mk_id (string_of_int (snd nvn));
                               hhterm_of_precdeclaration recdef]
  | CoFix (n,recdef) -> tuple [mk_id "$CoFix";
                               mk_id (string_of_int n);
                               hhterm_of_precdeclaration recdef]
  | Int _            -> raise (HammerError "Primitive integers not supported.")
  | Float _          -> raise (HammerError "Primitive floats not supported.")

and hhterm_of_constrarray a =
  tuple ((mk_id "$ConstrArray") :: List.map hhterm_of (Array.to_list a))
and hhterm_of_precdeclaration (a,b,c) =
  tuple [(mk_id "$PrecDeclaration") ; hhterm_of_namearray a;
         hhterm_of_constrarray b; hhterm_of_constrarray c]

let get_type_of env evmap t =
  EConstr.to_constr evmap (Retyping.get_type_of env evmap (EConstr.of_constr t))

(* only for constants *)
let hhproof_of c =
  begin match Global.body_of_constant Library.indirect_accessor c with
  | Some (b, _, _) -> hhterm_of b
  | None -> mk_id "$Axiom"
  end

let hhdef_of_global env sigma glob_ref : (string * Hh_term.hhdef) =
  let glob_ref = Globnames.canonical_gr glob_ref in
  let ty = fst (Typeops.type_of_global_in_context env glob_ref) in
  let kind = get_type_of env sigma ty in
  let const = match glob_ref with
    | Names.GlobRef.ConstRef c -> hhterm_of_constant c
    | Names.GlobRef.IndRef i   -> hhterm_of_inductive i
    | Names.GlobRef.ConstructRef cstr -> hhterm_of_construct cstr
    | Names.GlobRef.VarRef v -> hhterm_of_var v
  in
  let filename_aux = match glob_ref with
    | Names.GlobRef.ConstRef c -> Constant.to_string c
    | Names.GlobRef.IndRef i   -> MutInd.to_string (fst i)
    | Names.GlobRef.ConstructRef cstr -> MutInd.to_string ((Hhlib.comp fst fst) cstr)
    | Names.GlobRef.VarRef v -> Id.to_string v
  in
  let term = match glob_ref with
    | Names.GlobRef.ConstRef c -> lazy (hhproof_of c)
    | _ -> lazy (mk_id "$Axiom")
  in
  let opaque = match glob_ref with
    | Names.GlobRef.ConstRef c -> Declareops.is_opaque (Global.lookup_constant c)
    | _ -> true
  in
  let filename =
     let l = Str.split (Str.regexp "\\.") filename_aux in
     Filename.dirname (String.concat "/" l)
  in
  (filename, (const, opaque, hhterm_of kind, lazy (hhterm_of ty), term))

let hhdef_of_hyp env sigma (id, maybe_body, ty) =
  let kind = get_type_of env sigma ty in
  let body =
    match maybe_body with
    | Some b -> lazy (hhterm_of b)
    | None -> lazy (mk_id "$Axiom")
  in
  let opaque =
    match maybe_body with
    | Some b -> false
    | None -> true
  in
  (mk_comb(mk_id "$Const", mk_id (Id.to_string id)), opaque, hhterm_of kind, lazy (hhterm_of ty), body)

let econstr_to_constr x = EConstr.to_constr Evd.empty x

let make_good =
  function
  | Context.Named.Declaration.LocalAssum(x, y) ->
     (x.binder_name, None, econstr_to_constr y)
  | Context.Named.Declaration.LocalDef(x, y, z) ->
     (x.binder_name, Some (econstr_to_constr y), econstr_to_constr z)

let get_hyps gl =
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  List.map (Hhlib.comp (hhdef_of_hyp env sigma) make_good) (Proofview.Goal.hyps gl)

let get_goal gl =
  (mk_comb(mk_id "$Const", mk_id "_HAMMER_GOAL"),
   true,
   mk_comb(mk_id "$Sort", mk_id "$Prop"),
   lazy (hhterm_of (econstr_to_constr (Proofview.Goal.concl gl))),
   lazy (mk_comb(mk_id "$Const", mk_id "_HAMMER_GOAL")))

let string_of t = Hh_term.string_of_hhterm (hhterm_of t)

let string_of_hhdef_2 (filename, (const, hkind, hty, hterm)) =
  (filename,
   "tt(" ^ Hh_term.string_of_hhterm const ^ "," ^
     Hh_term.string_of_hhterm hkind ^ "," ^ Hh_term.string_of_hhterm (Lazy.force hty) ^ "," ^
     Hh_term.string_of_hhterm (Lazy.force hterm) ^ ").")

let string_of_goal gl =
  string_of (econstr_to_constr (Proofview.Goal.concl gl))

let my_search env =
  let save_in_list refl glob_ref env c = refl := glob_ref :: !refl in
  let ans = ref [] in
  let filter glob_ref kind env typ =
    if !Opt.search_blacklist then
      Search.blacklist_filter glob_ref kind env (Evd.from_env env) typ
    else
      true
  in
  let iter glob_ref kind env typ =
    if filter glob_ref kind env typ then save_in_list ans glob_ref env typ
  in
  let env = Global.env () in
  let () = Search.generic_search env iter in
  List.filter
    begin fun glob_ref ->
      try
        ignore (Typeops.type_of_global_in_context env glob_ref);
        true
      with _ ->
        false
    end
    (List.rev !ans)

let unique_hhdefs hhdefs =
  let hash = Hashtbl.create 128 in
  List.filter
    begin fun (_, def) ->
      let name = Hh_term.get_hhdef_name def in
      if Hashtbl.mem hash name then
        false
      else
        begin
          Hashtbl.add hash name true;
          true
        end
    end
    hhdefs

let get_defs env sigma : Hh_term.hhdef list =
  List.map snd (unique_hhdefs
                  (List.map (hhdef_of_global env sigma) (my_search env)))

let ltac_timeout tm tac (args: Tacinterp.Value.t list) =
  Timeout.ptimeout tm (Utils.ltac_eval tac args)

let globref_to_econstr r =
  match r with
  | Names.GlobRef.VarRef(v) -> EConstr.mkVar v
  | Names.GlobRef.ConstRef(c) -> EConstr.mkConst c
  | Names.GlobRef.IndRef(i) -> EConstr.mkInd i
  | Names.GlobRef.ConstructRef(cr) -> EConstr.mkConstruct cr

let globref_to_const r =
  match r with
  | Names.GlobRef.ConstRef(c) -> c
  | _ -> failwith "globref: not a constant"

let globref_to_inductive r =
  match r with
  | Names.GlobRef.IndRef(i) -> i
  | _ -> failwith "globref: not an inductive type"

let mk_lst_str pref lst =
  let get_name x =
    Hhlib.drop_prefix x "Top."
  in
  match lst with
  | [] -> ""
  | h :: t -> pref ^ " " ^ List.fold_right (fun x a -> get_name x ^ ", " ^ a) t (get_name h)

let get_tac_args env sigma info =
  let deps = info.Provers.deps in
  let defs = info.Provers.defs in
  let inverts =
    Hhlib.sort_uniq Pervasives.compare (info.Provers.inversions @ info.Provers.cases)
  in
  let map_locate =
    List.map
      begin fun s ->
        try
          Nametab.locate (Libnames.qualid_of_string s)
        with Not_found ->
          Names.GlobRef.VarRef(Id.of_string s)
      end
  in
  let (deps, defs, inverts) = (map_locate deps, map_locate defs, map_locate inverts) in
  let filter_vars =
    List.filter (fun r -> match r with Names.GlobRef.VarRef(_) -> true | _ -> false)
  in
  let filter_nonvars =
    List.filter (fun r -> match r with Names.GlobRef.VarRef(_) -> false | _ -> true)
  in
  let filter_consts =
    List.filter (fun r -> match r with Names.GlobRef.ConstRef(_) -> true | _ -> false)
  in
  let (vars, deps) = (filter_vars deps, filter_nonvars deps) in
  let (deps, defs, inverts) =
    (List.map globref_to_econstr deps,
     List.map globref_to_const (filter_consts defs),
     List.map globref_to_inductive inverts)
  in
  (deps, defs, inverts)

let check_goal_prop gl =
  let env = Proofview.Goal.env gl in
  let evmap = Proofview.Goal.sigma gl in
  let tp =
    EConstr.to_constr evmap (Retyping.get_type_of env evmap (Proofview.Goal.concl gl))
  in
  match Constr.kind tp with
  | Sort s -> Sorts.family s = InProp
  | _ -> false

(***************************************************************************************)

let run_tactics deps defs inverts msg_success msg_fail msg_batch =
  let mkopts opts =
    let opts =
      if defs <> [] then { opts with s_unfolding = SSome defs } else opts
    in
    if inverts <> [] then { opts with s_inversions = SSome inverts } else opts
  in
  let use_deps =
    Tactics.generalize deps <*>
      Tacticals.New.tclDO (List.length deps) (Tactics.intro_move None Logic.MoveFirst)
  in
  let rhauto =
    usolve (use_deps <*> sauto (mkopts (hauto_s_opts ())))
  and rqauto =
    usolve (use_deps <*> sauto (mkopts (qauto_s_opts ())))
  and rhlqauto =
    usolve (use_deps <*> sauto (mkopts
                                  (set_quick_opts true
                                     (set_eager_opts false (hauto_s_opts ())))))
  and rhcrush =
    usolve (use_deps <*> scrush (mkopts (hauto_s_opts ())))
  and rhfcrush =
    usolve (use_deps <*> fcrush (mkopts (hauto_s_opts ())))
  and rqblast =
    usolve (use_deps <*> qblast (mkopts (default_s_opts ())))
  and rhecrush =
    usolve (use_deps <*> ecrush (mkopts (hauto_s_opts ())))
  and rlhauto =
    usolve (use_deps <*> sauto (mkopts (set_eager_opts false (hauto_s_opts ()))))
  and rhauto_l_nodrew =
    usolve (use_deps <*> sauto (mkopts
                                  { (set_eager_opts false (hauto_s_opts ())) with
                                    s_directed_rewriting = false}))
  and rhdauto6_lq =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (set_quick_opts true
                        (set_eager_opts false (hauto_s_opts ()))) with
                     s_limit = 6; s_depth_cost_model = true }))
  and rhdauto6_lq_nodrew =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (set_quick_opts true
                        (set_eager_opts false (hauto_s_opts ()))) with
                     s_limit = 6; s_depth_cost_model = true;
                     s_directed_rewriting = false }))
  and rhdauto4 =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (hauto_s_opts ()) with
                     s_limit = 4; s_depth_cost_model = true }))
  and rlqdauto4 =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (set_eager_opts false (qauto_s_opts ())) with
                     s_limit = 4; s_depth_cost_model = true }))
  and rlqdauto4_nodrew =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (set_eager_opts false (qauto_s_opts ())) with
                     s_limit = 4; s_depth_cost_model = true;
                     s_directed_rewriting = false }))
  and rhbauto =
    usolve (use_deps <*>
              sauto
                (mkopts
                   (set_brefl_opts true (hauto_s_opts ()))))
  and rhbauto_nodrew =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (set_brefl_opts true (hauto_s_opts ())) with
                     s_directed_rewriting = false }))
  and rhbauto_norew =
    usolve (use_deps <*>
              sauto
                (mkopts
                   (set_rew_opts false
                      (set_brefl_opts true (hauto_s_opts ())))))
  and rhauto_nodrew =
    usolve (use_deps <*>
              sauto
                (mkopts { (hauto_s_opts ()) with s_directed_rewriting = false }))
  and rhfcrush_nodrew =
    usolve (use_deps <*>
              fcrush
                (mkopts { (hauto_s_opts ()) with s_directed_rewriting = false }))
  and rhauto_norew =
    usolve (use_deps <*>
              sauto
                (mkopts
                   (set_rew_opts false (hauto_s_opts ()))))
  and rhauto_lq_norew =
    usolve (use_deps <*>
              sauto
                (mkopts
                   (set_quick_opts true
                      (set_eager_opts false
                         (set_rew_opts false (hauto_s_opts ()))))))
  and rhauto_lq_nodrew =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (set_quick_opts true
                        (set_eager_opts false
                           (hauto_s_opts ()))) with
                     s_directed_rewriting = false}))
  and rhbauto_lq =
    usolve (use_deps <*>
              sauto
                (mkopts
                   (set_quick_opts true
                      (set_eager_opts false
                         (set_brefl_opts true (hauto_s_opts ()))))))
  and rhbauto_lq_nodrew =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (set_quick_opts true
                        (set_eager_opts false
                           (set_brefl_opts true (hauto_s_opts ())))) with
                     s_directed_rewriting = false }))
  and rhbfcrush =
    usolve (use_deps <*> fcrush (mkopts (set_brefl_opts true (hauto_s_opts ()))))
  and rhbfcrush_nodrew =
    usolve (use_deps <*> fcrush (mkopts
                                   { (set_brefl_opts true (hauto_s_opts ())) with
                                     s_directed_rewriting = false }))
  and rheauto =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (set_quick_opts true
                        (set_eager_opts false (hauto_s_opts ()))) with
                     s_exhaustive = true; s_limit = 2; s_depth_cost_model = true }))
  and rhbauto4000 =
    usolve (use_deps <*>
              sauto
                (mkopts
                   { (set_brefl_opts true (hauto_s_opts ())) with
                     s_limit = 4000 }))
  and reauto =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Tacticals.New.tclSOLVE [ Eauto.gen_eauto (Eauto.make_dimension None None) []
                                         (Some []) ])
  and rcongruence =
    usolve (use_deps <*> scongruence (mkopts (hauto_s_opts ())))
  and rfirstorder =
    usolve (use_deps <*> sfirstorder (mkopts (hauto_s_opts ())))
  and rtrivial =
    usolve (use_deps <*> strivial (mkopts (hauto_s_opts ())))
  and rreasy () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrreasy" [])
  and rrsimple () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrrsimple" [])
  and rrcrush () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrrcrush" [])
  and rryelles4 () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrryelles4" [])
  and rryelles6 () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrryelles6" [])
  and rrhreconstr4 () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrrhreconstr4" [])
  and rrhreconstr6 () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrrhreconstr6" [])
  and rryreconstr () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrryreconstr" [])
  and rrblast () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrrblast" [])
  and rrscrush () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrrscrush" [])
  and rrhrauto4 () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrrhrauto4" [])
  and rrexhaustive1 () =
    usolve (use_deps <*>
              sinit (mkopts (hauto_s_opts ())) <*>
              Utils.ltac_apply "Reconstr.qrrexhaustive1" [])
  in
  let pretactics =
    [ (reauto, "srun eauto"); (rcongruence, "scongruence");
      (rtrivial, "strivial"); (rfirstorder, "sfirstorder") ]
  in
  let tactics = [
      [ (rhauto, "hauto");
        (rqauto, "qauto");
        (rhfcrush, "hfcrush");
        (rhlqauto, "hauto lq: on")
      ];
      [ (rhcrush, "hcrush");
        (rhbauto, "hauto brefl: on");
        (rhauto_lq_nodrew, "hauto lq: on drew: off");
        (rhecrush, "hecrush")
      ];
      [ (rhdauto6_lq, "hauto depth: 6 lq: on");
        (rlqdauto4, "qauto depth: 4 l: on");
        (rqblast, "qblast");
        (rlhauto, "hauto l: on")
      ];
      [ (rhauto_nodrew, "hauto drew: off");
        (rhfcrush_nodrew, "hfcrush drew: off");
        (rhdauto4, "hauto depth: 4");
        (rhauto_l_nodrew, "hauto l: on drew: off")
      ];
      [ (rhbauto_lq, "hauto brefl: on lq: on");
        (rhbfcrush, "hfcrush brefl: on");
        (rheauto, "hauto depth: 2 lq: on exh: on");
        (rhbauto4000, "hauto limit: 4000 brefl: on")
      ];
      [ (rhauto_norew, "hauto rew: off");
        (rlqdauto4_nodrew, "qauto depth: 4 l: on drew: off");
        (rhauto_lq_norew, "hauto lq: on rew: off");
        (rhdauto6_lq_nodrew, "hauto depth: 6 lq: on drew: off")
      ];
      [ (rhbauto_lq_nodrew, "hauto brefl: on lq: on drew: off");
        (rhbfcrush_nodrew, "hfcrush brefl: on drew: off");
        (rhbauto_nodrew, "hauto brefl: on drew: off");
        (rhbauto_norew, "hauto brefl: on drew: off")
      ];
  ]
  in
  let tactics =
    catch_errors
      begin fun () ->
        tactics @
          [ [ (rreasy (), "srun Reconstr.rreasy");
              (rrsimple (), "srun Reconstr.rrsimple");
              (rrcrush (), "srun Reconstr.rrcrush");
              (rryelles4 (), "srun Reconstr.rryelles4") ];
            [ (rrblast (), "srun Reconstr.rrblast");
              (rrscrush (), "srun Reconstr.rrscrush");
              (rryreconstr (), "srun Reconstr.rryreconstr");
              (rrhreconstr4 (), "srun Reconstr.rrhreconstr4") ];
            [ (rryelles6 (), "srun Reconstr.rryelles6");
              (rrhreconstr6 (), "srun Reconstr.rrhreconstr6");
              (rrhrauto4 (), "srun Reconstr.rrhrauto4");
              (rrexhaustive1 (), "srun Reconstr.rrexhaustive1") ] ]
      end
      (fun _ -> tactics)
  in
  let run limit tacs f_success f_failure =
    Partac.partac limit (List.map fst tacs)
      begin fun k tac ->
        if k >= 0 then
          f_success (snd (List.nth tacs k)) tac
        else
          f_failure ()
      end
  in
  let rec hlp k lst =
    match lst with
    | [] ->
       begin
         msg_fail ();
         Tacticals.New.tclIDTAC
       end
    | tacs :: ts ->
       msg_batch k;
       run !Opt.reconstr_timelimit tacs
         begin fun name tac ->
           msg_success name;
           tac
         end
         begin fun () ->
           hlp (k + 1) ts
         end
  in
  run 1 pretactics
    begin fun name tac ->
      msg_success name;
      tac
    end
    begin fun () ->
      hlp 1 tactics
    end

let do_predict hyps deps goal =
  if !Opt.gs_mode > 0 then
    let greedy_sequence =
      [("CVC4 (nbayes-128)", !Opt.cvc4_enabled, Opt.cvc4_enabled, "nbayes", 128);
       ("Vampire (knn-1024)", !Opt.vampire_enabled, Opt.vampire_enabled, "knn", 1024);
       ("CVC4 (knn-64)", !Opt.cvc4_enabled, Opt.cvc4_enabled, "knn", 64);
       ("CVC4 (knn-256)", !Opt.cvc4_enabled, Opt.cvc4_enabled, "knn", 256);
       ("Vampire (nbayes-64)", !Opt.vampire_enabled, Opt.vampire_enabled, "nbayes", 64);
       ("CVC4 (nbayes-256)", !Opt.cvc4_enabled, Opt.cvc4_enabled, "nbayes", 256);
       ("Eprover (nbayes-64)", !Opt.eprover_enabled, Opt.eprover_enabled, "nbayes", 64);
       ("Z3 (nbayes-128)", !Opt.z3_enabled, Opt.z3_enabled, "nbayes", 128);
       ("Vampire (knn-64)", !Opt.vampire_enabled, Opt.vampire_enabled, "knn", 64);
       ("CVC4 (nbayes-32)", !Opt.cvc4_enabled, Opt.cvc4_enabled, "nbayes", 32);
       ("CVC4 (nbayes-1024)", !Opt.cvc4_enabled, Opt.cvc4_enabled, "nbayes", 1024);
       ("Z3 (nbayes-32)", !Opt.z3_enabled, Opt.z3_enabled, "nbayes", 32);
       ("Vampire (nbayes-128)", !Opt.vampire_enabled, Opt.vampire_enabled, "nbayes", 128);
       ("Eprover (knn-128)", !Opt.eprover_enabled, Opt.eprover_enabled, "knn", 128);
       ("Vampire (nbayes-32)", !Opt.vampire_enabled, Opt.vampire_enabled, "nbayes", 32);
       ("Z3 (knn-64)", !Opt.z3_enabled, Opt.z3_enabled, "knn", 64);
       ("Vampire (knn-256)", !Opt.vampire_enabled, Opt.vampire_enabled, "knn", 256);
       ("Eprover (nbayes-32)", !Opt.eprover_enabled, Opt.eprover_enabled, "nbayes", 32);
       ("Z3 (nbayes-64)", !Opt.z3_enabled, Opt.z3_enabled, "nbayes", 64);
       ("CVC4 (nbayes-64)", !Opt.cvc4_enabled, Opt.cvc4_enabled, "nbayes", 64);
       ("Eprover (nbayes-256)", !Opt.eprover_enabled, Opt.eprover_enabled, "nbayes", 256);
       ("Vampire (nbayes-1024)", !Opt.vampire_enabled, Opt.vampire_enabled, "nbayes", 1024);
       ("Z3 (nbayes-1024)", !Opt.z3_enabled, Opt.z3_enabled, "nbayes", 1024)]
    in
    let fname = Features.extract hyps deps goal in
    let jobs =
      List.map
        begin fun (pname, enabled, pref, pred_method, preds_num) _ ->
          if not enabled then
            exit 1;
          Opt.vampire_enabled := false;
          Opt.eprover_enabled := false;
          Opt.z3_enabled := false;
          Opt.cvc4_enabled := false;
          pref := true;
          Opt.parallel_mode := false;
          try
            let deps1 = Features.run_predict fname deps preds_num pred_method in
            (* All hypotheses are always passed to the ATPs (only deps
               are subject to premise selection) *)
            let info = Provers.predict deps1 hyps deps goal in
            Msg.info (pname ^ " succeeded");
            info
          with
          | HammerError(msg) ->
             Msg.error ("Hammer error: " ^ msg);
             exit 1
          | _ ->
             exit 1
        end
        (Hhlib.take !Opt.gs_mode (List.filter (fun (_, enabled, _, _, _) -> enabled) greedy_sequence))
    in
    let time = (float_of_int !Opt.atp_timelimit) *. 1.5
    in
    Msg.info ("Running provers (" ^ string_of_int !Opt.gs_mode ^ " threads)...");
    let clean () =
      Features.clean fname;
      if not !Opt.debug_mode then
        begin (* a hack *)
          ignore (Sys.command ("rm -f " ^ Filename.get_temp_dir_name () ^ "/coqhammer*"))
        end
    in
    let ret =
      try
        Parallel.run_parallel (fun _ -> ()) (fun _ -> ()) time jobs
      with e ->
        clean (); raise e
    in
    match ret with
    | None -> clean (); raise (HammerFailure "ATPs failed to find a proof.\nYou may try increasing the ATP time limit with 'Set Hammer ATPLimit N' (default: 20s).")
    | Some info ->
       begin
         let info =
           if List.length info.Provers.deps >= !Opt.minimize_threshold then
             Provers.minimize info hyps deps goal
           else
             info
         in
         clean ();
         let msg = Provers.prn_atp_info info in
         if msg <> "" then
           Msg.info msg;
         info
       end
  else
    let deps1 = Features.predict hyps deps goal in
    Provers.predict deps1 hyps deps goal

let try_sauto () =
  if !Opt.sauto_timelimit = 0 then
    Proofview.tclZERO (Failure "timeout")
  else
    Proofview.tclBIND
      (ltac_timeout !Opt.sauto_timelimit "Tactics.sauto_tac" [])
      (fun _ ->
        Msg.info "Replace the hammer tactic with: sauto";
        Tacticals.New.tclIDTAC)

(***************************************************************************************)

let hammer_tac () =
  Proofview.Goal.enter
    begin fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    Proofview.tclORELSE
      (try_sauto ())
      begin fun _ ->
      try_tactic begin fun () ->
        let goal = get_goal gl in
        let hyps = get_hyps gl in
        let defs = get_defs env sigma in
        if !Opt.debug_mode then
          Msg.info ("Found " ^ string_of_int (List.length defs) ^
                      " accessible Coq objects.");
        let info = do_predict hyps defs goal in
        let (deps, defs, inverts) = get_tac_args env sigma info in
        let sdeps = List.map (Utils.constr_to_string sigma) deps
        and sdefs = List.map Utils.constant_to_string defs
        and sinverts = List.map Utils.inductive_to_string inverts
        in
        Msg.info ("Reconstructing the proof...");
        run_tactics deps defs inverts
          begin fun tac ->
          Msg.info ("Tactic " ^ tac ^ " succeeded.");
          Msg.info ("Replace the hammer tactic with:\n\t" ^
                      tac ^ mk_lst_str " use:" sdeps ^
                        mk_lst_str " unfold:" sdefs ^
                          mk_lst_str " inv:" sinverts ^ ".")
          end
          begin fun () ->
            raise (HammerFailure "proof reconstruction failed.\nYou may try increasing the reconstruction time limit with 'Set Hammer ReconstrLimit N' (default: 5s).\nOther options are to disable the ATP which found this proof (Unset Hammer CVC4/Vampire/Eprover/Z3), or try to prove the goal manually using the displayed dependencies. Note that if the proof found by the ATP is inherently classical, it can never be reconstructed with CoqHammer's intuitionistic proof search procedure. As a last resort, you may also try enabling legacy reconstruction tactics with 'From Hammer Require Reconstr'.")
          end
          begin fun k ->
            Msg.info ("Trying reconstruction batch " ^ string_of_int k ^ "...")
          end
        end
      end
    end

let predict_tac n pred_method =
  try_goal_tactic
    begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let goal = get_goal gl in
      let hyps = get_hyps gl in
      let defs = get_defs env sigma in
      if !Opt.debug_mode then
        Msg.info ("Found " ^ string_of_int (List.length defs) ^ " accessible Coq objects.");
      if pred_method <> "knn" && pred_method <> "nbayes" then
        Msg.error "Invalid prediction method"
      else if n <= 0 then
        Msg.error "The number of predictions must be positive"
      else
        begin
          let old_pred_method = !Opt.predict_method
          and old_n = !Opt.predictions_num in
          Opt.predict_method := pred_method;
          Opt.predictions_num := n;
          let restore () =
            Opt.predict_method := old_pred_method;
            Opt.predictions_num := old_n
          in
          try
            let defs1 = Features.predict hyps defs goal in
            restore ();
            Msg.notice (Hhlib.sfold Hh_term.get_hhdef_name ", " defs1)
          with e ->
            restore (); raise e
        end;
      Tacticals.New.tclIDTAC
    end

let hammer_features_tac () =
  try_goal_tactic
    begin fun gl ->
      let features = Features.get_goal_features (get_hyps gl) (get_goal gl) in
      Msg.notice (Hhlib.sfold (fun x -> x) ", " features);
      Tacticals.New.tclIDTAC
    end

let hammer_print name =
  let env, sigma = let e = Global.env () in e, Evd.from_env e in
  try
    let glob = Utils.get_global name in
    let (_, (const, opaque, kind, ty, trm)) = hhdef_of_global env sigma glob in
    Msg.notice (Hh_term.string_of_hhterm const ^ " = ");
    Msg.notice (Hh_term.string_of_hhterm (Lazy.force trm));
    Msg.notice (" : " ^ Hh_term.string_of_hhterm (Lazy.force ty));
    Msg.notice (" : " ^ Hh_term.string_of_hhterm kind);
    if opaque then Msg.notice ("(opaque)")
  with Not_found ->
    Msg.error ("Not found: " ^ name)

let hammer_transl name0 =
  let env, sigma = let e = Global.env () in e, Evd.from_env e in
  try
    let glob = Utils.get_global name0 in
    let (_, def) = hhdef_of_global env sigma glob in
    let name = Hh_term.get_hhdef_name def in
    Coq_transl.remove_def name;
    Coq_transl.reinit (get_defs env sigma);
    List.iter
      begin fun (n, a) ->
        if not (Hhlib.string_begins_with n "_HAMMER_") then
          Msg.notice (n ^ ": " ^ Coqterms.string_of_coqterm a)
      end
      (Coq_transl.translate name)
  with Not_found ->
    Msg.error ("Not found: " ^ name0)

let hammer_transl_tac () =
  try_goal_tactic
    begin fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      let goal = get_goal gl in
      let hyps = get_hyps gl in
      let defs = get_defs env sigma in
      let name = Hh_term.get_hhdef_name goal in
      Coq_transl.remove_def name;
      List.iter (fun d -> Coq_transl.remove_def (Hh_term.get_hhdef_name d)) hyps;
      Coq_transl.reinit (goal :: hyps @ defs);
      List.iter
        begin fun (n, a) ->
          Msg.notice (n ^ ": " ^ Coqterms.string_of_coqterm a)
        end
        (Coq_transl.translate name);
      Tacticals.New.tclIDTAC
    end

let hammer_features name =
  let env, sigma = let e = Global.env () in e, Evd.from_env e in
  try
    let glob = Utils.get_global name in
    let (_, def) = hhdef_of_global env sigma glob in
    Msg.notice (Hhlib.sfold (fun x -> x) ", " (Features.get_def_features def))
  with Not_found ->
    Msg.error ("Not found: " ^ name)

let hammer_features_cached name =
  let env, sigma = let e = Global.env () in e, Evd.from_env e in
  try
    let glob = Utils.get_global name in
    let (_, def) = hhdef_of_global env sigma glob in
    Msg.notice (Hhlib.sfold (fun x -> x) ", " (Features.get_def_features_cached def))
  with Not_found ->
    Msg.error ("Not found: " ^ name)

let hammer_objects () =
  let env, sigma = let e = Global.env () in e, Evd.from_env e in
  Msg.info ("Found " ^ string_of_int (List.length (get_defs env sigma)) ^ " accessible Coq objects.")

let hammer_hook_tac prefix name =
  let premises = [("knn", 32); ("knn", 64); ("knn", 128); ("knn", 256); ("knn", 1024);
                  ("nbayes", 32); ("nbayes", 64); ("nbayes", 128); ("nbayes", 256); ("nbayes", 1024)]
  and provers = [("vampire", Provers.extract_vampire_data); ("eprover", Provers.extract_eprover_data);
                 ("z3", Provers.extract_z3_data); ("cvc4", Provers.extract_cvc4_data)]
  in
  let premise_prover_lst = Hhlib.mk_all_pairs premises provers
  in
  try_goal_tactic_nofail begin fun gl ->
    Msg.info ("Processing theorem " ^ name ^ "...");
    try
      if check_goal_prop gl then
        begin
          let fopt = open_in "coqhammer.opt" in
          let str = input_line fopt in
          close_in fopt;
          if str = "check" then
            Tacticals.New.tclIDTAC
          else if str = "gen-atp" then
            begin
              let env = Proofview.Goal.env gl in
              let sigma = Proofview.Goal.sigma gl in
              List.iter
                begin fun (met, n) ->
                  let str = met ^ "-" ^ string_of_int n in
                  Msg.info ("Parameters: " ^ str);
                  Opt.predictions_num := n;
                  Opt.predict_method := met;
                  Opt.search_blacklist := false;
                  Opt.filter_program := true;
                  Opt.filter_classes := true;
                  Opt.filter_hurkens := true;
                  let dir = "atp/problems/" ^ str in
                  ignore (Sys.command ("mkdir -p " ^ dir));
                  let goal = get_goal gl in
                  let hyps = get_hyps gl in
                  let defs = get_defs env sigma in
                  let defs1 = Features.predict hyps defs goal in
                  Provers.write_atp_file (dir ^ "/" ^ name ^ ".p") defs1 hyps defs goal
                end
                premises;
              Msg.info ("Done processing " ^ name ^ ".\n");
              Tacticals.New.tclIDTAC
            end
          else if str = "reconstr" then
            begin
              let rec hlp lst =
                match lst with
                | ((prem_sel, prem_num), (prover, extract)) :: lst2 ->
                   begin
                     let str = prover ^ "-" ^ prem_sel  ^ "-" ^ string_of_int prem_num
                     in
                     let dir = "atp/o/" ^ str
                     and odir = "out/" ^ str
                     in
                     let fname = dir ^ "/" ^ name ^ ".p"
                     and ofname =  odir ^ "/" ^ name ^ ".out"
                     in
                     ignore (Sys.command ("mkdir -p " ^ odir));
                     if Sys.command ("grep -q -s \"SZS status Theorem\" \"" ^ fname ^ "\"") = 0 &&
                       not (Sys.file_exists ofname)
                     then
                       let pid = Unix.fork () in
                       if pid = 0 then
                         begin
                           let env = Proofview.Goal.env gl in
                           let sigma = Proofview.Goal.sigma gl in
                           try
                             try_fun
                               begin fun () ->
                                 Msg.info ("Reconstructing theorem " ^ name ^ " (" ^ str ^ ")...");
                                 let info = extract fname in
                                 let (deps, defs, inverts) = get_tac_args env sigma info in
                                 run_tactics deps defs inverts
                                   begin fun tac ->
                                     let msg = "Success " ^ name ^ " " ^ str ^ " " ^ tac in
                                     ignore (Sys.command ("echo \"" ^ msg ^ "\" > \"" ^ ofname ^ "\""));
                                     Msg.info msg;
                                     exit 0
                                   end
                                   begin fun () ->
                                     let msg = "Failure " ^ name ^ " " ^ str in
                                     ignore (Sys.command ("echo \"" ^ msg ^ "\" > \"" ^ ofname ^ "\""));
                                     Msg.info msg;
                                     exit 1
                                   end
                                   (fun _ -> ())
                               end
                               (fun p -> Feedback.msg_notice p; exit 1)
                           with _ ->
                             exit 1
                         end
                       else
                         begin
                           ignore (Unix.waitpid [] pid);
                           hlp lst2
                         end
                     else
                       hlp lst2
                   end
                | [] ->
                   Tacticals.New.tclIDTAC
              in
              hlp premise_prover_lst
            end
          else if str = "prove" then
            begin
              let odir = "out/" in
              let ofname =  odir ^ "/" ^ name ^ ".out" in
              ignore (Sys.command ("mkdir -p " ^ odir));
              if not (Sys.file_exists ofname) then
                let pid = Unix.fork () in
                if pid = 0 then
                  try
                    ignore (Sys.command ("echo \"Failure " ^ name ^ "\" > \"" ^ ofname ^ "\""));
                    try_fun
                      begin fun () ->
                        Msg.info ("Proving theorem " ^ name ^ "...");
                        Proofview.tclORELSE
                          (Proofview.tclBIND
                             (ltac_timeout !Opt.reconstr_timelimit "Tactics.fcrush" [])
                             (fun _ ->
                               let msg = "Success " ^ name in
                               ignore (Sys.command ("echo \"" ^ msg ^ "\" > \"" ^ ofname ^ "\""));
                               Msg.info msg;
                               exit 0))
                          begin fun _ ->
                            let msg = "Failure " ^ name in
                            ignore (Sys.command ("echo \"" ^ msg ^ "\" > \"" ^ ofname ^ "\""));
                            Msg.info msg;
                            exit 1
                          end
                      end
                      (fun p -> Feedback.msg_notice p; exit 1)
                  with _ ->
                    exit 1
                else
                  begin
                    ignore (Unix.waitpid [] pid);
                    Tacticals.New.tclIDTAC
                  end
              else
                Tacticals.New.tclIDTAC
            end
          else
            failwith ("Unknown option in coqhammer.opt: " ^ str)
        end
      else
        begin
          Msg.info "Goal not a proposition.\n";
          Tacticals.New.tclIDTAC
        end
    with Sys_error s ->
      Msg.notice ("Warning: " ^ s);
      Tacticals.New.tclIDTAC
  end
