open Util
open Names
open Ltac_plugin

let intern_constr env evd cexpr =
  let (t, uctx) = Constrintern.interp_constr env evd cexpr in
  let sigma = Evd.from_ctx uctx in
  Typing.solve_evars env sigma t

let tacinterp tac =
  Tacinterp.tactic_of_value (Tacinterp.default_ist ()) tac

let to_constr r =
  match r with
  | Names.GlobRef.VarRef(v) -> EConstr.mkVar v
  | Names.GlobRef.ConstRef(c) -> EConstr.mkConst c
  | Names.GlobRef.IndRef(i) -> EConstr.mkInd i
  | Names.GlobRef.ConstructRef(cr) -> EConstr.mkConstruct cr

let get_global_from_id id =
  Nametab.locate (Libnames.qualid_of_ident id)

let get_global s =
  Nametab.locate (Libnames.qualid_of_string s)

let exists_global s =
  try
    ignore (get_global s);
    true
  with Not_found -> false

let get_constr s =
  to_constr (get_global s)

let get_inductive s =
  match get_global s with
  | Names.GlobRef.IndRef(i) -> i
  | _ -> failwith "not an inductive type"

let get_inductive_from_id id =
  match get_global_from_id id with
  | Names.GlobRef.IndRef(i) -> i
  | _ -> failwith "not an inductive type"

let get_inductive_from_qualid q =
  match Nametab.locate q with
  | Names.GlobRef.IndRef(i) -> i
  | _ -> failwith "not an inductive type"

let get_const s =
  match get_global s with
  | Names.GlobRef.ConstRef(c) -> c
  | _ -> failwith "not a constant"

let get_const_from_id id =
  match get_global_from_id id with
  | Names.GlobRef.ConstRef(c) -> c
  | _ -> failwith "not a constant"

let get_const_from_qualid q =
  match Nametab.locate q with
  | Names.GlobRef.ConstRef(c) -> c
  | _ -> failwith "not a constant"

let get_ind_name ind =
  Libnames.string_of_path (Nametab.path_of_global (Globnames.canonical_gr (Names.GlobRef.IndRef ind)))

let get_ind_nparams ind =
  let mind = fst (Inductive.lookup_mind_specif (Global.env ()) ind) in
  let open Declarations in
  mind.mind_nparams

let get_ind_constrs ind =
  let mind = fst (Inductive.lookup_mind_specif (Global.env ()) ind) in
  let open Declarations in
  Array.to_list mind.mind_packets.(snd ind).mind_user_lc

let get_ind_nconstrs ind =
  let mind = fst (Inductive.lookup_mind_specif (Global.env ()) ind) in
  let open Declarations in
  Array.length mind.mind_packets.(snd ind).mind_user_lc

let is_indexed_ind ind =
  let mind = fst (Inductive.lookup_mind_specif (Global.env ()) ind) in
  let open Declarations in
  mind.mind_packets.(snd ind).mind_nrealargs > 0

(***************************************************************************************)

let rec close f ctx t =
  match ctx with
  | [] -> t
  | (x,ty) :: l -> f (x, ty, close f l t)

(***************************************************************************************)

let get_tactic (s : string) =
  try
    (Tacenv.locate_tactic (Libnames.qualid_of_string s))
  with Not_found ->
    failwith ("tactic not found: " ^ s)

let get_tacexpr tac args =
  Tacexpr.TacArg(CAst.make
                   Tacexpr.(TacCall(CAst.make
                                      (Locus.ArgArg(None, get_tactic tac),
                                       args))))

let ltac_apply tac (args:Tacexpr.glob_tactic_arg list) =
  Tacinterp.eval_tactic (get_tacexpr tac args)

let ltac_eval tac (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Tacexpr.Reference (Locus.ArgVar CAst.(make id)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (get_tacexpr tac args)

let get_hyps gl =
  List.map
    (function
    | Context.Named.Declaration.LocalAssum(x, y) -> (Context.(x.binder_name), y)
    | Context.Named.Declaration.LocalDef(x, _, y) -> (Context.(x.binder_name), y))
    (Proofview.Goal.hyps gl)

(***************************************************************************************)

let rec drop_lambdas evd n t =
  let open Constr in
  let open EConstr in
  if n = 0 then
    t
  else
    match kind evd t with
    | Lambda (na, ty, body) -> drop_lambdas evd (n - 1) body
    | _ -> t

let rec take_lambdas evd n t =
  let open Constr in
  let open EConstr in
  if n = 0 then
    []
  else
    match kind evd t with
    | Lambda (na, ty, body) -> (na, ty) :: take_lambdas evd (n - 1) body
    | _ -> []

let rec drop_prods evd n t =
  let open Constr in
  let open EConstr in
  if n = 0 then
    t
  else
    match kind evd t with
    | Prod (na, ty, body) -> drop_prods evd (n - 1) body
    | _ -> t

let rec take_prods evd n t =
  let open Constr in
  let open EConstr in
  if n = 0 then
    []
  else
    match kind evd t with
    | Prod (na, ty, body) -> (na, ty) :: take_prods evd (n - 1) body
    | _ -> []

let rec drop_all_lambdas evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Lambda (na, ty, body) -> drop_all_lambdas evd body
  | _ -> t

let rec take_all_lambdas evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Lambda (na, ty, body) -> (na, ty) :: take_all_lambdas evd body
  | _ -> []

let rec drop_all_prods evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Prod (na, ty, body) -> drop_all_prods evd body
  | _ -> t

let rec take_all_prods evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Prod (na, ty, body) -> (na, ty) :: take_all_prods evd body
  | _ -> []

let destruct_app = EConstr.decompose_app

let destruct_prod evd t =
  let prods = take_all_prods evd t
  and (h, args) = destruct_app evd (drop_all_prods evd t)
  in
  (prods, h, args)

let destruct_app_red evd t =
  let open Constr in
  let open EConstr in
  let head0 =
    match kind evd t with
    | App (h, _) -> h
    | _ -> t
  in
  match kind evd head0 with
  | Const _ ->
     let (head, args) =
       try
         destruct_app evd (Tacred.try_red_product (Global.env ()) evd t)
       with Not_found | Tacred.Redelimination ->
         destruct_app evd t
     in
     (head0, head, args)
  | _ ->
     let (head, args) = destruct_app evd t in
     (head0, head, args)

let destruct_prod_red evd t =
  let t = Termops.strip_outer_cast evd t in
  let prods = take_all_prods evd t
  and (h0, h, args) = destruct_app_red evd (drop_all_prods evd t)
  in
  (prods, h0, h, args)

(***************************************************************************************)

let map_fold_constr f acc evd t =
  let open Constr in
  let open EConstr in
  let rec hlp m acc t =
    let fold_list k ac ar =
      let (ac1, lst) =
        Array.fold_left
          (fun (ac,l) x -> let (ac',x') = hlp k ac x in (ac',x'::l))
          (ac, [])
          ar
      in
      (ac1, List.rev lst)
    in
    let fold_arr k ac ar =
      let (ac, l) = fold_list k ac (Array.to_list ar) in
      (ac, Array.of_list l)
    in
    match kind evd t with
    | Rel _ | Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ | Int _ | Float _ ->
       f m acc t
    | Cast (ty1,ck,ty2) ->
       let (acc1, ty1') = hlp m acc ty1 in
       let (acc2, ty2') = hlp m acc1 ty2 in
       f m acc2 (mkCast(ty1',ck,ty2'))
    | Prod (na,ty,c)    ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, c') = hlp (m+1) acc1 c in
       f m acc2 (mkProd(na,ty',c'))
    | Lambda (na,ty,c)  ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, c') = hlp (m+1) acc1 c in
       f m acc2 (mkLambda(na,ty',c'))
    | LetIn (na,b,ty,c) ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, b') = hlp m acc1 b in
       let (acc3, c') = hlp (m+1) acc2 c in
       f m acc3 (mkLetIn(na,b',ty',c'))
    | App (a,args) ->
       let (acc1, a') = hlp m acc a in
       let (acc2, args') = fold_arr m acc1 args in
       f m acc2 (mkApp(a',args'))
    | Proj (p,c) ->
       let (acc1, c') = hlp m acc c in
       f m acc1 (mkProj(p,c'))
    | Evar (evk,cl) ->
       let (acc1, cl') = fold_list m acc cl in
       f m acc1 (mkEvar(evk,cl'))
    | Case (ci,p,iv,c,bl) ->
       let (acc, p') = hlp m acc p in
       let (acc, iv') = Constr.fold_map_invert (hlp m) acc iv in
       let (acc, c') = hlp m acc c in
       let (acc, bl') = fold_arr m acc bl in
       f m acc (mkCase(ci,p',iv',c',bl'))
    | Fix (nvn,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let (acc1, typs') = fold_arr m acc typs in
       let (acc2, bodies') = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 (mkFix(nvn,(fnames,typs',bodies')))
    | CoFix (n,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let (acc1, typs') = fold_arr m acc typs in
       let (acc2, bodies') = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 (mkCoFix(n,(fnames,typs',bodies')))
    | Array _ -> assert false
  in
  hlp 0 acc t

let map_constr f evd x = snd (map_fold_constr (fun m () t -> ((), f m t)) () evd x)

let fold_constr f acc evd t =
  let open Constr in
  let open EConstr in
  let rec hlp m acc t =
    let fold_arr k ac ar =
      Array.fold_left (hlp k) ac ar
    in
    match kind evd t with
    | Rel _ | Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ | Int _ | Float _ ->
       f m acc t
    | Cast (ty1,ck,ty2) ->
       let acc1 = hlp m acc ty1 in
       let acc2 = hlp m acc1 ty2 in
       f m acc2 t
    | Prod (na,ty,c) ->
       let acc1 = hlp m acc ty in
       let acc2 = hlp (m+1) acc1 c in
       f m acc2 t
    | Lambda (na,ty,c)  ->
       let acc1 = hlp m acc ty in
       let acc2 = hlp (m+1) acc1 c in
       f m acc2 t
    | LetIn (na,b,ty,c) ->
       let acc1 = hlp m acc ty in
       let acc2 = hlp m acc1 b in
       let acc3 = hlp (m+1) acc2 c in
       f m acc3 t
    | App (a,args) ->
       let acc1 = hlp m acc a in
       let acc2 = fold_arr m acc1 args in
       f m acc2 t
    | Proj (p,c) ->
       let acc1 = hlp m acc c in
       f m acc1 t
    | Evar (evk,cl) ->
       let acc1 = fold_list m acc cl in
       f m acc1 t
    | Case (ci,p,iv,c,bl) ->
       let acc = hlp m acc p in
       let acc = hlp m acc c in
       let acc = fold_invert (hlp m) acc iv in
       let acc = fold_arr m acc bl in
       f m acc t
    | Fix (nvn,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let acc1 = fold_arr m acc typs in
       let acc2 = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 t
    | CoFix (n,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let acc1 = fold_arr m acc typs in
       let acc2 = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 t
    | Array _ -> assert false
  in
  hlp 0 acc t

let fold_constr_shallow f acc evd t =
  let open Constr in
  let open EConstr in
  let rec hlp acc t =
    let fold_arr ac ar =
      Array.fold_left hlp ac ar
    in
    match kind evd t with
    | Rel _ | Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ | Int _ | Float _ ->
       f acc t
    | Cast (ty1,ck,ty2) ->
       let acc1 = hlp acc ty1 in
       let acc2 = hlp acc1 ty2 in
       f acc2 t
    | Prod (na,ty,c) ->
       let acc1 = hlp acc ty in
       f acc1 t
    | Lambda (na,ty,c) ->
       let acc1 = hlp acc ty in
       f acc1 t
    | LetIn (na,b,ty,c) ->
       let acc1 = hlp acc ty in
       let acc2 = hlp acc1 b in
       f acc2 t
    | App (a,args) ->
       let acc1 = hlp acc a in
       let acc2 = fold_arr acc1 args in
       f acc2 t
    | Proj (p,c) ->
       let acc1 = hlp acc c in
       f acc1 t
    | Evar (evk,cl) ->
       let acc1 = fold_list acc cl in
       f acc1 t
    | Case (ci,p,iv,c,bl) ->
       let acc = hlp acc p in
       let acc = hlp acc c in
       let acc = fold_invert hlp acc iv in
       let acc = fold_arr acc bl in
       f acc t
    | Fix (nvn,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let acc1 = fold_arr acc typs in
       f acc1 t
    | CoFix (n,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let acc1 = fold_arr acc typs in
       f acc1 t
    | Array _ -> assert false
  in
  hlp acc t

let map_fold_constr_ker f acc t =
  let open Constr in
  let rec hlp m acc t =
    let fold_list k ac ar =
      let (ac1, lst) =
        Array.fold_left
          (fun (ac,l) x -> let (ac',x') = hlp k ac x in (ac',x'::l))
          (ac, [])
          ar
      in
      (ac1, List.rev lst)
    in
    let fold_arr k ac ar =
      let (ac, l) = fold_list k ac (Array.to_list ar) in
      (ac, Array.of_list l)
    in
    match kind t with
    | Rel _ | Meta _ | Var _ | Sort _ | Const _ | Ind _ | Construct _ | Int _ | Float _ ->
       f m acc t
    | Cast (ty1,ck,ty2) ->
       let (acc1, ty1') = hlp m acc ty1 in
       let (acc2, ty2') = hlp m acc1 ty2 in
       f m acc2 (mkCast(ty1',ck,ty2'))
    | Prod (na,ty,c)    ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, c') = hlp (m+1) acc1 c in
       f m acc2 (mkProd(na,ty',c'))
    | Lambda (na,ty,c)  ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, c') = hlp (m+1) acc1 c in
       f m acc2 (mkLambda(na,ty',c'))
    | LetIn (na,b,ty,c) ->
       let (acc1, ty') = hlp m acc ty in
       let (acc2, b') = hlp m acc1 b in
       let (acc3, c') = hlp (m+1) acc2 c in
       f m acc3 (mkLetIn(na,b',ty',c'))
    | App (a,args) ->
       let (acc1, a') = hlp m acc a in
       let (acc2, args') = fold_arr m acc1 args in
       f m acc2 (mkApp(a',args'))
    | Proj (p,c) ->
       let (acc1, c') = hlp m acc c in
       f m acc1 (mkProj(p,c'))
    | Evar (evk,cl) ->
       let (acc1, cl') = fold_list m acc cl in
       f m acc1 (mkEvar(evk,cl'))
    | Case (ci,p,iv,c,bl) ->
       let (acc, p') = hlp m acc p in
       let (acc, iv') = Constr.fold_map_invert (hlp m) acc iv in
       let (acc, c') = hlp m acc c in
       let (acc, bl') = fold_arr m acc bl in
       f m acc (mkCase(ci,p',iv',c',bl'))
    | Fix (nvn,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let (acc1, typs') = fold_arr m acc typs in
       let (acc2, bodies') = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 (mkFix(nvn,(fnames,typs',bodies')))
    | CoFix (n,recdef) ->
       let (fnames,typs,bodies) = recdef in
       let (acc1, typs') = fold_arr m acc typs in
       let (acc2, bodies') = fold_arr (m + Array.length typs) acc1 bodies in
       f m acc2 (mkCoFix(n,(fnames,typs',bodies')))
    | Array _ -> assert false
  in
  hlp 0 acc t

let map_constr_ker f x = snd (map_fold_constr_ker (fun m () t -> ((), f m t)) () x)

let fold_constr_ker f acc x = fst (map_fold_constr_ker (fun m acc t -> (f m acc t, t)) acc x)

let rel_occurs evd t lst =
  let open Constr in
  let open EConstr in
  fold_constr
    begin fun n b x ->
      match kind evd x with
      | Rel j -> if List.mem (j - n) lst then true else b
      | _ -> b
    end
    false
    evd
    t

let do_shift evd k t =
  let open Constr in
  let open EConstr in
  map_constr
    begin fun n t ->
      match kind evd t with
      | Rel i when i > n -> mkRel (i + k)
      | _ -> t
    end
    evd
    t

let shift_binders_down evd k t =
  assert (k >= 0);
  if k = 0 then
    t
  else
    do_shift evd (-k) t

let shift_binders_up evd k t =
  assert (k >= 0);
  if k = 0 then
    t
  else
    do_shift evd k t

let is_False evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Ind (ind, _) when get_ind_name ind = "Coq.Init.Logic.False" -> true
  | _ -> false

let rec is_atom evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | App (h, _) -> is_atom evd h
  | Ind (ind, _) ->
     let s = get_ind_name ind in
     s <> "Coq.Init.Logic.and" && s <> "Coq.Init.Logic.or" && s <> "Coq.Init.Logic.ex"
  | Const _ | Sort _ | Evar _ | Meta _ | Var _ | Rel _ -> true
  | Prod (_, h, f) when is_atom evd h && is_False evd f -> true
  | _ -> false

let rec is_ind_atom evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | App (h, _) -> is_ind_atom evd t
  | Ind _ -> true
  | _ -> false

let is_product evd t =
  let open Constr in
  let open EConstr in
  match kind evd t with
  | Prod _ when not (is_atom evd t) -> true
  | _ -> false

let get_app_head evd t = match destruct_app evd t with (h, _) -> h

let get_head evd t = match destruct_prod evd t with (_, h, _) -> h

let get_app_head_red evd t = match destruct_app_red evd t with (_, h, _) -> h

let get_head_red evd t = match destruct_prod_red evd t with (_, _, h, _) -> h

let print_constr evd t =
  Feedback.msg_notice (Printer.pr_constr_env (Global.env ()) evd (EConstr.to_constr evd t))

let constr_to_string evd t =
  Pp.string_of_ppcmds (Printer.pr_constr_env (Global.env ()) evd (EConstr.to_constr evd t))

let constant_to_string c =
  Pp.string_of_ppcmds (Printer.pr_constant (Global.env ()) c)

let inductive_to_string ind =
  Pp.string_of_ppcmds (Printer.pr_inductive (Global.env ()) ind)

(******************************************************************************************)
(* Code copied from eauto.ml with minor modifications *)

let unify_e_resolve poly flags (c,clenv) =
  Proofview.Goal.enter begin fun gl ->
    let clenv', c = Auto.connect_hint_clenv ~poly c clenv gl in
    let clenv' = Clenv.clenv_unique_resolver ~flags clenv' gl in
    Proofview.tclTHEN
      (Proofview.Unsafe.tclEVARUNIVCONTEXT (Evd.evar_universe_context clenv'.Clenv.evd))
      (Tactics.Simple.eapply c)
  end

let e_exact poly flags (c,clenv) =
  Proofview.Goal.enter begin fun gl ->
    let clenv', c = Auto.connect_hint_clenv ~poly c clenv gl in
    Tacticals.New.tclTHEN
      (Proofview.Unsafe.tclEVARUNIVCONTEXT (Evd.evar_universe_context clenv'.Clenv.evd))
      (Eauto.e_give_exact c)
  end

let tac_of_hint db h concl =
  let open Hints in
  let st = Auto.auto_flags_of_state (Hint_db.transparent_state db) in
  match h with
  | {pri = b; pat = p; code = t; poly = poly} ->
     let tac = function
       | Res_pf (term,cl) -> Auto.unify_resolve ~poly st (term,cl)
       | ERes_pf (term,cl) -> unify_e_resolve poly st (term,cl)
       | Give_exact (c,cl) -> e_exact poly st (c,cl)
       | Res_pf_THEN_trivial_fail (term,cl) ->
          Tacticals.New.tclTHEN (unify_e_resolve poly st (term,cl))
            (Tacticals.New.tclSOLVE [Eauto.e_assumption;
                                     Tactics.reflexivity;
                                     Tactics.any_constructor true None])
       | Unfold_nth c -> Tactics.reduce
                           (Genredexpr.Unfold [Locus.AllOccurrences,c]) Locusops.onConcl
       | Extern tacast -> Auto.conclPattern concl p tacast
     in
     Hints.run_hint t tac

(******************************************************************************************)

type hint = int * Hints.hint_db * Hints.hint Hints.with_metadata

let hint_priority (p, _, _) = p

let hint_tactic (_, db, h) t = tac_of_hint db h t

let hint_to_string (_, _, h) =
  let open Hints in
  Pp.string_of_ppcmds @@ Hints.pr_hint (Global.env ()) Evd.empty h.code

let find_hints db secvars evd t =
  try
    let open Hints in
    let hdc = Hints.decompose_app_bound evd t in
    let hints =
      if Termops.occur_existential evd t then
        Hint_db.map_existential evd ~secvars hdc t db
      else
        Hint_db.map_auto evd ~secvars hdc t db
    in
    List.map (fun h -> (h.pri, db, h)) hints
  with Hints.Bound ->
    []

(******************************************************************************************)
