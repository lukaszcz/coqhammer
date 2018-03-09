DECLARE PLUGIN "hammer_plugin"

let hammer_version_string = "CoqHammer 1.0.* for Coq 8.7 and 8.7.1"

open Feedback
let () = Mltop.add_known_plugin (fun () ->
  Flags.if_verbose msg_info Pp.(str hammer_version_string))
  "Hammer"
;;

open Hammer_errors

open Util
open Names
open Term
open Libnames
open Globnames
open Nametab
open Misctypes
open Stdarg
open Ltac_plugin

let (++) f g x = f(g(x))

let mkdir s =
  try Unix.mkdir s 0o777 with Unix.Unix_error (Unix.EEXIST,_,_) -> ()

let rec mkdir_rec s =
  if s = "." || s = ".." || s = "" || s = "/" then ()
  else (mkdir_rec (Filename.dirname s); mkdir s)

(* To do: choose a proper printing function *)
let writel fn strl =
  match fn with
  | None ->
      let oc = open_out "default.p" in
      List.iter (Printf.fprintf oc "%s\n") strl;
      close_out oc
  | Some file ->
      let oc = open_out file in
      List.iter (Printf.fprintf oc "%s\n") strl;
      close_out oc

let append file str =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 file in
  output_string oc str;
  close_out oc

let export_statement dir (file,str) =
  let fileo = match dir with
             | None -> "./" ^ file ^ ".p"
             | Some s -> s ^ "/" ^ file ^ ".p"
  in
  let diro = Filename.dirname fileo in
  mkdir_rec diro;
  append fileo (str ^ "\n")

(***************************************************************************************)

let mk_id x = Hh_term.Id x
let mk_app x y = Hh_term.Comb(x, y)
let mk_comb (x, y) = mk_app x y

let tuple (l : Hh_term.hhterm list) =
  match l with
  | [h] -> h
  | h :: t ->
    List.fold_left mk_app h t

let get_current_context () =
  try
    Pfedit.get_current_goal_context ()
  with _ ->
    (Evd.empty, Global.env ())

let hhterm_of_global glob =
  mk_id (string_of_path (path_of_global (Globnames.canonical_gr glob)))

let hhterm_of_sort s = match Term.family_of_sort s with
  | InProp -> mk_id "$Prop"
  | InSet  -> mk_id "$Set"
  | InType -> mk_id "$Type"

let hhterm_of_constant c =
  tuple [mk_id "$Const"; hhterm_of_global (ConstRef c)]

let hhterm_of_inductive i =
  tuple [mk_id "$Ind"; hhterm_of_global (IndRef i);
         mk_id (string_of_int (Inductiveops.inductive_nparams i))]

let hhterm_of_construct cstr =
  tuple [mk_id "$Construct"; hhterm_of_inductive (fst cstr); hhterm_of_global (ConstructRef cstr)]

let hhterm_of_var v =
  tuple [mk_id "$Var"; hhterm_of_global (VarRef v)]

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
let hhterm_of_name name = match name with
  | Name.Name id -> tuple [mk_id "$Name"; mk_id (Id.to_string id)]
  | Name.Anonymous  -> tuple [mk_id "$Name"; mk_id "$Anonymous"]

let hhterm_of_namearray a =
  tuple ((mk_id "$NameArray") :: (List.map hhterm_of_name (Array.to_list a)))

let hhterm_of_bool b =
  if b then mk_app (mk_id "$Bool") (mk_id "$True")
  else mk_app (mk_id "$Bool") (mk_id "$False")

let rec hhterm_of (t : Term.constr) : Hh_term.hhterm =
  match Term.kind_of_term t with
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
                                tuple [hhterm_of_constant (Projection.constant p);
                                       hhterm_of_bool (Projection.unfolded p)];
                                hhterm_of c]
                         (* TODO: projections not really supported *)
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
and hhterm_of_constrarray a =
  tuple ((mk_id "$ConstrArray") :: List.map hhterm_of (Array.to_list a))
and hhterm_of_precdeclaration (a,b,c) =
  tuple [(mk_id "$PrecDeclaration") ; hhterm_of_namearray a;
         hhterm_of_constrarray b; hhterm_of_constrarray c]

let get_type_of env evmap t =
  EConstr.to_constr evmap (Retyping.get_type_of env evmap (EConstr.of_constr t))

(* only for constants *)
let hhproof_of c =
  begin match Global.body_of_constant c with
  | Some b -> hhterm_of b
  | None -> mk_id "$Axiom"
  end

let hhdef_of_global glob_ref : (string * Hh_term.hhdef) =
  let glob_ref = Globnames.canonical_gr glob_ref in
  let (evmap, env) = get_current_context () in
  let ty = fst (Global.type_of_global_in_context env glob_ref) in
  let kind = get_type_of env evmap ty in
  let const = match glob_ref with
    | ConstRef c -> hhterm_of_constant c
    | IndRef i   -> hhterm_of_inductive i
    | ConstructRef cstr -> hhterm_of_construct cstr
    | VarRef v -> hhterm_of_var v
  in
  let filename_aux = match glob_ref with
    | ConstRef c -> Constant.to_string c
    | IndRef i   -> MutInd.to_string (fst i)
    | ConstructRef cstr -> MutInd.to_string ((fst ++ fst) cstr)
    | VarRef v -> Id.to_string v
  in
  let term = match glob_ref with
    | ConstRef c -> lazy (hhproof_of c)
    | _ -> lazy (mk_id "$Axiom")
  in
  let filename =
     let l = Str.split (Str.regexp "\.") filename_aux in
     Filename.dirname (String.concat "/" l)
  in
  (filename, (const, hhterm_of kind, lazy (hhterm_of ty), term))

let hhdef_of_hyp (id, maybe_body, ty) =
  let (evmap, env) = get_current_context () in
  let kind = get_type_of env evmap ty in
  let body =
    match maybe_body with
    | Some b -> lazy (hhterm_of b)
    | None -> lazy (mk_id "$Axiom")
  in
  (mk_comb(mk_id "$Const", mk_id (Id.to_string id)), hhterm_of kind, lazy (hhterm_of ty), body)

let econstr_to_constr x = EConstr.to_constr Evd.empty x

let make_good =
  function
  | Context.Named.Declaration.LocalAssum(x, y) ->
     (x, None, econstr_to_constr y)
  | Context.Named.Declaration.LocalDef(x, y, z) ->
     (x, Some (econstr_to_constr y), econstr_to_constr z)

let get_hyps gl =
  List.map (hhdef_of_hyp ++ make_good) (Proofview.Goal.hyps gl)

let get_goal gl =
  (mk_comb(mk_id "$Const", mk_id "_HAMMER_GOAL"),
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

let save_in_list refl glob_ref env c = refl := glob_ref :: !refl

let my_search () =
  let ans = ref [] in
  let filter glob_ref env typ =
    if !Opt.search_blacklist then
      Search.blacklist_filter glob_ref env typ
    else
      true
  in
  let iter glob_ref env typ =
    if filter glob_ref env typ then save_in_list ans glob_ref env typ
  in
  let () = Search.generic_search None iter in
  List.filter
    begin fun glob_ref ->
      try
        let (_, env) = get_current_context () in
        ignore (Global.type_of_global_in_context env glob_ref);
        true
      with _ ->
        false
    end
    (List.rev !ans)

let my_print_refl dir l : unit =
  List.iter (export_statement dir) l

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

let all_objects dir =
  my_print_refl dir
    (List.map string_of_hhdef_2
       (unique_hhdefs (List.map hhdef_of_global (my_search ()))))

VERNAC COMMAND EXTEND Hammer_plugin_all_objects CLASSIFIED AS QUERY
| [ "Hammer_export" string(dir)] -> [ all_objects (Some dir) ]
END

let get_defs () : Hh_term.hhdef list =
  List.map snd (unique_hhdefs
                  (List.map hhdef_of_global (my_search ())))

let get_tactic (s : string) =
  (Nametab.locate_tactic (Libnames.qualid_of_string s))

let get_tacexpr tac args =
  Tacexpr.TacArg(None,
                 Tacexpr.TacCall(None,
                                 (Misctypes.ArgArg(None, get_tactic tac),
                                 args)))

let ltac_apply tac (args:Tacexpr.glob_tactic_arg list) =
  Tacinterp.eval_tactic (get_tacexpr tac args)

let ltac_lcall tac args =
  Tacexpr.TacArg(None,
                 Tacexpr.TacCall(None, (ArgVar(None, Id.of_string tac),args)))

let ltac_timeout tm tac (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Tacexpr.Reference (ArgVar (None, id)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Timeout.tclTIMEOUT tm (Tacinterp.eval_tactic_ist ist (get_tacexpr tac args))

let to_ltac_val c = Tacinterp.Value.of_constr (EConstr.of_constr c)

let to_constr r =
  match r with
  | VarRef(v) -> mkVar v
  | ConstRef(c) -> mkConst c
  | IndRef(i) -> mkInd i
  | ConstructRef(cr) -> mkConstruct cr

let get_global s =
  Nametab.locate (Libnames.qualid_of_string s)

let get_constr s =
  to_constr (get_global s)

let mk_pair x y =
  let (evmap, env) = get_current_context () in
  let pr = get_constr "pair" in
  let tx = get_type_of env evmap x in
  let ty = get_type_of env evmap y in
  mkApp (pr, [| tx; ty; x; y |])

let rec mk_lst lst =
  match lst with
  | [] -> get_constr "Reconstr.Empty"
  | [h] -> h
  | h :: t -> mk_pair (mk_lst t) h

let mk_lst_str lst =
  let get_name x =
    "@" ^ (Hhlib.drop_prefix (Hh_term.get_hhterm_name (hhterm_of x)) "Top.")
  in
  match lst with
  | [] -> "Reconstr.Empty"
  | h :: t -> "(" ^ List.fold_right (fun x a -> get_name x ^ ", " ^ a) t (get_name h) ^ ")"

let get_tac_args deps defs =
  let map_locate =
    List.map
      begin fun s ->
        try
          Nametab.locate (Libnames.qualid_of_string s)
        with Not_found ->
          VarRef(Id.of_string s)
      end
  in
  let (deps, defs) = (map_locate deps, map_locate defs) in
  let filter_vars = List.filter (fun r -> match r with VarRef(_) -> true | _ -> false) in
  let filter_nonvars = List.filter (fun r -> match r with VarRef(_) -> false | _ -> true) in
  let (vars, deps, defs) = (filter_vars deps, filter_nonvars deps, defs) in
  let map_to_constr = List.map to_constr in
  let (vars, deps, defs) = (map_to_constr vars, map_to_constr deps, map_to_constr defs) in
  let (tvars, tdeps, tdefs) = (mk_lst vars, mk_lst deps, mk_lst defs) in
  let args = [to_ltac_val tvars; to_ltac_val tdeps; to_ltac_val tdefs] in
  (vars, deps, defs, args)

let check_goal_prop gl =
  let (evmap, env) = get_current_context () in
  let tp = EConstr.to_constr evmap (Retyping.get_type_of env evmap (Proofview.Goal.concl gl)) in
  match Term.kind_of_term tp with
  | Sort s -> Term.family_of_sort s = InProp
  | _ -> false
    
let run_tactics vars deps defs args msg_invoke msg_success msg_fail msg_total_fail =
  let tactics =
    [("Reconstr.htrivial", "Reconstr.shtrivial", 2 * !Opt.reconstr_timelimit / 5);
     ("Reconstr.hobvious", "Reconstr.shobvious", 2 * !Opt.reconstr_timelimit / 5);
     ("Reconstr.heasy", "Reconstr.sheasy", 3 * !Opt.reconstr_timelimit / 5);
     ("Reconstr.hsimple", "Reconstr.shsimple", 3 * !Opt.reconstr_timelimit / 5);
     ("Reconstr.hcrush", "Reconstr.shcrush", !Opt.reconstr_timelimit);
     ("Reconstr.hyelles 4", "Reconstr.shyelles4", !Opt.reconstr_timelimit);
     ("Reconstr.hrauto 2", "Reconstr.shrauto2", !Opt.reconstr_timelimit);
     ("Reconstr.hblast", "Reconstr.shblast", 3 * !Opt.reconstr_timelimit / 2);
     ("Reconstr.hexhaustive 0", "Reconstr.shexhaustive0", !Opt.reconstr_timelimit);
     ("Reconstr.hreconstr 4", "Reconstr.shreconstr4", !Opt.reconstr_timelimit);
     ("Reconstr.hscrush", "Reconstr.shscrush", 3 * !Opt.reconstr_timelimit / 2);
     ("Reconstr.hrauto 4", "Reconstr.shrauto4", 2 * !Opt.reconstr_timelimit);
     ("Reconstr.hyelles 6", "Reconstr.shyelles6", 3 * !Opt.reconstr_timelimit / 2);
     ("Reconstr.hyreconstr", "Reconstr.shyreconstr", 2 * !Opt.reconstr_timelimit);
     ("Reconstr.hexhaustive 1", "Reconstr.shexhaustive1", 3 * !Opt.reconstr_timelimit / 2);
     ("Reconstr.hreconstr 6", "Reconstr.shreconstr6", 3 * !Opt.reconstr_timelimit / 2)] in
  let rec reconstr lst =
    match lst with
    | [] ->
       begin
         msg_total_fail ();
         ltac_apply "idtac" []
       end
    | (tac, cmd, timeout) :: t ->
       begin
         msg_invoke tac vars deps defs;
         Proofview.tclOR
           (Proofview.tclBIND
              (ltac_timeout timeout cmd args)
              (fun _ -> msg_success tac vars deps defs; ltac_apply "idtac" []))
           begin fun _ ->
             msg_fail tac timeout;
             reconstr t
           end
       end
  in
  reconstr tactics

let do_predict hyps defs goal =
  if !Opt.gs_mode > 0 then
    let greedy_sequence =
      [(!Opt.vampire_enabled, Opt.vampire_enabled, "knn", 1024);
       (!Opt.z3_enabled, Opt.z3_enabled, "knn", 128);
       (!Opt.eprover_enabled, Opt.eprover_enabled, "knn", 1024);
       (!Opt.vampire_enabled, Opt.vampire_enabled, "knn", 64);
       (!Opt.z3_enabled, Opt.z3_enabled, "nbayes", 32);
       (!Opt.z3_enabled, Opt.z3_enabled, "nbayes", 512);
       (!Opt.z3_enabled, Opt.z3_enabled, "nbayes", 128);
       (!Opt.eprover_enabled, Opt.eprover_enabled, "nbayes", 256);
       (!Opt.z3_enabled, Opt.z3_enabled, "nbayes", 16);
       (!Opt.eprover_enabled, Opt.eprover_enabled, "nbayes", 1024);
       (!Opt.vampire_enabled, Opt.vampire_enabled, "nbayes", 256);
       (!Opt.z3_enabled, Opt.z3_enabled, "knn", 64);
       (!Opt.eprover_enabled, Opt.eprover_enabled, "nbayes", 512);
       (!Opt.eprover_enabled, Opt.eprover_enabled, "nbayes", 128);
       (!Opt.vampire_enabled, Opt.vampire_enabled, "knn", 32);
       (!Opt.vampire_enabled, Opt.vampire_enabled, "knn", 256);
       (!Opt.vampire_enabled, Opt.vampire_enabled, "knn", 16);
       (!Opt.vampire_enabled, Opt.vampire_enabled, "nbayes", 32);
       (!Opt.z3_enabled, Opt.z3_enabled, "nbayes", 64);
	   (!Opt.cvc4_enabled, Opt.cvc4_enabled, "knn", 64);
       (!Opt.cvc4_enabled, Opt.cvc4_enabled, "nbayes", 128)]
    in
    let fname = Features.extract hyps defs goal in
    let jobs =
      List.map
        begin fun (enabled, pref, pred_method, preds_num) _ ->
          if not enabled then
            exit 1;
          Opt.vampire_enabled := false;
          Opt.eprover_enabled := false;
          Opt.z3_enabled := false;
          pref := true;
          Opt.parallel_mode := false;
          try
            let defs1 = Features.run_predict fname defs preds_num pred_method in
            Provers.predict defs1 hyps defs goal
          with
          | HammerError(msg) ->
             Msg.error ("Hammer error: " ^ msg);
             exit 1
          | _ ->
             exit 1
        end
        (Hhlib.take !Opt.gs_mode (List.filter (fun (enabled, _, _, _) -> enabled) greedy_sequence))
    in
    let time = (float_of_int !Opt.atp_timelimit) *. 1.5
    in
    Msg.info ("Running provers (using " ^ string_of_int !Opt.gs_mode ^ " threads)...");
    match Parallel.run_parallel (fun _ -> ()) (fun _ -> ()) time jobs with
    | None -> Features.clean fname; raise (HammerFailure "ATPs failed to find a proof")
    | Some x -> Features.clean fname; x
  else
    let defs1 = Features.predict hyps defs goal in
    Provers.predict defs1 hyps defs goal

let try_scrush () =
  if !Opt.scrush_timelimit = 0 then
    Proofview.tclZERO (Failure "timeout")
  else
    Proofview.tclBIND
      (ltac_timeout !Opt.scrush_timelimit "Reconstr.scrush" [])
      (fun _ ->
        Msg.info "Replace the hammer tactic with: Reconstr.scrush";
        ltac_apply "idtac" [])

(***************************************************************************************)

let hammer_tac () =
  Proofview.Goal.nf_enter
    begin fun gl ->
        Proofview.tclOR
          (try_scrush ())
          begin fun _ ->
            try
              let goal = get_goal gl in
              let hyps = get_hyps gl in
              let defs = get_defs () in
              if !Opt.debug_mode then
                Msg.info ("Found " ^ string_of_int (List.length defs) ^ " accessible Coq objects.");
              let (deps, defs) = do_predict hyps defs goal in
              let (vars, deps, defs, args) = get_tac_args deps defs in
              run_tactics vars deps defs args
                begin fun tac _ _ _ ->
                  Msg.info ("Trying tactic " ^ tac ^ "...")
                end
                begin fun tac vars deps defs ->
                  Msg.info ("Tactic " ^ tac ^ " succeeded.");
                  Msg.info ("Replace the hammer tactic with:\n\t" ^
                               tac ^ " " ^ mk_lst_str vars ^ "\n\t\t" ^ mk_lst_str deps ^
                               "\n\t\t" ^ mk_lst_str defs ^ ".")
                end
                begin fun tac timeout ->
                  if !Opt.debug_mode then
                    Msg.info ("Tactic " ^ tac ^ " failed to solve the goal in " ^
                                 string_of_int timeout ^ "s.")
                end
                begin fun () ->
                  Msg.error ("Hammer failed to solve the goal.")
                end
            with
            | HammerError(msg) ->
               Msg.error ("Hammer error: " ^ msg);
              ltac_apply "idtac" []
            | HammerFailure(msg) ->
               Msg.error ("Hammer failed: " ^ msg);
              ltac_apply "idtac" []
            | Failure s ->
               Msg.error ("CoqHammer bug: " ^ s);
              Msg.error "Please report.";
              ltac_apply "idtac" []
            | Sys.Break ->
               raise Sys.Break
            | e ->
               Msg.error ("CoqHammer bug: please report: " ^ Printexc.to_string e);
              ltac_apply "idtac" []
          end
    end

TACTIC EXTEND Hammer_tac
| [ "hammer" ] -> [ hammer_tac () ]
END

let hammer_cleanup () =
  Coq_transl.cleanup ();
  Features.cleanup ()

VERNAC COMMAND EXTEND Hammer_plugin_cleanup CLASSIFIED AS SIDEFF
| [ "Hammer_cleanup" ] -> [ hammer_cleanup () ]
END

let hammer_print name =
  try
    let glob = get_global name in
    let (_, (const, kind, ty, trm)) = hhdef_of_global glob in
    Msg.notice (Hh_term.string_of_hhterm const ^ " = ");
    Msg.notice (Hh_term.string_of_hhterm (Lazy.force trm));
    Msg.notice (" : " ^ Hh_term.string_of_hhterm (Lazy.force ty));
    Msg.notice (" : " ^ Hh_term.string_of_hhterm kind)
  with Not_found ->
    Msg.error ("Not found: " ^ name)

VERNAC COMMAND EXTEND Hammer_plugin_print CLASSIFIED AS QUERY
| [ "Hammer_print" string(name) ] -> [ hammer_print name ]
END

let hammer_dump name0 =
  try
    let glob = get_global name0 in
    let (_, def) = hhdef_of_global glob in
    let name = Hh_term.get_hhdef_name def in
    Coq_transl.remove_def name;
    Coq_transl.reinit [def];
    List.iter
      begin fun (n, a) ->
        if not (Hhlib.string_begins_with n "_HAMMER_") then
          Msg.notice (n ^ ": " ^ Coq_transl.string_of_coqterm a)
      end
      (Coq_transl.translate name)
  with Not_found ->
    Msg.error ("Not found: " ^ name0)

VERNAC COMMAND EXTEND Hammer_plugin_dump CLASSIFIED AS QUERY
| [ "Hammer_dump" string(name) ] -> [ hammer_dump name ]
END

let hammer_version () =
  Msg.info hammer_version_string

VERNAC COMMAND EXTEND Hammer_plugin_version CLASSIFIED AS QUERY
| [ "Hammer_version" ] -> [ hammer_version () ]
END

let hammer_hook_tac prefix name =
  Proofview.Goal.nf_enter begin fun gl ->
    Msg.info ("Processing theorem " ^ name ^ "...");
    if check_goal_prop gl then
      begin
        let fopt = open_in "/home/burak/Desktop/coqhammer/eval/coqhammer.opt" in
        let str = input_line fopt in
        close_in fopt;
        if str = "check" then
          ltac_apply "idtac" []
        else if str = "gen-atp" then
          begin
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
                let defs = get_defs () in
                let defs1 = Features.predict hyps defs goal in
                Provers.write_atp_file (dir ^ "/" ^ name ^ ".p") defs1 hyps defs goal
              end
              [("knn", 16); ("knn", 32); ("knn", 64); ("knn", 128); ("knn", 256);
               ("knn", 512); ("knn", 1024);
               ("nbayes", 16); ("nbayes", 32); ("nbayes", 64); ("nbayes", 128); ("nbayes", 256);
               ("nbayes", 512); ("nbayes", 1024)];
            Msg.info ("Done processing " ^ name ^ ".\n");
            ltac_apply "idtac" []
          end
        else
          begin
            let idx = String.index str '-' in
            let prover = String.sub str 0 idx in
            let extract =
              if prover = "eprover" then
                Provers.extract_eprover_data
              else if prover = "vampire" then
                Provers.extract_vampire_data
              else if prover = "z3" then
                Provers.extract_z3_data
              else
                failwith "unknown prover"
            in
            let dir = "atp/o/" ^ str
            and odir = "out/" ^ str
            in
            let fname = dir ^ "/" ^ name ^ ".p"
            and ofname =  odir ^ "/" ^ name ^ ".out"
            and tfname =  odir ^ "/" ^ name ^ ".try"
            in
            ignore (Sys.command ("mkdir -p " ^ odir));
            if Sys.command ("grep -q -s \"SZS status Theorem\" \"" ^ fname ^ "\"") = 0 &&
              not (Sys.file_exists ofname)
            then
              try
                Msg.info ("Reconstructing theorem " ^ name ^ "...");
                let tries_num =
                  try
                    let tfile = open_in tfname in
                    let r = int_of_string (input_line tfile) in
                    close_in tfile;
                    r
                  with _ ->
                    0
                in
                if tries_num < 2 then
                  begin
                    ignore (Sys.command ("echo " ^ string_of_int (tries_num + 1) ^
                                            " > \"" ^ tfname ^ "\""));
                    let (deps, defs) = extract fname in
                    let (vars, deps, defs, args) = get_tac_args deps defs in
                    run_tactics vars deps defs args
                      (fun _ _ _ _ -> ())
                      begin fun tac vars deps defs ->
                        let msg = "Success " ^ name ^ " " ^ str ^ " " ^ tac in
                        ignore (Sys.command ("echo \"" ^ msg ^ "\" > \"" ^ ofname ^ "\""));
                        Msg.info msg
                      end
                      (fun _ _ -> ())
                      begin fun () ->
                        let msg = "Failure " ^ name ^ " " ^ str in
                        ignore (Sys.command ("echo \"" ^ msg ^ "\" > \"" ^ ofname ^ "\""));
                        Msg.info msg
                      end
                  end
                else
                  begin
                    let msg = "Failure " ^ name ^ " " ^ str ^ ": gave up after " ^
                      string_of_int tries_num ^ " tries"
                    in
                    ignore (Sys.command ("echo \"" ^ msg ^ "\" > \"" ^ ofname ^ "\""));
                    Msg.info msg;
                    ltac_apply "idtac" []
                  end
              with (HammerError s) ->
                Msg.info s;
                ltac_apply "idtac" []
            else
              begin
                ltac_apply "idtac" []
              end
          end
      end
    else
      begin
        Msg.info "Goal not a proposition.\n";
        ltac_apply "idtac" []
      end
  end

TACTIC EXTEND Hammer_hook_tac
| [ "hammer_hook" string(prefix) string(name) ] -> [ hammer_hook_tac prefix name ]
END
