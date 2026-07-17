(* Translation from Coq to FOL *)

open Hammer_lib
open Coqterms
open Coq_transl_opts
open Hh_term

(***************************************************************************************)
(* Adjust variable names *)

let adjust_varnames =
  let rename_abs n (vname, ty, body) =
    (string_of_int n ^ "_" ^ vname, ty, body)
  in
  map_coqterm0
    begin fun n ctx tm ->
      match tm with
      | Var(x) ->
        let i = int_of_string x - 1
        in
        let nthctx = List.nth ctx i
        in
        let vname = fst nthctx
        in
        Var(string_of_int (n - 1 - i) ^ "_" ^ vname)
      | Lam a ->
          Lam (rename_abs n a)
      | Prod a ->
          Prod (rename_abs n a)
      | Quant(op, a) ->
          Quant(op, rename_abs n a)
      | Let(value, a) ->
          Let(value, rename_abs n a)
      | Fix(cft, m, recargs, names, types, bodies) ->
          let names2 =
            List.rev
              (fst
                 (List.fold_left
                    (fun (acc, k) name -> ((string_of_int k ^ "_" ^ name) :: acc, k + 1))
                    ([], n)
                    names))
          in
          Fix(cft, m, recargs, names2, types, bodies)
      | _ ->
          tm
    end

(***************************************************************************************)
(* Adjust logical operators *)

let adjust_logops =
  map_coqterm
    begin fun ctx tm ->
      match tm with
      | App(Const(op), Lam a) when op = "!" || op = "?" ->
        Quant(op, a)
      | App(App(App(Const("="), ty), x), y) ->
        Equal(x, y)
      | _ ->
        tm
    end

(***************************************************************************************)
(* Initialization *)

let reinit (lst : hhdef list) =
  let conv h t =
    let def = Coq_convert.to_coqdef h t in
    let def = coqdef_map adjust_varnames def in
    let def = coqdef_map adjust_logops def in
    if opt_simpl then
      coqdef_map simpl def
    else
      def
  in
  let rec add_defs lst =
    match lst with
    | h :: t ->
      let name = get_hhdef_name h in
      if not (Defhash.mem name) then
        Defhash.add_lazy name (lazy (conv h t));
      add_defs t
    | [] ->
        ()
  in
  log 1 "Reinitializing...";
  let hastype_type = mk_fun_ty (Const("$Any")) (mk_fun_ty SortType SortProp) in
  begin
    try
      List.iter Defhash.add logop_defs;
      if opt_hastype then
        Defhash.add ("$HasType", Const("$HasType"), hastype_type, SortType)
    with _ -> ()
  end;
  add_defs lst

(***************************************************************************************)
(* Axioms monad *)

(* the second element is a function which given a list of axioms
   prepends to it a fixed list of axioms (in time proportional to the
   prepended list) and returns the result *)
(* type 'a axioms_monad = 'a * ((string * fol) -> (string * fol)) *)

let return tm = (tm, fun axs -> axs)
let bind (x, mk1) f =
  let (y, mk2) = f x
  in
  (y, (fun axs -> mk2 (mk1 axs)))

let (>>=) = bind
let (>>) m1 m2 = bind m1 (fun _ -> m2)
let lift f m = m >>= fun x -> return (f x)

let listM_nth lst n =
  let rec hlp i selected lst =
    match lst with
    | [] ->
       begin
         match selected with
         | Some r -> return r
         | None -> failwith "listM_nth"
       end
    | h :: t ->
       h >>= fun r ->
       hlp (i + 1) (if i = n then Some r else selected) t
  in
  hlp 0 None lst

let add_axiom ax =
  log 3 ("add_axiom: " ^ fst ax);
  ((), fun axs ->
    debug 1 (fun () ->
      if List.exists (fun ax2 -> fst ax2 = fst ax) axs then
        failwith ("duplicate axiom name: " ^ fst ax));
    ax :: axs)

let extract_axioms m = (snd m) []

(* general axioms for any Coq translation *)
let coq_axioms = [
  ("_HAMMER_COQ_TRUE", Const("$True"));
  ("_HAMMER_COQ_FALSE", App(Const("~"), Const("$False")));
  ("_HAMMER_COQ_TYPE_TYPE", mk_hastype (Const("Type")) (Const("Type")))
] @
  if opt_set_to_type then
    []
  else
    [
      ("_HAMMER_COQ_SET_TYPE", mk_hastype (Const("Set")) (Const("Type")));
      ("_HAMMER_COQ_SET_SUB_TYPE",
       mk_forall "X" type_any
         (mk_impl
            (mk_hastype (Var("X")) (Const("Set")))
            (mk_hastype (Var("X")) (Const("Type")))))
    ]

(***************************************************************************************)
(* Coqterms hash *)

let coqterm_hash = Hashing.create lift

(* Nested anonymous lifts have no definition-style axiom name of their own.
   Keep the enclosing declaration while translating so their structural case
   dependencies are delivered with the declaration that introduced them. *)
let translation_owner = ref ""

(* The ordinal separates erased proof-case occurrences within one declaration.
   Structurally identical occurrences at the same ordinal in other declarations
   may still share a cached lift, avoiding owner-specific cache growth. *)
let proof_case_counter = ref 0

let fresh_proof_case_key () =
  incr proof_case_counter;
  "$proof-case\000" ^ string_of_int !proof_case_counter

let case_occurrence_key ctx tm =
  let proof_scrutinee =
    match tm with
    | Case(_, (Cast(Const("$Proof"), _) | Const("$Proof")), _, _, _, _) -> true
    | _ -> false
  in
  let proof_dependencies =
    List.fold_right
      (fun (name, _) acc ->
         if var_occurs name tm &&
            (try Coq_typing.check_proof_var ctx name with _ -> false)
         then name :: acc
         else acc)
      ctx []
  in
  match proof_scrutinee, proof_dependencies with
  | true, _ -> fresh_proof_case_key ()
  | false, [] -> ""
  | false, _ -> !translation_owner ^ "\000" ^ String.concat "\000" proof_dependencies

(* Split equations are meaningful together with the structural theory of the
   type they inspect.  Keep that semantic dependency separately from ordinary
   premise selection so [get_axioms] can deliver it unconditionally. *)
module Case_dependencies = struct
  let table = Hashtbl.create 128
  let clear () = Hashtbl.clear table
  let add owner indname =
    let previous = try Hashtbl.find table owner with Not_found -> [] in
    if not (List.mem indname previous) then
      Hashtbl.replace table owner (indname :: previous)
  let find owner = try Hashtbl.find table owner with Not_found -> []
  let remove owner = Hashtbl.remove table owner
end

(* Hash-consed lifts replay their exact case dependencies on cache hits.  A
   scoped collector records dependencies while constructing a cache miss;
   nested lifts propagate their dependencies to the enclosing cached lift. *)
module Lift_dependencies = struct
  let table = Hashtbl.create 128
  let collectors = ref []
  let clear () = Hashtbl.clear table; collectors := []
  let record indname =
    match !collectors with
    | dependencies :: _ -> dependencies := indname :: !dependencies
    | [] -> ()
  let find name = try Hashtbl.find table name with Not_found -> []
  let add name dependencies =
    let previous = find name in
    Hashtbl.replace table name
      (Hhlib.sort_uniq String.compare (dependencies @ previous))
end

let with_lift_dependencies make =
  let dependencies = ref [] in
  let previous_collectors = !(Lift_dependencies.collectors) in
  Lift_dependencies.collectors := dependencies :: previous_collectors;
  let result =
    try make ()
    with e ->
      Lift_dependencies.collectors := previous_collectors;
      raise e
  in
  Lift_dependencies.collectors := previous_collectors;
  let delivered =
    match flatten_app (fst result) with
    | Const name, _
         when String.length name >= 2 && String.sub name 0 2 = "$_" ->
       if !dependencies <> [] then Lift_dependencies.add name !dependencies;
       Lift_dependencies.find name
    | _ -> Hhlib.sort_uniq String.compare !dependencies
  in
  List.iter
    (fun dependency ->
       Case_dependencies.add !translation_owner dependency;
       Lift_dependencies.record dependency)
    delivered;
  result

let is_transport_constant name =
  List.exists (fun basename -> Coq_stdnames.is_init_logic basename name)
    [ "eq_rect"; "eq_rec"; "eq_ind"; "eq_rect_r"; "eq_rec_r"; "eq_ind_r" ]

let is_false_rect_constant name = Coq_stdnames.is_init_logic "False_rect" name

let is_wf_fix_constant name = Coq_stdnames.is_init_wf "Fix" name

let is_wf_fix_f_constant name = Coq_stdnames.is_init_wf "Fix_F" name

let is_program_fix_sub_constant name = Coq_stdnames.is_program_wf "Fix_sub" name

let is_program_fix_f_sub_constant name = Coq_stdnames.is_program_wf "Fix_F_sub" name

let specif_constant basename =
  let core = "Corelib.Init.Specif." ^ basename
  and coq = "Coq.Init.Specif." ^ basename
  and stdlib = "Stdlib.Init.Specif." ^ basename in
  if Defhash.mem core then core else if Defhash.mem coq then coq else stdlib

let erase_false_rect_type_arg ctx tm =
  if opt_refinement_types then
    match flatten_app tm with
    | Const name, ty :: args
         when is_false_rect_constant name && args <> [] && ty <> type_any &&
              Coq_erasure.has_erasable_content ctx ty ->
       (* Impossible branches may mention a collapsed refinement package in
          the eliminated result type, but the proof argument is erased and the
          branch is unreachable.  Keep the ordinary opaque eliminator and replace
          only the type parameter by [$Any] so no sig/exist bridge leaks into a
          definition axiom. *)
       Some (mk_long_app (Const name) (type_any :: args))
    | _ -> None
  else
    None

let transport_full_arity = 6

let erase_transport_head tm =
  if opt_prop_case_erasure then
    match flatten_app tm with
    | Const name, args
         when is_transport_constant name && List.length args >= transport_full_arity ->
       (* Transport erasure maps fully applied casts to the transported value in
          the proof-irrelevant model.  Preserve applications after the transport
          spine, e.g. [(eq_rect ... f ... e) x] erases to [f x].
          Reconstruction-sensitive cases are isolated by [opt_erasure_guards]. *)
       Some (mk_long_app (List.nth args 3) (Hhlib.drop transport_full_arity args))
    | _ -> None
  else
    None

let transport_erasure_premise tm =
  if opt_erasure_guards then
    match flatten_app tm with
    | Const name, args
         when is_transport_constant name && List.length args >= transport_full_arity ->
       let a = List.nth args 1
       and b = List.nth args 4
       in
       (* Transport/UIP debt note: transport erasure is valid in the junk model
          by proof irrelevance but is not generally replayable as a CIC source
          theorem; the guarded option emits the converted source equality as a
          premise. *)
       Some (mk_eq a b)
    | _ -> None
  else
    None

let proof_like_after_erasure ctx tm =
  match tm with
  | Var name ->
     (try Coq_typing.check_proof_var ctx name with _ -> false)
  | _ ->
     match flatten_app tm with
     | Const name, args ->
        if Coq_stdnames.is_init_logic "eq_refl" name then
          List.length args >= 2
        else if Coq_stdnames.is_init_logic "eq_trans" name then
          List.length args >= 6
        else if Coq_stdnames.is_init_logic "eq_sym" name then
          List.length args >= 4
        else if Coq_stdnames.is_jmeq "JMeq_refl" name then
          List.length args >= 2
        else
          false
     | _ -> false

(***************************************************************************************)
(* Inversion axioms for inductive types *)

let mk_inversion_conjs params_num args targs cacc =
  let rec mk_conjs ctx args targs cacc =
    match args, targs with
    | ((name, ty) :: args2), (y :: targs2) ->
      let cacc2 =
        if Coq_typing.check_prop ctx ty then
          cacc
        else
          (mk_eq (Var(name)) y) :: cacc
      in
      mk_conjs ((name, ty) :: ctx) args2 targs2 cacc2
    | [], [] ->
      if cacc = [] then
        Const("$True")
      else
        join_right mk_and cacc
    | _ ->
      failwith "mk_inversion_conjs"
  in
  let args2 = Hhlib.drop params_num args
  and ctx = List.rev (Hhlib.take params_num args)
  in
  mk_conjs ctx args2 targs cacc

let mk_inversion params indname constrs matched_term f =
  let rec mk_disjs constrs acc =
    match constrs with
    | cname :: constrs2 ->
      let (_, targs, cargs) = Coq_typing.destruct_type_app (coqdef_type (Defhash.find cname))
      in
      let params_num = List.length params
      in
      let cargs1 = Hhlib.take params_num cargs
      in
      let cargs2 =
        List.map
          (fun (name, ty) -> (name, subst_params cargs1 params ty))
          (Hhlib.drop params_num cargs)
      in
      let targs2 =
        List.map
          (fun tm -> subst_params cargs1 params tm)
          (Hhlib.drop params_num targs)
      in
      let eqt = mk_eq matched_term (mk_long_app (Const(cname)) (params @ mk_vars cargs2))
      in
      let disj = mk_long_exists cargs2 (f cname targs2 cargs2 eqt)
      in
      mk_disjs constrs2 (disj :: acc)
    | [] -> List.rev acc
  in
  let disjs = mk_disjs constrs []
  in
  match disjs with
  | [] -> Const("$False")
  | _ -> join_right mk_or disjs

let mk_prop_inversion params indname args constrs =
  let rec mk_disjs constrs acc =
    match constrs with
    | cname :: constrs2 ->
      let ty = coqdef_type (Defhash.find cname)
      in
      let (_, targs, cargs) = Coq_typing.destruct_type_app ty
      in
      let params_num = List.length params
      in
      let cargs1 = Hhlib.take params_num cargs
      in
      let cargs2 =
        List.map
          (fun (name, ty) -> (name, subst_params cargs1 params ty))
          (Hhlib.drop params_num cargs)
      in
      let targs2 =
        List.map
          (fun tm -> subst_params cargs1 params tm)
          (Hhlib.drop params_num targs)
      in
      let disj =
        mk_long_exists cargs2
          (mk_inversion_conjs params_num args targs2 [])
      in
      mk_disjs constrs2 (disj :: acc)
    | [] -> List.rev acc
  in
  if args = [] then
    begin
      if constrs = [] then
        Const("$False")
      else
        Const("$True")
    end
  else
    let disjs = mk_disjs constrs []
    in
    match disjs with
    | [] -> Const("$False")
    | _ -> join_right mk_or disjs

let rec mk_guards ctx vars tm =
  match vars with
  | (name, ty) :: vars2 ->
     if Coq_typing.check_prop ctx ty then
       (mk_impl ty
          (mk_guards ((name, ty) :: ctx) vars2 (subst_proof name ty tm)))
     else
       (mk_impl (App(App(Const("$HasType"), Var(name)), ty))
          (mk_guards ((name, ty) :: ctx) vars2 tm))
  | [] ->
     tm

(* The following mutually recursively defined functions return
   (coqterm axioms_monad) or (unit axioms_monad). *)

let program_wf_simpl tm =
  (* projector, packing constructor, index of the packed field it selects *)
  let proj_table =
    [ "projT1", "existT", 2;
      "projT2", "existT", 3;
      "proj1_sig", "exist", 2;
      "proj2_sig", "exist", 3 ]
  in
  let rebuild_app head args =
    match args with
    | [] -> head
    | _ -> mk_long_app head args
  in
  let rec simpl_rec tm =
    let tm =
      match tm with
      | App(x, y) -> App(simpl_rec x, simpl_rec y)
      | Lam(vname, vtype, body) -> Lam(vname, simpl_rec vtype, simpl_rec body)
      | Prod(vname, vtype, body) -> Prod(vname, simpl_rec vtype, simpl_rec body)
      | Quant(op, (vname, vtype, body)) -> Quant(op, (vname, simpl_rec vtype, simpl_rec body))
      | Let(value, (vname, _, body)) -> simpl_rec (substvar vname (simpl_rec value) body)
      | Case(indname, matched_term, return_type, raw_return_type, params_num, branches) ->
         Case(indname, simpl_rec matched_term, simpl_rec return_type,
              simpl_rec raw_return_type, params_num,
              List.map (fun (n, branch) -> (n, simpl_rec branch)) branches)
      | Cast(body, ty) -> Cast(simpl_rec body, simpl_rec ty)
      | Fix(cft, k, recargs, names, types, bodies) ->
         Fix(cft, k, recargs, names, List.map simpl_rec types, List.map simpl_rec bodies)
      | _ -> tm
    in
    match tm with
    | App(Lam(vname, _, body), x) -> simpl_rec (substvar vname x body)
    | _ ->
       begin
         match flatten_app tm with
         | Const pname, [_; _; packed] ->
            begin
              try
                let (_, ctor, idx) =
                  List.find
                    (fun (p, _, _) -> Coq_stdnames.is_init_specif p pname)
                    proj_table
                in
                begin match flatten_app packed with
                | Const cname, cargs
                    when Coq_stdnames.is_init_specif ctor cname && List.length cargs = 4 ->
                   simpl_rec (List.nth cargs idx)
                | _ -> tm
                end
              with Not_found ->
                tm
            end
         | head, args -> rebuild_app head args
       end
  in
  simpl_rec tm

(* Per-translation WF-recursion marker.  Proof-only erasure sets it before
   falling back whenever an Acc/proof-recursive path would otherwise emit an
   unsafe unconditional equation. *)
let wf_mark = ref false

let rec add_inversion_axioms0 mkinv indname axname fvars lvars constrs matched_term f =
  (* Note: the correctness of calling `prop_to_formula' below
     depends on the implementation of `convert_term' (that it
     never invokes check_prop on an application of the form
     App(..App(Const(cname),_)..)) *)
  let inv = mkinv indname constrs matched_term f
  in
  match inv with
  | Const("$False") -> return ()
  | _ ->
     let m =
       if !opt_closure_guards then
         close (fvars @ lvars)
           (fun ctx -> prop_to_formula ctx inv)
       else if opt_lambda_guards then
         let ctx = List.rev fvars
         in
         let mtfvars = get_fvars ctx matched_term
         in
         let fvars0 =
           List.filter (fun (name, _) -> not (List.mem_assoc name mtfvars)) fvars
         and fvars1 = mtfvars
         in
         (close fvars0
            (fun ctx1 ->
              make_guarded_forall ctx1 fvars1
                (fun _ -> prop_to_formula ctx (mk_long_forall lvars inv))))
       else
         let vars = fvars @ lvars
         in
         let ctx = List.rev vars
         in
         let vars1 = get_fvars ctx matched_term
         in
         make_fol_forall [] vars (mk_guards [] vars1 inv)
     in
     m >>= fun tm -> add_axiom (mk_axiom axname tm)

(***************************************************************************************)
(* Lambda-lifting, fix-lifting and case-lifting *)

and emit_definition_equation ?premise axname name fvars lvars body =
  let vars = fvars @ lvars in
  let mk_eqv ctx =
    let mk_eqv =
      if Coq_typing.check_prop ctx body then
        mk_equiv
      else
        mk_eq
    in
    let lhs = mk_long_app (Const(name)) (mk_vars vars) in
    let eqv = mk_eqv lhs body in
    match premise with
    | Some prem -> mk_impl prem eqv
    | None -> eqv
  in
  let closed =
    if !wf_mark && opt_wf_recursion_eqs then
      (* WF-recursion model note: these equations are not read as
         delta-unfolding in the term model.  They are Coq theorems only with
         the erased PI premises (Fix_eq), and semantically describe a total
         extension outside those premises; the consistency canaries check this
         load-bearing path. *)
      make_fol_forall_keep_prop_premises [] vars (mk_eqv (List.rev vars))
    else
      close fvars
        begin fun ctx ->
          let eqv = mk_eqv (List.rev_append lvars ctx) in
          if !opt_closure_guards || opt_lambda_guards then
            prop_to_formula ctx (mk_long_forall lvars eqv)
          else
            make_fol_forall ctx lvars eqv
        end
  in
  closed
  >>=
  (fun tm -> add_axiom (mk_axiom axname tm))
  >>
  convert (List.rev fvars) (mk_long_app (Const(name)) (mk_vars fvars))

and lambda_lifting wf_fix_names axname name fvars lvars1 tm =
  debug 3 (fun () -> print_header "lambda_lifting" tm (fvars @ lvars1));
  let rec extract_lambdas tm acc =
    match tm with
    | Lam(vname, vtype, body) -> extract_lambdas body ((vname, vtype) :: acc)
    | _ -> (List.rev acc, tm)
  in
  let (lvars2, body2) = extract_lambdas tm []
  in
  let lvars = lvars1 @ lvars2
  in
  match erase_transport_head body2 with
  | Some body3 ->
     let premise = transport_erasure_premise body2 in
     emit_definition_equation ?premise axname name fvars lvars body3
  | None ->
  let wf_recursion_equation tm =
    if not opt_wf_recursion_eqs || name = "" then
      None
    else
      let rec_call_args xname yname lvars_ext =
        List.map
          (fun (vname, _) -> if vname = xname then Var(yname) else Var(vname))
          (fvars @ lvars_ext)
      in
      let build a_ty rel f x lvars_ext =
        match x with
        | Var xname when List.mem_assoc xname lvars_ext ->
           let yname = refresh_varname "wfarg" in
           let hname = refresh_varname "wfproof" in
           let rel_y_x = mk_long_app rel [ Var(yname); x ] in
           let rec_fun =
             Lam(yname, a_ty,
                 Lam(hname, rel_y_x,
                     mk_long_app (Const(name)) (rec_call_args xname yname lvars_ext)))
           in
           let unfolded = simpl (mk_long_app f [ x; rec_fun ]) in
           Some(lvars_ext, unfolded)
        | _ -> None
      in
      let build_program_sub helper_name a_ty rel f x =
        let yname = refresh_varname "wfarg" in
        let zname = refresh_varname "wfarg" in
        let subset_pred = Lam(zname, a_ty, mk_long_app rel [ Var(zname); x ]) in
        let proj1_sig = specif_constant "proj1_sig" in
        let rec_arg = mk_long_app (Const(proj1_sig)) [ a_ty; subset_pred; Var(yname) ] in
        let rec_fun = Lam(yname, type_any, mk_long_app (Const(helper_name)) [ rec_arg ]) in
        Some(lvars, program_wf_simpl (mk_long_app f [ x; rec_fun ]))
      in
      let program_fix_sub_components tm =
        match flatten_app tm with
        | Const cname, args when is_program_fix_sub_constant cname && List.length args >= 5 ->
           Some(List.nth args 0, List.nth args 1, List.nth args 4)
        | Const cname, args when is_program_fix_f_sub_constant cname && List.length args >= 4 ->
           Some(List.nth args 0, List.nth args 1, List.nth args 3)
        | _ -> None
      in
      try
        match flatten_app tm with
        | Const helper_name, [x] ->
           begin
             try
               match program_fix_sub_components (coqdef_value (Defhash.find helper_name)) with
               | Some(a_ty, rel, f) -> build_program_sub helper_name a_ty rel f x
               | None -> None
             with _ -> None
           end
        | Const cname, args when is_program_fix_sub_constant cname && List.length args >= 6 ->
           let a_ty = List.nth args 0
           and rel = List.nth args 1
           and f = List.nth args 4
           and x = List.nth args 5
           in
           build_program_sub name a_ty rel f x
        | Const cname, args when is_program_fix_f_sub_constant cname && List.length args >= 5 ->
           let a_ty = List.nth args 0
           and rel = List.nth args 1
           and f = List.nth args 3
           and x = List.nth args 4
           in
           build_program_sub name a_ty rel f x
        | _ ->
        match flatten_app tm with
        | Const cname, args when is_wf_fix_constant cname && List.length args >= 5 ->
           let a_ty = List.nth args 0
           and rel = List.nth args 1
           and f = List.nth args 4
           and rest = Hhlib.drop 5 args
           in
           begin match rest with
           | [] ->
              let xname = refresh_varname "wfarg" in
              build a_ty rel f (Var xname) (lvars @ [ (xname, a_ty) ])
           | [Var xname as x] when List.mem_assoc xname lvars ->
              build a_ty rel f x lvars
           | _ -> None
           end
        | Const cname, args when is_wf_fix_f_constant cname && List.length args >= 6 ->
           let a_ty = List.nth args 0
           and rel = List.nth args 1
           and f = List.nth args 3
           and x = List.nth args 4
           in
           build a_ty rel f x lvars
        | _ -> None
      with _ -> None
  in
  match wf_recursion_equation body2 with
  | Some(lvars, body3) ->
     wf_mark := true;
     begin match simpl body3 with
     | Fix(_) -> fix_lifting wf_fix_names axname name fvars lvars body3
     | Case(_) -> case_lifting wf_fix_names axname name fvars lvars body3
     | _ -> emit_definition_equation axname name fvars lvars body3
     end
  | None ->
  match body2 with
  | Fix(_) ->
     fix_lifting wf_fix_names axname name fvars lvars body2
  | Case(_) ->
     case_lifting wf_fix_names axname name fvars lvars body2
  | _ ->
     emit_definition_equation axname name fvars lvars body2

and fix_lifting wf_fix_names axname dname fvars lvars tm =
  debug 3 (fun () -> print_header "fix_lifting" tm (fvars @ lvars));
  match tm with
  | Fix(cft, k, recargs, names, types, bodies) ->
      let fix_pref = "$_fix_" ^ unique_id () ^ "_"
      in
      let names1 = List.map ((^) fix_pref) names
      in
      let names2 =
        if axname = "" then names1 else Hhlib.take k names1 @ [ dname ] @ Hhlib.drop (k + 1) names1
      and axnames =
        if axname = "" then names1 else Hhlib.take k names1 @ [ axname ] @ Hhlib.drop (k + 1) names1
      in
      let vars = mk_vars (fvars @ lvars)
      in
      let env = List.map2 (fun name name2 -> (name, mk_long_app (Const(name2)) vars)) names names2
      in
      let prep body =
        List.fold_left (fun tm (name, value) -> simple_subst name value tm) body env
      in
      List.iter2
        (fun name2 ty ->
          let ty2 = mk_long_prod fvars (mk_long_prod lvars ty)
          in
          try
            Defhash.add (mk_def name2 (Const(name2)) ty2
                           (if Coq_typing.check_prop [] ty2 then SortProp else SortType))
          with _ -> ())
        names2 types;
      let recarg_is_prop recarg ty =
        try
          let args = Coq_typing.get_type_args ty in
          let (_, recarg_ty) = List.nth args recarg in
          Coq_typing.check_prop (List.rev (fvars @ lvars @ Hhlib.take recarg args)) recarg_ty
        with _ ->
          false
      in
      let recargs_available = List.length recargs = List.length names2 in
      let wf_fix_names2 =
        if cft <> CoqFix then
          (* Cofix unfolding is a status-quo axiom path: no new WF premise
             discipline applies to cofixpoints in this refactor. *)
          []
        else if not recargs_available then
          names2
        else
          List.fold_right
            (fun (name2, (ty, recarg)) acc ->
               if recarg_is_prop recarg ty then name2 :: acc else acc)
            (List.combine names2 (List.combine types recargs)) []
      in
      if wf_fix_names2 <> [] then
        wf_mark := true;
      let wf_fix_names = wf_fix_names2 @ wf_fix_names in
      listM_nth
        (List.map2
           (fun (axname2, name2) body ->
             lambda_lifting wf_fix_names axname2 name2 fvars lvars (prep body))
           (List.combine axnames names2)
           bodies)
        k
  | _ ->
      failwith "fix_lifting"

and case_lifting wf_fix_names axname0 name0 fvars lvars tm =
  debug 3 (fun () -> print_header "case_lifting" tm (fvars @ lvars));
  let internal_error msg =
    raise (Hammer_errors.HammerError ("internal translation error: " ^ msg))
  in
  let dependency_owner =
    let prefix = "$_def_" in
    if String.length axname0 >= String.length prefix &&
       String.sub axname0 0 (String.length prefix) = prefix
    then String.sub axname0 (String.length prefix)
           (String.length axname0 - String.length prefix)
    else if axname0 <> "" then axname0 else !translation_owner
  in
  let get_case_type_args indty rt params_num =
    let args = Coq_typing.get_type_args indty
    in
    let rec pom n tm =
      match tm with
      | Lam(_, ty, body) ->
        if n = 0 then
          let (_, tyargs) = flatten_app ty in
          tyargs
        else
          pom (n - 1) body
      | _ ->
         internal_error
           ("case return predicate is not eta-long: " ^ string_of_coqterm tm)
    in
    let n = List.length args
    in
    if n < params_num then
      internal_error
        ("case predicate has fewer arguments than its parameters: " ^ string_of_coqterm rt)
    else
      pom (n - params_num) rt
  in
  let get_case_scrutinee_type indty rt params_num =
    let rec pom n tm =
      match tm with
      | Lam(_, ty, body) ->
         if n = 0 then ty else pom (n - 1) body
      | _ ->
         internal_error "normalized case return predicate is not eta-long"
    in
    let n = List.length (Coq_typing.get_type_args indty) in
    if n < params_num then
      internal_error "normalized case predicate has fewer arguments than its parameters"
    else
      pom (n - params_num) rt
  in
  let get_params indty rt params_num =
    let tyargs = get_case_type_args indty rt params_num in
    if List.length tyargs < params_num then
      internal_error
        ("case predicate has fewer type arguments than its parameters: " ^
         string_of_coqterm rt)
    else
      Hhlib.take params_num tyargs
  in
  let rec get_branch cname cstrs brs =
      match cstrs, brs with
      | c :: cstrs2, b :: brs2 ->
         if c = cname then b else get_branch cname cstrs2 brs2
      | _ -> internal_error "case branch does not match constructor telescope"
    in
    let constructor_args params params_num cname =
      let cdef =
        try Defhash.find cname with Not_found ->
          internal_error ("missing constructor declaration: " ^ cname)
      in
      let (_, targs, cargs) = Coq_typing.destruct_type_app (coqdef_type cdef)
      in
      let cargs1 = Hhlib.take params_num cargs
      in
      let cargs2 =
        List.map
          (fun (name, ty) -> (name, subst_params cargs1 params ty))
          (Hhlib.drop params_num cargs)
      in
      let targs2 =
        List.map
          (fun tm -> subst_params cargs1 params tm)
          (Hhlib.drop params_num targs)
      in
      (targs2, cargs2)
    in
    let subst_proof_args base_ctx args body =
      let rec hlp ctx args body =
        match args with
        | [] -> body
        | (name, ty) :: args2 ->
           let body2 =
             if Coq_typing.check_prop ctx ty then
               subst_proof name ty body
             else
               body
           in
           hlp ((name, ty) :: ctx) args2 body2
      in
      hlp base_ctx args body
    in
    let refresh_case_args vars args =
      let refresh_name used name =
        if List.mem name used then
          refresh_varname name
        else
          name
      in
      let subst_renamings renamings tm =
        List.fold_left
          (fun tm (name, name2) ->
             if name = name2 then tm else substvar name (Var name2) tm)
          tm renamings
      in
      let rec hlp used renamings acc args =
        match args with
        | [] -> List.rev acc
        | (name, ty) :: args2 ->
           let name2 = refresh_name used name in
           let ty2 = subst_renamings renamings ty in
           hlp (name2 :: used) ((name, name2) :: renamings) ((name2, ty2) :: acc) args2
      in
      hlp (List.map fst vars) [] [] args
    in
    (* Refinement occurrence collapse: matching a subset value exposes the
       erased carrier itself, and the remaining proof payload binders are erased. *)
    let collapse_subset_case ~matched_term ~vars ~constrs ~branches ~params ~params_num carrier_idx =
      match constrs, branches with
      | [cname], [(n, branch)] ->
         let (_, args) = constructor_args params params_num cname in
         if List.length args <> n then
           internal_error "subset constructor telescope arity mismatch"
         else
           let args = refresh_case_args vars args in
           let body = simpl (mk_long_app branch (mk_vars args)) in
           let rec subst_args ctx idx body = function
             | [] -> body
             | (arg_name, arg_ty) :: args2 ->
                let body2 =
                  if idx = carrier_idx then
                    substvar arg_name matched_term body
                  else if Coq_typing.check_prop ctx arg_ty then
                    subst_proof arg_name arg_ty body
                  else
                    internal_error "subset constructor has an unexpected informative payload"
                in
                subst_args ((arg_name, arg_ty) :: ctx) (idx + 1) body2 args2
           in
           subst_args (List.rev vars) 0 body args
      | _ -> internal_error "subset case is not a singleton constructor case"
    in
    let is_acc_ind indname = Coq_stdnames.is_init_wf "Acc" indname in
    let term_fvars_subset names tm =
      fold_coqterm
        (fun ctx acc tm ->
           acc &&
           match tm with
           | Var name when not (List.mem_assoc name ctx) -> List.mem name names
           | _ -> true)
        true tm
    in
    let collapse_prop_singleton vars indname constrs params params_num branches =
      match constrs, branches with
      | [cname], [(n, branch)] ->
         let (_, args) = constructor_args params params_num cname in
         if List.length args <> n then
           internal_error "propositional singleton constructor telescope arity mismatch"
         else
           let args = refresh_case_args vars args in
           let body = simpl (mk_long_app branch (mk_vars args)) in
           let body = subst_proof_args (List.rev vars) args body in
           if wf_fix_names <> [] && is_acc_ind indname && term_mentions_const wf_fix_names body then
             begin
               (* WF guardrail: erasing an Acc proof on a recursive path would
                  produce the forbidden unconditional WF-unfolding equation.
                  Fix_eq justifies only the premised equation, and the total-
                  extension model accounts for values outside the premise; with
                  the option off the occurrence-lifted symbol stays unconstrained. *)
               wf_mark := true;
               if opt_wf_recursion_eqs then Some body else None
             end
           else
             Some body
      | _ -> internal_error "propositional singleton has an unexpected constructor shape"
    in
    let combine_premises p1 p2 =
      match p1, p2 with
      | None, None -> None
      | Some p, None | None, Some p -> Some p
      | Some p1, Some p2 -> Some (mk_and p1 p2)
    in
    let constructor_index_premise indname indty params params_num actual_tyargs targs =
      let type_args = Coq_typing.get_type_args indty in
      let actual_args = Hhlib.drop params_num actual_tyargs
      and index_formals = Hhlib.drop params_num type_args
      and ctx = List.rev (Hhlib.take params_num type_args)
      in
      let targs =
        if Coq_stdnames.is_init_logic "eq" indname && targs = [] &&
           List.length actual_args = 1 && params <> []
        then [List.hd (List.rev params)]
        else targs
      in
      if index_formals = [] then
        None
      else
      let rec conjs ctx actuals targs formals acc =
        match actuals, targs, formals with
        | actual :: actuals2, targ :: targs2, (name, ty) :: formals2 ->
           let acc =
             if Coq_typing.check_prop ctx ty then
               acc
             else
               mk_eq actual targ :: acc
           in
           conjs ((name, ty) :: ctx) actuals2 targs2 formals2 acc
        | [], [], [] ->
           begin match acc with
           | [] -> None
           | _ -> Some (join_right mk_and acc)
           end
        | _ ->
           internal_error
             ("constructor result indices do not align with the case predicate (" ^
              string_of_int (List.length actuals) ^ " actual, " ^
              string_of_int (List.length targs) ^ " constructor, " ^
              string_of_int (List.length formals) ^ " formal arguments remain)")
      in
      conjs ctx actual_args targs index_formals []
    in
    let emit_equation ?premise axname vars lhs rhs is_prop =
      let mk_eqv = if is_prop then mk_equiv lhs rhs else mk_eq lhs rhs in
      let mk_eqv =
        match premise with
        | Some prem -> mk_impl prem mk_eqv
        | None -> mk_eqv
      in
      (* Split equations carry only computation.  Constructor-pattern equations
         need no guards, and inversion axioms still provide exhaustiveness after
         the old packaged case split is dropped.  When ClosureGuards is enabled
         we use the ordinary guarded closure machinery uniformly. *)
      begin
        if !wf_mark && opt_wf_recursion_eqs then
          (* WF-recursion model note: premised equations are read through the
             total-extension model outside the erased PI premises, not as
             unconditional delta-unfolding; Fix_eq justifies only the premised
             form and the canaries guard consistency. *)
          make_fol_forall_keep_prop_premises [] vars mk_eqv
        else if !opt_closure_guards then
          close vars (fun ctx -> prop_to_formula ctx mk_eqv)
        else
          make_fol_forall [] vars mk_eqv
      end >>= fun r ->
      add_axiom (mk_axiom axname r)
    in
    let emit_leaf ?premise axname vars lhs body =
      let ctx = List.rev vars in
      emit_equation ?premise axname vars lhs body (Coq_typing.check_prop ctx body)
    in
    (* A propositional match denotes a formula, not a program value.  Its
       lifted predicate is bounded from below by all branches and from above
       by one constructor branch; the inhabitation guard keeps both bounds
       vacuous on junk values and empty propositions. *)
    let emit_prop_case axname vars lhs indname indty params params_num
        constrs matched_term branches =
      let ctx = List.rev vars in
      let scrutinee, scrutinee_ty =
        match matched_term with
        | Var name ->
           begin try (name, List.assoc name vars) with Not_found ->
             raise (Hammer_errors.HammerError
                      "internal translation error: case scrutinee is not in scope")
           end
        | _ ->
           raise (Hammer_errors.HammerError
                    "internal translation error: propositional case was not normalized")
      in
      let (_, actual_tyargs) = flatten_app scrutinee_ty in
      let close_fol body =
        let rec close ctx = function
          | (name, ty) :: rest ->
             if Coq_typing.check_prop ctx ty then
               prop_to_formula ctx ty >>= fun premise ->
               close ((name, ty) :: ctx) rest >>= fun r ->
               return (mk_impl premise r)
             else
               close ((name, ty) :: ctx) rest >>= fun r ->
               return (mk_forall name type_any r)
          | [] -> return body
        in
        close [] vars
      in
      let quantify lower args body =
        let rec loop ctx = function
          | (name, ty) :: rest ->
             if Coq_typing.check_prop ctx ty then
               prop_to_formula ctx ty >>= fun premise ->
               loop ((name, ty) :: ctx) rest >>= fun r ->
               return (if lower then mk_impl premise r else mk_and premise r)
             else
               make_guard ctx ty (Var name) >>= fun guard ->
               loop ((name, ty) :: ctx) rest >>= fun r ->
               let connective = if lower then mk_impl guard r else mk_and guard r in
               return ((if lower then mk_forall else mk_exists) name type_any connective)
          | [] -> return body
        in
        loop ctx args
      in
      let one_branch cname =
        let n, branch = get_branch cname constrs branches in
        let targs, args = constructor_args params params_num cname in
        if List.length args <> n then
          raise (Hammer_errors.HammerError
                   "internal translation error: constructor telescope arity mismatch");
        let args0 = args in
        let args = refresh_case_args vars args in
        let targs =
          List.map
            (fun tm ->
               List.fold_left2
                 (fun tm (name, _) (name2, _) ->
                    if name = name2 then tm else substvar name (Var name2) tm)
                 tm args0 args)
            targs
        in
        let body = simpl (mk_long_app branch (mk_vars args)) in
        let body = subst_proof_args ctx args body in
        prop_to_formula (List.rev (vars @ args)) body >>= fun branch_formula ->
        let pattern = mk_long_app (Const(cname)) (params @ mk_vars args) in
        prop_to_formula (List.rev (vars @ args)) (mk_eq (Var scrutinee) pattern)
        >>= fun scrutinee_formula ->
        let index =
          if Coq_stdnames.is_init_logic "eq" indname then
            Some scrutinee_ty
          else
            constructor_index_premise indname indty params params_num actual_tyargs targs
        in
        begin match index with
        | None -> return scrutinee_formula
        | Some premise ->
           prop_to_formula (List.rev (vars @ args)) premise >>= fun index_formula ->
           return (mk_and scrutinee_formula index_formula)
        end >>= fun branch_condition ->
        quantify true args (mk_impl branch_condition branch_formula) >>= fun lower ->
        quantify false args (mk_and branch_condition branch_formula) >>= fun upper ->
        return (lower, upper)
      in
      let rec branches_fol = function
        | cname :: rest ->
           one_branch cname >>= fun branch ->
           branches_fol rest >>= fun more ->
           return (branch :: more)
        | [] -> return []
      in
      begin
        if Coq_typing.check_prop ctx scrutinee_ty then
          prop_to_formula ctx scrutinee_ty
        else
          make_guard ctx scrutinee_ty (Var scrutinee)
      end >>= fun inhabitation ->
      convert ctx lhs >>= fun predicate ->
      branches_fol constrs >>= fun bounds ->
      let lowers = List.map fst bounds and uppers = List.map snd bounds in
      let lower_conjs = match lowers with [] -> Const("$True") | _ -> join_right mk_and lowers in
      let upper_disjs = match uppers with [] -> Const("$False") | _ -> join_right mk_or uppers in
      close_fol (mk_impl (mk_and inhabitation lower_conjs) predicate) >>= fun lower ->
      add_axiom (mk_axiom (axname ^ "$lower") lower) >>
      close_fol (mk_impl (mk_and inhabitation predicate) upper_disjs) >>= fun upper ->
      add_axiom (mk_axiom (axname ^ "$upper") upper)
    in
    let rec infer_term_type ctx = function
      | Var name ->
         begin try Some (List.assoc name ctx) with Not_found -> None end
      | Const name ->
         begin
           try Some (coqdef_type (Defhash.find name)) with Not_found -> None
         end
      | App(fn, arg) ->
         begin match infer_term_type ctx fn with
         | Some fn_ty ->
            begin
              try
                match simpl fn_ty with
                | Prod(name, _, body) -> Some (simpl (substvar name arg body))
                | _ -> None
              with _ -> None
            end
         | None -> None
         end
      | Lam(name, ty, body) ->
         begin match infer_term_type ((name, ty) :: ctx) body with
         | Some body_ty -> Some (Prod(name, ty, body_ty))
         | None -> None
         end
      | Case(_, matched, _, raw_return_type, params_num, _) ->
         begin match infer_term_type ctx matched with
         | Some matched_ty ->
            let (_, actual_tyargs) = flatten_app matched_ty in
            if List.length actual_tyargs < params_num then
              None
            else
              let indices = Hhlib.drop params_num actual_tyargs in
              Some (simpl (mk_long_app raw_return_type (indices @ [matched])))
         | None -> None
         end
      | Cast(_, ty) -> Some ty
      | Fix(_, k, _, _, types, _) ->
         begin try Some (List.nth types k) with _ -> None end
      | Let(value, (name, ty, body)) ->
         begin match infer_term_type ((name, ty) :: ctx) body with
         | Some body_ty -> Some (simpl (substvar name value body_ty))
         | None -> None
         end
      | _ -> None
    in
    let case_aux_value vars indname matched_term return_type raw_return_type params_num branches indty =
      let z = refresh_varname "case" in
      let ctx = List.rev vars in
      let fallback_scrutinee_ty =
        get_case_scrutinee_type indty return_type params_num
      in
      let scrutinee_ty =
        if Coq_typing.check_prop ctx fallback_scrutinee_ty then
          match infer_term_type ctx matched_term with
          | Some ty -> ty
          | None -> fallback_scrutinee_ty
        else
          fallback_scrutinee_ty
      in
      let scrutinee_is_prop = Coq_typing.check_prop ctx scrutinee_ty in
      let aux_case = Lam(z, scrutinee_ty,
                         Case(indname, Var(z), return_type, raw_return_type,
                              params_num, branches)) in
      let occurrence_key =
        if scrutinee_is_prop then
          fresh_proof_case_key ()
        else
          case_occurrence_key ctx aux_case
      in
      with_lift_dependencies (fun () ->
        Hashing.find_or_insert_keyed occurrence_key coqterm_hash ctx aux_case
          begin fun cctx ctm ->
            match ctm with
            | Lam(_, _, Case(indname2, _, _, _, _, _)) ->
               let name = "$_case_" ^ indname2 ^ "$" ^ unique_id () in
               lambda_lifting [] name name (ctx_to_vars cctx) [] ctm
            | _ -> internal_error "case auxiliary lifting lost its normalized case body"
          end) >>= fun aux ->
      if scrutinee_is_prop then
        return aux
      else
        convert ctx matched_term >>= fun mt ->
        return (App(aux, mt))
    in
    (* Termination follows the structure of the generated statement: first the
       number of root case/lambda/fix nodes remaining to compile, then the node
       count.  Non-variable scrutinees are replaced by fresh variables in
       hash-consed auxiliary cases; the remaining branches recurse into proper
       bodies or delegate to value translation. *)
    let rec compile_case ?premise lhs vars axname body =
      match simpl body with
      | Case(indname, matched_term, return_type, raw_return_type, params_num, branches) as case_body ->
         let df =
           try Defhash.find indname with Not_found ->
             internal_error ("missing inductive declaration: " ^ indname)
         in
         begin
           match df with
           | (_, IndType(_, constrs, pnum), indty, _) ->
              if pnum <> params_num then
                internal_error "case parameter arity disagrees with its inductive declaration";
              let raw_params = get_params indty raw_return_type params_num in
              let normalized_scrutinee_ty =
                get_case_scrutinee_type indty return_type params_num
              in
              let (_, normalized_tyargs) = flatten_app normalized_scrutinee_ty in
              let params =
                if List.length normalized_tyargs >= params_num then
                  Hhlib.take params_num normalized_tyargs
                else
                  raw_params
              in
              let record_case_dependency () =
                (* Every emitted case equation relies on the structural theory
                   of its scrutinee, including proposition-valued matches
                   translated as lower/upper bounds. *)
                Lift_dependencies.record indname;
                if dependency_owner <> "" then
                  Case_dependencies.add dependency_owner indname;
                if !translation_owner <> "" && !translation_owner <> dependency_owner then
                  Case_dependencies.add !translation_owner indname
              in
              let rec return_target_is_prop ctx = function
                | Lam(name, ty, body) -> return_target_is_prop ((name, ty) :: ctx) body
                | SortProp -> true
                | Quant(_) | Equal(_) -> true
                | target ->
                   let raw_logic_head =
                     match flatten_app target with
                     | Const name, _ ->
                        List.exists
                          (fun basename -> Coq_stdnames.is_init_logic basename name)
                          [ "True"; "False"; "and"; "or"; "iff"; "eq"; "ex" ]
                     | _ -> false
                   in
                   raw_logic_head || Coq_typing.check_prop ctx target
              in
              if return_target_is_prop (List.rev vars) return_type then
                if not opt_prop_case_erasure then begin
                  log 2 ("case-axiom-omitted: prop-case-erasure " ^ axname);
                  return ()
                end
                else begin
                  record_case_dependency ();
                  match matched_term with
                  | Var _ ->
                     emit_prop_case axname vars lhs indname indty params params_num
                       constrs matched_term branches
                  | _ ->
                     case_aux_value vars indname matched_term return_type raw_return_type
                       params_num branches indty
                     >>= fun rhs -> emit_equation ?premise (axname ^ "$link") vars lhs rhs true
                end
              else if Coq_typing.check_type_target_is_prop indty then
                if not opt_prop_case_erasure then begin
                  log 2 ("case-axiom-omitted: prop-case-erasure " ^ axname);
                  return ()
                end
                else begin
                  match matched_term with
                  | Var proof_name ->
                  begin
                    match Coq_erasure.classify (List.rev vars) indname params with
                    | Coq_erasure.CEmpty ->
                       (* An elimination from an empty proposition is unreachable.
                          Its lifted denotation is intentionally unconstrained. *)
                       return ()
                    | Coq_erasure.CPropSingleton ->
                       begin
                         match collapse_prop_singleton vars indname constrs params params_num branches with
                         | None ->
                            (* The WF-recursion ablation deliberately omits this
                               equation; it never substitutes an opaque value. *)
                            return ()
                         | Some body2 ->
                            record_case_dependency ();
                            (* Singleton erasure: the proof match computes as
                               its unique branch after proof arguments are erased.
                               The source proposition is load-bearing for indexed
                               singletons such as equality and [eq_true]. *)
                            let premise =
                              try
                                combine_premises premise (Some (List.assoc proof_name vars))
                              with Not_found ->
                                internal_error "singleton proof scrutinee is absent from the normalized context"
                            in
                            compile_case ?premise lhs vars axname body2
                       end
                    | Coq_erasure.CRegular | Coq_erasure.CSubset _ | Coq_erasure.CEnum _ ->
                       raise (Hammer_errors.HammerError
                                ("internal translation error: informative elimination from a non-singleton proposition " ^
                                 indname ^ " with return predicate " ^
                                 string_of_coqterm return_type))
                  end
                  | _ ->
                     record_case_dependency ();
                     case_aux_value vars indname matched_term return_type raw_return_type
                       params_num branches indty
                     >>= fun rhs ->
                     emit_equation ?premise (axname ^ "$link") vars lhs rhs false
                end
              else begin
                record_case_dependency ();
                let collapse_subset_case carrier_idx =
                  collapse_subset_case ~matched_term ~vars ~constrs ~branches
                    ~params ~params_num carrier_idx
                in
                let regular_case () =
                  match matched_term with
                  | Var scrutinee when var_occurs scrutinee lhs ->
                     let scrutinee_ty =
                       try List.assoc scrutinee vars with Not_found ->
                         internal_error "case scrutinee is absent from the normalized context"
                     in
                     let (_, actual_tyargs) = flatten_app scrutinee_ty in
                     let rec split_scrutinee acc = function
                       | [] -> internal_error "case scrutinee is absent from the normalized context"
                       | (name, _) :: vars_after when name = scrutinee ->
                          (List.rev acc, vars_after)
                       | var :: vars2 -> split_scrutinee (var :: acc) vars2
                     in
                     let vars_before, vars_after = split_scrutinee [] vars in
                     let prepare_branch cname =
                       let (n, branch) = get_branch cname constrs branches
                       in
                       let (targs, args) = constructor_args params params_num cname
                       in
                       if List.length args <> n then
                         internal_error
                           ("constructor telescope arity mismatch for " ^ cname ^
                            " in " ^ indname ^ ": branch binds " ^ string_of_int n ^
                            " but normalized constructor has " ^
                            string_of_int (List.length args))
                       else
                         let args0 = args in
                         let args = refresh_case_args vars args in
                         let refresh_terms tms =
                           List.map
                             (fun tm ->
                                List.fold_left2
                                  (fun tm (name, _) (name2, _) ->
                                     if name = name2 then tm else substvar name (Var name2) tm)
                                  tm args0 args)
                             tms
                         in
                         let targs = refresh_terms targs in
                         let bound_names = List.map fst (vars @ args) in
                         if not (List.for_all (term_fvars_subset bound_names) (actual_tyargs @ targs)) then
                           internal_error "case index arguments escape the normalized scope"
                         else
                         let index_premise =
                           constructor_index_premise indname indty params params_num
                             actual_tyargs targs
                         in
                         let premise = combine_premises premise index_premise in
                         let pattern = mk_long_app (Const(cname)) (params @ mk_vars args)
                         in
                         let branch_body = simpl (mk_long_app branch (mk_vars args))
                         in
                         let branch_body = subst_proof_args (List.rev vars) args branch_body
                         in
                         let subst_scrutinee_type (name, ty) = (name, substvar scrutinee pattern ty) in
                         let lhs2 = substvar scrutinee pattern lhs
                         and body2 = substvar scrutinee pattern branch_body
                         and axname2 = axname ^ "$" ^ short_name cname
                         and vars2 = vars_before @ args @ List.map subst_scrutinee_type vars_after
                         in
                         (premise, lhs2, vars2, axname2, body2)
                     in
                     (* Validate every constructor telescope and index scope
                        before the first split equation is emitted. *)
                     let prepared = List.map prepare_branch constrs in
                     List.fold_left
                       (fun acc (premise, lhs2, vars2, axname2, body2) ->
                          acc >> compile_case ?premise lhs2 vars2 axname2 body2)
                       (return ()) prepared
                  | _ ->
                     case_aux_value vars indname matched_term return_type raw_return_type
                       params_num branches indty
                     >>= fun rhs ->
                     emit_equation ?premise (axname ^ "$link") vars lhs rhs
                       (Coq_typing.check_prop (List.rev vars) case_body)
                in
                if opt_refinement_types then
                  match Coq_erasure.classify (List.rev vars) indname params with
                  | Coq_erasure.CSubset { carrier_idx; _ } ->
                     compile_case ?premise lhs vars axname (collapse_subset_case carrier_idx)
                  | Coq_erasure.CEnum _ ->
                     (* Enum scrutinees (e.g. sumbool) need no special collapse;
                        split-form validity applies to the erased constructor tags,
                        while enum guards reuse the existing inversion scheme. *)
                     regular_case ()
                  | Coq_erasure.CEmpty | Coq_erasure.CPropSingleton | Coq_erasure.CRegular ->
                     regular_case ()
                else
                  regular_case ()
              end
           | _ -> internal_error "case scrutinee declaration is not inductive"
         end
      | Lam(vname, vtype, body2) ->
         if Coq_typing.check_prop (List.rev vars) vtype then
           compile_case ?premise lhs vars axname (subst_proof vname vtype body2)
         else
           compile_case ?premise (App(lhs, Var(vname))) (vars @ [ (vname, vtype) ]) axname body2
      | Fix(_) as fix_body ->
         (* The right-hand side is the ordinary value translation of the inner
            fix, reusing the existing fix_lifting machinery. *)
         emit_leaf ?premise axname vars lhs fix_body
      | body2 ->
         emit_leaf ?premise axname vars lhs body2
    in
    match tm with
    | Cast(Const("$Proof"), _) | Const("$Proof") ->
       return (Const("$Proof"))
    | Case(indname, _, _, _, _, _) ->
       let fname =
         if name0 = "" then "$_case_" ^ indname ^ "$" ^ unique_id () else name0
       in
       let axname = if name0 = "" then fname else axname0 in
       convert (List.rev fvars) (mk_long_app (Const(fname)) (mk_vars fvars))
       >>= fun replacement ->
       compile_case (mk_long_app replacement (mk_vars lvars)) (fvars @ lvars) axname tm >>
       return replacement
    | _ ->
       raise (Hammer_errors.HammerError "internal translation error: expected case expression")

(*****************************************************************************************)
(* Convert definitions to axioms *)

(* Invariant: there is no variable covering in `tm'; the variables
   from ctx are pairwise distinct and they do not occur bound in `tm' *)
and convert ctx tm =
  debug 3 (fun () -> print_header "convert" tm ctx);
  match tm with
  | Quant(op, (name, ty, body)) ->
     assert (ty <> type_any);
     let mk = if op = "!" then mk_impl else mk_and
     in
     if Coq_typing.check_prop ctx ty then
       (prop_to_formula ctx ty) >>= fun x1 ->
       (prop_to_formula ctx (subst_proof name ty body)) >>= fun x2 ->
       return (mk x1 x2)
     else
       (make_guard ctx ty (Var(name))) >>= fun x1 ->
       (prop_to_formula ((name, ty) :: ctx) body) >>= fun x2 ->
       return (Quant(op, (name, type_any, mk x1 x2)))
  | Equal(x, y) ->
     convert_term ctx x >>= fun x1 ->
     convert_term ctx y >>= fun x2 ->
     return (Equal(x1, x2))
  | App(App(Const(c), x), y) when is_bin_logop c ->
      prop_to_formula ctx x >>= fun x2 ->
      prop_to_formula ctx y >>= fun y2 ->
      assert (x2 <> Const("$Proof"));
      assert (y2 <> Const("$Proof"));
      return (App(App(Const(c), x2), y2))
  | App(Const("~"), x) ->
      prop_to_formula ctx x >>= fun x2 ->
      assert (x2 <> Const("$Proof"));
      return (App(Const("~"), x2))
  | App(App(Const("$HasType"), x), y) ->
      convert ctx x >>= fun x2 ->
      make_guard ctx y x2
  | App(_) ->
      let convert_extra_app base extras =
        let rec hlp acc = function
          | [] -> return acc
          | arg :: args ->
             if acc = Const("$Proof") then
               return (Const("$Proof"))
             else
               convert_term ctx arg >>= fun arg2 ->
               if arg2 = Const("$Proof") then
                 hlp acc args
               else
                 hlp (App(acc, arg2)) args
        in
        hlp base extras
      in
      let subset_constructor_spine () =
        let align_actuals cargs args =
          let is_prop_formal formals actuals ty =
            try Coq_typing.check_prop ctx (simpl (subst_params (List.rev formals) (List.rev actuals) ty))
            with _ -> false
          in
          let required_nonprop_count formals actuals rest_formals =
            let rec count formals actuals acc = function
              | [] -> acc
              | (formal_name, formal_ty) :: formals2 ->
                 if is_prop_formal formals actuals formal_ty then
                   count ((formal_name, formal_ty) :: formals) (Const("$Proof") :: actuals) acc formals2
                 else
                   count ((formal_name, formal_ty) :: formals) (Var formal_name :: actuals) (acc + 1) formals2
            in
            count formals actuals 0 rest_formals
          in
          let rec hlp formals actuals rest_formals rest_args =
            match rest_formals with
            | [] -> (List.rev actuals, rest_args)
            | (formal_name, formal_ty) :: formals2 ->
               let formal_ty = simpl (subst_params (List.rev formals) (List.rev actuals) formal_ty) in
               let formal_is_prop =
                 try Coq_typing.check_prop ctx formal_ty with _ -> false
               in
               begin match rest_args with
               | arg :: args2 ->
                  if formal_is_prop &&
                       not (proof_like_after_erasure ctx arg) &&
                       List.length rest_args <=
                         required_nonprop_count
                           ((formal_name, formal_ty) :: formals)
                           (Const("$Proof") :: actuals)
                           formals2
                  then
                    (* [type_to_guard] prunes proof binders from the term spine.
                       Keep a placeholder in the aligned spine so later
                       informative arguments retain their constructor positions
                       before subset constructors are erased to their carrier. *)
                    hlp ((formal_name, formal_ty) :: formals) (Const("$Proof") :: actuals) formals2 rest_args
                  else
                    hlp ((formal_name, formal_ty) :: formals) (arg :: actuals) formals2 args2
               | [] ->
                  if formal_is_prop then
                    hlp ((formal_name, formal_ty) :: formals) (Const("$Proof") :: actuals) formals2 []
                  else
                    (List.rev actuals, [])
               end
          in
          hlp [] [] cargs args
        in
        try
          match flatten_app tm with
          | Const cname, args ->
             let (target, _, cargs) = Coq_typing.destruct_type_app (coqdef_type (Defhash.find cname)) in
             begin
               match target with
               | Const indname ->
                  begin
                    match Defhash.find indname with
                    | (_, IndType(_, constrs, params_num), _, _) when List.mem cname constrs && List.length args >= params_num ->
                       let params = Hhlib.take params_num args in
                       begin
                         match Coq_erasure.classify ctx indname params with
                         | Coq_erasure.CSubset { carrier_idx; _ } ->
                            let actuals, extras = align_actuals cargs args in
                            let carrier_pos = params_num + carrier_idx in
                            if List.length actuals > carrier_pos then
                              Some (`Carrier (List.nth actuals carrier_pos, extras))
                            else
                              Some (`UnderApplied (cname, args, cargs))
                         | _ -> None
                       end
                    | _ -> None
                  end
               | _ -> None
             end
          | _ -> None
        with _ -> None
      in
      let eta_expand_subset_constructor cname args cargs =
        let provided = List.length args in
        let missing = Hhlib.drop provided cargs in
        let rec build actuals = function
          | [] -> mk_long_app (Const cname) actuals
          | (formal_name, formal_ty) :: rest ->
             let var_name = refresh_varname formal_name in
             let previous_formals = Hhlib.take (List.length actuals) cargs in
             let var_ty = simpl (subst_params previous_formals actuals formal_ty) in
             Lam(var_name, var_ty, build (actuals @ [Var var_name]) rest)
        in
        build args missing
      in
      begin match if opt_erasure_guards then None else erase_transport_head tm with
      | Some tm2 -> convert ctx tm2
      | None ->
      begin match erase_false_rect_type_arg ctx tm with
      | Some tm2 -> convert ctx tm2
      | None ->
      begin
      match if opt_refinement_types then subset_constructor_spine () else None with
      | Some (`Carrier (carrier_arg, extras)) ->
         (* Refinement occurrence collapse: subset constructors erase to
            their carrier at each occurrence.  Trailing applications are
            preserved on the translated carrier. *)
         convert ctx carrier_arg >>= fun carrier ->
         convert_extra_app carrier extras
      | Some (`UnderApplied (cname, args, cargs)) ->
         (* Under-applied subset constructors are eta-expanded and then lifted;
            the lifted symbol's equation may look like a bridge [F x = x],
            which is legitimate only because it is generated at this partial
            application occurrence by the same refinement-collapse rule. *)
         remove_lambda ctx (eta_expand_subset_constructor cname args cargs)
      | None ->
      begin
      match tm with
      | App(x, y) ->
      convert ctx x >>= fun x2 ->
      if x2 = Const("$Proof") then
        return (Const("$Proof"))
      else
        convert_term ctx y >>= fun y2 ->
        if y2 = Const("$Proof") then
          return x2
        else
          return (App(x2, y2))
      | _ -> failwith "convert: app"
      end
      end
      end
      end
  | Lam(_) ->
      remove_lambda ctx tm
  | Case(_) ->
      remove_case ctx tm
  | Cast(Const("$Proof"), _) ->
      return (Const("$Proof"))
  | Cast(_) ->
      remove_cast ctx tm
  | Fix(_) ->
      remove_fix ctx tm
  | Let(_) ->
      remove_let ctx tm
  | Prod(_) ->
      if Coq_typing.check_prop ctx tm then
        prop_to_formula ctx tm
      else
        remove_type ctx tm
  | SortProp ->
      return (Const("Prop"))
  | SortSet ->
      return (Const("Set"))
  | SortType ->
      return (Const("Type"))
  | Var(name) ->
      if Coq_typing.check_proof_var ctx name then
        return (Const("$Proof"))
      else
        return (Var(name))
  | Const(_) ->
      return tm
  | IndType(_) ->
      failwith "convert"

and convert_term ctx tm =
  debug 3 (fun () -> print_header "convert_term" tm ctx);
  if proof_like_after_erasure ctx tm then
    return (Const("$Proof"))
  else
  let should_lift =
    match tm with
    | Var(_) | Const(_) -> false
    | App(App(Const(c), _), _) when is_bin_logop c -> true
    | App(Const("~"), _) -> true
    | App(_) -> false
    | _ -> Coq_typing.check_prop ctx tm
  in
  if should_lift then
    let name = "$_prop_" ^ unique_id ()
    in
    let fvars = get_fvars ctx tm
    in
    convert ctx (mk_long_app (Const(name)) (mk_vars fvars)) >>= fun tm2 ->
    close fvars
      begin fun ctx ->
        convert ctx tm >>= fun r ->
        return (mk_equiv tm2 r)
      end >>= fun r ->
    add_axiom (mk_axiom name r) >>
    return tm2
  else
    convert ctx tm

and prop_to_formula ctx tm =
  debug 3 (fun () -> print_header "prop_to_formula" tm ctx);
  match tm with
  | Prod(vname, ty1, ty2) ->
     if Coq_typing.check_prop ctx ty1 then
       prop_to_formula ctx ty1 >>= fun tm1 ->
       prop_to_formula ctx (subst_proof vname ty1 ty2) >>= fun tm2 ->
       return (mk_impl tm1 tm2)
     else
       make_guard ctx ty1 (Var(vname)) >>= fun tm1 ->
       prop_to_formula ((vname, ty1) :: ctx) ty2 >>= fun tm2 ->
       return (mk_forall vname type_any (mk_impl tm1 tm2))
  | _ ->
    convert ctx tm

(* `x' does not get converted *)
and guard_leaf ctx ty x =
  debug 3 (fun () -> print_header_nonl "guard_leaf" ty ctx; print_coqterm x; print_newline ());
  let fallback () =
    convert ctx ty >>= fun ty1 ->
    return (mk_hastype x ty1)
  in
  let rec formulas ctx = function
    | [] -> return []
    | prop_ty :: prop_tys ->
       prop_to_formula ctx prop_ty >>= fun f ->
       formulas ctx prop_tys >>= fun fs ->
       return (f :: fs)
  in
  let conjoin = function
    | [] -> Const("$True")
    | fs -> join_right mk_and fs
  in
  if not opt_refinement_types then
    fallback ()
  else
    let ty_nf = simpl (Coq_typing.reify (Coq_typing.eval ty))
    in
    try
      match flatten_app ty_nf with
      | Const indname, args ->
         begin match Defhash.find indname with
         | (_, IndType(_, constrs, params_num), _, _) ->
            let params = Hhlib.take params_num args
            in
            begin match Coq_erasure.classify ctx indname params with
            | Coq_erasure.CSubset { carrier_idx; carrier_name; prop_args } ->
               begin match constrs with
               | [cname] ->
                  let (_, _, cargs) = Coq_typing.destruct_type_app (coqdef_type (Defhash.find cname))
                  in
                  let cparams = Hhlib.take params_num cargs
                  in
                  let cargs =
                    List.map
                      (fun (name, ty) -> (name, subst_params cparams params ty))
                      (Hhlib.drop params_num cargs)
                  in
                  let (_, carrier_ty) = List.nth cargs carrier_idx
                  in
                  (* A refinement guard is expanded at the occurrence itself:
                     the carrier guard is conjoined with the translated payload.
                     The same leaf is used in hypotheses and conclusions.
                     Substitute the erased carrier before translating the payload
                     so beta-redexes in predicate parameters disappear shallowly. *)
                  let carrier_ty = simpl carrier_ty in
                  let payload_ctx =
                    match x with
                    | Var name when not (List.mem_assoc name ctx) -> (name, carrier_ty) :: ctx
                    | _ -> ctx
                  in
                  convert payload_ctx x >>= fun carrier ->
                  make_guard ctx carrier_ty carrier >>= fun carrier_guard ->
                  let payload_ctx =
                    match carrier with
                    | Var name when not (List.mem_assoc name ctx) -> (name, carrier_ty) :: ctx
                    | _ -> payload_ctx
                  in
                  formulas payload_ctx
                    (List.map
                       (fun (_, prop_ty) -> simpl (substvar carrier_name carrier prop_ty))
                       prop_args) >>= fun payloads ->
                  return (conjoin (carrier_guard :: payloads))
               | _ -> fallback ()
               end
            | Coq_erasure.CEnum ctors ->
               let one_ctor (cname, payloads) =
                 convert ctx (mk_long_app (Const cname) params) >>= fun ctor ->
                 formulas ctx payloads >>= fun payloads ->
                 return (mk_and (mk_eq x ctor) (conjoin payloads))
               in
               let rec disjs = function
                 | [] -> return []
                 | ctor :: ctors ->
                    one_ctor ctor >>= fun f ->
                    disjs ctors >>= fun fs ->
                    return (f :: fs)
               in
               (* A CEnum guard reuses the existing inversion scheme as a
                  self-contained disjunction of constructor tags and their
                  propositional payload formulas; non-guard occurrences still use
                  the ordinary inversion axiom. *)
               disjs ctors >>= fun fs ->
               return (match fs with [] -> Const("$False") | _ -> join_right mk_or fs)
            | Coq_erasure.CEmpty ->
               (* The guard for an empty classified type is false, matching the
                  zero-constructor inversion scheme. *)
               return (Const("$False"))
            | Coq_erasure.CPropSingleton | Coq_erasure.CRegular ->
               fallback ()
            end
         | _ -> fallback ()
         end
      | _ -> fallback ()
    with _ ->
      fallback ()

(* `x' does not get converted *)
and make_guard ctx ty x =
  debug 3 (fun () -> print_header_nonl "make_guard" ty ctx; print_coqterm x; print_newline ());
  match ty with
  | Prod(_) ->
     if opt_type_lifting then
       remove_type ctx ty >>= fun ty1 ->
       return (mk_hastype x ty1)
     else
       (* refresh_bvars is necessary here to correctly translate
          e.g. Prod(x, Prod(x, ty1, ty2), ty3) *)
       type_to_guard ctx (refresh_bvars ty) x
  | _ ->
     guard_leaf ctx ty x

(* `x' does not get converted *)
and type_to_guard ctx ty x =
  debug 3 (fun () -> print_header_nonl "type_to_guard" ty ctx; print_coqterm x; print_newline ());
  match ty with
  | Prod(vname, ty1, ty2) ->
     if Coq_typing.check_prop ctx ty1 then
       prop_to_formula ctx ty1 >>= fun tm1 ->
       (* Prop domains use pruned arity: proof arguments are formulas, not term
          arguments, so [x] is deliberately left unapplied across the implication,
          matching the erased program occurrence. *)
       type_to_guard ctx (subst_proof vname ty1 ty2) x >>= fun tm2 ->
       return (mk_impl tm1 tm2)
     else
       make_guard ctx ty1 (Var(vname)) >>= fun tm1 ->
       type_to_guard ((vname, ty1) :: ctx) ty2 (App(x, (Var(vname)))) >>= fun tm2 ->
       return (mk_forall vname type_any (mk_impl tm1 tm2))
  | _ ->
     guard_leaf ctx ty x

and make_fol_forall ctx vars tm =
  let rec hlp ctx vars tm =
    match vars with
    | (name, ty) :: vars2 ->
      if Coq_typing.check_prop ctx ty then
        hlp ((name, ty) :: ctx) vars2 (subst_proof name ty tm)
      else
        hlp ((name, ty) :: ctx) vars2 tm >>= fun r ->
        return (mk_forall name type_any r)
    | [] ->
      prop_to_formula ctx tm
  in
  hlp ctx vars tm

and make_fol_forall_keep_prop_premises ctx vars tm =
  let rec hlp ctx vars tm =
    match vars with
    | (name, ty) :: vars2 ->
       if Coq_typing.check_prop ctx ty then
         prop_to_formula ctx ty >>= fun premise ->
         hlp ((name, ty) :: ctx) vars2 (subst_proof name ty tm) >>= fun r ->
         return (mk_impl premise r)
       else
         hlp ((name, ty) :: ctx) vars2 tm >>= fun r ->
         return (mk_forall name type_any r)
    | [] ->
       prop_to_formula ctx tm
  in
  hlp ctx vars tm

and make_guarded_forall ctx vars cont =
  let rec hlp ctx vars =
    match vars with
    | (name, ty) :: vars2 ->
       begin
         make_guard ctx ty (Var(name)) >>= fun guard ->
         hlp ((name, ty) :: ctx) vars2 >>= fun r ->
         return (mk_forall name type_any (mk_impl guard r))
       end
    | [] ->
       cont ctx
  in
  hlp ctx vars

and close vars cont =
  if !opt_closure_guards then
    make_guarded_forall [] vars cont
  else
    let rec hlp ctx vars =
      match vars with
      | (name, ty) :: vars2 ->
         begin
           hlp ((name, ty) :: ctx) vars2 >>= fun r ->
           return (mk_forall name type_any r)
         end
      | [] ->
         cont ctx
    in
    hlp [] vars

and remove_lambda ctx tm =
  debug 3 (fun () -> print_header "remove_lambda" tm ctx);
  with_lift_dependencies (fun () ->
    Hashing.find_or_insert coqterm_hash ctx tm
      begin fun cctx ctm ->
        let name = "$_lam_" ^ unique_id ()
        in
        lambda_lifting [] name name (ctx_to_vars cctx) [] ctm
      end)

and remove_case ctx tm =
  debug 3 (fun () -> print_header "remove_case" tm ctx);
  with_lift_dependencies (fun () ->
    Hashing.find_or_insert_keyed (case_occurrence_key ctx tm) coqterm_hash ctx tm
      begin fun cctx ctm ->
        case_lifting [] "" "" (ctx_to_vars cctx) [] ctm
      end)

and remove_cast ctx tm =
  debug 3 (fun () -> print_header "remove_cast" tm ctx);
  match tm with
  | Cast(trm, ty) ->
      let fvars = get_fvars ctx tm
      and fname = "$_cast_" ^ unique_id ()
      in
      convert ctx (mk_long_app (Const(fname)) (mk_vars fvars)) >>= fun tm2 ->
      let ty2 = mk_long_prod fvars ty
      in
      let srt = if Coq_typing.check_prop [] ty2 then SortProp else SortType
      in
      if srt <> SortProp then
        begin
          let def = mk_def fname (mk_long_lam fvars trm) ty2 srt
          in
          add_def_eq_axiom def >>
          return tm2
        end
      else
        return (Const("$Proof"))
  | _ ->
      failwith "remove_cast"

and remove_fix ctx tm =
  debug 3 (fun () -> print_header "remove_fix" tm ctx);
  with_lift_dependencies (fun () ->
    Hashing.find_or_insert coqterm_hash ctx tm
      begin fun cctx ctm ->
        fix_lifting [] "" "" (ctx_to_vars cctx) [] ctm
      end)

and remove_let ctx tm =
  debug 3 (fun () -> print_header "remove_let" tm ctx);
  match tm with
  | Let(value, (name, ty, body)) ->
      let name2 = "$_let_" ^ name ^ "_" ^ unique_id ()
      and fvars = get_fvars ctx (App(value, ty))
      in
      let ty2 = mk_long_prod fvars ty
      and val2 = mk_long_app (Const(name2)) (mk_vars fvars)
      in
      let srt = if Coq_typing.check_prop [] ty2 then SortProp else SortType
      in
      let def = mk_def name2 (mk_long_lam fvars value) ty2 srt
      in
      Defhash.add def;
      begin
        if srt <> SortProp then
          add_def_eq_axiom def
        else
          return ()
      end >>
      convert ctx (simple_subst name val2 body)
  | _ ->
      failwith "remove_let"

and remove_type ctx ty =
  debug 3 (fun () -> print_header "remove_type" ty ctx);
  with_lift_dependencies (fun () ->
    Hashing.find_or_insert coqterm_hash ctx ty
      begin fun cctx cty ->
        let name = "$_type_" ^ unique_id ()
        and vars = ctx_to_vars cctx
        in
        add_def_eq_type_axiom name name vars cty >>
        convert cctx (mk_long_app (Const(name)) (mk_vars vars))
      end)

and add_def_eq_type_axiom axname name fvars ty =
  debug 2 (fun () -> print_header "add_def_eq_type_axiom" ty fvars);
  let vname = "var_" ^ unique_id ()
  in
  close fvars
    begin fun ctx ->
      convert ctx (mk_long_app (Const(name)) (mk_vars fvars)) >>= fun tp ->
      type_to_guard ctx ty (Var(vname)) >>= fun guard ->
      return (mk_forall vname type_any
                (mk_equiv (mk_hastype (Var(vname)) tp) guard))
    end >>= fun r ->
  add_axiom (mk_axiom axname r)

and add_typing_axiom name ty =
  debug 2 (fun () -> print_endline ("add_typing_axiom: " ^ name));
  if not (is_logop name) && name <> "$True" && name <> "$False" && ty <> type_any then
    begin
      if opt_refinement_types && Coq_erasure.has_erasable_content [] ty then
        begin
          (* When the type contains erasure-relevant refinements/enums, emit the
             applied forall-form directly through type_to_guard.  This bypasses
             type lifting/optimization so payloads are expanded per occurrence. *)
          type_to_guard [] (refresh_bvars ty) (Const(name)) >>= fun guard ->
          add_axiom (mk_axiom ("$_typeof_" ^ name) guard)
        end
      else if opt_omit_prop_typing_axioms && Coq_typing.check_type_target_is_prop ty then
        return ()
      else if opt_type_optimization &&
          (Coq_typing.check_type_target_is_type ty || Coq_typing.check_type_target_is_prop ty) then
        begin
          let fix_ax ax =
            let xvar = refresh_varname "X"
            in
            let rec hlp tm =
              match tm with
              | Quant("!", (vname, _, body)) ->
                Quant("!", (vname, type_any, hlp body))
              | App(App(Const("=>"), x), y) ->
                App(App(Const("=>"), x), hlp y)
              | Equal(x, y) ->
                if opt_hastype then
                  mk_equiv
                    (App(App(Const "$HasType", x), Var(xvar)))
                    (App(App(Const "$HasType", y), Var(xvar)))
                else
                  mk_equiv (App(x, Var(xvar))) (App(y, Var(xvar)))
              | _ -> failwith "add_typing_axiom: fix_ax"
            in
            mk_forall xvar type_any (hlp ax)
          in
          let name2 = "$_type_" ^ name ^ "_" ^ unique_id ()
          and args = Coq_typing.get_type_args ty
          in
          (* TODO: fix proof arguments in ax *)
          let ys = mk_vars args
          in
          let ax =
            mk_long_forall args
              (mk_eq
                 (mk_long_app (Const(name2)) ys)
                 (mk_long_app (Const(name)) ys))
          in
          make_guard [] ty (Const(name2)) >>= fun guard ->
          add_axiom (mk_axiom ("$_tydef_" ^ name2) (fix_ax ax)) >>
          add_axiom (mk_axiom ("$_typeof_" ^ name) guard)
        end
      else
        begin
          make_guard [] ty (Const(name)) >>= fun guard ->
          add_axiom (mk_axiom ("$_typeof_" ^ name) guard)
        end
    end
  else
    return ()

and add_def_eq_axiom (name, value, ty, srt) =
  debug 2 (fun () -> print_endline ("add_def_eq_axiom: " ^ name));
  let axname = "$_def_" ^ name
  in
  let emit_transport_definition () =
    try
      let vars = Coq_typing.get_type_args ty in
      match Hhlib.drop 3 vars with
      | (proof_name, _) :: _ ->
         (* Transport erasure for the standard transport family itself maps
            the transport to its carried proof/value.  Reconstruction-sensitive
            cases are the same as user constants whose bodies are eq_rect/eq_rec
            or eq_ind wrappers. *)
         let premise = transport_erasure_premise (mk_long_app (Const name) (mk_vars vars)) in
         emit_definition_equation ?premise axname name [] vars (Var(proof_name)) >>
         return ()
      | [] -> return ()
    with _ ->
      return ()
  in
  if is_transport_constant name then
    emit_transport_definition ()
  else
  match value with
  | Lam(_) ->
     lambda_lifting [] axname name [] [] value >>
     return ()
  | Fix(_) ->
     fix_lifting [] axname name [] [] value >>
     return ()
  | Case(_) ->
     case_lifting [] axname name [] [] value >>= fun replacement ->
     begin
       match replacement with
       | Const(c) when c = name ->
          return ()
       | _ ->
          (* Anonymous occurrences are lifted to a dependency-applied symbol.
             Named definitions normally return [name] after emitting their
             equations; this bridge is retained for the remaining value forms. *)
          begin
            match ty with
            | SortProp ->
               prop_to_formula [] replacement >>= fun r ->
               add_axiom (mk_axiom axname (mk_equiv (Const(name)) r))
            | SortType | SortSet ->
               add_def_eq_type_axiom axname name [] replacement
            | _ ->
               convert [] replacement >>= fun r ->
               add_axiom (mk_axiom axname (mk_eq (Const(name)) r))
          end
     end
  | Const(c) when c = name ->
     return ()
  | _ ->
      begin
        match ty with
        | SortProp ->
           begin
             prop_to_formula [] value >>= fun r ->
             add_axiom (mk_axiom axname (mk_equiv (Const(name)) r))
           end
        | SortType | SortSet ->
           add_def_eq_type_axiom axname name [] value
        | _ ->
           begin
             convert [] value >>= fun r ->
             add_axiom (mk_axiom axname (mk_eq (Const(name)) r))
           end
      end

and skip_refinement_decl_axioms indname =
  opt_refinement_types && opt_refinement_decl_skips &&
  match Coq_erasure.classify_decl indname with
  | Some (Coq_erasure.CSubset _) -> true
  | _ -> false

and add_injection_axioms params_num constr =
  debug 2 (fun () -> print_endline ("add_injection_axioms: " ^ constr));
  let ty = coqdef_type (Defhash.find constr)
  in
  (* Status quo structural axiom: constructor injectivity is pre-existing.  For
     proof fields, proof irrelevance permits replacing the old generated
     $Proof = $Proof conjuncts by a neutral tautology; the consistency canaries
     are intentionally ATP-level tests, and preserving this harmless clutter
     keeps their search profile stable while removing the misleading proof
     equality from generated axioms. *)
  let proof_irrel_marker =
    mk_eq (Const("Hammer.ProofIrrel")) (Const("Hammer.ProofIrrel"))
  in
  let add_arg_eq is_param ctx ty name1 name2 conjs =
    if is_param then
      (* Constructor parameters are fixed by a homogeneous CIC equality; they
         are not injective payloads.  More importantly, a parameter-dependent
         declaration may collapse some constructor instances to their carrier,
         so inferring parameter equality from the erased FOL premise would be
         unsound. *)
      conjs
    else if Coq_typing.check_prop ctx ty then
      proof_irrel_marker :: conjs
    else
      (mk_eq (Var(name1)) (Var(name2))) :: conjs
  in
  let conjoin = function
    | [] -> Const("$True")
    | conjs -> join_left mk_and conjs
  in
  let rec hlp arg_index ctx ty1 ty2 args1 args2 conjs =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), Prod(name2, lty2, value2) ->
      let lname1 = refresh_varname name1
      and lname2 = refresh_varname name2
      in
      let lvalue1 = simple_subst name1 (Var(lname1)) value1
      and lvalue2 = simple_subst name2 (Var(lname2)) value2
      in
      let conjs2 =
        add_arg_eq (arg_index < params_num) ctx lty1 lname1 lname2 conjs
      in
      mk_forall lname1 lty1
        (mk_forall lname2 lty2
           (hlp (arg_index + 1) ((lname1, lty1) :: (lname2, lty2) :: ctx)
              lvalue1 lvalue2 (Var(lname1) :: args1) (Var(lname2) :: args2) conjs2))
    | _ ->
      mk_impl
        (mk_eq (mk_long_app (Const(constr)) (List.rev args1))
           (mk_long_app (Const(constr)) (List.rev args2)))
        (conjoin conjs)
  in
  let rec hlp2 arg_index ctx ty1 ty2 args1 args2 conjs =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), Prod(name2, lty2, value2) ->
      let lname1 = refresh_varname name1
      and lname2 = refresh_varname name2
      in
      let lvalue1 = simple_subst name1 (Var(lname1)) value1
      and lvalue2 = simple_subst name2 (Var(lname2)) value2
      in
      let conjs2 =
        add_arg_eq (arg_index < params_num) ctx lty1 lname1 lname2 conjs
      in
      (hlp2 (arg_index + 1) ((lname1, lty1) :: (lname2, lty2) :: ctx)
         lvalue1 lvalue2 (Var(lname1) :: args1) (Var(lname2) :: args2) conjs2)
      >>= fun r ->
      return (mk_forall lname1 type_any (mk_forall lname2 type_any r))
    | _ ->
      prop_to_formula ctx
        (mk_impl
           (mk_eq (mk_long_app (Const(constr)) (List.rev args1))
              (mk_long_app (Const(constr)) (List.rev args2)))
           (conjoin conjs))
  in
  match ty with
  | Prod(_) ->
     begin
       if !opt_closure_guards || opt_injectivity_guards then
         prop_to_formula [] (hlp 0 [] ty ty [] [] [])
       else
         hlp2 0 [] ty ty [] [] []
     end >>= fun ax ->
     add_axiom (mk_axiom ("$_inj_" ^ constr) ax)
  | _ ->
     return ()

and add_discrim_axioms constr1 constr2 =
  debug 2 (fun () -> print_endline ("add_discrim_axioms: " ^ constr1 ^ ", " ^ constr2));
  let ty1 = coqdef_type (Defhash.find constr1)
  and ty2 = coqdef_type (Defhash.find constr2)
  in
  let rec hlp ty1 ty2 args1 args2 =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), _ ->
      let lname1 = refresh_varname name1
      in
      let lvalue1 = simple_subst name1 (Var(lname1)) value1
      in
      mk_forall lname1 lty1 (hlp lvalue1 ty2 (Var(lname1) :: args1) args2)
    | _, Prod(name2, lty2, value2) ->
      let lname2 = refresh_varname name2
      in
      let lvalue2 = simple_subst name2 (Var(lname2)) value2
      in
      mk_forall lname2 lty2 (hlp ty1 lvalue2 args1 (Var(lname2) :: args2))
    | _ ->
      mk_not
        (mk_eq
           (mk_long_app (Const(constr1)) (List.rev args1))
           (mk_long_app (Const(constr2)) (List.rev args2)))
  in
  let rec hlp2 ctx ty1 ty2 args1 args2 =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), _ ->
       let lname1 = refresh_varname name1
       in
       let lvalue1 = simple_subst name1 (Var(lname1)) value1
       in
       (hlp2 ((lname1, lty1) :: ctx) lvalue1 ty2
          (Var(lname1) :: args1) args2) >>= fun r ->
       return (mk_forall lname1 type_any r)
    | _, Prod(name2, lty2, value2) ->
       let lname2 = refresh_varname name2
       in
       let lvalue2 = simple_subst name2 (Var(lname2)) value2
       in
       (hlp2 ((lname2, lty2) :: ctx) ty1 lvalue2
          args1 (Var(lname2) :: args2)) >>= fun r ->
       return (mk_forall lname2 type_any r)
    | _ ->
       prop_to_formula ctx
         (mk_not
            (mk_eq
               (mk_long_app (Const(constr1)) (List.rev args1))
               (mk_long_app (Const(constr2)) (List.rev args2))))
  in
  begin
    if !opt_closure_guards || opt_discrimination_guards then
      prop_to_formula [] (hlp ty1 ty2 [] [])
    else
      hlp2 [] ty1 ty2 [] []
  end >>= fun ax ->
  add_axiom (mk_axiom ("$_discrim_" ^ constr1 ^ "$" ^ constr2) ax)

and add_inversion_axioms is_prop indname constrs =
  debug 2 (fun () -> print_endline ("add_inversion_axioms: " ^ indname));
  let df = Defhash.find indname
  in
  match df with
  | (_, IndType(_, constrs, params_num), indtype, indsort) ->
     let args = Coq_typing.get_type_args indtype
     and vname = "X" ^ unique_id ()
     in
     assert (params_num <= List.length args);
     let vty = mk_long_app (Const(indname)) (mk_vars args)
     in
     let lvars = args @ [(vname, vty)]
     in
     let params = mk_vars (Hhlib.take params_num args)
     in
     if is_prop then
       add_inversion_axioms0
         (fun _ constrs _ _ -> mk_prop_inversion params indname args constrs) indname
         ("$_inversion_" ^ indname) [] lvars constrs (Var(vname)) (fun _ _ _ eqt -> eqt)
     else
       add_inversion_axioms0 (mk_inversion params)
         indname ("$_inversion_" ^ indname)
         [] lvars constrs (Var(vname))
         begin fun _ targs2 _ eqt ->
         if opt_precise_inversion then
           mk_inversion_conjs params_num args targs2 [eqt]
         else
           eqt
         end
  | _ ->
     failwith "impossible"

and add_def_axioms ((name, value, ty, srt) as def) =
  debug 2 (fun () -> print_endline ("add_def_axioms: " ^ name));
  match value with
  | IndType(_, constrs, params_num) ->
     if srt = SortProp then
       (prop_to_formula [] ty) >>= fun r ->
       add_axiom (mk_axiom name r)
     else
       begin
         if Coq_typing.check_type_target_is_prop ty then
           begin
             begin
               if opt_prop_inversion_axioms && name <> Hhutils.lib_ref_name "core.eq.type" then
                 (* Status quo structural axiom: propositional inversion remains
                    the exhaustiveness principle used after losing the old
                    packaged case split; this is covered by the split/disjunctive
                    case interderivability theorem. *)
                 add_inversion_axioms true name constrs
               else
                 return ()
             end >>
             if not opt_omit_toplevel_prop_typing_axioms then
               add_typing_axiom name ty
             else
               return ()
           end
        else
          begin
            let skip_refinement_decl = skip_refinement_decl_axioms name in
            (if skip_refinement_decl then
               return ()
             else
               List.fold_left
                 (fun acc c -> add_injection_axioms params_num c >> acc)
                 (return ()) constrs) >>
            List.fold_left (fun acc (c1, c2) -> add_discrim_axioms c1 c2) (return ()) (Hhlib.mk_pairs constrs) >>
            add_typing_axiom name ty >>
            if opt_inversion_axioms && not skip_refinement_decl then
              (* Status quo structural axiom: inversion remains the emitted
                 exhaustiveness principle; the split/disjunctive-case
                 interderivability theorem justifies relying on it after the old
                 packaged case disjunction is no longer emitted. *)
              add_inversion_axioms false name constrs
            else
              return ()
          end
      end
  | _ ->
     if srt = SortProp then
       begin
         prop_to_formula [] ty >>= fun r ->
         add_axiom (mk_axiom name r) >>
         if is_transport_constant name then
           add_def_eq_axiom def
         else
           return ()
       end
     else
       begin
         add_typing_axiom name ty >>
         add_def_eq_axiom def
       end

(***************************************************************************************)
(* Axioms hash *)

module Axhash = struct
  let axhash = Hashtbl.create 1024
  let clear () = Hashtbl.clear axhash
  let add name lst =
    if Hashtbl.mem axhash name then
      failwith ("Axhash.add: " ^ name);
    Hashtbl.add axhash name lst
  let remove name = Hashtbl.remove axhash name
  let mem name = Hashtbl.mem axhash name
  let find name =
    try Hashtbl.find axhash name with Not_found -> failwith ("Axhash.find: " ^ name)
end

(***************************************************************************************)
(* Translation *)

let translate name =
  wf_mark := false;
  proof_case_counter := 0;
  log 1 ("translate: " ^ name);
  let previous_owner = !translation_owner in
  translation_owner := name;
  try
    let axs = extract_axioms (add_def_axioms (Defhash.find name)) in
    translation_owner := previous_owner;
    Hhlib.sort_uniq (fun x y -> Stdlib.compare (fst x) (fst y)) axs
  with e ->
    translation_owner := previous_owner;
    raise e

let retranslate lst =
  List.iter
    begin fun name ->
      if not (Axhash.mem name) then
        Axhash.add name (translate name)
    end
    lst

let get_axioms lst =
  let structural = List.concat (List.map Case_dependencies.find lst) in
  retranslate structural;
  coq_axioms @
    Hhlib.sort_uniq (fun x y -> Stdlib.compare (fst x) (fst y))
      (List.concat
         (List.map Axhash.find (Hhlib.sort_uniq String.compare (lst @ structural))))

let remove_def name =
  Defhash.remove name;
  Axhash.remove name;
  Case_dependencies.remove name

let cleanup () =
  Defhash.clear ();
  Axhash.clear ();
  Coq_erasure.clear ();
  Case_dependencies.clear ();
  Lift_dependencies.clear ();
  translation_owner := "";
  Hashing.clear coqterm_hash

(******************************************************************************)

let write_problem fname name deps =
  let axioms = get_axioms (name :: deps)
  in
  let oc = open_out fname
  in
  try
    Tptp_out.write_fol_problem
      (output_string oc)
      (List.remove_assoc name axioms)
      (name, List.assoc name axioms);
    close_out oc
  with e ->
    close_out oc;
    raise e
