(* Translation from Coq to FOL *)

(* TODO: *)
(* 1. Omit (some) type arguments (inductive type parameters?) to
   polymorphic functions/constructors (e.g. cons). *)
(* 2. Omit (some) type guards when the type may be inferred (e.g.
   forall x : nat, Even(x) -> phi probably may be translated to
   forall x, Even(x) -> phi', because Even(x) implies nat(x)). *)
(* 3. Heuristic monomorphisation (instantiation of polymorphic
   definitions with types). *)

open Coqterms
open Coq_transl_opts
open Hh_term

(***************************************************************************************)
(* Definitions hash *)

let defhash = Hashtbl.create 1024

let defhash_add_lazy name x =
  if Hashtbl.mem defhash name then
    failwith ("duplicate global definition of " ^ name);
  Hashtbl.add defhash name (ref x)

let defhash_add x =
  defhash_add_lazy (coqdef_name x) (lazy x)

let defhash_remove name =
  Hashtbl.remove defhash name

let defhash_clear () = Hashtbl.clear defhash

let defhash_find name =
  try
    Lazy.force !(Hashtbl.find defhash name)
  with Not_found ->
    failwith ("defhash_find: " ^ name)

let defhash_mem name = Hashtbl.mem defhash name

let defhash_to_vlist () = Hashtbl.fold (fun _ rv acc -> rv :: acc) defhash []

let defhash_iter0 f = List.iter (fun rv -> ignore (f (Lazy.force !rv))) (defhash_to_vlist ())

let defhash_map0 f =
  List.iter
    begin fun rv ->
      let v = !rv in
      rv := lazy (f (Lazy.force v))
    end
    (defhash_to_vlist ())

let defhash_map f = defhash_map0 (fun (name, value, ty, srt) -> (name, f value, f ty, srt))

let hastype_type = mk_fun_ty (Const("$Any")) (mk_fun_ty SortType SortProp)

let add_logop_defs () =
  List.iter defhash_add logop_defs;
  if opt_hastype then
    defhash_add ("$HasType", Const("$HasType"), hastype_type, SortType)

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
      | Fix(cft, m, names, types, bodies) ->
          let names2 =
            List.rev
              (fst
                 (List.fold_left
                    (fun (acc, k) name -> ((string_of_int k ^ "_" ^ name) :: acc, k + 1))
                    ([], n)
                    names))
          in
          Fix(cft, m, names2, types, bodies)
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
      if not (defhash_mem name) then
        defhash_add_lazy name (lazy (conv h t));
      add_defs t
    | [] ->
        ()
  in
  log 1 "Reinitializing...";
  (try add_logop_defs () with _ -> ());
  add_defs lst

(***************************************************************************************)
(* Normalization by evaluation *)

type coqvalue =
  N of coqneutral
| PROD of coqterm Lazy.t * coqvalue_abstr
| LAM of coqterm Lazy.t * coqvalue_abstr
| FIX of coqterm Lazy.t * coqvalue Lazy.t
and coqneutral =
| VAR of string
| CONST of string
| APP of coqneutral * coqvalue Lazy.t
| TERM of coqterm Lazy.t
and coqvalue_abstr =  string * coqterm Lazy.t * (coqvalue Lazy.t -> coqvalue)

let rec reify v =
  let rec reify_neutral n =
    match n with
    | VAR x -> Var(x)
    | CONST c -> Const(c)
    | APP (x, y) -> App(reify_neutral x, reify (Lazy.force y))
    | TERM t -> Lazy.force t
  in
  match v with
  | N x -> reify_neutral x
  | PROD(t, _) -> Lazy.force t
  | LAM(t, _) -> Lazy.force t
  | FIX(t, _) -> Lazy.force t

(* evaluation to normal form *)
let eval (tm : coqterm) : coqvalue =
  let rec eval (env : (string * coqvalue Lazy.t) list) (tm : coqterm) : coqvalue =
    debug 5 (fun () -> print_newline (); print_endline "eval"; print_coqterm tm; print_newline ());
    let delay_subst env tm =
      if env = [] then
        lazy tm
      else
        lazy (dsubst (List.map (fun (n, v) -> (n, lazy (reify (Lazy.force v)))) env) tm)
    and delay_eval env tm =
      lazy (eval env tm)
    in
    let eval_abstr env (name, ty, value) =
      (name, delay_subst env ty, (fun x -> eval ((name, x) :: env) value))
    in
    match tm with
    | Var(x) ->
      begin
        try
          Lazy.force (List.assoc x env)
        with Not_found ->
          N (VAR(x))
      end
    | Const(c) ->
      begin
        let tm2 = try coqdef_value (defhash_find c) with _ -> tm
        in
        if tm2 = tm then
          N (CONST c)
        else
          match tm2 with
          | IndType(_) ->
              N (CONST c)
          | _ ->
              eval [] tm2
      end
    | App(x, y) ->
      let rec apply x y =
        match x with
        | LAM(_, (_, _, f)) -> f y
        | FIX(_, v) -> apply (Lazy.force v) y
        | N x2 -> N (APP(x2, y))
        | _ -> failwith "apply"
      in
      apply (eval env x) (delay_eval env y)
    | Cast(x, y) ->
      eval env x
    | Lam a ->
      LAM(delay_subst env tm, eval_abstr env a)
    | Prod a ->
      PROD(delay_subst env tm, eval_abstr env a)
    | Let(value, (vname, ty, body)) ->
      eval ((vname, delay_eval env value) :: env) body
    | Case(indname, matched_term, return_type, params_num, branches) ->
      let rec eval_valapp v args =
        match args with
        | h :: t ->
          begin
            match v with
            | LAM(_, (_, _, f)) -> eval_valapp (f h) t
            | N n -> eval_valapp (N (APP(n, h))) t
            | _ -> failwith "eval_app"
          end
        | [] -> v
      and flatten_valapp v =
        let rec hlp n acc =
          match n with
          | (APP(x, y)) ->
            hlp x (y :: acc)
          | _ ->
            (N n, acc)
        in
        match v with
        | N n -> hlp n []
        | _ -> (v, [])
      in
      begin
        let mt2 = eval env matched_term
        in
        try
          begin
            let (v, args) = flatten_valapp mt2
            and (_, IndType(_, constrs, _), indtype, indsort) =
              try defhash_find indname with _ -> raise Not_found
            in
            match v with
            | (N (CONST c)) when List.mem c constrs ->
              let i = Hhlib.index c constrs
              in
              let (n, b) = List.nth branches i
              in
              if List.length args > n + params_num then
                begin
                  print_coqterm tm;
                  print_list print_string constrs;
                  print_int i; print_newline ();
                  print_int n; print_newline ();
                  print_int params_num; print_newline ();
                  failwith ("eval: bad number of constructor arguments: " ^ c)
                end
              else
                eval_valapp (eval env b) (Hhlib.drop params_num args)
            | _ ->
              N (TERM (delay_subst env
                         (Case(indname, reify mt2, return_type, params_num, branches))))
          end
        with Not_found ->
          N (TERM (delay_subst env
                     (Case(indname, reify mt2, return_type, params_num, branches))))
      end
    | Fix(cft, k, names, types, bodies) ->
      let rec mkenv m lst acc =
        match lst with
        | h :: t ->
            let fx = Fix(cft, m, names, types, bodies)
            in
            let v =
              if cft = CoqFix then
                lazy (FIX(delay_subst env fx, delay_eval env fx))
              else
                lazy (N (TERM (delay_subst env fx)))
            in
            mkenv (m + 1) t ((h, v) :: acc)
        | [] ->
            acc
      in
      FIX(delay_subst env tm, lazy (eval (mkenv 0 names env) (List.nth bodies k)))
    | _ ->
      N (TERM (delay_subst env tm))
  in
  eval [] tm

(***************************************************************************************)
(* Limited typechecking *)

let rec check_prop args ctx tm =
  let is_prop_tgt args ty =
    let rec hlp args v =
      match v with
      | PROD(_, (_, _, f)) ->
          begin
            match args with
            | h :: args2 ->
                hlp args2 (f (lazy (eval h)))
            | _ ->
                false
          end
      | FIX(_, v2) ->
          hlp args (Lazy.force v2)
      | N (TERM tm) ->
          if args = [] then
            Lazy.force tm = SortProp
          else
            false
      | _ ->
          false
    in
    hlp args (eval ty)
  in
  debug 4 (fun () -> print_header "check_prop" tm ctx);
  match tm with
  | Var(x) ->
      begin
        try
          is_prop_tgt args (List.assoc x ctx)
        with Not_found ->
          print_list (fun (name, _) -> print_string name) (List.rev ctx);
          failwith ("check_prop: var not found: " ^ x)
      end
  | Const(c) ->
      begin
        try
          is_prop_tgt args (coqdef_type (defhash_find c))
        with _ ->
          false
      end
  | App(x, y) ->
      check_prop (y :: args) ctx x
  | Lam(vname, ty, body) ->
      begin (* NOTE: the lambda case is incomplete, but this should be enough in practice *)
        match args with
        | _ :: args2 ->
            check_prop args2 ((vname, ty) :: ctx) body
        | _ ->
            false
      end
  | Prod(vname, ty1, ty2) ->
      if args = [] then
        check_prop [] ((vname, ty1) :: ctx) ty2
      else
        false
  | Cast(v, ty2) ->
      is_prop_tgt args ty2
  | Case(indname, matched_term, return_type, params_num, branches) ->
      (* NOTE: this is incorrect if `params_num' is smaller than the
         number of arguments of the inductive type `indname' *)
      is_prop_tgt args (App(return_type, matched_term))
  | Fix(_, k, names, types, bodies) ->
      is_prop_tgt args (List.nth types k)
  | Let(value, (name, ty, body)) ->
      check_prop args ctx (dsubst [(name, lazy (Cast(value, ty)))] body)
  | SortProp | SortSet | SortType ->
      false
  | Quant(_) | Equal(_) ->
      args = []
  | _ ->
      failwith "check_prop"

let check_prop ctx tm =
  match tm with
  | App(Const("~"), _) -> true
  | App(App(Const(c), _), _) when is_bin_logop c -> true
  | _ -> check_prop [] ctx tm

let check_proof_var ctx name =
  let rec pom ctx name =
    match ctx with
    | (n, ty) :: ctx2 when n = name ->
      check_prop ctx2 ty
    | _ :: ctx2 ->
      pom ctx2 name
    | _ ->
      failwith "check_proof_var"
  in
  pom ctx name

let check_type_target_is_prop ty =
  let rec hlp v =
    match v with
    | PROD(_, (name, _, f)) ->
      hlp (f (lazy (N (VAR name))))
    | FIX(_, v2) ->
      hlp (Lazy.force v2)
    | N (TERM tm) ->
      Lazy.force tm = SortProp
    | _ ->
      false
  in
  hlp (eval ty)

let check_type_target_is_type ty =
  let rec hlp v =
    match v with
    | PROD(_, (name, _, f)) ->
      hlp (f (lazy (N (VAR name))))
    | FIX(_, v2) ->
      hlp (Lazy.force v2)
    | N (TERM tm) ->
      let tm2 = Lazy.force tm
      in
      tm2 = SortSet || tm2 = SortType
    | _ ->
      false
  in
  hlp (eval ty)

let destruct_type_eval ty =
  let rec hlp v acc =
    match v with
    | PROD(_, (name, ty, f)) ->
      let name2 = refresh_varname name
      in
      hlp (f (lazy (N (VAR name2))))
        ((name2, refresh_bvars (Lazy.force ty)) :: acc)
    | FIX(_, v2) -> hlp (Lazy.force v2) acc
    | _ -> (v, List.rev acc)
  in
  hlp (eval ty) []

let destruct_type_noeval ty =
  let rec hlp t acc =
    match t with
    | Prod(name, ty, body) ->
      let name2 = refresh_varname name
      in
      hlp (substvar name (Var(name2)) body)
        ((name2, refresh_bvars ty) :: acc)
    | _ -> (t, List.rev acc)
  in
  hlp ty []

let get_type_args ty = snd (destruct_type_eval ty)

let destruct_type ty =
  if opt_eval_type_targets then
    let (x, y) = destruct_type_eval ty in (reify x, y)
  else
    destruct_type_noeval ty

let destruct_type_for_ind indname ty =
  let (target, cargs) = destruct_type ty
  in
  let (tgt, targs) = flatten_app target
  in
  if tgt <> Const(indname) then
    let (target2, cargs2) = destruct_type_eval ty
    in
    let (_, targs2) = flatten_app (reify target2)
    in
    (targs2, cargs2)
  else
    (targs, cargs)

(***************************************************************************************)
(* Axioms *)

(* general axioms for any Coq translation *)
let coq_axioms = [
  ("_HAMMER_COQ_TRUE", Const("$True"));
  ("_HAMMER_COQ_FALSE", App(Const("~"), Const("$False")));
  ("_HAMMER_COQ_PROP_TYPE", mk_hastype (Const("Prop")) (Const("Type")));
  ("_HAMMER_COQ_SET_TYPE", mk_hastype (Const("Set")) (Const("Type")));
  ("_HAMMER_COQ_TYPE_TYPE", mk_hastype (Const("Type")) (Const("Type")));
  ("_HAMMER_COQ_SET_SUB_TYPE",
   mk_forall "X" type_any
     (mk_impl
        (mk_hastype (Var("X")) (Const("Set")))
        (mk_hastype (Var("X")) (Const("Type")))))
]

let axioms_stack = ref []

let clear_axioms () = axioms_stack := []

let add_axiom ax = log 3 ("add_axiom: " ^ fst ax); axioms_stack := ax :: !axioms_stack

let axioms () = !axioms_stack

(***************************************************************************************)
(* Inversion axioms for inductive types *)

let mk_inversion_conjs params_num args targs cacc =
  let rec mk_conjs ctx args targs cacc =
    match args, targs with
    | ((name, ty) :: args2), (y :: targs2) ->
      let cacc2 =
        if check_prop ctx ty then
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

let rec subst_params lst prms tm =
  match lst with
  | [] -> tm
  | (name, _) :: t ->
    let tm2 = subst_params t (List.tl prms) tm
    in
    if var_occurs name tm2 then
      substvar name (List.hd prms) tm2
    else
      tm2

let mk_inversion params indname constrs matched_term f =
  let rec mk_disjs constrs acc =
    match constrs with
    | cname :: constrs2 ->
      let (targs, cargs) = destruct_type_for_ind indname (coqdef_type (defhash_find cname))
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
      let ty = coqdef_type (defhash_find cname)
      in
      let (targs, cargs) = destruct_type_for_ind indname ty
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

let rec add_inversion_axioms0 mkinv indname axname fvars lvars constrs matched_term f =
  (* Note: the correctness of calling `prop_to_formula' below
     depends on the implementation of `convert_term' (that it
     never invokes check_prop on an application of the form
     App(..App(Const(cname),_)..)) *)
  let inv = mkinv indname constrs matched_term f
  in
  match inv with
  | Const("$False") -> ()
  | _ ->
    let tm =
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
             mk_guarded_forall ctx1 fvars1
               (fun _ -> prop_to_formula ctx (mk_long_forall lvars inv))))
      else
        let vars = fvars @ lvars
        in
        let ctx = List.rev vars
        in
        let vars1 = get_fvars ctx matched_term
        in
        mk_fol_forall [] vars (mk_guards [] vars1 inv)
    in
    add_axiom (mk_axiom axname tm)

(***************************************************************************************)
(* Lambda-lifting, fix-lifting and case-lifting *)

and lambda_lifting axname name fvars lvars1 tm =
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
  match body2 with
  | Fix(_) ->
    fix_lifting axname name fvars lvars body2
  | Case(_) ->
    case_lifting axname name fvars lvars body2
  | _ ->
    let ax =
      mk_axiom axname
        (close fvars
           begin fun ctx ->
             let mk_eqv =
               if check_prop (List.rev_append lvars ctx) body2 then
                 mk_equiv
               else
                 mk_eq
             in
             let eqv = mk_eqv (mk_long_app (Const(name)) (mk_vars (fvars @ lvars))) body2
             in
             if !opt_closure_guards || opt_lambda_guards then
               prop_to_formula ctx (mk_long_forall lvars eqv)
             else
               mk_fol_forall ctx lvars eqv
           end)
    in
    add_axiom ax;
    convert (List.rev fvars) (mk_long_app (Const(name)) (mk_vars fvars))

and fix_lifting axname dname fvars lvars tm =
  debug 3 (fun () -> print_header "fix_lifting" tm (fvars @ lvars));
  match tm with
  | Fix(cft, k, names, types, bodies) ->
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
            defhash_add (mk_def name2 (Const(name2)) ty2
                           (if check_prop [] ty2 then SortProp else SortType))
          with _ -> ())
        names2 types;
      List.nth
        (List.map2
           (fun (axname2, name2) body ->
             lambda_lifting axname2 name2 fvars lvars (prep body))
           (List.combine axnames names2)
           bodies)
        k
  | _ ->
      failwith "fix_lifting"

and case_lifting axname0 name0 fvars lvars tm =
  debug 3 (fun () -> print_header "case_lifting" tm (fvars @ lvars));
  let get_params indty rt params_num =
    let (_, args) = destruct_type_eval indty
    in
    let rec pom n tm =
      match tm with
      | Lam(_, ty, body) ->
        if n = 0 then
          let (_, tyargs) = flatten_app ty
          in
          assert (List.length tyargs >= params_num);
          Hhlib.take params_num tyargs
        else
          pom (n - 1) body
      | _ -> failwith "get_params"
    in
    let n = List.length args
    in
    assert (n >= params_num);
    pom (n - params_num) rt
  in
  let generic_match () =
    let name = "$_case_" ^ unique_id ()
    in
    let def = (name, Const(name), Const("$Any"), SortType)
    in
    defhash_add def;
    Const(name)
  in
  try
    begin
      match tm with
      | Cast(Const("$Proof"), _) | Const("$Proof") ->
        generic_match ()
      | Case(indname, matched_term, return_type, params_num, branches) ->
        let (_, IndType(_, constrs, pnum), indty, _) =
          try defhash_find indname with _ -> raise Not_found
        in
        assert (pnum = params_num);
        if check_type_target_is_prop indty then
          generic_match ()
        else
          let fname = if name0 = "" then "$_case_" ^ indname ^ "_" ^ unique_id () else name0
          in
          let axname = if name0 = "" then fname else axname0
          in
          let case_replacement =
            convert (List.rev fvars) (mk_long_app (Const(fname)) (mk_vars fvars))
          in
          let case_repl2 = mk_long_app case_replacement (mk_vars lvars)
          in
          let params = get_params indty return_type params_num
          in
          let rec hlp constrs branches params params_num vars tm =
            let rec get_branch cname cstrs brs =
              match cstrs, brs with
              | c :: cstrs2, b :: brs2 ->
                if c = cname then
                  b
                else
                  get_branch cname cstrs2 brs2
              | _ -> failwith "case_lifting: get_branch"
            in
            begin fun cname _ args eqt ->
              let (n, branch) = get_branch cname constrs branches
              in
              assert (List.length args <= n);
            (* We may have List.length args < n if there are some lets
               in the type and they get evaluated away. We do not
               properly deal with this (rare) situation: the generated
               formula will in this case not be correct (the branch
               (`cr' below) will miss arguments). *)
              let ctx = List.rev (vars @ args)
              in
              let ys = mk_vars args
              in
              let cr = simpl (mk_long_app branch ys)
              in
              match cr with
              | Case(indname2, mt2, return_type2, pnum2, branches2) ->
                let (_, IndType(_, constrs2, pn), indty2, _) =
                  try defhash_find indname2 with _ -> raise Not_found
                in
                assert (pn = pnum2);
                if check_type_target_is_prop indty2 then
                  eqt
                else
                  let params2 = get_params indty2 return_type2 pnum2
                  in
                  mk_guards []
                    (get_fvars ctx mt2)
                    (mk_and eqt (mk_inversion params2 indname constrs2 mt2
                                   (hlp constrs2 branches2 params2 pnum2 (vars @ args) cr)))
              | _ ->
                let eqv =
                  if check_prop ctx cr then
                    mk_equiv case_repl2 cr
                  else
                    mk_eq case_repl2 cr
                in
                mk_and eqt eqv
            end
          in
          add_inversion_axioms0
            (mk_inversion params) indname axname fvars lvars constrs matched_term
            (hlp constrs branches params params_num (fvars @ lvars) tm);
          case_replacement
      | _ ->
        failwith "case_lifting"
    end
  with Not_found ->
    log 2 ("case exception: " ^ name0);
    generic_match ()

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
      if check_prop ctx ty then
        mk (prop_to_formula ctx ty)
          (prop_to_formula ctx (subst_proof name ty body))
      else
        Quant(op, (name, type_any,
                   mk (type_to_guard ctx ty (Var(name)))
                     (prop_to_formula ((name, ty) :: ctx) body)))
  | Equal(x, y) ->
      Equal(convert_term ctx x, convert_term ctx y)
  | App(App(Const(c), x), y) when is_bin_logop c ->
      let x2 = prop_to_formula ctx x
      and y2 = prop_to_formula ctx y
      in
      assert (x2 <> Const("$Proof"));
      assert (y2 <> Const("$Proof"));
      App(App(Const(c), x2), y2)
  | App(Const("~"), x) ->
      let x2 = prop_to_formula ctx x
      in
      assert (x2 <> Const("$Proof"));
      App(Const("~"), x2)
  | App(App(Const("$HasType"), x), y) ->
      type_to_guard ctx y (convert ctx x)
  | App(x, y) ->
      let x2 = convert ctx x
      in
      if x2 = Const("$Proof") then
        Const("$Proof")
      else
        let y2 = convert_term ctx y
        in
        if y2 = Const("$Proof") then
          x2
        else
          App(x2, y2)
  | Lam(_) ->
      remove_lambda ctx tm
  | Case(_) ->
      remove_case ctx tm
  | Cast(Const("$Proof"), _) ->
      Const("$Proof")
  | Cast(_) ->
      remove_cast ctx tm
  | Fix(_) ->
      remove_fix ctx tm
  | Let(_) ->
      remove_let ctx tm
  | Prod(_) ->
      if check_prop ctx tm then
        prop_to_formula ctx tm
      else
        remove_type ctx tm
  | SortProp ->
      Const("Prop")
  | SortSet ->
      Const("Set")
  | SortType ->
      Const("Type")
  | Var(name) ->
      if check_proof_var ctx name then
        Const("$Proof")
      else
        Var(name)
  | Const(_) ->
      tm
  | IndType(_) ->
      failwith "convert"

and convert_term ctx tm =
  debug 3 (fun () -> print_header "convert_term" tm ctx);
  let should_lift =
    match tm with
    | Var(_) | Const(_) -> false
    | App(App(Const(c), _), _) when is_bin_logop c -> true
    | App(Const("~"), _) -> true
    | App(_) -> false
    | _ -> check_prop ctx tm
  in
  if should_lift then
    let name = "$_prop_" ^ unique_id ()
    in
    let fvars = get_fvars ctx tm
    in
    let tm2 = convert ctx (mk_long_app (Const(name)) (mk_vars fvars))
    in
    add_axiom (mk_axiom name
                 (close fvars (fun ctx -> mk_equiv tm2 (convert ctx tm))));
    tm2
  else
    convert ctx tm

and prop_to_formula ctx tm =
  debug 3 (fun () -> print_header "prop_to_formula" tm ctx);
  match tm with
  | Prod(vname, ty1, ty2) ->
    if check_prop ctx ty1 then
      mk_impl (prop_to_formula ctx ty1) (prop_to_formula ctx (subst_proof vname ty1 ty2))
    else
      mk_forall vname type_any
        (mk_impl
           (type_to_guard ctx ty1 (Var(vname)))
           (prop_to_formula ((vname, ty1) :: ctx) ty2))
  | _ ->
    convert ctx tm

(* `x' does not get converted *)
and type_to_guard ctx ty x =
  debug 3 (fun () -> print_header_nonl "type_to_guard" ty ctx; print_coqterm x; print_newline ());
  match ty with
  | Prod(vname, ty1, ty2) ->
    if check_prop ctx ty1 then
      mk_impl (prop_to_formula ctx ty1) (type_to_guard ctx (subst_proof vname ty1 ty2) x)
    else
      mk_forall vname type_any
        (mk_impl
           (type_to_guard ctx ty1 (Var(vname)))
           (type_to_guard ((vname, ty1) :: ctx) ty2 (App(x, (Var(vname))))))
  | _ ->
    mk_hastype x (convert ctx ty)

and mk_fol_forall ctx vars tm =
  let rec hlp ctx vars tm =
    match vars with
    | (name, ty) :: vars2 ->
      if check_prop ctx ty then
        hlp ((name, ty) :: ctx) vars2 (subst_proof name ty tm)
      else
        mk_forall name type_any
          (hlp ((name, ty) :: ctx) vars2 tm)
    | [] ->
      prop_to_formula ctx tm
  in
  hlp ctx vars tm

and mk_guarded_forall ctx vars cont =
  let rec hlp ctx vars =
    match vars with
    | (name, ty) :: vars2 ->
      mk_forall name type_any
        (mk_impl (type_to_guard ctx ty (Var(name)))
           (hlp ((name, ty) :: ctx) vars2))
    | [] ->
        cont ctx
  in
  hlp ctx vars

and mk_guards ctx vars tm =
  match vars with
  | (name, ty) :: vars2 ->
    if check_prop ctx ty then
      (mk_impl ty
         (mk_guards ((name, ty) :: ctx) vars2 (subst_proof name ty tm)))
    else
      (mk_impl (App(App(Const("$HasType"), Var(name)), ty))
         (mk_guards ((name, ty) :: ctx) vars2 tm))
  | [] ->
    tm

and close vars cont =
  if !opt_closure_guards then
    mk_guarded_forall [] vars cont
  else
    let rec hlp ctx vars =
      match vars with
      | (name, ty) :: vars2 ->
        mk_forall name type_any
          (hlp ((name, ty) :: ctx) vars2)
      | [] ->
        cont ctx
    in
    hlp [] vars

and remove_lambda ctx tm =
  debug 3 (fun () -> print_header "remove_lambda" tm ctx);
  let name = "$_lam_" ^ unique_id ()
  in
  lambda_lifting name name (get_fvars ctx tm) [] tm

and remove_case ctx tm =
  debug 3 (fun () -> print_header "remove_case" tm ctx);
  case_lifting "" "" (get_fvars ctx tm) [] tm
(* TODO: for case lifting get_fvars should always include the proof
   variables tm may depend on; otherwise the resulting FOL problem
   may be inconsistent *)

and remove_cast ctx tm =
  debug 3 (fun () -> print_header "remove_cast" tm ctx);
  match tm with
  | Cast(trm, ty) ->
      let fvars = get_fvars ctx tm
      and fname = "$_cast_" ^ unique_id ()
      in
      let tm2 = convert ctx (mk_long_app (Const(fname)) (mk_vars fvars))
      and ty2 = mk_long_prod fvars ty
      in
      let srt = if check_prop [] ty2 then SortProp else SortType
      in
      if srt <> SortProp then
        begin
          let def = mk_def fname (mk_long_lam fvars trm) ty2 srt
          in
          add_def_eq_axiom def;
          tm2
        end
      else
        Const("$Proof")
  | _ ->
      failwith "remove_cast"

and remove_fix ctx tm =
  debug 3 (fun () -> print_header "remove_fix" tm ctx);
  fix_lifting "" "" (get_fvars ctx tm) [] tm

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
      let srt = if check_prop [] ty2 then SortProp else SortType
      in
      let def = mk_def name2 (mk_long_lam fvars value) ty2 srt
      in
      defhash_add def;
      if srt <> SortProp then
        begin
          add_def_eq_axiom def
        end;
      convert ctx (simple_subst name val2 body)
  | _ ->
      failwith "remove_let"

and remove_type ctx ty =
  debug 3 (fun () -> print_header "remove_type" ty ctx);
  let name = "$_type_" ^ unique_id ()
  and fvars = get_fvars ctx ty
  in
  add_def_eq_type_axiom name name fvars ty;
  convert ctx (mk_long_app (Const(name)) (mk_vars fvars))

and add_def_eq_type_axiom axname name fvars ty =
  debug 2 (fun () -> print_header "add_def_eq_type_axiom" ty fvars);
  let vname = "var_" ^ unique_id ()
  in
  add_axiom (mk_axiom axname
               (close fvars
                  (fun ctx ->
                    (mk_forall vname type_any
                       (mk_equiv
                          (mk_hastype
                             (Var(vname))
                             (convert ctx (mk_long_app (Const(name)) (mk_vars fvars))))
                          (type_to_guard ctx ty (Var(vname))))))))

and add_typing_axiom name ty =
  debug 2 (fun () -> print_endline ("add_typing_axiom: " ^ name));
  if not (is_logop name) && name <> "$True" && name <> "$False" && ty <> type_any then
    begin
      if opt_omit_prop_typing_axioms && check_type_target_is_prop ty then
        ()
      else if opt_type_optimization &&
          (check_type_target_is_type ty || check_type_target_is_prop ty) then
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
          and args = get_type_args ty
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
          add_axiom (mk_axiom ("$_tydef_" ^ name2) (fix_ax ax));
          add_axiom (mk_axiom ("$_typeof_" ^ name) (type_to_guard [] ty (Const(name2))))
        end
      else
        add_axiom (mk_axiom ("$_typeof_" ^ name) (type_to_guard [] ty (Const(name))))
    end

and add_def_eq_axiom (name, value, ty, srt) =
  debug 2 (fun () -> print_endline ("add_def_eq_axiom: " ^ name));
  let axname = "$_def_" ^ name
  in
  match value with
  | Lam(_) ->
      ignore (lambda_lifting axname name [] [] value)
  | Fix(_) ->
      ignore (fix_lifting axname name [] [] value)
  | Const(c) when c = name ->
      ()
  | _ ->
      begin
        match ty with
        | SortProp ->
            add_axiom (mk_axiom axname (mk_equiv (Const(name)) (prop_to_formula [] value)))
        | SortType | SortSet ->
            add_def_eq_type_axiom axname name [] value
        | _ ->
            add_axiom (mk_axiom axname (mk_eq (Const(name)) (convert [] value)))
      end

and add_injection_axioms constr =
  debug 2 (fun () -> print_endline ("add_injection_axioms: " ^ constr));
  let ty = coqdef_type (defhash_find constr)
  in
  let rec hlp ty1 ty2 args1 args2 conjs =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), Prod(name2, lty2, value2) ->
      let lname1 = refresh_varname name1
      and lname2 = refresh_varname name2
      in
      let lvalue1 = simple_subst name1 (Var(lname1)) value1
      and lvalue2 = simple_subst name2 (Var(lname2)) value2
      in
      mk_forall lname1 lty1
        (mk_forall lname2 lty2
           (hlp lvalue1 lvalue2
              (Var(lname1) :: args1) (Var(lname2) :: args2)
              ((mk_eq (Var(lname1)) (Var(lname2))) :: conjs)))
    | _ ->
      mk_impl
        (mk_eq (mk_long_app (Const(constr)) (List.rev args1))
           (mk_long_app (Const(constr)) (List.rev args2)))
        (join_left mk_and conjs)
  in
  let rec hlp2 ctx ty1 ty2 args1 args2 conjs =
    match ty1, ty2 with
    | Prod(name1, lty1, value1), Prod(name2, lty2, value2) ->
      let lname1 = refresh_varname name1
      and lname2 = refresh_varname name2
      in
      let lvalue1 = simple_subst name1 (Var(lname1)) value1
      and lvalue2 = simple_subst name2 (Var(lname2)) value2
      in
      mk_forall lname1 type_any
        (mk_forall lname2 type_any
           (hlp2 ((lname1, lty1) :: (lname2, lty2) :: ctx) lvalue1 lvalue2
              (Var(lname1) :: args1) (Var(lname2) :: args2)
              ((mk_eq (Var(lname1)) (Var(lname2))) :: conjs)))
    | _ ->
      prop_to_formula ctx
	(mk_impl
           (mk_eq (mk_long_app (Const(constr)) (List.rev args1))
              (mk_long_app (Const(constr)) (List.rev args2)))
           (join_left mk_and conjs))
  in
  match ty with
  | Prod(_) ->
     let ax =
       if !opt_closure_guards || opt_injectivity_guards then
	 prop_to_formula [] (hlp ty ty [] [] [])
       else
	 hlp2 [] ty ty [] [] []
     in
     add_axiom (mk_axiom ("$_inj_" ^ constr) ax)
  | _ ->
    ()

and add_discrim_axioms constr1 constr2 =
  debug 2 (fun () -> print_endline ("add_discrim_axioms: " ^ constr1 ^ ", " ^ constr2));
  let ty1 = coqdef_type (defhash_find constr1)
  and ty2 = coqdef_type (defhash_find constr2)
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
      mk_forall lname1 type_any (hlp2 ((lname1, lty1) :: ctx) lvalue1 ty2
				   (Var(lname1) :: args1) args2)
    | _, Prod(name2, lty2, value2) ->
      let lname2 = refresh_varname name2
      in
      let lvalue2 = simple_subst name2 (Var(lname2)) value2
      in
      mk_forall lname2 type_any (hlp2 ((lname2, lty2) :: ctx) ty1 lvalue2
				   args1 (Var(lname2) :: args2))
    | _ ->
      prop_to_formula ctx
	(mk_not
           (mk_eq
              (mk_long_app (Const(constr1)) (List.rev args1))
              (mk_long_app (Const(constr2)) (List.rev args2))))
  in
  let ax =
    if !opt_closure_guards || opt_discrimination_guards then
      prop_to_formula [] (hlp ty1 ty2 [] [])
    else
      hlp2 [] ty1 ty2 [] []
  in
  add_axiom (mk_axiom ("$_discrim_" ^ constr1 ^ "$" ^ constr2) ax)

and add_inversion_axioms is_prop indname constrs =
  debug 2 (fun () -> print_endline ("add_inversion_axioms: " ^ indname));
  let (_, IndType(_, constrs, params_num), indtype, indsort) = defhash_find indname
  in
  let args = get_type_args indtype
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

and add_def_axioms ((name, value, ty, srt) as def) =
  debug 2 (fun () -> print_endline ("add_def_axioms: " ^ name));
  match value with
  | IndType(_, constrs, _) ->
    if srt = SortProp then
      add_axiom (mk_axiom name (prop_to_formula [] ty))
    else
      begin
        if check_type_target_is_prop ty then
          begin
            if opt_prop_inversion_axioms && name <> "Coq.Init.Logic.eq" then
              add_inversion_axioms true name constrs;
            if not opt_omit_toplevel_prop_typing_axioms then
              add_typing_axiom name ty
          end
        else
          begin
            List.iter add_injection_axioms constrs;
            iter_pairs add_discrim_axioms constrs;
            add_typing_axiom name ty;
            if opt_inversion_axioms then
              add_inversion_axioms false name constrs
          end;
      end
  | _ ->
    if srt = SortProp then
      add_axiom (mk_axiom name (prop_to_formula [] ty))
    else
      begin
        add_typing_axiom name ty;
        add_def_eq_axiom def
      end

(***************************************************************************************)
(* Axioms hash *)

let axhash = Hashtbl.create 1024

let axhash_clear () = Hashtbl.clear axhash

let axhash_add name lst =
  if Hashtbl.mem axhash name then
    failwith ("axhash_add: " ^ name);
  Hashtbl.add axhash name lst

let axhash_remove name = Hashtbl.remove axhash name

let axhash_mem name = Hashtbl.mem axhash name

let axhash_find name =
  try Hashtbl.find axhash name with Not_found -> failwith ("axhash_find: " ^ name)

(***************************************************************************************)
(* Translation *)

let translate name =
  log 1 ("translate: " ^ name);
  clear_axioms ();
  add_def_axioms (defhash_find name);
  let axs = axioms ()
  in
  clear_axioms ();
  axs

let retranslate lst =
  List.iter
    begin fun name ->
      if not (axhash_mem name) then
        axhash_add name (translate name)
    end
    lst

let get_axioms lst =
  coq_axioms @ List.concat (List.map axhash_find lst)

let remove_def name =
  defhash_remove name;
  axhash_remove name

let cleanup () =
  defhash_clear ();
  axhash_clear ()

(******************************************************************************)

let write_problem fname name deps =
  let axioms = get_axioms (name :: deps)
  in
  let oc = open_out fname
  in
  Tptp_out.write_fol_problem
    (output_string oc)
    (List.remove_assoc name axioms)
    (name, List.assoc name axioms);
  close_out oc
