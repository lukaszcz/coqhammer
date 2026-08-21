(* coqterm datatype and helper functions *)
open Hammer_lib
open Coq_transl_opts
open Hhlib

type coqfixtype = CoqFix | CoqCoFix

type coqterm =
  Var of string
| Const of string
| App of coqterm * coqterm
| Lam of coqabstraction
| Case of string (* name of inductive type matched on *) * coqterm (* matched term *) *
    coqterm (* normalized return type *) *
    coqterm (* raw CIC return type, before logical lowering *)
(* Both return-type forms are lambda-abstractions that take as their arguments the
   non-parameter arguments of the inductive definition and the term
   matched on.  Translation uses the normalized form for formulas and guards,
   and the raw form to recover instantiated parameters and indices. *) *
  int (* params_num: number of parameters *) *
  (int * coqterm) list
(* case branches: pairs (num of args (n), branch term); m-th branch on
   the list corresponds to the m-th constructor; arguments to each
   branch are the arguments of the corresponding constructor, with
   parameters omitted (parameters are the first params_num arguments
   of the constructor); each branch term is of the form \x_1...x_n . b
   where n is the number of arguments and b is the branch expression;
   it is always the case for each branch that params_num + n is the
   total number of arguments to the corresponding constructor *)
| Cast of coqterm (* term *) * coqterm (* type *)
| Fix of coqfixtype * int (* 0-based result index *) * int list (* recargs *) *
    string list (* name list *) * coqterm list (* type list *) * coqterm list (* body list *)
| Let of coqterm (* value *) * coqabstraction
| Prod of coqabstraction
| IndType of string (* inductive type name *) * string list (* constructor names *) * int (* params_num *)
| SortProp | SortSet | SortType
| Quant of string (* "?" or "!" *) * coqabstraction
| Equal of coqterm * coqterm
and coqabstraction = string (* var name *) * coqterm (* var type *) * coqterm (* body *)

type coqdef = (* coq global definition *)
  string (* name *) * coqterm (* value *) * coqterm (* type *) * coqterm (* sort *)

type coqcontext = (string * coqterm) list

(* fol is a coqterm for which is_fol holds *)
type fol = coqterm
type fol_axioms = (string * fol) list

(* Axiom names identify formulas throughout a translated problem.  Merge all
   bundles through this function so duplicate replay is harmless only when the
   formulas agree; silently retaining either side of a conflicting collision
   would make the result depend on traversal order. *)
let compose_axioms bundles =
  let sorted =
    List.sort (fun x y -> String.compare (fst x) (fst y))
      (List.concat bundles)
  in
  let rec deduplicate acc = function
    | [] -> List.rev acc
    | ((name, formula) as axiom) :: rest ->
       let rec consume = function
         | (name2, formula2) :: tail when name2 = name ->
            (* Replaying a cached bundle shares its formulas physically, so the
               duplicates this is here to tolerate are almost always the same
               object; the structural comparison then never has to walk them. *)
            if formula2 != formula && formula2 <> formula then
              raise (Hammer_errors.HammerError
                       ("internal translation error: axiom name collision for " ^
                        name));
            consume tail
         | tail -> tail
       in
       deduplicate (axiom :: acc) (consume rest)
  in
  deduplicate [] sorted

let is_fol tm =
  match tm with
  | Fix(_) | Case(_) | Lam(_) | Cast(_) | Prod(_) | IndType(_) | Let(_) |
      SortProp | SortSet | SortType -> false
  | _ -> true

let mk_fun_ty ty1 ty2 = Prod("$Anonymous", ty1, ty2)
let quant_type = Prod("T", SortType, mk_fun_ty (mk_fun_ty (Var("1")) SortProp) SortProp)
let eq_type = Prod("T", SortType, mk_fun_ty (Var("1")) (mk_fun_ty (Var("2")) SortProp))

let logop_defs = [
  ("&", Const("&"), mk_fun_ty SortProp (mk_fun_ty SortProp SortProp), SortType);
  ("|", Const("|"), mk_fun_ty SortProp (mk_fun_ty SortProp SortProp), SortType);
  ("=>", Const("=>"), mk_fun_ty SortProp (mk_fun_ty SortProp SortProp), SortType);
  ("<=>", Const("<=>"), mk_fun_ty SortProp (mk_fun_ty SortProp SortProp), SortType);
  ("~", Const("~"), mk_fun_ty SortProp SortProp, SortType);
  ("?", Const("?"), quant_type, SortType);
  ("!", Const("!"), quant_type, SortType);
  ("=", Const("="), eq_type, SortType);
  ("$True", Const("$True"), SortProp, SortType);
  ("$False", Const("$False"), SortProp, SortType);
  ("$Any", Const("$Any"), SortType, SortType);
  ("$Proof", Const("$Proof"), Const("$Any"), SortType)
]

let type_any = Const("$Any")

(***************************************************************************************)
(* Miscellaneous helper functions *)

let comp f g x = f (g x)

let coqdef_name (name, _, _, _) = name
let coqdef_value (_, value, _, _) = value
let coqdef_type (_, _, ty, _) = ty
let coqdef_sort (_, _, _, srt) = srt

let coqdef_map f (name, value, ty, srt) = (name, f value, f ty, srt)

let unique_id_counter = ref 0

let unique_id () =
  incr unique_id_counter;
  if !unique_id_counter = 0 then
    failwith "unique_id";
  string_of_int !unique_id_counter

let reset_unique_id () = unique_id_counter := 0

let refresh_varname name = "var_" ^ name ^ "_" ^ unique_id ()

let mk_vars l = List.map (fun (x, _) -> Var(x)) l

let mk_binop op x y = App(App(Const(op), x), y)
let mk_uniop op x = App(Const(op), x)
let mk_quant op var varty body = Quant(op, (var, varty, body))
let mk_hastype x y =
  if opt_hastype then
    App(App(Const "$HasType", x), y)
  else
    App(y, x)

let mk_and = mk_binop "&"
let mk_or = mk_binop "|"
let mk_impl = mk_binop "=>"
let mk_equiv = mk_binop "<=>"
let mk_not = mk_uniop "~"
let mk_forall = mk_quant "!"
let mk_exists = mk_quant "?"

let mk_eq x y = Equal(x, y)

let is_bin_logop c = (c = "&" || c = "|" || c = "=>" || c = "<=>")
let is_logop c = is_bin_logop c || c = "~" || c = "?" || c = "!" || c = "="

let strip_suffix name = try String.sub name 0 (String.rindex name '$') with Not_found -> name

(* the last dot-separated segment of a (possibly qualified) name *)
let short_name name =
  try
    let i = String.rindex name '.' in
    String.sub name (i + 1) (String.length name - i - 1)
  with Not_found -> name

let rec mk_long f varlst body =
  match varlst with
  | (var, varty) :: t ->
    f var varty (mk_long f t body)
  | [] ->
    body

let mk_long_forall = mk_long mk_forall
let mk_long_exists = mk_long mk_exists
let mk_long_lam = mk_long (fun var varty body -> Lam(var, varty, body))
let mk_long_prod = mk_long (fun var varty body -> Prod(var, varty, body))

let rec join_right f lst =
  match lst with
  | [x] -> x
  | x :: t -> f x (join_right f t)
  | _ -> failwith "join_right"

let join_left f lst =
  let rec hlp lst acc =
    match lst with
    | [] -> acc
    | x :: t -> hlp t (f acc x)
  in
  match lst with
  | h :: t -> hlp t h
  | [] -> failwith "join_left"

let mk_long_app left args = join_left (fun x y -> App(x, y)) (left :: args)

let flatten_app tm =
  let rec hlp tm acc =
    match tm with
    | App(x, y) -> hlp x (y :: acc)
    | _ -> (tm, acc)
  in
  hlp tm []

let flatten_fol_quant op tm =
  let rec hlp tm acc =
    match tm with
    | Quant(op2, (vname, ty, body)) when op = op2 ->
      assert (ty = type_any);
      hlp body (vname :: acc)
    | _ -> (tm, List.rev acc)
  in
  hlp tm []

let mk_def name value ty srt = (name, value, ty, srt)
let mk_axiom name thm = (name, thm)

(* f n ctx acc tm:
   ctx -- list of (vname, vtype) pairs
   n -- length of ctx
*)
let map_fold_coqterm0 f acc tm =
  let rec do_map_fold n ctx acc tm =
    let map_fold_lst f n ctx lst acc2 =
      List.fold_right
        begin fun x (lst, acc) ->
          let (x2, acc2) = f n ctx acc x
          in
          (x2 :: lst, acc2)
        end
        lst
        ([], acc2)
    in
    match tm with
    | Var(_) ->
      f n ctx acc tm
    | Const(_) ->
      f n ctx acc tm
    | App(x, y) ->
      let (x2, acc2) = do_map_fold n ctx acc x
      in
      let (y2, acc3) = do_map_fold n ctx acc2 y
      in
      let tm2 = App(x2, y2)
      in
      f n ctx acc3 tm2
    | Lam(name, ty, body) ->
      let (ty2, acc2) = do_map_fold n ctx acc ty
      in
      let (body2, acc3) = do_map_fold (n + 1) ((name, ty2) :: ctx) acc2 body
      in
      let tm2 = Lam(name, ty2, body2)
      in
      f n ctx acc3 tm2
    | Case(indname, x, ty, raw_ty, npar, lst) ->
      let (x2, acc2) = do_map_fold n ctx acc x
      in
      let (ty2, acc3) = do_map_fold n ctx acc2 ty
      in
      let (raw_ty2, acc4) = do_map_fold n ctx acc3 raw_ty
      in
      let (lst2, acc4) =
        map_fold_lst
          begin fun n ctx acc (nargs, x) ->
            let (x2, acc2) = do_map_fold n ctx acc x
            in
            ((nargs, x2), acc2)
          end
          n ctx lst acc4
      in
      let tm2 = Case(indname, x2, ty2, raw_ty2, npar, lst2)
      in
      f n ctx acc4 tm2
    | Cast(x, y) ->
      let (x2, acc2) = do_map_fold n ctx acc x
      in
      let (y2, acc3) = do_map_fold n ctx acc2 y
      in
      let tm2 = Cast(x2, y2)
      in
      f n ctx acc3 tm2
    | Fix(cft, k, recargs, names, types, bodies) ->
      let (types2, acc2) = map_fold_lst do_map_fold n ctx types acc
      and m = List.length types
      in
      let ctx2 = Hhlib.rev_combine names types2 ctx
      in
      let rec mk_bodies2 bodies acc =
        match bodies with
        | b :: b2 ->
          let (bb, acc2) = mk_bodies2 b2 acc
          in
          let (x, acc3) = do_map_fold (n + m) ctx2 acc2 b
          in
          (x :: bb, acc3)
        | [] -> ([], acc)
      in
      let (bodies2, acc3) = mk_bodies2 bodies acc2
      in
      let tm2 = Fix(cft, k, recargs, names, types2, bodies2)
      in
      f n ctx acc3 tm2
    | Let(value, (name, ty, body)) ->
      let (value2, acc2) = do_map_fold n ctx acc value
      in
      let (ty2, acc3) = do_map_fold n ctx acc2 ty
      in
      let (body2, acc4) = do_map_fold (n + 1) ((name, ty2) :: ctx) acc3 body
      in
      let tm2 = Let(value2, (name, ty2, body2))
      in
      f n ctx acc4 tm2
    | Prod(name, ty, body) ->
      let (ty2, acc2) = do_map_fold n ctx acc ty
      in
      let (body2, acc3) = do_map_fold (n + 1) ((name, ty2) :: ctx) acc2 body
      in
      let tm2 = Prod(name, ty2, body2)
      in
      f n ctx acc3 tm2
    | IndType(indname, constrs, params_num) ->
      f n ctx acc tm
    | SortProp | SortSet | SortType ->
      f n ctx acc tm
    | Quant(op, (vname, vtype, body)) ->
      let (vtype2, acc2) = do_map_fold n ctx acc vtype
      in
      let (body2, acc3) = do_map_fold (n + 1) ((vname, vtype2) :: ctx) acc2 body
      in
      let tm2 = Quant(op, (vname, vtype2, body2))
      in
      f n ctx acc3 tm2
    | Equal(x, y) ->
      let (x2, acc2) = do_map_fold n ctx acc x
      in
      let (y2, acc3) = do_map_fold n ctx acc2 y
      in
      let tm2 = Equal(x2, y2)
      in
      f n ctx acc3 tm2
  in
  do_map_fold 0 [] acc tm

let map_fold_coqterm f = map_fold_coqterm0 (fun _ ctx acc x -> f ctx acc x)

let map_coqterm0 f tm = fst (map_fold_coqterm0 (fun n ctx acc x -> (f n ctx x, acc)) () tm)
let map_coqterm f = map_coqterm0 (fun _ ctx x -> f ctx x)

let fold_coqterm0 g acc tm = snd (map_fold_coqterm0 (fun n ctx acc x -> (x, g n ctx acc x)) acc tm)
let fold_coqterm g acc = fold_coqterm0 (fun _ ctx acc x -> g ctx acc x) acc

let term_mentions_const names tm =
  fold_coqterm
    (fun _ acc tm ->
       acc ||
       match tm with
       | Const c -> List.mem c names
       | IndType(indname, constrs, _) ->
           List.mem indname names || List.exists (fun c -> List.mem c names) constrs
       | _ -> false)
    false tm

let get_const_names tm =
  let lst =
    fold_coqterm
      begin fun _ acc tm ->
        match tm with
        | Const(c) ->
          c :: acc
        | IndType(name, constrs, params_num) ->
          let lst = name :: constrs @ acc
          in
          if opt_induction_principles then
            (name ^ "_ind") :: lst
          else
            lst
        | _ ->
          acc
      end
      []
      tm
  in
  Hhlib.sort_uniq (Stdlib.compare) lst

let var_occurs vname tm =
  try
    fold_coqterm
      begin fun ctx acc tm ->
        match tm with
        | Var(v) when v = vname && not (List.mem_assoc v ctx) ->
            raise Exit
        | _ -> acc
      end
      false
      tm
  with Exit ->
    true

let get_fvars ctx tm =
  let rec hlp vars tm acc =
    match vars with
    | ((name, ty) as v) :: t ->
        let tm2 = Lam(name, ty, tm)
        in
        if var_occurs name tm then
          hlp t tm2 (v :: acc)
        else
          hlp t tm2 acc
    | [] ->
        acc
  in
  hlp ctx tm []

(* [get_fvars] reports only the free variables the context happens to bind.
   The two below report the free variables of the term itself, which is what a
   scoping check needs: a term whose free variables are not all bound by the
   context it is translated in has escaped its binders. *)
let get_free_varnames tm =
  Hhlib.sort_uniq (Stdlib.compare)
    (fold_coqterm
       begin fun ctx acc tm ->
         match tm with
         | Var(name) when not (List.mem_assoc name ctx) ->
             name :: acc
         | _ ->
             acc
       end
       []
       tm)

let term_fvars_subset names tm =
  List.for_all (fun name -> List.mem name names) (get_free_varnames tm)

let vars_to_ctx = List.rev
let ctx_to_vars = List.rev

let dsubst lst tm =
  let getname x i acc =
    try
      (List.assoc i acc, acc)
    with _ ->
      let name = refresh_varname x
      in
      (name, (i, name) :: acc)
  in
  let rename_abs n (name, ty, v) acc =
    try
      let name2 = List.assoc n acc
      in
      ((name2, ty, v), List.remove_assoc n acc)
    with _ ->
      (* we're in this case if Var(name) does not occur free *)
      ((refresh_varname name, ty, v), acc)
  in
  let rename_fix_names names n acc =
    let (names2, acc2, _) =
      List.fold_left
        begin fun (names2, acc, k) name ->
          try
            let name2 = List.assoc k acc
            in
            (name2 :: names2, List.remove_assoc k acc, k + 1)
          with _ ->
            (name :: names2, acc, k + 1)
        end
        ([], acc, n)
        names
    in
    (List.rev names2, acc2)
  in
  if lst = [] then
    tm
  else
    fst
      (map_fold_coqterm0
         begin fun n ctx acc tm ->
           match tm with
           | Var(x) ->
               begin
                 try
                   let i = Hhlib.assoc_index x ctx
                   in
                   begin
                     let (name, acc2) = getname x (n - i - 1) acc
                     in
                     (Var(name), acc2)
                   end
                 with _ ->
                   begin
                     match Hhlib.massoc x lst with
                     | Some v -> (Lazy.force v, acc)
                     | None -> (tm, acc)
                   end
               end
           | Lam abs ->
               let (abs2, acc2) = rename_abs n abs acc
               in
               (Lam abs2, acc2)
           | Prod abs ->
               let (abs2, acc2) = rename_abs n abs acc
               in
               (Prod abs2, acc2)
           | Quant(op, abs) ->
               let (abs2, acc2) = rename_abs n abs acc
               in
               (Quant(op, abs2), acc2)
           | Let(value, abs) ->
               let (abs2, acc2) = rename_abs n abs acc
               in
               (Let(value, abs2), acc2)
           | Fix(cft, k, recargs, names, types, bodies) ->
               let (names2, acc2) = rename_fix_names names n acc
               in
               (Fix(cft, k, recargs, names2, types, bodies), acc2)
           | _ ->
               (tm, acc)
         end
         []
         tm)

let substvar vname tm = dsubst [(vname, lazy tm)]

let rec subst_params formals params tm =
  match formals with
  | [] -> tm
  | (name, _) :: formals2 ->
      match params with
      | [] -> failwith "subst_params: not enough parameters"
      | param :: params2 ->
          let tm2 = subst_params formals2 params2 tm in
          if var_occurs name tm2 then substvar name param tm2 else tm2

let refresh_bvars = substvar "dummy" (Var("dummy"))

(* `simple_subst' assumes that the free variables of `value' cannot be captured *)
let simple_subst vname value =
  map_coqterm
    begin fun ctx tm ->
      match tm with
      | Var(x) when x = vname && not (List.mem_assoc x ctx) -> value
      | _ -> tm
    end

(* The opaque proof of `ty'.  The type is retained on the cast, so it must stay
   meaningful in the context the cast is placed in. *)
let mk_proof_cast ty = Cast(Const("$Proof"), refresh_bvars ty)

let subst_proof name ty = simple_subst name (mk_proof_cast ty)

let simpl =
  map_coqterm
    begin fun ctx tm ->
      match tm with
      | App(Lam(vname, _, body), x) -> substvar vname x body
      | _ -> tm
    end

(* Head-normalize `tm' far enough to expose the head of its weak head normal
   form -- typically an application of an inductive type.  `unfold' resolves a
   global constant to its definition value, `None' when the constant is opaque
   or absent; this module cannot reach the definition hash itself, hence the
   callback.  Only head steps are taken -- beta, delta, iota and let
   substitution -- with no reduction under binders and no recursion into
   arguments, the scrutinee of a `Case' being the sole exception since iota
   needs it.  All steps share the `budget' fuel counter and the current term is
   returned unreduced once it runs out: an unbounded type-level unfolder is a
   known blow-up hazard here.  `Fix' is deliberately not reduced.  It is the
   caller, not the reducer, that decides whether a stuck head is a refusal. *)
let whnf_head ~budget ~unfold tm =
  let fuel = ref budget
  in
  let step () =
    if !fuel <= 0 then
      false
    else
      begin
        decr fuel;
        true
      end
  in
  let find_branch constrs branches cname =
    let rec hlp i constrs =
      match constrs with
      | [] -> None
      | c :: constrs2 -> if c = cname then List.nth_opt branches i else hlp (i + 1) constrs2
    in
    hlp 0 constrs
  in
  let rec whnf tm args =
    match tm with
    | App(x, y) ->
      whnf x (y :: args)
    | Lam(vname, _, body) when args <> [] && step () ->
      whnf (substvar vname (List.hd args) body) (List.tl args)
    | Let(value, (vname, _, body)) when step () ->
      whnf (substvar vname value body) args
    | Const(c) ->
      begin
        match unfold c with
        (* an inductive's own entry must not be unfolded: that would destroy
           the head we are trying to expose; self-referential entries (e.g. the
           logical operators above) must not loop *)
        | Some(IndType(_)) | None -> mk_long_app tm args
        | Some(value) when value <> tm && step () -> whnf value args
        | Some(_) -> mk_long_app tm args
      end
    | Case(indname, matched, _, _, params_num, branches) ->
      begin
        match iota indname matched params_num branches with
        | Some(tm2) -> whnf tm2 args
        | None -> mk_long_app tm args
      end
    | _ ->
      mk_long_app tm args
  and iota indname matched params_num branches =
    match unfold indname with
    | Some(IndType(_, constrs, _)) ->
      begin
        match flatten_app (whnf matched []) with
        | (Const(cname), cargs) ->
          begin
            match find_branch constrs branches cname with
            | Some(n, br) when List.length cargs = params_num + n && step () ->
              Some(mk_long_app br (Hhlib.drop params_num cargs))
            | _ -> None
          end
        | _ -> None
      end
    | _ -> None
  in
  whnf tm []

(***************************************************************************************)
(* Printing *)

let write_coqterm out tm =
  let rec write tm =
    match tm with
    | Var(x) ->
      out x
    | Const(c) ->
      out c
    | App(x, y) ->
      out "(";
      write x;
      out " @ ";
      write y;
      out ")"
    | Lam(vname, vtype, tm) ->
      out "^[";
      out vname;
      out " : ";
      write vtype;
      out "]: (";
      write tm;
      out ")"
    | Case(indname, mtm, rt, _, nparams, branches) ->
      out "(match ";
      write mtm;
      out " : ";
      out indname;
      out " return ";
      write rt;
      out " with ";
      oiter out (fun (n, br) -> write br) " | " branches;
      out " end)"
    | Cast(tm, ty) ->
      out "(";
      write tm;
      out " : ";
      write ty;
      out ")"
    | Fix(cft, res, recargs, names, types, bodies) ->
      out "(";
      out (match cft with CoqFix -> "fix" | CoqCoFix -> "cofix");
      out " ";
      out (string_of_int res);
      out " [";
      oiter out (fun i -> out (string_of_int i)) ";" recargs;
      out "] ";
      oiter
        out
        (fun ((n, ty), tm) -> out "("; out n; out " : "; write ty; out " := "; write tm; out ")")
        "; "
        (List.combine (List.combine names types) bodies);
      out ")"
    | Let(value, (name, ty, body)) ->
      out "let ";
      out name;
      out " : ";
      write ty;
      out " := ";
      write value;
      out " in ";
      write body
    | Prod(vname, vtype, tm) ->
      out "(Prod (";
      out vname;
      out " : ";
      write vtype;
      out ")";
      write tm;
      out ")"
    | IndType(indname, constrs, params_num) ->
      out "<inductive type: ";
      out indname;
      out " (";
      out (string_of_int params_num);
      out ")>"
    | SortType ->
      out "Type"
    | SortSet ->
      out "Set"
    | SortProp ->
      out "Prop"
    | Quant(op, (vname, vtype, body)) ->
      out op;
      out "[";
      out vname;
      out " : ";
      write vtype;
      out "]: (";
      write body;
      out ")"
    | Equal(x, y) ->
      out "(";
      write x;
      out " = ";
      write y;
      out ")"
  in
  write tm

let print_coqterm tm = write_coqterm print_string tm; print_newline ()

let string_of_coqterm tm =
  let s = ref "" in
  let out s2 = s := !s ^ s2 in
  write_coqterm out tm;
  !s

let print_list f lst =
  print_string "[";
  oiter print_string f ";\n" lst;
  print_endline "]"

let print_var (name, ty) =
  print_string name; print_string " : "; write_coqterm print_string ty

let print_ctx ctx =
  print_list print_var (List.rev ctx)

let print_header_nonl str tm ctx =
  print_newline ();
  print_endline str;
  print_coqterm tm;
  print_ctx ctx

let print_header str tm ctx =
  print_header_nonl str tm ctx;
  print_newline ()
