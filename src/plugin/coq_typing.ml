(* Typing and type destruction *)

open Hammer_lib
open Coq_transl_opts
open Coqterms

(***************************************************************************************)
(* Normalization by evaluation *)

type coqvalue =
  N of coqneutral
| PROD of coqterm Lazy.t * coqvalue_abstr
| LAM of coqterm Lazy.t * coqvalue_abstr
(* The integer is the position of the recursive argument, as declared by the
   fixpoint itself; -1 stands for a fixpoint with no guard to check (a cofix,
   or a declaration whose recursive index did not survive conversion). *)
| FIX of coqterm Lazy.t * coqvalue Lazy.t * int
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
  | FIX(t, _, _) -> Lazy.force t

(* A constructor and an axiom have the same declaration shape -- both are
   opaque constants standing for themselves -- so constructorhood is read off
   the target of the declared type, which for a constructor is always a literal
   telescope ending in an application of its own inductive.  An inductive that
   is not in the hash cannot vouch for the name, and the answer is then `no':
   the sole caller uses it to decide whether a fixpoint may be unfolded, and
   leaving a fixpoint folded is always safe. *)
let constructor_hash : (string, bool) Hashtbl.t = Hashtbl.create 257

let is_constructor name =
  match Hashtbl.find_opt constructor_hash name with
  | Some b -> b
  | None ->
     let rec target ty =
       match ty with
       | Prod(_, _, ty2) -> target ty2
       | _ -> ty
     in
     let b =
       match (try Some (Defhash.find name) with _ -> None) with
       | Some (_, Const c, ty, _) when c = name ->
          begin match flatten_app (target ty) with
          | Const indname, _ ->
             begin match (try Some (Defhash.find indname) with _ -> None) with
             | Some (_, IndType(_, constrs, _), _, _) -> List.mem name constrs
             | _ -> false
             end
          | _ -> false
          end
       | _ -> false
     in
     Hashtbl.add constructor_hash name b;
     b

let clear_constructor_hash () = Hashtbl.clear constructor_hash

(* Iota for a fixpoint fires only when its recursive argument has a constructor
   at the head.  Unfolding it unconditionally is not a conversion, and on a
   definition by well-founded recursion it does not even terminate: the
   recursive call of `Fix_F' is guarded by `Acc_inv' applied to the
   accessibility proof, which stays stuck on an abstract proof, so each
   unfolding hands back a fixpoint applied to another stuck argument.  Nothing
   in the term bounds that, and the fuel an `Acc_intro_generator' witness
   supplies bounds only closed computation, not this. *)
let is_constructor_headed v =
  let rec head n =
    match n with
    | APP(x, _) -> head x
    | _ -> n
  in
  match v with
  | N n -> begin match head n with CONST c -> is_constructor c | _ -> false end
  | _ -> false

(* Apply a value to a whole argument spine.  A fixpoint whose guard does not
   hold -- because the recursive argument is not a constructor application, or
   because the spine does not even reach it -- is left folded and turned into
   the head of a neutral, exactly as an opaque constant would be. *)
let rec apply_args v args =
  match args with
  | [] -> v
  | y :: rest ->
     begin
       match v with
       | LAM(_, (_, _, f)) -> apply_args (f y) rest
       | FIX(t, body, recarg) ->
          if recarg >= 0 &&
             (recarg >= List.length args ||
              not (is_constructor_headed (Lazy.force (List.nth args recarg))))
          then
            apply_args (N (TERM t)) args
          else
            apply_args (Lazy.force body) args
       | N n -> apply_args (N (APP(n, y))) rest
       | _ -> failwith "apply"
     end

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
        let tm2 = try coqdef_value (Defhash.find c) with _ -> tm
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
    | App(_, _) ->
      (* The spine is applied as a whole: the guard of a fixpoint is a
         condition on one particular argument, which a one-argument-at-a-time
         application cannot see. *)
      let (hd, args) = flatten_app tm
      in
      apply_args (eval env hd) (List.map (delay_eval env) args)
    | Cast(x, y) ->
      eval env x
    | Lam a ->
      LAM(delay_subst env tm, eval_abstr env a)
    | Prod a ->
      PROD(delay_subst env tm, eval_abstr env a)
    | Let(value, (vname, ty, body)) ->
      eval ((vname, delay_eval env value) :: env) body
    | Case(indname, matched_term, return_type, raw_return_type, params_num, branches) ->
      let eval_valapp = apply_args
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
            and df =
              try Defhash.find indname with _ -> raise Not_found
            in
            match df with
            | (_, IndType(_, constrs, _), indtype, indsort) ->
               begin
                 match v with
                 | (N (CONST c)) when List.mem c constrs ->
                    let i = Hhlib.index c constrs
                    in
                    let (n, b) = List.nth branches i
                    in
                    if List.length args > n + params_num then
                      begin
                        debug 2 (fun () ->
                          print_coqterm tm;
                          print_list print_string constrs;
                          print_int i; print_newline ();
                          print_int n; print_newline ();
                          print_int params_num; print_newline ());
                        failwith ("eval: bad number of constructor arguments: " ^ c)
                      end
                    else
                      eval_valapp (eval env b) (Hhlib.drop params_num args)
                 | _ ->
                    N (TERM (delay_subst env
                               (Case(indname, reify mt2, return_type, raw_return_type, params_num, branches))))
               end
            | _ ->
               failwith "impossible"
          end
        with Not_found ->
          N (TERM (delay_subst env
                     (Case(indname, reify mt2, return_type, raw_return_type, params_num, branches))))
      end
    | Fix(cft, k, recargs, names, types, bodies) ->
      (* A cofix has no recursive argument to guard on, and neither has a
         fixpoint whose declared index is missing; both keep the unconditional
         unfolding they had. *)
      let recarg m =
        if cft = CoqFix then
          match List.nth_opt recargs m with Some i -> i | None -> -1
        else
          -1
      in
      let rec mkenv m lst acc =
        match lst with
        | h :: t ->
            let fx = Fix(cft, m, recargs, names, types, bodies)
            in
            let v =
              if cft = CoqFix then
                lazy (FIX(delay_subst env fx, delay_eval env fx, recarg m))
              else
                lazy (N (TERM (delay_subst env fx)))
            in
            mkenv (m + 1) t ((h, v) :: acc)
        | [] ->
            acc
      in
      FIX(delay_subst env tm, lazy (eval (mkenv 0 names env) (List.nth bodies k)), recarg k)
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
      | FIX(_, v2, _) ->
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
          failwith
            ("check_prop: var not found: " ^ x ^ " in context ["
             ^ String.concat "; " (List.map fst ctx) ^ "]")
      end
  | Const(c) ->
      begin
        try
          is_prop_tgt args (coqdef_type (Defhash.find c))
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
  | Case(indname, matched_term, return_type, _, params_num, branches) ->
      (* NOTE: this is incorrect if `params_num' is smaller than the
         number of arguments of the inductive type `indname' *)
      is_prop_tgt args (App(return_type, matched_term))
  | Fix(_, k, _, names, types, bodies) ->
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
  let rec pom ctx2 =
    match ctx2 with
    | (n, ty) :: ctx3 when n = name ->
      check_prop ctx3 ty
    | _ :: ctx3 ->
      pom ctx3
    | _ ->
      (* Reaching this means a term was translated in a context that does not
         bind all of its free variables. *)
      failwith
        ("check_proof_var: " ^ name ^ " is not bound in ["
         ^ String.concat "; " (List.map fst ctx) ^ "]")
  in
  pom ctx

let check_type_target_is_prop ty =
  let rec hlp v =
    match v with
    | PROD(_, (name, _, f)) ->
      hlp (f (lazy (N (VAR name))))
    | FIX(_, v2, _) ->
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
    | FIX(_, v2, _) ->
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
    | FIX(_, v2, _) -> hlp (Lazy.force v2) acc
    | _ -> (v, List.rev acc)
  in
  hlp (eval ty) []

let destruct_type ty =
  let (x, y) = destruct_type_eval ty
  in
  (reify x, y)

let destruct_type_app ty =
  let (target, cargs) = destruct_type ty
  in
  let (tgt, targs) = flatten_app target
  in
  (tgt, targs, cargs)

let get_type_args ty = snd (destruct_type_eval ty)
let get_type_target ty = fst (destruct_type ty)
let get_type_app_target ty = let (t, _, _) = destruct_type_app ty in t
