(* Author: Evan Marzion, modified by Lukasz Czajka *)

open Hammer_lib
open Coqterms
open Hhlib
open Coq_transl_opts

type namesubst = (string * string) list

(***************************************************************************************)
(* Coqterm hashing *)

let var i =
  "v_CANONICAL_" ^ (string_of_int i)

(* creates a list of m canonical vars starting at n *)
let vars n m =
  List.map var (range n (n+m))

(* substitutes all occ. of the name oldn with the name newn in term t *)
let sub newn oldn t = substvar oldn (Var(newn)) t

let subs pairs t = dsubst (List.map (fun (newn,oldn) -> (oldn, lazy (Var(newn)))) pairs) t

(* canonical representation using variable renaming starting at n
   along with variable substitutions *)
let rec can_aux n t =
  let f = can_aux n in
    match t with
    | Var x                 -> Var x
    | Const x               -> Const x
    | App(t1,t2)            -> App (f t1, f t2)
    | Lam(x,t1,t2)          -> let v = var n in Lam(v, f t1, can_aux (n+1) (sub v x t2))
    | Case(indt,t1,t2,raw_t2,m,cs) ->
      Case(indt, f t1, f t2, f raw_t2, m, List.map (fun (p,u) -> (p, f u)) cs)
    | Cast(t1,t2)           -> Cast(f t1, f t2)
    | Fix(t,i,recargs,xs,ts1,ts2) -> let m = List.length xs in
                                     let newvars = vars n m in
                                     let newbodies = List.map (fun b -> can_aux (n+m) (subs (zip (vars n m) xs) b)) ts2
                                     in Fix(t, i, recargs, newvars, List.map f ts1, newbodies)
    | Let(t1,(x,t2,t3))     -> let v = var n in Let(f t1, (v,f t2, can_aux (n+1) (sub v x t3)))
    | Prod(x,t1,t2)         -> let v = var n in Prod(v, f t1, can_aux (n+1) (sub v x t2))
    | IndType(indt,xs,n)    -> IndType(indt,xs,n)
    | SortProp              -> SortProp
    | SortSet               -> SortSet
    | SortType              -> SortType
    | Quant(q,(x,t1,t2))    -> let v = var n in Quant(q,(v,f t1,can_aux (n+1) (sub v x t2)))
    | Equal(t1,t2)          -> Equal(f t1,f t2)

(* The context renaming has to be simultaneous.  Lifted definitions reintroduce
   canonical names into the terms they are built from, so a context may already
   bind a variable literally called [v_CANONICAL_k]; renaming one entry at a
   time would make an earlier entry's new name collide with that variable and
   the next step would then rename both together. *)
let canonical ctx tm =
  let vars = List.rev ctx in
  let subst = List.mapi (fun n (x, _) -> (var n, x)) vars in
  let cctx = List.rev (List.mapi (fun n (_, tp) -> (var n, subs subst tp)) vars) in
  (cctx, can_aux (List.length vars) (subs subst tm), List.rev subst)

type 'a lift_fun = (coqterm -> coqterm) -> 'a -> 'a
type 'a coqterms_hash = (string * coqcontext * coqterm, 'a) Hashtbl.t * 'a lift_fun

let create lift = (Hashtbl.create 128, lift)

let clear tbl = Hashtbl.clear (fst tbl)

let find_or_insert_keyed key tbl ctx tm mk =
  debug 4 (fun () -> print_header "find_or_insert" tm ctx);
  let (tbl, lift) = tbl in
  (* [get_fvars] silently keeps only the free variables the context binds, so a
     term that escaped its binders would be canonicalized against a context too
     short for it and the fresh canonical binders would capture the variables
     left out.  The escape is the bug; report it here, where the term still
     shows which variable got loose. *)
  let escaped =
    List.filter (fun name -> not (List.mem_assoc name ctx)) (get_free_varnames tm)
  in
  if escaped <> [] then
    raise (Hammer_errors.HammerError
             ("internal translation error: free variables " ^
              String.concat ", " escaped ^ " escape the context of " ^
              string_of_coqterm tm));
  let ctx' = vars_to_ctx (get_fvars ctx tm) in
  let (cctx,ctm,sigma) = canonical ctx' tm in
  debug 4 begin fun () ->
    print_header "canonical (result)" ctm cctx;
    print_list (fun (x,y) -> print_string ("(" ^ x ^ "," ^ y ^ ")")) sigma
  end;
  let revsigma = List.map (fun (x,y) -> (y,x)) sigma in
  try
    lift (subs revsigma) (Hashtbl.find tbl (key,cctx,ctm))
  with _ ->
    let x = mk cctx ctm in
    Hashtbl.add tbl (key,cctx,ctm) x;
    lift (subs revsigma) x

let find_or_insert tbl ctx tm mk =
  find_or_insert_keyed "" tbl ctx tm mk
