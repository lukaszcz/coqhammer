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
   the next step would then rename both together.  Context types are terms too:
   normalize their own binders above the context-variable range, or fresh Rocq
   names for anonymous product binders prevent valid exact cache hits. *)
let canonical ctx tm =
  let vars = List.rev ctx in
  let subst = List.mapi (fun n (x, _) -> (var n, x)) vars in
  let first_inner = List.length vars in
  let cctx =
    List.rev
      (List.mapi
         (fun n (_, tp) -> (var n, can_aux first_inner (subs subst tp)))
         vars)
  in
  (cctx, can_aux first_inner (subs subst tm), List.rev subst)

(***************************************************************************************)
(* Instance matching between canonical lifts *)

(* A lifted symbol names a Coq term.  If the term of one lift is a syntactic
   instance of the term of another, the two symbols denote the same Coq object
   at the matching arguments, which is what lets the translator relate them by
   an equation.  The match below is purely syntactic on [coqterm]: no
   conversion, no reduction. *)

exception No_match

(* Binds the [j]-th pattern variable to [ti].  [benv] maps the schema-side
   binders currently in scope to their instance-side counterparts, so its
   codomain is exactly the set of instance-side binders in scope: an image
   mentioning one of them would escape its binder in the equation the caller
   emits.  Reject such a match instead. *)
let bind_pattern_var subst benv j ti =
  match subst.(j) with
  | Some t ->
    if t <> ti then
      raise No_match
  | None ->
    let inner = List.map snd benv in
    if List.exists (fun v -> List.mem v inner) (get_free_varnames ti) then
      raise No_match;
    subst.(j) <- Some ti

(* Both sides number their inner binders from their own context length, so
   binder names are never compared directly -- only through [benv]. *)
let rec do_match pvars subst benv ts ti =
  let recur = do_match pvars subst benv in
  match ts, ti with
  | Var x, _ when List.mem_assoc x benv ->
    if ti <> Var(List.assoc x benv) then
      raise No_match
  | Var x, _ when List.mem_assoc x pvars ->
    bind_pattern_var subst benv (List.assoc x pvars) ti
  | Var _, _ ->
    (* a schema variable which is neither a pattern variable nor bound inside
       the schema term: the schema is ill-scoped *)
    raise No_match
  | Const c1, Const c2 when c1 = c2 -> ()
  | App(a1, a2), App(b1, b2) -> recur a1 b1; recur a2 b2
  | Cast(a1, a2), Cast(b1, b2) -> recur a1 b1; recur a2 b2
  | Equal(a1, a2), Equal(b1, b2) -> recur a1 b1; recur a2 b2
  | Lam(x, a1, a2), Lam(y, b1, b2) ->
    recur a1 b1;
    do_match pvars subst ((x, y) :: benv) a2 b2
  | Prod(x, a1, a2), Prod(y, b1, b2) ->
    recur a1 b1;
    do_match pvars subst ((x, y) :: benv) a2 b2
  | Quant(q1, (x, a1, a2)), Quant(q2, (y, b1, b2)) when q1 = q2 ->
    recur a1 b1;
    do_match pvars subst ((x, y) :: benv) a2 b2
  | Let(a0, (x, a1, a2)), Let(b0, (y, b1, b2)) ->
    recur a0 b0;
    recur a1 b1;
    do_match pvars subst ((x, y) :: benv) a2 b2
  | Case(indt1, a1, a2, ra1, m1, cs1), Case(indt2, b1, b2, ra2, m2, cs2)
    when indt1 = indt2 && m1 = m2 && List.length cs1 = List.length cs2 &&
         List.for_all2 (fun (n1, _) (n2, _) -> n1 = n2) cs1 cs2 ->
    recur a1 b1;
    recur a2 b2;
    recur ra1 ra2;
    List.iter2 (fun (_, u1) (_, u2) -> recur u1 u2) cs1 cs2
  | Fix(cft1, i1, recargs1, xs1, ts1, bs1), Fix(cft2, i2, recargs2, xs2, ts2, bs2)
    when cft1 = cft2 && i1 = i2 && recargs1 = recargs2 &&
         List.length xs1 = List.length xs2 &&
         List.length ts1 = List.length ts2 && List.length bs1 = List.length bs2 ->
    List.iter2 recur ts1 ts2;
    let benv2 = zip xs1 xs2 @ benv in
    List.iter2 (do_match pvars subst benv2) bs1 bs2
  | IndType(_, _, _), IndType(_, _, _) when ts = ti -> ()
  | SortProp, SortProp | SortSet, SortSet | SortType, SortType -> ()
  | _ -> raise No_match

let bound_count subst =
  Array.fold_left (fun n x -> if x = None then n else n + 1) 0 subst

(* [get_fvars] pulls a context variable in when it occurs only in the type of
   another included variable, so a canonical context may bind variables absent
   from the term.  The term traversal leaves those unbound; recover them by
   matching the type the schema context assigns to an already-bound pattern
   variable against the type the instance context assigns to its image.  Such
   variables do not occur in the schema term, so their images cannot affect
   [ctm_s[sigma] = ctm_i]; this fixpoint exists only to produce a plausible,
   well-scoped argument list.  A type which fails to match therefore does not
   invalidate the match -- it just yields no new binding. *)
let resolve_from_ctx_types pvars subst svars cctx_i =
  let progress = ref true in
  while !progress do
    progress := false;
    Array.iteri
      begin fun j im ->
        match im with
        | Some (Var w) when List.mem_assoc w cctx_i ->
          let subst2 = Array.copy subst in
          begin
            try
              do_match pvars subst2 [] (snd (List.nth svars j)) (List.assoc w cctx_i);
              if bound_count subst2 > bound_count subst then
                begin
                  Array.blit subst2 0 subst 0 (Array.length subst);
                  progress := true
                end
            with No_match -> ()
          end
        | _ -> ()
      end
      (Array.copy subst)
  done

(* [match_instance cctx_s ctm_s cctx_i ctm_i] treats the canonical variables
   bound by [cctx_s] as pattern variables and returns their images, in the
   canonical order [v_CANONICAL_0 .. v_CANONICAL_(k-1)] with
   [k = List.length cctx_s], such that substituting them into [ctm_s] yields
   [ctm_i] syntactically.

   The images are checked to be well-scoped in [cctx_i] rather than assumed to
   be: [bind_pattern_var] rejects an image escaping an instance-side binder,
   but that leaves the images exactly as well-scoped as [ctm_i] and the types
   in [cctx_i] are, and nothing establishes that here.  [canonical] renames the
   context it is handed rather than deriving it from the term, so a caller
   which hash-conses a term against a context too short for it -- what
   `case_aux_value' in coq_transl.ml guards against before lifting -- would
   otherwise be handed a substitution mentioning a variable neither side of the
   link equation binds. *)
let match_instance cctx_s ctm_s cctx_i ctm_i =
  (* [ctx_to_vars] lists the context in the canonical order
     [v_CANONICAL_0 .. v_CANONICAL_(k-1)] *)
  let svars = ctx_to_vars cctx_s in
  let pvars = List.mapi (fun j (x, _) -> (x, j)) svars in
  match ctm_s with
  | Var x when List.mem_assoc x pvars ->
    (* a bare pattern variable matches everything and says nothing *)
    None
  | _ ->
    let subst = Array.make (List.length svars) None in
    try
      do_match pvars subst [] ctm_s ctm_i;
      resolve_from_ctx_types pvars subst svars cctx_i;
      let images =
        Array.to_list
          (Array.map (function Some t -> t | None -> raise No_match) subst)
      in
      let inames = List.map fst cctx_i in
      if List.for_all (term_fvars_subset inames) images then
        Some images
      else
        None
    with No_match ->
      None

(***************************************************************************************)
(* Registry of lifted symbols, indexed for instance matching *)

type lift_link = {
  ll_name : string;        (* the registered partner symbol *)
  ll_ctx : coqcontext;     (* the partner's canonical context *)
  ll_tm : coqterm;         (* the partner's canonical term *)
  ll_new_is_schema : bool; (* true: the partner is an instance of the new lift *)
  ll_subst : coqterm list; (* images of the schema's canonical variables, in order *)
}

type lift_counters = {
  lc_registered : int;      (* register_lift calls *)
  lc_queried : int;         (* find_lift_link calls *)
  lc_linked_fwd : int;      (* links found with the partner as schema *)
  lc_linked_rev : int;      (* links found with the new lift as schema *)
  lc_attempts : int;        (* candidate match attempts *)
  lc_filtered : int;        (* examined entries rejected by the pre-filters *)
  lc_truncated : int;       (* find_lift_link calls that stopped at a cap,
                               leaving entries unexamined *)
  lc_noconst_dropped : int; (* entries dropped from the capped constant-free list *)
}

let zero_counters = {
  lc_registered = 0;
  lc_queried = 0;
  lc_linked_fwd = 0;
  lc_linked_rev = 0;
  lc_attempts = 0;
  lc_filtered = 0;
  lc_truncated = 0;
  lc_noconst_dropped = 0;
}

(* Two exact pre-filters on a candidate pair, both read off [do_match]: a
   successful match walks the schema in lockstep with the instance and stops
   early only at a schema-side [Var], which stands for a pattern variable or a
   binder and contains no constant.

   Constants: every [Const] the schema walk reaches forces an equal [Const] in
   the instance, and every [IndType] forces a literally equal [IndType] (hence
   the same inductive, constructor and induction-principle names).  So the
   schema's constant set is included in the instance's, and a pair failing the
   inclusion cannot match.

   Size: aligned nodes contribute 1 on each side, and the only place the two
   sides may differ is a schema-side [Var] of size 1 against an instance
   subterm of size at least 1.  So the schema's size is at most the instance's.
   Mind the direction: the schema is the *smaller* term.

   Both are filters only: they reject pairs [match_instance] rejects anyway,
   and neither can reject a matching pair.  [resolve_from_ctx_types] only adds
   bindings and never fails a match, so the context types constrain nothing
   here and only the terms are measured. *)

(* the number of nodes [do_match] walks; the [Case] inductive name and the
   [Fix] indices are compared for equality rather than descended into, so they
   contribute nothing *)
let rec term_size tm =
  match tm with
  | Var _ | Const _ | IndType _ | SortProp | SortSet | SortType -> 1
  | App(t1, t2) | Cast(t1, t2) | Equal(t1, t2)
  | Lam(_, t1, t2) | Prod(_, t1, t2) | Quant(_, (_, t1, t2)) ->
    1 + term_size t1 + term_size t2
  | Let(t1, (_, t2, t3)) -> 1 + term_size t1 + term_size t2 + term_size t3
  | Case(_, t1, t2, raw_t2, _, cs) ->
    List.fold_left (fun n (_, u) -> n + term_size u)
      (1 + term_size t1 + term_size t2 + term_size raw_t2) cs
  | Fix(_, _, _, _, ts1, ts2) ->
    let add n t = n + term_size t in
    List.fold_left add (List.fold_left add 1 ts1) ts2

(* inclusion of sorted deduplicated name lists, as [get_const_names] returns
   them (it sorts with [Stdlib.compare], which on strings is [String.compare]) *)
let rec is_subset lst1 lst2 =
  match lst1, lst2 with
  | [], _ -> true
  | _, [] -> false
  | x :: t1, y :: t2 ->
    let c = String.compare x y in
    if c = 0 then
      is_subset t1 t2
    else if c > 0 then
      is_subset lst1 t2
    else
      false

type lift_entry = {
  le_name : string;
  le_ctx : coqcontext;
  le_tm : coqterm;
  le_consts : string list; (* [get_const_names le_tm], for the subset filter *)
  le_size : int;           (* [term_size le_tm], for the size filter *)
}

type lift_registry = {
  (* An entry is indexed under [(top_tag, c)] for *every* constant [c]
     occurring in its canonical term.  Matching preserves the top constructor
     (the only schema term whose top is a variable is a bare pattern variable,
     which [match_instance] rejects), and a schema's constants are a subset of
     every instance's.  Indexing under all constants therefore makes both
     lookup directions correct: probing [(tag(new), c)] for each constant [c]
     of the new term finds every schema the new term instantiates (the schema's
     constants are among the new term's), and every instance of the new term
     used as a schema (an instance contains all of the new term's constants, so
     it is indexed under each of them). *)
  lr_index : (string * string, lift_entry list) Hashtbl.t;
  (* Entries with no constant at all filter badly, so they are kept apart and
     capped. *)
  mutable lr_noconst : lift_entry list;
  mutable lr_noconst_len : int;
  mutable lr_counters : lift_counters;
}

(* maximum number of constant-free entries kept per kind *)
let max_noconst_entries = 256
(* maximum number of viable candidates collected by one [find_lift_link] call *)
let max_match_candidates = 64
(* Maximum number of entries one [find_lift_link] call looks at.  The candidate
   cap bounds the match attempts but not the walk which feeds them: an entry
   rejected by the pre-filters, already seen under another of the query's
   constants, or equal to the query itself never becomes a candidate, so
   without a second bound a bucket of such entries is walked in full and the
   lookup cost still grows with the translation.

   The bound is a multiple of the candidate cap rather than the cap itself
   because a lookup does reach past a long stretch of rejects to a partner that
   matches: over Stdlib translations with up to 8192 selected premises, single
   lookups walked as many as 1339 entries, but the furthest entry a returned
   link came from sat at position 430.  Cutting the walk at 512 costs none of
   those links. *)
let max_examined_entries = 8 * max_match_candidates

let top_tag tm =
  match tm with
  | Var _ -> "Var"
  | Const _ -> "Const"
  | App _ -> "App"
  | Lam _ -> "Lam"
  | Case _ -> "Case"
  | Cast _ -> "Cast"
  | Fix _ -> "Fix"
  | Let _ -> "Let"
  | Prod _ -> "Prod"
  | IndType _ -> "IndType"
  | SortProp -> "SortProp"
  | SortSet -> "SortSet"
  | SortType -> "SortType"
  | Quant _ -> "Quant"
  | Equal _ -> "Equal"

(* one registry per lift kind ("type", "lam", "case", "fix"): lifts of
   different kinds are never linked *)
let registries : (string, lift_registry) Hashtbl.t = Hashtbl.create 8

let get_registry kind =
  try
    Hashtbl.find registries kind
  with Not_found ->
    let reg = { lr_index = Hashtbl.create 128; lr_noconst = []; lr_noconst_len = 0;
                lr_counters = zero_counters }
    in
    Hashtbl.add registries kind reg;
    reg

let register_lift kind name cctx ctm =
  let reg = get_registry kind in
  let consts = get_const_names ctm in
  let entry = { le_name = name; le_ctx = cctx; le_tm = ctm;
                le_consts = consts; le_size = term_size ctm } in
  reg.lr_counters <-
    { reg.lr_counters with lc_registered = reg.lr_counters.lc_registered + 1 };
  match consts with
  | [] ->
    if reg.lr_noconst_len >= max_noconst_entries then
      begin
        log 1 ("hashing: dropping constant-free " ^ kind ^ " lift " ^ name ^
               ": the cap of " ^ string_of_int max_noconst_entries ^
               " constant-free entries is reached");
        reg.lr_counters <-
          { reg.lr_counters with
            lc_noconst_dropped = reg.lr_counters.lc_noconst_dropped + 1 }
      end
    else
      begin
        reg.lr_noconst <- entry :: reg.lr_noconst;
        reg.lr_noconst_len <- reg.lr_noconst_len + 1
      end
  | consts ->
    let tag = top_tag ctm in
    List.iter
      begin fun c ->
        let key = (tag, c) in
        let entries = try Hashtbl.find reg.lr_index key with Not_found -> [] in
        Hashtbl.replace reg.lr_index key (entry :: entries)
      end
      consts

(* the substitution is the identity renaming and both contexts bind the same
   number of variables: the two terms are alpha-equal and the link says
   nothing; [len_other] is the length of the instance side's context *)
let is_identity_subst len_other subst =
  let rec hlp j lst =
    match lst with
    | [] -> true
    | Var x :: t when x = var j -> hlp (j + 1) t
    | _ -> false
  in
  List.length subst = len_other && hlp 0 subst

(* The index makes the lookup a filter, not a decision procedure, and it is
   deliberately incomplete in one direction: a constant-free query has no
   bucket to probe but the capped constant-free list, so an instance of it
   which does contain constants is not found -- as is a partner sitting past
   the point where the caps below stop the walk.  Missing a link only forgoes
   an equation. *)
let find_lift_link kind cctx ctm =
  let reg = get_registry kind in
  let tag = top_tag ctm in
  let consts = get_const_names ctm in
  let size = term_size ctm in
  let seen = Hashtbl.create 32 in
  let filtered = ref 0 in
  (* A candidate is kept with the directions the pre-filters leave open: it is
     forward-viable when the partner may be the schema of the new term, and
     reverse-viable when the new term may be the schema of the partner.  A
     candidate viable in neither direction cannot match either way, so it is
     dropped before the candidate cap and before the attempt counter. *)
  (* The buckets are walked entry by entry and the walk stops at whichever of
     the two caps it reaches first, so the caps bound the cost of the lookup
     itself: a bucket is the whole set of entries containing one constant and
     grows with the translation, so concatenating and filtering every bucket
     before capping would be unbounded work, and so would walking past
     unboundedly many entries which the pre-filters reject before they can
     count against the candidate cap.  The constant-free list is capped at
     registration and is pre-filtered by tag as a whole.  Order is the one the
     concatenation gave: the buckets of the query's constants in order, then
     the constant-free entries. *)
  let buckets =
    List.map
      (fun c -> try Hashtbl.find reg.lr_index (tag, c) with Not_found -> [])
      consts @
    [List.filter (fun e -> top_tag e.le_tm = tag) reg.lr_noconst]
  in
  let acc = ref [] in
  let acc_len = ref 0 in
  let examined = ref 0 in
  let truncated = ref false in
  let rec collect buckets =
    match buckets with
    | [] -> ()
    | [] :: bs -> collect bs
    | (e :: es) :: bs ->
      if !acc_len >= max_match_candidates || !examined >= max_examined_entries then
        (* entries are left unexamined: neither the number of viable candidates
           nor the number of rejects is known *)
        truncated := true
      else
        begin
          (* every entry the walk reaches costs a [seen] probe and, for a fresh
             one, the self-exclusion test and the pre-filters, so the entries
             which never become candidates are counted too *)
          incr examined;
          if not (Hashtbl.mem seen e.le_name || (e.le_ctx = cctx && e.le_tm = ctm))
          then
            begin
              Hashtbl.add seen e.le_name ();
              let fwd = e.le_size <= size && is_subset e.le_consts consts
              and rev = size <= e.le_size && is_subset consts e.le_consts in
              if fwd || rev then
                begin
                  acc := (e, fwd, rev) :: !acc;
                  incr acc_len
                end
              else
                incr filtered
            end;
          collect (es :: bs)
        end
  in
  collect buckets;
  let truncated = !truncated in
  if truncated then
    log 1 ("hashing: more indexed " ^ kind ^ " lifts than one lookup examines; " ^
           "stopped at " ^ string_of_int !acc_len ^ " viable candidate(s) in " ^
           string_of_int !examined ^ " entries (caps " ^
           string_of_int max_match_candidates ^ " and " ^
           string_of_int max_examined_entries ^ ")");
  let candidates = List.rev !acc in
  let attempts = ref 0 in
  let mk_link e new_is_schema subst =
    { ll_name = e.le_name; ll_ctx = e.le_ctx; ll_tm = e.le_tm;
      ll_new_is_schema = new_is_schema; ll_subst = subst }
  in
  (* Prefer the direction in which the partner is the more general term. *)
  let rev_link = ref None in
  let rec scan lst =
    match lst with
    | [] -> !rev_link
    | (e, fwd, rev) :: t ->
      let link =
        if fwd then
          begin
            incr attempts;
            match match_instance e.le_ctx e.le_tm cctx ctm with
            | Some subst when not (is_identity_subst (List.length cctx) subst) ->
              Some (mk_link e false subst)
            | _ -> None
          end
        else
          None
      in
      match link with
      | Some _ -> link
      | None ->
        if rev && !rev_link = None then
          begin
            incr attempts;
            match match_instance cctx ctm e.le_ctx e.le_tm with
            | Some subst when not (is_identity_subst (List.length e.le_ctx) subst) ->
              rev_link := Some (mk_link e true subst)
            | _ -> ()
          end;
        scan t
  in
  let link = scan candidates in
  let cnt = reg.lr_counters in
  reg.lr_counters <-
    { cnt with
      lc_queried = cnt.lc_queried + 1;
      lc_attempts = cnt.lc_attempts + !attempts;
      lc_filtered = cnt.lc_filtered + !filtered;
      lc_truncated = cnt.lc_truncated + (if truncated then 1 else 0);
      lc_linked_fwd =
        cnt.lc_linked_fwd +
          (match link with Some l when not l.ll_new_is_schema -> 1 | _ -> 0);
      lc_linked_rev =
        cnt.lc_linked_rev +
          (match link with Some l when l.ll_new_is_schema -> 1 | _ -> 0) };
  link

(* The counters accumulate over the whole process for the diagnostic; only
   [reset_counters] clears them. *)
let clear_lifts () =
  Hashtbl.iter
    begin fun _ reg ->
      Hashtbl.clear reg.lr_index;
      reg.lr_noconst <- [];
      reg.lr_noconst_len <- 0
    end
    registries

let counters kind =
  try (Hashtbl.find registries kind).lr_counters with Not_found -> zero_counters

let all_counters () =
  List.sort (fun (k1, _) (k2, _) -> String.compare k1 k2)
    (Hashtbl.fold (fun kind reg acc -> (kind, reg.lr_counters) :: acc) registries [])

let reset_counters () =
  Hashtbl.iter (fun _ reg -> reg.lr_counters <- zero_counters) registries

(***************************************************************************************)

type 'a lift_fun = (coqterm -> coqterm) -> 'a -> 'a
type 'a coqterms_hash =
  (string * coqcontext * coqterm, 'a) Hashtbl.t * ('a lift_fun * ('a -> 'a))

type canonical_key = {
  ck_ctx : coqcontext;
  ck_tm : coqterm;
  ck_revsigma : namesubst;
}

let create ?(compact = fun x -> x) lift =
  (Hashtbl.create 128, (lift, compact))

(* The lift registry mirrors the entries of the lift table, so it is emptied
   with the table: an entry surviving into the next translation would link a
   fresh lift to a symbol that no longer exists.  There is exactly one
   [coqterms_hash] in the plugin (Coq_transl.coqterm_hash, cleared by
   Coq_transl.cleanup), so this is also the lifecycle point the registry
   needs. *)
let clear tbl =
  Hashtbl.clear (fst tbl);
  clear_lifts ()

(* Hash-table keys must only be made here.  [get_fvars] silently keeps only the
   free variables the context binds, so canonicalizing an escaped variable
   against a short context could capture it under a fresh canonical binder.
   Keeping the checked result abstract prevents direct-hit paths from
   duplicating, or accidentally omitting, this invariant. *)
let check_key_scope ctx tm =
  let escaped =
    List.filter (fun name -> not (List.mem_assoc name ctx)) (get_free_varnames tm)
  in
  if escaped <> [] then
    raise (Hammer_errors.HammerError
             ("internal translation error: free variables " ^
              String.concat ", " escaped ^ " escape the context of " ^
              string_of_coqterm tm))

let canonical_key ctx tm =
  check_key_scope ctx tm;
  let ctx' = vars_to_ctx (get_fvars ctx tm) in
  let (cctx, ctm, sigma) = canonical ctx' tm in
  debug 4 begin fun () ->
    print_header "canonical (result)" ctm cctx;
    print_list (fun (x, y) -> print_string ("(" ^ x ^ "," ^ y ^ ")")) sigma
  end;
  { ck_ctx = cctx; ck_tm = ctm;
    ck_revsigma = List.map (fun (x, y) -> (y, x)) sigma }

let canonical_pair_key cctx ctm =
  check_key_scope cctx ctm;
  { ck_ctx = cctx; ck_tm = ctm; ck_revsigma = [] }

let key_context key = key.ck_ctx
let key_term key = key.ck_tm

let find_key name tbl key =
  Hashtbl.find_opt (fst tbl) (name, key.ck_ctx, key.ck_tm)

let lift_key tbl key value =
  let (_, (lift, _)) = tbl in
  lift (subs key.ck_revsigma) value

let find_or_insert_key name tbl key mk =
  let (table, (_, compact)) = tbl in
  let value =
    match Hashtbl.find_opt table (name, key.ck_ctx, key.ck_tm) with
    | Some value -> value
    | None ->
       let value = compact (mk key.ck_ctx key.ck_tm) in
       Hashtbl.add table (name, key.ck_ctx, key.ck_tm) value;
       value
  in
  lift_key tbl key value

let insert_key name tbl key value =
  let (table, (_, compact)) = tbl in
  Hashtbl.replace table (name, key.ck_ctx, key.ck_tm) (compact value)

let find_or_insert_keyed name tbl ctx tm mk =
  debug 4 (fun () -> print_header "find_or_insert" tm ctx);
  find_or_insert_key name tbl (canonical_key ctx tm) mk

let find_or_insert tbl ctx tm mk =
  find_or_insert_keyed "" tbl ctx tm mk
