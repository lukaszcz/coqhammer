(* Tests for the instance matcher and the lift registry in Hashing.

   A link equation between two lifted symbols is justified only by "both names
   are images of one Coq term", so a wrong match is a direct unsoundness.  The
   negative cases below (capture, inconsistent repeated pattern variables,
   binder-depth and arity mismatches, confusable canonical numbering) are the
   soundness cases; the positive ones pin the substitution the translator will
   substitute into the equation. *)

open Coqterms

let failures = ref 0

let report label expected actual =
  incr failures;
  Printf.eprintf "FAIL %s: expected %s, got %s\n" label expected actual

let show_subst s =
  match s with
  | None -> "None"
  | Some l -> "[" ^ String.concat "; " (List.map string_of_coqterm l) ^ "]"

let check_subst label expected actual =
  if expected <> actual then
    report label (show_subst expected) (show_subst actual)

let check_int label expected actual =
  if expected <> actual then
    report label (string_of_int expected) (string_of_int actual)

let check_bool label expected actual =
  if expected <> actual then
    report label (string_of_bool expected) (string_of_bool actual)

let check_hammer_error label make =
  try
    ignore (make ());
    report label "HammerError" "success"
  with Hammer_lib.Hammer_errors.HammerError _ -> ()

(* A same-name replay is valid only for the same formula.  Exercise the shared
   merge path directly so a collision cannot again be hidden independently by
   cache compaction, declaration translation, or final-theory composition. *)
let () =
  let a = ("collision", Const "a") in
  check_int "identical axiom replay deduplicates" 1
    (List.length (compose_axioms [[a]; [a]]));
  check_hammer_error "different-formula axiom collision rejects"
    (fun () -> compose_axioms [[a]; [("collision", Const "b")]])

(* canonical variable names; a canonical context lists its variables in reverse
   canonical order (Coqterms.ctx_to_vars = List.rev) *)
let v i = "v_CANONICAL_" ^ string_of_int i
let mk_ctx tys = List.rev (List.mapi (fun j ty -> (v j, ty)) tys)

(***************************************************************************************)
(* Positive cases *)

(* The plan's motivating pair: [forall X Y, ... (g : X -> Y)] against the same
   type over section constants. *)
let () =
  check_subst "arrow schema over constants"
    (Some [Const "X"; Const "Y"])
    (Hashing.match_instance
       (mk_ctx [SortType; SortType]) (Prod(v 2, Var(v 0), Var(v 1)))
       [] (Prod(v 0, Const "X", Const "Y")))

(* A dependent product: the codomain applies a pattern variable to the bound
   variable. *)
let () =
  check_subst "dependent product"
    (Some [Const "A"; Const "P"])
    (Hashing.match_instance
       (mk_ctx [SortType; mk_fun_ty (Var(v 0)) SortType])
       (Prod(v 2, Var(v 0), App(Var(v 1), Var(v 2))))
       [] (Prod(v 0, Const "A", App(Const "P", Var(v 0)))))

let () =
  check_subst "repeated pattern variable"
    (Some [Const "A"])
    (Hashing.match_instance
       (mk_ctx [SortType]) (Prod(v 1, Var(v 0), Var(v 0)))
       [] (Prod(v 0, Const "A", Const "A")))

(* [v0] does not occur in the schema term at all -- [get_fvars] kept it because
   it occurs in the type of [v1].  Only the context-type fixpoint can bind it. *)
let () =
  check_subst "pattern variable from the context type"
    (Some [Const "nat"; Var(v 0)])
    (Hashing.match_instance
       (mk_ctx [SortType; Var(v 0)]) (App(Const "f", Var(v 1)))
       (mk_ctx [Const "nat"]) (App(Const "f", Var(v 0))))

(* The instance is itself a schema: both contexts are non-empty and the images
   live in the instance's context. *)
let () =
  check_subst "instance is itself a schema"
    (Some [Var(v 0); Const "Y"])
    (Hashing.match_instance
       (mk_ctx [SortType; SortType]) (Prod(v 2, Var(v 0), Var(v 1)))
       (mk_ctx [SortType]) (Prod(v 1, Var(v 0), Const "Y")))

(* The schema's inner binder is [v_CANONICAL_2] and the instance's context
   binds a variable of that very name; here the instance's codomain refers to
   its own binder, so the match must succeed. *)
let () =
  check_subst "confusable numbering, genuine binder"
    (Some [Var(v 0); Const "P"])
    (Hashing.match_instance
       (mk_ctx [SortType; mk_fun_ty (Var(v 0)) SortType])
       (Prod(v 2, Var(v 0), App(Var(v 1), Var(v 2))))
       (mk_ctx [SortType; SortType; SortType])
       (Prod(v 3, Var(v 0), App(Const "P", Var(v 3)))))

(***************************************************************************************)
(* Negative cases *)

(* Capture: the image of [v0] would be the variable bound by the instance's own
   product, so the equation the caller emits would be ill-scoped. *)
let () =
  check_subst "capture rejected" None
    (Hashing.match_instance
       (mk_ctx [SortType]) (Prod(v 1, Const "A", Var(v 0)))
       [] (Prod(v 0, Const "A", Var(v 0))))

(* An instance term with a free variable its own context does not bind.  The
   capture test above covers escape from a binder inside [ctm_i]; this covers
   escape from [cctx_i] itself, which no binder in either term accounts for.
   [canonical] renames the context it is handed rather than deriving it from
   the term, so a caller can produce this pair, and the equation it would close
   over [cctx_i] would leave [z] free. *)
let () =
  check_subst "image escaping the instance context rejected" None
    (Hashing.match_instance
       (mk_ctx [SortType]) (Prod(v 1, Const "A", Var(v 0)))
       [] (Prod(v 0, Const "A", Var "z")))

(* The same instance term against a context which does bind it: the image is
   well-scoped and the match stands, so it is the scope check and not the shape
   of the term that rejected the pair above. *)
let () =
  check_subst "image bound by the instance context accepted"
    (Some [Var "z"])
    (Hashing.match_instance
       (mk_ctx [SortType]) (Prod(v 1, Const "A", Var(v 0)))
       ["z", SortType] (Prod(v 0, Const "A", Var "z")))

let () =
  check_subst "inconsistent repeated pattern variable" None
    (Hashing.match_instance
       (mk_ctx [SortType]) (Prod(v 1, Var(v 0), Var(v 0)))
       [] (Prod(v 0, Const "A", Const "B")))

let () =
  check_subst "differing recargs" None
    (Hashing.match_instance
       (mk_ctx [SortType]) (Fix(CoqFix, 0, [0], ["f"], [Var(v 0)], [Const "b"]))
       [] (Fix(CoqFix, 0, [1], ["f"], [Const "T"], [Const "b"])))

let () =
  check_subst "differing branch arities" None
    (Hashing.match_instance
       (mk_ctx [SortType]) (Case("I", Var(v 0), Const "r", Const "r", 0, [(1, Const "b")]))
       [] (Case("I", Const "T", Const "r", Const "r", 0, [(2, Const "b")])))

let () =
  check_subst "differing quantifier" None
    (Hashing.match_instance
       (mk_ctx [SortType]) (Quant("!", (v 1, Var(v 0), Const "$True")))
       [] (Quant("?", (v 0, Const "A", Const "$True"))))

let () =
  check_subst "differing constant heads" None
    (Hashing.match_instance
       (mk_ctx [SortType]) (App(Const "f", Var(v 0)))
       [] (App(Const "g", Const "A")))

let () =
  check_subst "bare pattern variable schema" None
    (Hashing.match_instance (mk_ctx [SortType]) (Var(v 0)) [] (Const "A"))

(* The schema's inner binder [v_CANONICAL_2] must not be confused with the
   instance context's variable of the same name: the instance's codomain refers
   to the context variable, not to the bound one. *)
let () =
  check_subst "confusable numbering, context variable" None
    (Hashing.match_instance
       (mk_ctx [SortType; mk_fun_ty (Var(v 0)) SortType])
       (Prod(v 2, Var(v 0), App(Var(v 1), Var(v 2))))
       (mk_ctx [SortType; SortType; SortType])
       (Prod(v 3, Var(v 0), App(Const "P", Var(v 2)))))

(* A pattern variable left unbound by both the term traversal and the
   context-type fixpoint yields no substitution. *)
let () =
  check_subst "unresolved pattern variable" None
    (Hashing.match_instance
       (mk_ctx [SortType; SortType]) (App(Const "f", Var(v 1)))
       [] (App(Const "f", Const "A")))

(***************************************************************************************)
(* The registry *)

(* [list A -> list B] as a schema over its two arguments, and one instance. *)
let list_schema_ctx = mk_ctx [SortType; SortType]
let list_schema =
  Prod(v 2, App(Const "list", Var(v 0)), App(Const "list", Var(v 1)))
let list_instance =
  Prod(v 0, App(Const "list", Const "X"), App(Const "list", Const "Y"))

let () =
  Hashing.clear_lifts ();
  Hashing.register_lift "type" "$_type_1077" list_schema_ctx list_schema;
  match Hashing.find_lift_link "type" [] list_instance with
  | None -> report "link to a registered schema" "a link" "None"
  | Some l ->
    check_bool "link to a registered schema: direction" false l.Hashing.ll_new_is_schema;
    check_subst "link to a registered schema: subst"
      (Some [Const "X"; Const "Y"]) (Some l.Hashing.ll_subst);
    if l.Hashing.ll_name <> "$_type_1077" then
      report "link to a registered schema: name" "$_type_1077" l.Hashing.ll_name

let () =
  Hashing.clear_lifts ();
  Hashing.register_lift "type" "$_type_44" [] list_instance;
  match Hashing.find_lift_link "type" list_schema_ctx list_schema with
  | None -> report "link to a registered instance" "a link" "None"
  | Some l ->
    check_bool "link to a registered instance: direction" true l.Hashing.ll_new_is_schema;
    check_subst "link to a registered instance: subst"
      (Some [Const "X"; Const "Y"]) (Some l.Hashing.ll_subst);
    check_int "link to a registered instance: partner context" 0
      (List.length l.Hashing.ll_ctx)

(* An alpha-equal partner says nothing. *)
let () =
  Hashing.clear_lifts ();
  Hashing.register_lift "type" "$_type_1077" list_schema_ctx list_schema;
  check_bool "alpha-equal partner is not a link" true
    (Hashing.find_lift_link "type" list_schema_ctx list_schema = None)

(* Lifts of different kinds are never linked. *)
let () =
  Hashing.clear_lifts ();
  Hashing.register_lift "type" "$_type_1077" list_schema_ctx list_schema;
  check_bool "kinds do not link" true
    (Hashing.find_lift_link "lam" [] list_instance = None)

(* Clearing drops the entries but keeps the counters. *)
let () =
  Hashing.clear_lifts ();
  let registered = (Hashing.counters "type").Hashing.lc_registered in
  Hashing.register_lift "type" "$_type_2" list_schema_ctx list_schema;
  Hashing.clear_lifts ();
  check_int "clear_lifts keeps the counters" (registered + 1)
    (Hashing.counters "type").Hashing.lc_registered;
  check_bool "clear_lifts drops the entries" true
    (Hashing.find_lift_link "type" [] list_instance = None)

(***************************************************************************************)
(* The pre-filters *)

(* A partner sharing a constant with the query sits in a probed bucket, but its
   own constants are not included in the query's: it can be neither a schema
   nor an instance of the query, so it must be dropped without an attempt. *)
let () =
  Hashing.clear_lifts ();
  Hashing.register_lift "filter" "$_type_f1" [] (App(Const "f", Const "extra"));
  check_bool "constants not a subset: no link" true
    (Hashing.find_lift_link "filter" [] (App(Const "f", Const "z")) = None);
  check_int "constants not a subset: filtered" 1
    (Hashing.counters "filter").Hashing.lc_filtered;
  check_int "constants not a subset: not attempted" 0
    (Hashing.counters "filter").Hashing.lc_attempts

(* [f (g a)] is larger than the query [f v0], so it cannot be a schema of it,
   but the query is a schema of it.  An inverted size comparison would attempt
   the forward direction, skip the reverse one and lose the link. *)
let () =
  Hashing.clear_lifts ();
  Hashing.register_lift "size" "$_type_s1" []
    (App(Const "f", App(Const "g", Const "a")));
  begin match
    Hashing.find_lift_link "size" (mk_ctx [SortType]) (App(Const "f", Var(v 0)))
  with
  | None -> report "larger partner is an instance" "a link" "None"
  | Some l ->
    check_bool "larger partner is an instance: direction" true
      l.Hashing.ll_new_is_schema;
    check_subst "larger partner is an instance: subst"
      (Some [App(Const "g", Const "a")]) (Some l.Hashing.ll_subst)
  end;
  (* only the reverse direction is viable, so only it is attempted *)
  check_int "larger partner is an instance: one attempt" 1
    (Hashing.counters "size").Hashing.lc_attempts;
  check_int "larger partner is an instance: nothing filtered" 0
    (Hashing.counters "size").Hashing.lc_filtered

(* A constant-free entry passes the subset test against every query, so it
   still links to an instance which does contain constants. *)
let () =
  Hashing.clear_lifts ();
  Hashing.register_lift "nocst" "$_type_nc" (mk_ctx [SortType])
    (Prod(v 1, Var(v 0), Var(v 0)));
  begin match Hashing.find_lift_link "nocst" [] (Prod(v 0, Const "A", Const "A")) with
  | None -> report "constant-free schema links" "a link" "None"
  | Some l ->
    check_bool "constant-free schema links: direction" false
      l.Hashing.ll_new_is_schema;
    check_subst "constant-free schema links: subst"
      (Some [Const "A"]) (Some l.Hashing.ll_subst)
  end;
  check_int "constant-free schema links: nothing filtered" 0
    (Hashing.counters "nocst").Hashing.lc_filtered

(* More candidates in one bucket than the per-call cap.  The candidates have to
   pass the pre-filters to reach the cap, so they carry exactly the query's
   constants and its size while differing from it structurally. *)
let () =
  Hashing.clear_lifts ();
  for i = 0 to 70 do
    Hashing.register_lift "cap" ("$_type_cap_" ^ string_of_int i) []
      (App(App(Const "c", Const "k"), Const "k"))
  done;
  ignore (Hashing.find_lift_link "cap" [] (App(Const "c", App(Const "k", Const "k"))));
  check_int "candidate cap counted" 1 (Hashing.counters "cap").Hashing.lc_truncated;
  check_int "candidate cap: nothing filtered" 0
    (Hashing.counters "cap").Hashing.lc_filtered;
  (* no candidate matches in either direction and both are viable, so both are
     attempted on each of the 64 candidates examined *)
  check_int "candidate cap honoured" 128 (Hashing.counters "cap").Hashing.lc_attempts

(* Entries the pre-filters reject never become candidates, so the candidate cap
   alone would let a bucket of them be walked in full.  The walk is bounded by
   the entries it examines as well: 512 of the 600 rejects here are looked at,
   and the partner registered before them -- entries are prepended, so it is
   last in the bucket -- is never reached. *)
let mk_reject i = App(Const "shared", Const ("d_" ^ string_of_int i))
let walk_query = App(Const "shared", Const "q")
let walk_schema_ctx = mk_ctx [SortType]
let walk_schema = App(Const "shared", Var(v 0))

let () =
  Hashing.clear_lifts ();
  Hashing.register_lift "walk" "$_type_walk_schema" walk_schema_ctx walk_schema;
  for i = 0 to 599 do
    Hashing.register_lift "walk" ("$_type_walk_" ^ string_of_int i) [] (mk_reject i)
  done;
  check_bool "examined cap: partner out of reach" true
    (Hashing.find_lift_link "walk" [] walk_query = None);
  check_int "examined cap: rejects examined" 512
    (Hashing.counters "walk").Hashing.lc_filtered;
  check_int "examined cap counted" 1 (Hashing.counters "walk").Hashing.lc_truncated;
  check_int "examined cap: nothing attempted" 0
    (Hashing.counters "walk").Hashing.lc_attempts

(* The same partner behind a stretch of rejects the walk does get through: it is
   the bound that loses the link above, not the pre-filters. *)
let () =
  Hashing.clear_lifts ();
  Hashing.register_lift "walk2" "$_type_walk2_schema" walk_schema_ctx walk_schema;
  for i = 0 to 99 do
    Hashing.register_lift "walk2" ("$_type_walk2_" ^ string_of_int i) [] (mk_reject i)
  done;
  begin match Hashing.find_lift_link "walk2" [] walk_query with
  | None -> report "partner behind rejects" "a link" "None"
  | Some l ->
    check_bool "partner behind rejects: direction" false l.Hashing.ll_new_is_schema;
    check_subst "partner behind rejects: subst"
      (Some [Const "q"]) (Some l.Hashing.ll_subst)
  end;
  check_int "partner behind rejects: nothing truncated" 0
    (Hashing.counters "walk2").Hashing.lc_truncated

(* Context types are part of an alpha-canonical cache key too.  Rocq gives
   anonymous product binders fresh names in each declaration; leaving those
   names raw makes exact hits (and therefore owner-bundle replay) depend on
   declaration order. *)
let () =
  let made = ref 0 in
  let table = Hashing.create (fun _ x -> x) in
  let context binder =
    [ ("f", Prod(binder, Var "Z", Var "Z")); ("Z", SortType) ]
  in
  let term = Lam("x", Var "Z", App(Var "f", Var "x")) in
  let make _ _ = incr made; !made in
  check_int "context-type alpha cache first value" 1
    (Hashing.find_or_insert table (context "anon1") term make);
  check_int "context-type alpha cache exact hit" 1
    (Hashing.find_or_insert table (context "anon2") term make);
  check_int "context-type alpha cache made once" 1 !made

(* Entries with no constant at all are capped in number. *)
let () =
  Hashing.clear_lifts ();
  for i = 0 to 300 do
    Hashing.register_lift "noconst" ("$_type_nc_" ^ string_of_int i)
      (mk_ctx [SortType]) (Prod(v 1, Var(v 0), SortType))
  done;
  check_int "constant-free entries capped" (301 - 256)
    (Hashing.counters "noconst").Hashing.lc_noconst_dropped

let () =
  if !failures > 0 then
    begin
      Printf.eprintf "%d hashing instance-match check(s) failed\n" !failures;
      exit 1
    end
  else
    print_endline "hashing instance-match checks passed"
