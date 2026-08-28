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

(* Cached translations use a difference list for their side axioms.  Leaving
   that composition unevaluated retains a shared expression DAG; repeated
   instance reuse can expand it many times when the enclosing declaration is
   finally extracted.  Freeze and validate each cache miss once. *)
let compact_axioms (tm, mk) =
  let axioms = compose_axioms [mk []] in
  (* [axioms @ []] is [axioms], so serving the empty tail without copying lets
     [extract_axioms] read a compacted bundle in constant time.  Cached bundles
     are extracted whole on every replay, which would otherwise allocate a
     throwaway copy of the entire axiom list per cache hit. *)
  (tm, fun tail -> if tail == [] then axioms else axioms @ tail)

let coqterm_hash = Hashing.create ~compact:compact_axioms lift

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
  let mem owner indname = List.mem indname (find owner)
  let remove owner = Hashtbl.remove table owner
end

(* Hash-consed lifts replay their exact case dependencies on cache hits.  A
   scoped collector records dependencies while constructing a cache miss;
   nested lifts propagate their dependencies to the enclosing cached lift. *)
module Lift_owners = struct
  (* Availability belongs to a (symbol, declaration) pair.  One cached lift may
     be replayed into several declarations; recording only its last owner makes
     schema reuse depend on which declaration happened to be translated last.

     The table is keyed by owner and holds that owner's symbol set, so
     [remove_def] can drop one declaration's whole ownership in one step: the
     [remove_def] + [reinit] diagnostics keep the translation caches, and an
     ownership pair surviving a re-declaration would authorize schema reuse
     that a fresh process would not perform. *)
  let table : (string, (string, unit) Hashtbl.t) Hashtbl.t = Hashtbl.create 128
  let clear () = Hashtbl.clear table
  let add name owner =
    if owner <> "" then
      let symbols =
        match Hashtbl.find_opt table owner with
        | Some symbols -> symbols
        | None ->
           let symbols = Hashtbl.create 16 in
           Hashtbl.add table owner symbols;
           symbols
      in
      Hashtbl.replace symbols name ()
  let mem name owner =
    match Hashtbl.find_opt table owner with
    | Some symbols -> Hashtbl.mem symbols name
    | None -> false
  let remove owner = Hashtbl.remove table owner
end

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

(* Translation normally records ownership and structural delivery eagerly.
   Schema applications are exceptional: their translated arity decides whether
   they may be used at all.  Capture these side effects while checking such an
   application, then either commit all of them with its axiom bundle or discard
   all of them on fallback. *)
module Translation_effects = struct
  type delivery =
    | Case_dependency of string * string
    | Lift_owner of string * string

  let collectors = ref []

  let is_applied = function
    | Case_dependency(owner, indname) -> Case_dependencies.mem owner indname
    | Lift_owner(name, owner) -> Lift_owners.mem name owner

  let apply = function
    | Case_dependency(owner, indname) -> Case_dependencies.add owner indname
    | Lift_owner(name, owner) -> Lift_owners.add name owner

  let record delivery =
    match !collectors with
    | effects :: _ -> effects := (delivery, is_applied delivery) :: !effects
    | [] -> apply delivery

  let case_dependency owner indname =
    if owner <> "" then record (Case_dependency(owner, indname))

  let lift_owner name owner =
    if owner <> "" then record (Lift_owner(name, owner))

  let capture make =
    let effects = ref [] in
    let previous = !collectors in
    collectors := effects :: previous;
    let result =
      Fun.protect ~finally:(fun () -> collectors := previous) make
    in
    (result, List.rev !effects)

  let commit effects = List.iter (fun (delivery, _) -> record delivery) effects

  let unchanged effects =
    List.for_all
      (fun (delivery, was_applied) -> is_applied delivery = was_applied)
      effects
end

(* [make] sets [reuses_lift] when the value it returns reuses a lift symbol
   that is already registered -- a replayed cache entry, or a schema applied to
   a matching substitution -- instead of minting one of its own.  The
   distinction decides who owns the structural theory collected while [make]
   ran.  When a lift is minted, those dependencies are properties of the lifted
   term itself and belong to the new symbol permanently.  When a symbol is
   reused they are properties of THIS occurrence only -- typically of
   converting the substitution arguments -- and attaching them to the shared
   symbol would deliver inversion and discrimination theory for inductives the
   symbol never inspects to every later user of it.

   Either way the occurrence itself needs the union of the symbol's recorded
   theory and its own dependencies; in the minting case [add] followed by
   [find] computes exactly that union, so one expression serves both and only
   the [add] is suppressed on reuse. *)
let with_lift_dependencies ?reuses_lift make =
  let dependencies = ref [] in
  let previous_collectors = !(Lift_dependencies.collectors) in
  Lift_dependencies.collectors := dependencies :: previous_collectors;
  let result =
    Fun.protect
      ~finally:(fun () -> Lift_dependencies.collectors := previous_collectors)
      make
  in
  let reused =
    match reuses_lift with
    | Some flag -> !flag
    | None -> false
  in
  let delivered =
    match flatten_app (fst result) with
    | Const name, _
         when String.length name >= 2 && String.sub name 0 2 = "$_" ->
       if reused then
         Hhlib.sort_uniq String.compare
           (!dependencies @ Lift_dependencies.find name)
       else begin
         (* [add] stores the sorted union with what the symbol already had, and
            nothing else writes the table, so its entry is already the union
            this occurrence must deliver. *)
         if !dependencies <> [] then
           Lift_dependencies.add name !dependencies;
         Lift_dependencies.find name
       end
    | _ -> Hhlib.sort_uniq String.compare !dependencies
  in
  List.iter
    (fun dependency ->
       Translation_effects.case_dependency !translation_owner dependency;
       Lift_dependencies.record dependency)
    delivered;
  result

(* Isolate both dependency propagation and eager ownership effects while a
   translated candidate is being validated.  Cache metadata created during the
   attempt remains valid and reusable, but no declaration is said to contain
   that metadata until [commit_speculation] accompanies a retained result. *)
let speculate_translation make =
  let dependencies = ref [] in
  let previous_collectors = !(Lift_dependencies.collectors) in
  Lift_dependencies.collectors := [dependencies];
  let (result, effects) =
    Fun.protect
      ~finally:(fun () -> Lift_dependencies.collectors := previous_collectors)
      (fun () -> Translation_effects.capture make)
  in
  (result, Hhlib.sort_uniq String.compare !dependencies, effects)

let discarded_speculations = ref 0
let discarded_speculation_effects = ref 0

let discard_speculation dependencies effects =
  if not (Translation_effects.unchanged effects) then
    raise (Hammer_errors.HammerError
             "internal translation error: rejected schema candidate leaked effects");
  let count = List.length dependencies + List.length effects in
  if count > 0 then begin
    incr discarded_speculations;
    discarded_speculation_effects := !discarded_speculation_effects + count
  end

let speculation_stats () =
  (!discarded_speculations, !discarded_speculation_effects)

let commit_speculation dependencies effects =
  Translation_effects.commit effects;
  List.iter Lift_dependencies.record dependencies

(* A lift symbol as [Hashing.register_lift]/[Hashing.find_lift_link] mint it:
   a kind prefix followed by a [unique_id] of digits.  Axioms derived from a
   lift's definition append a [$]-separated suffix ([$term], [$lower],
   [$upper], [$link], [$<constructor>]), so the defining symbol is the axiom
   name truncated at the first [$] after the prefix.  Only the kinds that emit
   link equations are recognized: they are the ones whose symbols a later
   occurrence can be offered for reuse, which is what ownership decides.  Of
   those, [Lift_owners] is today queried for lambda lifts only. *)
let defined_lift_symbol axname =
  let matches prefix =
    Hhlib.string_begins_with axname prefix &&
    String.length axname > String.length prefix
  in
  let prefix =
    if matches "$_lam_" then Some "$_lam_"
    else if matches "$_type_" then Some "$_type_"
    else None
  in
  match prefix with
  | None -> None
  | Some prefix ->
     let start = String.length prefix in
     let stop =
       try String.index_from axname start '$' with Not_found -> String.length axname
     in
     if stop = start then None else Some (String.sub axname 0 stop)

(* Replaying a cached bundle into a declaration makes available not only its
   head symbol but the definition axioms of every lift nested inside it, so
   every symbol the bundle defines is owned by the current declaration.
   Without this a later instance of a nested lift is refused reuse and mints a
   duplicate symbol plus a link equation -- sound, but it defeats the sharing.
   Costs one O(bundle) pass over the axiom list per cache hit. *)
let record_bundle_owners value =
  List.iter
    (fun (axname, _) ->
       match defined_lift_symbol axname with
       | Some name -> Translation_effects.lift_owner name !translation_owner
       | None -> ())
    (extract_axioms value)

(***************************************************************************************)
(* Lift-sharing diagnostic *)

(* Lifting mints one symbol per occurrence shape, so one Coq object reached at
   two shapes gets two unrelated names and nothing in the problem relates them.
   Whether sharing those lifts across instantiation is worth its risk is a
   question about corpora, and these counters answer it: they report how many
   symbols each lift kind mints and how many of them an instance match would
   relate, without emitting anything.  Behind COQHAMMER_LIFT_STATS, so a
   default build neither counts nor pays for the matching. *)

let () =
  Lift_stats.add_source
    begin fun () ->
      List.concat_map
        begin fun (kind, c) ->
          let open Hashing in
          List.map (fun (field, n) -> ("hash." ^ kind ^ "." ^ field, n))
            [ ("registered", c.lc_registered); ("queried", c.lc_queried);
              ("linked_fwd", c.lc_linked_fwd); ("linked_rev", c.lc_linked_rev);
              ("attempts", c.lc_attempts); ("filtered", c.lc_filtered);
              ("truncated", c.lc_truncated);
              ("noconst_dropped", c.lc_noconst_dropped) ]
        end
        (Hashing.all_counters ())
    end

let count_lift kind field =
  if Lift_stats.enabled () then Lift_stats.count (kind ^ "." ^ field)

(* [<kind>.minted] counts every symbol the kind mints and the outcome fields
   partition it.  [remove_lambda] adds a fifth outcome, [unnamed], for a lift
   which does not name itself and so neither registers nor links: folding those
   into [unlinked] would report a missing partner where there is no name to
   link one to. *)
let link_outcome link =
  match link with
  | Some l when l.Hashing.ll_new_is_schema -> "linked_rev"
  | Some _ -> "linked_fwd"
  | None -> "unlinked"

(* Looks for a lift this one is related to by instantiation, registers this
   lift, and returns the link so the caller can emit its equation.  Called
   exactly once per minted symbol: registering twice would make a lift a
   candidate partner of itself under a second name. *)
let link_lift kind name cctx ctm =
  let link = Hashing.find_lift_link kind cctx ctm in
  count_lift kind "minted";
  count_lift kind (link_outcome link);
  Hashing.register_lift kind name cctx ctm;
  link

(* Type and lambda lifts link unconditionally: the equation they emit needs the
   registry whether or not the diagnostic is on.  The kinds which do not emit
   link equations yet register only for the diagnostic, so a default build pays
   nothing for them. *)
let record_lift_stats kind name cctx ctm =
  if Lift_stats.enabled () then ignore (link_lift kind name cctx ctm)

(* Stage 2 of the plan would translate a dependent product as
   [$_prod(A, F)], and its codomain object [F] is canonical only when
   [fun x : A => B] eta-contracts to a term not mentioning [x].  Separating the
   two shapes is what decides whether that stage is worth writing. *)
let codomain_eta_contracts vname ty =
  match ty with
  | App(cod, Var(x)) when x = vname -> not (var_occurs vname cod)
  | _ -> false

let record_type_lift_shape eligible cctx cty =
  if Lift_stats.enabled () then
    let shape =
      if eligible then
        (* translated structurally as [$_arrow], so no name is minted *)
        "arrow"
      else
        match cty with
        | Prod(vname, ty1, ty2) ->
           if (try Coq_typing.check_prop cctx ty1 with _ -> false) then
             "prop_domain"
           else if not (var_occurs vname ty2) then
             (* a non-dependent non-Prop-domain product which the eligibility
                test nevertheless rejected: a canary, expected to stay at 0 *)
             "nondep_other"
           else if codomain_eta_contracts vname ty2 then
             "dep_eta"
           else
             "dep_noneta"
        | _ ->
           "other"
    in
    Lift_stats.count ("type.shape." ^ shape)

(* A structural former identifies a type by its *translated* parts, so two Coq
   types differing only in erased content share one object -- [T eq_refl -> nat]
   and [T q -> nat] with [q] an erased proof variable are both
   [$_arrow(cT, cnat)] -- while [guard_leaf] may classify only one of them as a
   refinement.  One object then carries two different unfolding axioms.  That is
   not unsound: every identification [convert] makes is an equality valid under
   proof irrelevance, so the several guards are simultaneously true of the same
   object.  What it does mean is that sharing propagates any per-type guard bug
   to every occurrence, so census how often the guards actually differ.  Nothing
   emitted changes. *)
let type_unfolding_hash : (coqterm, coqterm) Hashtbl.t = Hashtbl.create 128

(* Every binder of an unfolding axiom is minted fresh -- the subject variable
   and, through [make_guard], each variable the guard quantifies -- so two
   structurally identical unfoldings differ as built.  Compare them
   alpha-normalized.  The context to canonicalize against is the free variables
   the formula actually mentions, not the lift's whole context: canonical
   numbering continues past the context, a lift's context may bind variables
   its type never mentions, and their count would otherwise shift the number of
   every bound variable.  Subjects need no normalization -- they are built from
   the canonical variables already, so one object is one term.

   Normalizing and comparing whole formulas is not free, so it is done only
   when someone is looking: with the diagnostic on, or in a debug build. *)
(* Which of a term's leading lambda binders erase, outermost first.
   [match_instance] is syntactic on unerased [coqterm]s, so a schema whose
   binder type is a canonical variable matches an instance whose binder is a
   proof.  The schema's binder survives translation and the instance's does
   not, so the two lifts' symbols are applied at different arities: the
   instance's link application then has exactly the shape of its own saturated
   definition equation, and the two together equate a value with a function.
   Comparing the profiles is what keeps a link between such a pair from being
   emitted. *)
let binder_erasure_profile ctx tm =
  let rec collect ctx tm acc =
    match tm with
    | Lam(vname, ty, body) ->
       let erased = try Coq_typing.check_prop ctx ty with _ -> false in
       collect ((vname, ty) :: ctx) body (erased :: acc)
    | _ -> List.rev acc
  in
  collect ctx tm []

let record_unfolding_sharing axname fvars subject fla =
  if Lift_stats.enabled () || opt_debug_level >= 1 then
    let names = get_free_varnames fla in
    let ctx = vars_to_ctx (List.filter (fun (x, _) -> List.mem x names) fvars) in
    let (_, fla, _) = Hashing.canonical ctx fla in
    match Hashtbl.find_opt type_unfolding_hash subject with
    | None -> Hashtbl.add type_unfolding_hash subject fla
    | Some fla0 ->
       if fla0 = fla then
         Lift_stats.count "type.guard_shared"
       else
         begin
           Lift_stats.count "type.guard_heterogeneous";
           log 1 ("heterogeneous unfolding for the shared type object " ^
                  string_of_coqterm subject ^ " in " ^ axname)
         end

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
  if opt_dependent_types then
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
  if opt_dependent_types then
    match flatten_app tm with
    | Const name, args
         when name <> !translation_owner && is_transport_constant name &&
              List.length args >= transport_full_arity ->
       (* Inline an occurrence of the generic transport definition equation.
          The defining equation's own left-hand side stays intact.  Preserve
          applications after the transport spine, e.g. [(eq_rect ... f ... e) x]
          becomes [f x]. *)
       Some (mk_long_app (List.nth args 3) (Hhlib.drop transport_full_arity args))
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

let nbe tm = simpl (Coq_typing.reify (Coq_typing.eval tm))

(* Constructor applications are rigid only at constructor heads.  Equal heads
   may still clash in any corresponding informative argument, including
   parameters; a variable or any other non-constructor head is deliberately
   never unified.  Proof arguments are exempt: distinct proofs of a proposition
   are not discriminable in CIC, so a branch whose declared pattern differs
   from the occurrence only inside a proof subterm is still reachable and must
   not be pruned.  The constructor telescope decides which positions those are;
   an unavailable one leaves every position informative, which is the status
   quo. *)
let rec rigid_clash ctx u t =
  match flatten_app u, flatten_app t with
  | (Const c1, args1), (Const c2, args2)
       when Coq_typing.is_constructor c1 && Coq_typing.is_constructor c2 ->
     if c1 <> c2 then
       true
     else
       let formals =
         try
           let (_, _, cargs) =
             Coq_typing.destruct_type_app (coqdef_type (Defhash.find c1))
           in
           cargs
         with _ -> []
       in
       let rec some_pair_clashes formals xs ys =
         match xs, ys with
         | x :: xs2, y :: ys2 ->
            let (is_proof, formals2) =
              match formals with
              | (name, ty) :: formals2 ->
                 ((try Coq_typing.check_prop ctx ty with _ -> false),
                  List.map (fun (n, t) -> (n, simple_subst name x t)) formals2)
              | [] -> (false, [])
            in
            (not is_proof && rigid_clash ctx x y) ||
              some_pair_clashes formals2 xs2 ys2
         | _ -> false
       in
       some_pair_clashes formals args1 args2
  | _ -> false

(* True only for a proposition whose formula rendering is `p(t)' for a
   Const-headed application `t': then, and only then, does the definitional
   equivalence have a genuine term on each side and may be duplicated as a
   term-level equation.  A logical connective, `$True'/`$False' or any head
   other than a constant (a quantifier, a lambda, a case, an equality, or a
   Var-headed diagonal like `Proper') renders as a compound formula, which is
   not a term. *)
let is_atomic_prop_body body =
  match flatten_app body with
  | (Const(c), _) -> not (is_logop c) && c <> "$True" && c <> "$False"
  | _ -> false

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
  let lhs = mk_long_app (Const(name)) (mk_vars vars) in
  let body_is_prop = Coq_typing.check_prop (List.rev vars) body in
  let mk_eqv ctx =
    let mk_eqv =
      if Coq_typing.check_prop ctx body then
        mk_equiv
      else
        mk_eq
    in
    let eqv = mk_eqv lhs body in
    match premise with
    | Some prem -> mk_impl prem eqv
    | None -> eqv
  in
  (* the equivalence and the term equation are closed the same way; each call
     builds its own computation, since binding one twice would run it twice *)
  let close_formula mk_body =
    if !wf_mark then
      (* WF-recursion model note: these equations are not read as
         delta-unfolding in the term model.  They are Coq theorems only with
         the erased PI premises (Fix_eq), and semantically describe a total
         extension outside those premises; the consistency canaries check this
         load-bearing path. *)
      make_fol_forall_keep_prop_premises [] vars (mk_body (List.rev vars))
    else
      close fvars
        begin fun ctx ->
          let tm = mk_body (List.rev_append lvars ctx) in
          if !opt_closure_guards || opt_lambda_guards then
            prop_to_formula ctx (mk_long_forall lvars tm)
          else
            make_fol_forall ctx lvars tm
        end
  in
  (* A transparent Prop-valued definition with an atomic body also occurs in
     term position, where the equivalence identifies nothing; see
     `opt_prop_def_term_eqs'.  A premised or WF-marked equation is not a
     conversion, so it gets no term-level counterpart. *)
  let term_eq =
    opt_prop_def_term_eqs && premise = None && not !wf_mark &&
    body_is_prop && is_atomic_prop_body body
  in
  close_formula mk_eqv
  >>=
  (fun tm -> add_axiom (mk_axiom axname tm))
  >>
  begin
    if term_eq then
      close_formula (fun _ -> mk_eq lhs body) >>=
      (fun tm -> add_axiom (mk_axiom (axname ^ "$term") tm))
    else
      return ()
  end
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
     emit_definition_equation axname name fvars lvars body3
  | None ->
  let wf_recursion_equation tm =
    if name = "" then
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
    (* Substituting a constructor argument away has to reach the types of the
       arguments that follow it: those types are carried into the [$Proof] casts
       that replace erased payloads, so an argument still mentioned there would
       be left with nothing to bind it.  [replacement] returns [None] for the
       arguments that stay. *)
    let subst_telescope_args base_ctx args body replacement =
      let rec hlp ctx idx args body =
        match args with
        | [] -> body
        | (name, ty) :: args2 ->
           let (args2, body) =
             match replacement ctx idx ty with
             | None -> (args2, body)
             | Some value ->
                (List.map (fun (n, t) -> (n, simple_subst name value t)) args2,
                 simple_subst name value body)
           in
           hlp ((name, ty) :: ctx) (idx + 1) args2 body
      in
      hlp base_ctx 0 args body
    in
    let subst_proof_args base_ctx args body =
      subst_telescope_args base_ctx args body
        (fun ctx _ ty ->
           if Coq_typing.check_prop ctx ty then Some (mk_proof_cast ty) else None)
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
    (* Carry the renaming [refresh_case_args] performed on a constructor
       telescope over to terms expressed in the original binders -- the result
       index patterns, which must keep referring to the arguments the branch
       now binds. *)
    let refresh_case_terms args0 args tms =
      List.map
        (fun tm ->
           List.fold_left2
             (fun tm (name, _) (name2, _) ->
                if name = name2 then tm else substvar name (Var name2) tm)
             tm args0 args)
        tms
    in
    (* The preparation every case branch shares, whichever equation shape the
       branch ends up in: the constructor telescope is refreshed away from the
       enclosing context, the arguments the occurrence indices ford are
       instantiated, the proof payloads of the branch body are erased and the
       constructor pattern is built from the resulting spine.  [indices] and
       [informative] are empty when the occurrence exposes no index telescope,
       which simply fords nothing. *)
    let prepare_case_branch vars indname params params_num constrs branches
        indices informative cname =
      let (n, branch) = get_branch cname constrs branches in
      let (patterns, args0) =
        Coq_erasure.constructor_index_data params params_num cname
      in
      if List.length args0 <> n then
        internal_error
          ("constructor telescope arity mismatch for " ^ cname ^ " in " ^
           indname ^ ": branch binds " ^ string_of_int n ^
           " but normalized constructor has " ^ string_of_int (List.length args0))
      else
        let args = refresh_case_args vars args0 in
        let patterns = refresh_case_terms args0 args patterns in
        (* Fording solves a constructor argument whose result-index pattern is
           that argument itself.  Such a branch is reachable only at the
           scrutinee's own index, so the argument is instantiated with that
           index instead of being quantified: a binder left universal while
           occurring only on the right-hand side of the branch equation is
           outright inconsistent once the constructor collapses to its
           carrier. *)
        let solved =
          let rec hlp acc informative actuals patterns =
            match informative, actuals, patterns with
            | keep :: informative2, actual :: actuals2, Var name :: patterns2
                 when keep && List.mem_assoc name args &&
                        not (List.mem_assoc name acc) ->
               hlp ((name, actual) :: acc) informative2 actuals2 patterns2
            | _ :: informative2, _ :: actuals2, _ :: patterns2 ->
               hlp acc informative2 actuals2 patterns2
            | _ -> List.rev acc
          in
          hlp [] informative indices patterns
        in
        let subst_solved tm =
          List.fold_left
            (fun tm (name, value) ->
               if var_occurs name tm then substvar name value tm else tm)
            tm solved
        in
        let patterns = List.map subst_solved patterns in
        let spine =
          List.map
            (fun (name, _) ->
               match Hhlib.massoc name solved with
               | Some value -> value
               | None -> Var name)
            args
        in
        let args =
          List.fold_right
            (fun (name, ty) acc ->
               if List.mem_assoc name solved then acc else (name, subst_solved ty) :: acc)
            args []
        in
        let body = simpl (mk_long_app branch spine) in
        let body = subst_proof_args (List.rev vars) args body in
        (args, patterns, mk_long_app (Const(cname)) (params @ spine), body)
    in
    (* Refinement occurrence collapse: matching a subset value exposes the
       erased carrier itself, and the remaining proof payload binders are erased.
       [Coq_erasure.validate_subset] only classifies a constructor as [CSubset]
       when every non-carrier field is a proposition that stays propositional
       once the carrier binder is replaced by the (opaque) subset value -- in
       particular the carrier never heads a proof-payload type.  So the
       [check_prop] below cannot fail on a well-classified subset, and the
       informative-payload internal error is an unreachable consistency check. *)
    let collapse_subset_case ~matched_term ~vars ~constrs ~branches subset_args carrier_idx =
      match constrs, branches with
      | [_], [(n, branch)] ->
         let args = subset_args in
         if List.length args <> n then
           internal_error "subset constructor telescope arity mismatch"
         else
           let args = refresh_case_args vars args in
           let body = simpl (mk_long_app branch (mk_vars args)) in
           subst_telescope_args (List.rev vars) args body
             (fun ctx idx arg_ty ->
                if idx = carrier_idx then
                  Some matched_term
                else if Coq_typing.check_prop ctx arg_ty then
                  Some (mk_proof_cast arg_ty)
                else
                  internal_error "subset constructor has an unexpected informative payload")
      | _ -> internal_error "subset case is not a singleton constructor case"
    in
    let is_acc_ind indname = Coq_stdnames.is_init_wf "Acc" indname in
    let collapse_prop_singleton vars indname constrs params params_num branches =
      match constrs, branches with
      | [cname], [(n, branch)] ->
         let (_, args) =
           Coq_erasure.constructor_index_data params params_num cname
         in
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
                  extension model accounts for values outside the premise. *)
               wf_mark := true;
               Some body
             end
           else
             Some body
      | _ -> internal_error "propositional singleton has an unexpected constructor shape"
    in
    let case_index_formals indty params params_num =
      Coq_erasure.index_formals_of
        (Coq_typing.get_type_args indty) params params_num
    in
    let constructor_index_condition index_formals informative actual_indices patterns =
      (* [instantiate] is partial in the arity, and the two arities are derived
         differently -- the formals by evaluating the inductive's arity, the
         actual indices by the syntactic telescope length of the occurrence --
         so check them here rather than let the mismatch surface as an
         [Invalid_argument] past the alignment report below. *)
      if List.length index_formals <> List.length actual_indices then
        internal_error
          ("case predicate indices do not match the declared index telescope (" ^
           string_of_int (List.length actual_indices) ^ " actual, " ^
           string_of_int (List.length index_formals) ^ " declared)");
      let patterns =
        List.map (Coq_erasure.instantiate index_formals actual_indices) patterns
      in
      let rec conjs actuals patterns informative acc =
        match actuals, patterns, informative with
        | actual :: actuals2, pattern :: patterns2, keep :: informative2 ->
           let acc =
             (* A forded position was already instantiated with the occurrence
                index, so its equality is a tautology. *)
             if keep && actual <> pattern then
               mk_eq actual pattern :: acc
             else
               acc
           in
           conjs actuals2 patterns2 informative2 acc
        | [], [], [] ->
           begin match acc with
           | [] -> None
           | _ -> Some (join_right mk_and acc)
           end
        | _ ->
           internal_error
             ("constructor result indices do not align with the case predicate (" ^
              string_of_int (List.length actuals) ^ " actual, " ^
              string_of_int (List.length patterns) ^ " constructor, " ^
              string_of_int (List.length informative) ^ " formal arguments remain)")
      in
      conjs actual_indices patterns informative []
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
        if !wf_mark then
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
      let actual_indices = Coq_erasure.occurrence_indices indname scrutinee_ty in
      let () =
        match actual_indices with
        | None -> log 2 ("case-index-omitted: " ^ axname)
        | Some _ -> ()
      in
      let index_formals = case_index_formals indty params params_num in
      let informative =
        match actual_indices with
        | None -> []
        | Some _ -> Coq_erasure.informative_index_mask ctx index_formals
      in
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
               make_guard ((name, ty) :: ctx) ty (Var name) >>= fun guard ->
               loop ((name, ty) :: ctx) rest >>= fun r ->
               let connective = if lower then mk_impl guard r else mk_and guard r in
               return ((if lower then mk_forall else mk_exists) name type_any connective)
          | [] -> return body
        in
        loop ctx args
      in
      let one_branch cname =
        let indices = match actual_indices with None -> [] | Some indices -> indices in
        let (args, patterns, pattern, body) =
          prepare_case_branch vars indname params params_num constrs branches
            indices informative cname
        in
        prop_to_formula (List.rev (vars @ args)) body >>= fun branch_formula ->
        prop_to_formula (List.rev (vars @ args)) (mk_eq (Var scrutinee) pattern)
        >>= fun scrutinee_formula ->
        let index =
          match actual_indices with
          | None -> None
          | Some indices ->
             constructor_index_condition index_formals informative indices patterns
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
           try Some (coqdef_type (Defhash.find name)) with Failure _ -> None
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
      | Case(indname, matched, _, raw_return_type, params_num, _) ->
         begin match infer_term_type ctx matched with
         | Some matched_ty ->
            begin match Coq_erasure.occurrence_indices indname matched_ty with
            | Some indices ->
               Some (simpl (mk_long_app raw_return_type (indices @ [matched])))
            | None -> None
            end
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
      (* get_case_scrutinee_type reads the type off the return predicate, so for
         an indexed family it mentions the predicate's own index binders, which
         nothing here binds.  The binder standing for the scrutinee must be typed
         in the scope of [vars] alone, or the lifted case is hash-consed against
         a context too short for it; the scrutinee's inferred type is that same
         type with the indices instantiated.  When inference cannot recover such
         a closed type, the auxiliary link is omitted instead of being lifted
         against a context too short for it. *)
      let is_closed ty = term_fvars_subset (List.map fst vars) ty in
      let scrutinee_ty =
        if is_closed scrutinee_ty then
          Some scrutinee_ty
        else
          match infer_term_type ctx matched_term with
          | Some ty when is_closed ty -> Some ty
          | _ -> None
      in
      match scrutinee_ty with
      | None -> return None
      | Some scrutinee_ty ->
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
               record_lift_stats "case_aux" name cctx ctm;
               lambda_lifting [] name name (ctx_to_vars cctx) [] ctm
            | _ -> internal_error "case auxiliary lifting lost its normalized case body"
          end) >>= fun aux ->
      if scrutinee_is_prop then
        return (Some aux)
      else
        convert ctx matched_term >>= fun mt ->
        return (Some (App(aux, mt)))
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
           try Defhash.find indname with Failure _ ->
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
                Translation_effects.case_dependency dependency_owner indname;
                if !translation_owner <> dependency_owner then
                  Translation_effects.case_dependency !translation_owner indname
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
                if not opt_dependent_types then begin
                  log 2 ("case-axiom-omitted: dependent-types " ^ axname);
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
                     >>= function
                     | None -> return ()
                     | Some rhs -> emit_equation ?premise (axname ^ "$link") vars lhs rhs true
                end
              else if Coq_typing.check_type_target_is_prop indty then
                if not opt_dependent_types then begin
                  log 2 ("case-axiom-omitted: dependent-types " ^ axname);
                  return ()
                end
                else begin
                  match matched_term with
                  | Var _ ->
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
                            (* Singleton elimination is proof-irrelevant: the
                               unique branch is the value for every inhabitant,
                               so the equation needs no premise. *)
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
                     >>= function
                     | None -> return ()
                     | Some rhs ->
                        emit_equation ?premise (axname ^ "$link") vars lhs rhs false
                end
              else begin
                record_case_dependency ();
                let collapse_subset_case subset_args carrier_idx =
                  collapse_subset_case ~matched_term ~vars ~constrs ~branches
                    subset_args carrier_idx
                in
                let regular_case () =
                  match matched_term with
                  | Var scrutinee when var_occurs scrutinee lhs ->
                     let pruning_data =
                       if not opt_dependent_types then
                         None
                       else
                         let scrutinee_ty =
                           try List.assoc scrutinee vars with Not_found ->
                             internal_error
                               "case scrutinee is absent from the normalized context"
                         in
                         match Coq_erasure.occurrence_indices indname scrutinee_ty with
                         | None -> None
                         | Some indices ->
                            (* The scrutinee's indices and the informative
                               positions of the index telescope are the same
                               for every branch, so normalize the actuals and
                               decide propositional-ness once here rather than
                               once per constructor. *)
                            let formals =
                              case_index_formals indty params params_num
                            in
                            Some (indices, List.map nbe indices,
                                  Coq_erasure.informative_index_mask
                                    (List.rev vars) formals)
                     in
                     let branch_indices =
                       match pruning_data with
                       | None -> ([], [])
                       | Some (indices, _, informative) -> (indices, informative)
                     in
                     let branch_clashes patterns =
                       match pruning_data with
                       | None -> false
                       | Some (_, indices, informative) ->
                          if List.length indices <> List.length patterns ||
                             List.length patterns <> List.length informative
                          then
                            internal_error
                              "constructor result indices do not align with the scrutinee occurrence"
                          else
                            List.exists2
                              (fun (actual, keep) pattern ->
                                 keep && rigid_clash (List.rev vars) actual pattern)
                              (List.combine indices informative) patterns
                     in
                     let rec split_scrutinee acc = function
                       | [] -> internal_error "case scrutinee is absent from the normalized context"
                       | (name, _) :: vars_after when name = scrutinee ->
                          (List.rev acc, vars_after)
                       | var :: vars2 -> split_scrutinee (var :: acc) vars2
                     in
                     let vars_before, vars_after = split_scrutinee [] vars in
                     let prepare_branch cname =
                       let (indices, informative) = branch_indices in
                       let (args, patterns, pattern, branch_body) =
                         prepare_case_branch vars indname params params_num constrs
                           branches indices informative cname
                       in
                       let subst_scrutinee_type (name, ty) = (name, substvar scrutinee pattern ty) in
                       let lhs2 = substvar scrutinee pattern lhs
                       and body2 = substvar scrutinee pattern branch_body
                       and axname2 = axname ^ "$" ^ short_name cname
                       and vars2 = vars_before @ args @ List.map subst_scrutinee_type vars_after
                       in
                       (branch_clashes patterns, lhs2, vars2, axname2, body2)
                     in
                     (* Validate every constructor telescope before filtering
                        any impossible branch or emitting the first equation. *)
                     let prepared = List.map prepare_branch constrs in
                     let prepared =
                       List.filter
                         (fun (clashes, _, _, axname2, _) ->
                            if clashes then log 2 ("case-branch-pruned: " ^ axname2);
                            not clashes)
                         prepared
                     in
                     List.fold_left
                       (fun acc (_, lhs2, vars2, axname2, body2) ->
                          acc >> compile_case ?premise lhs2 vars2 axname2 body2)
                       (return ()) prepared
                  | _ ->
                     case_aux_value vars indname matched_term return_type raw_return_type
                       params_num branches indty
                     >>= function
                     | None -> return ()
                     | Some rhs ->
                        emit_equation ?premise (axname ^ "$link") vars lhs rhs
                          (Coq_typing.check_prop (List.rev vars) case_body)
                in
                if opt_dependent_types then
                  match Coq_erasure.classify (List.rev vars) indname params with
                  | Coq_erasure.CSubset {
                      carrier_idx; subset_args; index_formals = []; _
                    } ->
                     compile_case ?premise lhs vars axname
                       (collapse_subset_case subset_args carrier_idx)
                  | Coq_erasure.CSubset _ -> regular_case ()
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
       (make_guard ((name, ty) :: ctx) ty (Var(name))) >>= fun x1 ->
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
                         | Coq_erasure.CSubset
                             { carrier_idx; subset_args; solved; index_formals; _ } ->
                            (* The retained telescope reaches a solved argument
                               through the index formal that fords it.  A
                               constructor application has the argument itself
                               and no occurrence type to read the index from, so
                               the ordinary telescope is what aligns the actual
                               spine and eta-expands the missing fields. *)
                            let cargs =
                              Hhlib.take params_num cargs @
                                Coq_erasure.unford_telescope index_formals solved
                                  subset_args
                            in
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
      begin match erase_transport_head tm with
      | Some tm2 -> convert ctx tm2
      | None ->
      begin match erase_false_rect_type_arg ctx tm with
      | Some tm2 -> convert ctx tm2
      | None ->
      begin
      match if opt_dependent_types then subset_constructor_spine () else None with
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
       make_guard ((vname, ty1) :: ctx) ty1 (Var(vname)) >>= fun tm1 ->
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
  let internal_error msg =
    raise
      (Hammer_errors.HammerError
         ("internal translation error: indexed guard " ^ msg))
  in
  let nth_index indices pos =
    try List.nth indices pos with Failure _ ->
      internal_error "refers to an index outside the occurrence telescope"
  in
  let subst_env env tm =
    List.fold_left
      (fun tm (name, value) ->
         if var_occurs name tm then substvar name value tm else tm)
      tm env
  in
  let instantiate formals indices tm =
    if List.length formals <> List.length indices then
      internal_error "instantiates a telescope at the wrong index arity"
    else
      simpl (Coq_erasure.instantiate formals indices tm)
  in
  (* Instantiate a retained constructor telescope from left to right.  Every
     local argument of an enum is either solved by an occurrence index or is an
     erased proof; a subset additionally has its one residual carrier.  Keeping
     an explicit substitution environment is important for dependent
     telescopes: proof casts use the already-instantiated types of preceding
     arguments, rather than a second constructor destruction with unrelated
     binder names.  [substvar] is capture-avoiding, so occurrence variables are
     safe even when source binders reuse their printed names. *)
  let prepare_telescope formals indices solved residuals proof_names args =
    let rec prepare env acc = function
      | [] -> (List.rev acc, env)
      | (name, ty) :: args2 ->
         let ty = subst_env env (instantiate formals indices ty) in
         let value =
           match Hhlib.massoc name solved with
           | Some pos -> nth_index indices pos
           | None ->
              begin match Hhlib.massoc name residuals with
              | Some value -> value
              | None when List.mem name proof_names -> mk_proof_cast ty
              | None -> internal_error "has an unaccounted constructor argument"
              end
         in
         prepare ((name, value) :: env) ((name, ty, value) :: acc) args2
    in
    prepare [] [] args
  in
  let prepare_term formals indices env tm =
    simpl (subst_env env (instantiate formals indices tm))
  in
  let index_equations formals indices env eqs =
    List.map
      (fun (pos, pattern) ->
         mk_eq (nth_index indices pos)
           (prepare_term formals indices env pattern))
      eqs
  in
  (* Decide the shape of the guard before building any formula.  An inductive,
     constructor or telescope which is unavailable or malformed simply carries
     no refinement structure, and such a leaf legitimately degrades to plain
     typing; the declaration lookups of [saturated_occurrence] are therefore
     the only failures allowed to mean "no refinement here".  Payload
     translation is kept outside, so a bug in it surfaces instead of quietly
     weakening the guard.  That same helper decides exact saturation, which the
     case path reads too: a partial family application is a type former and
     must retain its complete ordinary typing atom. *)
  let classify_leaf ty =
    match Coq_erasure.saturated_occurrence ty with
    | Some (indname, params, indices) ->
       begin match Coq_erasure.classify ctx indname params with
       | (Coq_erasure.CSubset _ | Coq_erasure.CEnum _ |
          Coq_erasure.CEmpty) as cls ->
          Some (params, indices, cls)
       | Coq_erasure.CPropSingleton | Coq_erasure.CRegular -> None
       end
    | None -> None
  in
  if not opt_dependent_types then
    fallback ()
  else
    match (try classify_leaf ty with _ -> None) with
    | None ->
       fallback ()
    | Some (_, indices, Coq_erasure.CSubset {
        carrier_idx; carrier_name; subset_args; prop_args; solved; index_eqs;
        index_formals
      }) ->
       (* A refinement guard is expanded at the occurrence itself: the carrier
          guard is conjoined with the translated payload and residual result-
          index equations.  The same leaf is used in hypotheses and conclusions.
          The retained named telescope lets solved arguments, erased proofs and
          the carrier be substituted coherently through dependent payloads. *)
       convert ctx x >>= fun carrier ->
       let proof_names = List.map fst prop_args in
       let prepared, env =
         prepare_telescope index_formals indices solved
           [carrier_name, carrier] proof_names subset_args
       in
       let carrier_ty =
         try
           let (_, ty, _) = List.nth prepared carrier_idx in ty
         with Failure _ ->
           internal_error "subset carrier is outside its constructor telescope"
       in
       make_guard ctx carrier_ty carrier >>= fun carrier_guard ->
       formulas ctx
         (List.map
            (fun (_, prop_ty) ->
               prepare_term index_formals indices env prop_ty)
            prop_args) >>= fun payloads ->
       formulas ctx
         (index_equations index_formals indices env index_eqs) >>= fun equations ->
       return (conjoin (carrier_guard :: payloads @ equations))
    | Some (params, indices, Coq_erasure.CEnum enum) ->
       let one_ctor ctor =
         let proof_names =
           List.map fst ctor.Coq_erasure.enum_payloads
         in
         let prepared, env =
           prepare_telescope enum.Coq_erasure.enum_index_formals indices
             ctor.Coq_erasure.enum_solved [] proof_names
             ctor.Coq_erasure.enum_args
         in
         let args = List.map (fun (_, _, value) -> value) prepared in
         convert ctx
           (mk_long_app (Const ctor.Coq_erasure.enum_name) (params @ args))
           >>= fun tag ->
         formulas ctx
           (List.map
              (fun (_, payload_ty) ->
                 prepare_term enum.Coq_erasure.enum_index_formals indices env
                   payload_ty)
              ctor.Coq_erasure.enum_payloads) >>= fun payloads ->
         formulas ctx
           (index_equations enum.Coq_erasure.enum_index_formals indices env
              ctor.Coq_erasure.enum_index_eqs) >>= fun equations ->
         return (mk_and (mk_eq x tag) (conjoin (payloads @ equations)))
       in
       let rec disjs = function
         | [] -> return []
         | ctor :: ctors ->
            one_ctor ctor >>= fun f ->
            disjs ctors >>= fun fs ->
            return (f :: fs)
       in
       (* A CEnum guard reuses the existing inversion scheme as a self-contained
          disjunction of constructor tags, payload formulas and instantiated
          result-index equations; non-guard occurrences still use the ordinary
          declaration-level inversion axiom. *)
       disjs enum.Coq_erasure.enum_constructors >>= fun fs ->
       return (match fs with [] -> Const("$False") | _ -> join_right mk_or fs)
    | Some (_, _, Coq_erasure.CEmpty) ->
       (* The guard for an empty classified type is false, matching the
          zero-constructor inversion scheme. *)
       return (Const("$False"))
    | Some (_, _, (Coq_erasure.CPropSingleton | Coq_erasure.CRegular)) ->
       internal_error "received a non-expandable classification"

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
       make_guard ((vname, ty1) :: ctx) ty1 (Var(vname)) >>= fun tm1 ->
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
         make_guard ((name, ty) :: ctx) ty (Var(name)) >>= fun guard ->
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

(* A lifted symbol is defined at the number of context arguments which survive
   translation.  Validate an application by translating it first and reading
   the actual retained spine; syntactic proof tests are only approximations of
   the conversion path and must never authorize an equation or schema reuse. *)
and retained_context_arity ctx =
  List.length
    (List.filter
       (fun (name, _) ->
          not (try Coq_typing.check_proof_var ctx name with _ -> false))
       (ctx_to_vars ctx))

and translate_schema_application ctx schema_name schema_ctx subst =
  let candidate = convert ctx (mk_long_app (Const schema_name) subst) in
  match flatten_app (fst candidate) with
  | Const name, args
      when name = schema_name && List.length args = retained_context_arity schema_ctx ->
     Some candidate
  | _ -> None

and remove_lambda ctx tm =
  debug 3 (fun () -> print_header "remove_lambda" tm ctx);
  (* Set when the value returned below names an already-registered lift instead
     of minting one, so that the dependencies collected on the way are not
     attributed to that shared symbol; see [with_lift_dependencies]. *)
  let reuses_lift = ref false in
  with_lift_dependencies ~reuses_lift (fun () ->
    let key = Hashing.canonical_key ctx tm in
    let cctx = Hashing.key_context key
    and ctm = Hashing.key_term key in
    (* The link is looked up before the lift minted below registers itself, so
       that lift cannot match itself.  It is computed once here and shared by
       both the instance-reuse path and the minting path.  Deferred because an
       exact cache hit needs no link at all, and the lookup is a registry scan
       over every lambda lift examined so far: forcing it eagerly would pay
       that scan once per lambda occurrence instead of once per minted lift.
       Every path that does need it forces it before anything registers. *)
    let link = lazy (Hashing.find_lift_link "lam" cctx ctm) in
    (* When a lambda is a syntactic instance of a schema available in this
       declaration, applying the schema symbol to the matching substitution
       names exactly the same Coq term.  Reuse is authorized only after that
       candidate application has gone through the real conversion path and its
       retained arity has been checked.  A rejected attempt contributes neither
       axioms nor ownership/structural-delivery effects. *)
    let reuse_instance () =
      match Lazy.force link with
      | Some link when not link.Hashing.ll_new_is_schema &&
                       Lift_owners.mem link.Hashing.ll_name !translation_owner &&
                       binder_erasure_profile cctx ctm =
                         binder_erasure_profile link.Hashing.ll_ctx link.Hashing.ll_tm ->
         let schema_key =
           Hashing.canonical_pair_key link.Hashing.ll_ctx link.Hashing.ll_tm
         in
         begin match Hashing.find_key "" coqterm_hash schema_key with
         | None -> None
         | Some cached ->
            let (candidate, dependencies, effects) =
              speculate_translation (fun () ->
                translate_schema_application cctx link.Hashing.ll_name
                  link.Hashing.ll_ctx link.Hashing.ll_subst)
            in
            begin match candidate with
            | None ->
               discard_speculation dependencies effects;
               None
            | Some candidate ->
               commit_speculation dependencies effects;
               reuses_lift := true;
               let value = cached >> candidate in
               (* Cache the instance under its own key, so a further occurrence
                  of the same lambda is an exact hit instead of re-running the
                  registry scan and the speculative translation -- which would
                  also make reuse depend on the registry's examination cap.

                  Only when the speculation contributed no dependencies: an
                  exact hit re-translates nothing, so all it can deliver is the
                  theory recorded for its head symbol.  Since a reusing
                  occurrence must not extend that symbol's entry, caching an
                  instance whose arguments did contribute structural
                  dependencies would silently under-deliver them on replay.
                  Such instances keep re-speculating per occurrence.

                  [value] is built over [Hashing.key_context key] and is stored
                  before any [lift_key] renaming, as [insert_key] requires. *)
               if dependencies = [] then
                 Hashing.insert_key "" coqterm_hash key value;
               record_bundle_owners value;
               Some (Hashing.lift_key coqterm_hash key value)
            end
         end
      | _ -> None
    in
    let reuse =
      match Hashing.find_key "" coqterm_hash key with
      | Some cached ->
         (* Replaying the complete cached bundle makes its symbols available
            to this owner.  Record the pairs after constructing that replay, so
            a later schema instance in the same declaration is order-independent
            across earlier owners of the same cache entry. *)
         reuses_lift := true;
         let result = Hashing.lift_key coqterm_hash key cached in
         begin match fst (flatten_app (fst result)) with
         | Const name -> Translation_effects.lift_owner name !translation_owner
         | _ -> ()
         end;
         record_bundle_owners cached;
         Some result
      | None -> reuse_instance ()
    in
    match reuse with
    | Some result -> result
    | None ->
    Hashing.find_or_insert_key "" coqterm_hash key
      begin fun cctx ctm ->
        let name = "$_lam_" ^ unique_id ()
        in
        (* A lambda lift's definition equation relates [name] and its body only
           when both are applied to the lambda-bound arguments; the unapplied
           object this returns is not identified by it, and identifying two
           pointwise equal functions in general needs functional
           extensionality.  A link equation is not that: it says the two lifts'
           canonical terms are related by syntactic instantiation, so the two
           symbols name one and the same Coq lambda term.  Like the type-lift
           links it is true by construction, and needs no extensionality --
           provided the two symbols take the same number of arguments, which
           [add_link_axiom] checks, matching being syntactic on the unerased
           term while arity is settled after erasure.

           [link] is computed above, before this lift registers itself below,
           so this lift cannot match itself.  Reaching here means the reuse
           attempt already forced it, so this is the memoized value. *)
        count_lift "lam" "minted";
        lambda_lifting [] name name (ctx_to_vars cctx) [] ctm >>= fun result ->
        (* [lambda_lifting] does not always name the lift [name]: a [Fix] body
           it delegates to [fix_lifting] and a [Case] body to [case_lifting],
           which mint their own symbols, and only its [emit_definition_equation]
           paths return [name] applied to the lift's context.  An equation about
           [name] is meaningful only in that last case, so read the head of what
           was actually returned rather than predicting it from the body's shape
           -- a [Fix] does come back under [name] when [fix_lifting] reaches its
           own [lambda_lifting] for the selected component.  With an empty
           context the result is the bare [Const name]. *)
        match fst (flatten_app result) with
        | Const cname when cname = name ->
           count_lift "lam" (link_outcome (Lazy.force link));
           Hashing.register_lift "lam" name cctx ctm;
           Translation_effects.lift_owner name !translation_owner;
           add_link_axiom name cctx ctm (Lazy.force link) >>
           return result
        | _ ->
           count_lift "lam" "unnamed";
           return result
      end)

and remove_case ctx tm =
  debug 3 (fun () -> print_header "remove_case" tm ctx);
  with_lift_dependencies (fun () ->
    Hashing.find_or_insert_keyed (case_occurrence_key ctx tm) coqterm_hash ctx tm
      begin fun cctx ctm ->
        (* [case_lifting] mints its symbols internally, so the diagnostic
           identifies the entry by a fresh name of its own; it uses the name
           only to tell registry entries apart. *)
        record_lift_stats "case" ("$_case_" ^ unique_id ()) cctx ctm;
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
        record_lift_stats "fix" ("$_fix_" ^ unique_id ()) cctx ctm;
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
  (* A non-dependent product with a non-Prop domain is translated structurally,
     as an application of the single former [$_arrow], instead of being lifted
     to a constant minted per occurrence shape.  Two occurrences of one arrow
     type then denote the same term up to their arguments -- a goal-side
     [A -> B] over local constants and a premise-side one under [forall A B]
     unify directly -- whereas per-occurrence names left them unrelated, with
     nothing to bridge them since the unfolding axiom is only an implication.
     Prop domains keep the lifted name: [type_to_guard] prunes proof binders
     from the term spine, so [P -> B] is not a function object and its
     unfolding is not the one [$_arrow] stands for.  Dependent products have
     no canonical former yet. *)
  let eligible =
    match ty with
    | Prod(vname, ty1, ty2) ->
       not (var_occurs vname ty2) && not (Coq_typing.check_prop ctx ty1)
    | _ -> false
  in
  with_lift_dependencies (fun () ->
    Hashing.find_or_insert coqterm_hash ctx ty
      begin fun cctx cty ->
        record_type_lift_shape eligible cctx cty;
        match cty with
        | Prod(_, ty1, ty2) when eligible ->
           (* The subject is converted once and used both as the result and as
              the axiom's subject: converting it twice could mint two different
              symbols for a lift inside it that is not hash-consed.  Bind the
              conversion here rather than passing it on unbound and using it
              again: a translation is a computation that emits axioms, so using
              one twice runs it twice, and since the domain and codomain of an
              arrow are themselves translated through this branch, the doubling
              compounds to 2^n on a telescope of n nested arrows. *)
           convert cctx (mk_long_app (Const("$_arrow")) [ty1; ty2]) >>= fun subject ->
           add_type_unfolding_axiom ("$_arrow_" ^ unique_id ())
             (ctx_to_vars cctx) cty (return subject) >>
           return subject
        | _ ->
           let name = "$_type_" ^ unique_id ()
           and vars = ctx_to_vars cctx
           in
           let link = link_lift "type" name cctx cty in
           (* The instance's own unfolding axiom stays: the schema's axiom read
              through the link is sound but need not be the same statement,
              since [guard_leaf] classifies the unnormalized Coq type.  Both are
              individually true of the one object, so keeping both is correct. *)
           add_def_eq_type_axiom name name vars cty >>
           add_link_axiom name cctx cty link >>
           convert cctx (mk_long_app (Const(name)) (mk_vars vars))
      end)

(* A lifted symbol names a Coq term, so when one lift's term is a syntactic
   instance of another's the two symbols denote the same Coq object at the
   matching arguments and this equation is true by construction -- both sides
   are images of one Coq term.  Being an equality it bridges in both
   directions, which the unfolding axiom cannot do: that one is only an
   implication (commit 951862d) and nothing else relates two names minted for
   the same type at two occurrence shapes.

   The equation is emitted inside the [mk] of the lift minted *second*, so it
   lives in that lift's monadic prepender and travels with it into every
   declaration which uses the lift.  A problem holding only one side is still
   sound: the absent side is then an alias with no axioms of its own.

   Uniformly, the equation is closed over the instance side's canonical
   context, applies the instance's symbol to that context's own variables and
   the schema's symbol to the matching substitution. *)
and add_link_axiom name cctx ctm link =
  match link with
  | None -> return ()
  | Some link when
      binder_erasure_profile cctx ctm
      <> binder_erasure_profile link.Hashing.ll_ctx link.Hashing.ll_tm ->
     (* The two lifts translate to symbols of different arities, so no equation
        between them at their own contexts is well-formed. *)
     Lift_stats.count "link.erasure_mismatch";
     return ()
  | Some link ->
     let open Hashing in
     let (inst_name, inst_ctx, schema_name, schema_ctx) =
       if link.ll_new_is_schema then
         (* the partner is the instance of the lift just minted *)
         (link.ll_name, link.ll_ctx, name, cctx)
       else
         (name, cctx, link.ll_name, link.ll_ctx)
     in
     let vars = ctx_to_vars inst_ctx in
     (* Matching is syntactic on unerased terms, so a surviving schema-context
        variable may be instantiated by a proof which conversion drops.  Run
        the same checked application path used by lambda schema reuse.  Its
        speculative side axioms and dependency deliveries are retained only if
        the translated spine has the symbol's real definition arity. *)
     let (rhs, dependencies, effects) =
       speculate_translation (fun () ->
         translate_schema_application inst_ctx schema_name schema_ctx link.ll_subst)
     in
     begin match rhs with
     | None ->
        discard_speculation dependencies effects;
        Lift_stats.count "link.arg_erasure_mismatch";
        return ()
     | Some rhs ->
        commit_speculation dependencies effects;
        (* Built through the same path [add_def_eq_type_axiom] uses, so arity
           and [$HasType] handling are unchanged. *)
        close vars
          begin fun ctx ->
            convert ctx (mk_long_app (Const(inst_name)) (mk_vars vars)) >>= fun lhs ->
            rhs >>= fun rhs ->
            return (mk_eq lhs rhs)
          end >>= fun r ->
        add_axiom (mk_axiom ("$_link_" ^ unique_id ()) r)
     end

and add_def_eq_type_axiom axname name fvars ty =
  debug 2 (fun () -> print_header "add_def_eq_type_axiom" ty fvars);
  add_type_unfolding_axiom axname fvars ty
    (convert (vars_to_ctx fvars) (mk_long_app (Const(name)) (mk_vars fvars)))

(* [subject] is the translated object standing for the type [ty] -- a lifted
   constant applied to [fvars], or the canonical [$_arrow] application.  It is
   translated in the context [close] hands to the continuation below, which is
   [vars_to_ctx fvars] in either closure mode. *)
and add_type_unfolding_axiom axname fvars ty subject =
  debug 2 (fun () -> print_header "add_type_unfolding_axiom" ty fvars);
  let vname = "var_" ^ unique_id ()
  in
  close fvars
    begin fun ctx ->
      subject >>= fun tp ->
      (* The axiom quantifies [vname] over the inhabitants of [ty], so [ty] is
         its type: the guard is built in a context that binds it, as every
         subject of a guard must be bound in the context it is translated in. *)
      type_to_guard ((vname, ty) :: ctx) ty (Var(vname)) >>= fun guard ->
      (* [ty] is a function/product type, so [guard] is its extensional
         unfolding: [vname] applied across the domain lands in the codomain.
         Membership implies that behaviour, but the converse is unsound: over an
         empty domain the unfolding holds vacuously of every object, so an
         equivalence would let any term (e.g. a non-function) inhabit the arrow
         type, and a functional-extensionality premise would then collapse
         equality (deriving [$false] from ContradictoryAxioms).  The typing of
         genuine inhabitants is always asserted directly at their binder or
         [$_typeof_] axiom, so the forward implication alone loses no provable
         function application.  This holds for a canonical [$_arrow] subject
         exactly as for a lifted name: canonicalization changes which object the
         unfolding speaks about, never its direction or strength.

         All of that is about *products*.  [remove_type] is only ever reached on
         a product, so a non-product [ty] here is the body of a transparent
         type definition, and then [type_to_guard] falls through to
         [guard_leaf]: the guard is not an extensional unfolding but another
         membership statement -- plain typing at the body, or the subset/enum/
         empty description of the very same type.  [tp] and [ty] are convertible
         by delta, so the two memberships are equivalent by conversion and there
         is no domain to be empty.  951862d weakened this case only as collateral
         damage. *)
      let connective =
        match ty with
        | Prod(_) -> mk_impl
        | _ -> mk_equiv
      in
      let fla =
        mk_forall vname type_any (connective (mk_hastype (Var(vname)) tp) guard)
      in
      record_unfolding_sharing axname fvars tp fla;
      return fla
    end >>= fun r ->
  add_axiom (mk_axiom axname r)

and add_typing_axiom name ty =
  debug 2 (fun () -> print_endline ("add_typing_axiom: " ^ name));
  if not (is_logop name) && name <> "$True" && name <> "$False" && ty <> type_any then
    begin
      if opt_dependent_types && Coq_erasure.has_erasable_content [] ty then
        begin
          (* When the type contains erasure-relevant refinements/enums, emit the
             applied forall-form directly through type_to_guard.  This bypasses
             type lifting/optimization so payloads are expanded per occurrence. *)
          type_to_guard [] (refresh_bvars ty) (Const(name)) >>= fun guard ->
          (* That unfolding says how [name] behaves when applied, but not that it
             inhabits its own type.  A premise quantifying over a function is
             guarded by exactly that membership ([make_guard] lifts a product and
             states it), so without it the premise cannot be instantiated at
             [name] at all -- and every function into an enum or a refinement
             lands here, [elt -> bool] being the common case.  The membership is
             true by construction, [name] being declared at [ty]; it is the same
             formula the branches below emit for a constant with no erasable
             content.  Only products need it: for a leaf type the two guards
             coincide, and under subset erasure [name] denotes its carrier. *)
          begin
            match ty with
            | Prod(_) when opt_type_lifting ->
               make_guard [] (refresh_bvars ty) (Const(name)) >>= fun memb ->
               return (mk_and memb guard)
            | _ ->
               return guard
          end >>= fun r ->
          add_axiom (mk_axiom ("$_typeof_" ^ name) r)
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
             add_axiom (mk_axiom axname (mk_equiv (Const(name)) r)) >>
             (* the definition also occurs in term position; see
                `opt_prop_def_term_eqs' *)
             if opt_prop_def_term_eqs && is_atomic_prop_body value then
               convert [] value >>= fun r2 ->
               add_axiom (mk_axiom (axname ^ "$term") (mk_eq (Const(name)) r2))
             else
               return ()
           end
        | SortType | SortSet ->
           add_def_eq_type_axiom axname name [] value
        | _ ->
           begin
             convert [] value >>= fun r ->
             add_axiom (mk_axiom axname (mk_eq (Const(name)) r))
           end
      end

(* A declaration that erases to its carrier at every occurrence has no
   constructor symbol left for the declaration-level structural axioms to
   describe: injectivity of the erased constructor degenerates to a tautology,
   and inversion asserts a constructor shape the occurrence-level expansion
   never produces.  Only declaration-independent classifications qualify --
   [classify_decl] returns [None] for parameter-dependent declarations, whose
   structural axioms are therefore kept. *)
and skip_refinement_decl_axioms indname =
  opt_dependent_types &&
  match Coq_erasure.classify_decl indname with
  | Some (Coq_erasure.CSubset _) -> true
  | _ -> false

and add_injection_axioms params_num constr =
  debug 2 (fun () -> print_endline ("add_injection_axioms: " ^ constr));
  if not (Defhash.mem constr) then
    (* Search filters can omit a constructor independently of its inductive;
       without its telescope the optional injectivity axiom must be omitted. *)
    return ()
  else
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
  if not (Defhash.mem constr1 && Defhash.mem constr2) then
    (* Search filters can omit constructors independently of their inductive;
       without both telescopes the optional discrimination axiom is omitted. *)
    return ()
  else
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
  if not (List.for_all Defhash.mem constrs) then
    (* Search filters can omit constructors independently of their inductive.
       Exhaustiveness over a partial constructor list would be unsound, so omit
       the inversion axiom unless every constructor telescope is available. *)
    return ()
  else
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
       prop_to_formula [] ty >>= fun r ->
       add_axiom (mk_axiom name r)
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
  let axs =
    Fun.protect ~finally:(fun () -> translation_owner := previous_owner)
      (fun () -> extract_axioms (add_def_axioms (Defhash.find name)))
  in
  compose_axioms [axs]

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
  compose_axioms
    (coq_axioms ::
       List.map Axhash.find
         (Hhlib.sort_uniq String.compare (lst @ structural)))

let remove_def name =
  Defhash.remove name;
  Axhash.remove name;
  Case_dependencies.remove name;
  (* Everything attributed to this declaration goes with it.  [remove_def] is
     used together with [reinit] -- not [cleanup] -- to re-translate one
     declaration while keeping the translation caches, so a surviving
     ownership pair would let a later occurrence reuse a lift a fresh process
     would have minted anew, making translation output order-dependent.
     [Lift_dependencies] is keyed by symbol rather than by owner and stays
     consistent with the surviving [coqterm_hash], so it is left alone. *)
  Lift_owners.remove name

let cleanup () =
  reset_unique_id ();
  discarded_speculations := 0;
  discarded_speculation_effects := 0;
  Defhash.clear ();
  Coq_typing.clear_constructor_hash ();
  Axhash.clear ();
  Coq_erasure.clear ();
  Case_dependencies.clear ();
  Lift_dependencies.clear ();
  Lift_owners.clear ();
  Hashtbl.clear type_unfolding_hash;
  translation_owner := "";
  Hashing.clear coqterm_hash

(******************************************************************************)

let output_problem_axioms oc name axioms =
  Tptp_out.write_fol_problem
    (output_string oc)
    (List.remove_assoc name axioms)
    (name, List.assoc name axioms)

let output_problem oc name deps =
  output_problem_axioms oc name (get_axioms (name :: deps))

let write_problem fname name deps =
  let axioms = get_axioms (name :: deps) in
  let oc = open_out fname in
  (* [flush] inside the body so a write error still reaches the caller, which
     [close_out_noerr] in the finally would swallow. *)
  Fun.protect ~finally:(fun () -> close_out_noerr oc)
    (fun () -> output_problem_axioms oc name axioms; flush oc)
