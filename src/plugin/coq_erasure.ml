(* Classification of inductive instances for proof/content erasure.

   This module only chooses the translation path.  CPropSingleton/CEmpty cover
   proof-only matches, CSubset/CEnum cover shallow expansion of informative
   payloads, and CRegular leaves the ordinary translation unchanged. *)

open Hammer_lib
open Coqterms
open Coq_transl_opts

type index_eqs = (int * coqterm) list
type index_formals = (string * coqterm) list

type enum_constructor = {
  enum_name : string;
  enum_args : (string * coqterm) list;
  enum_payloads : (string * coqterm) list;
  enum_solved : (string * int) list;
  enum_index_eqs : index_eqs;
}

type enum_data = {
  enum_constructors : enum_constructor list;
  enum_index_formals : index_formals;
}

type ind_class =
  | CEmpty
  | CPropSingleton
  | CSubset of {
      carrier_idx : int;
      carrier_name : string;
      subset_args : (string * coqterm) list;
      prop_args : (string * coqterm) list;
      solved : (string * int) list;
      index_eqs : index_eqs;
      index_formals : index_formals;
    }
  | CEnum of enum_data
  | CRegular

let instantiate formals actuals tm =
  if List.length formals <> List.length actuals then
    invalid_arg "Coq_erasure.instantiate: index arity mismatch"
  else
    subst_params formals actuals tm

type arg_info = {
  arg_index : int;
  arg_name : string;
  arg_ty : coqterm;
  arg_is_prop : bool;
}

type ctor_info = {
  ctor_name : string;
  ctor_args : arg_info list;
  ctor_solved : (int * int) list;
  ctor_eqs : index_eqs;
  ctor_index_formals : index_formals;
}

type memo_class =
  | MEmpty
  | MPropSingleton
  | MSubset of int * int list
  | MEnum of (string * int list) list
  | MRegular

(* The bindings of [ctx] that the classification of an occurrence at [params]
   can read: the free variables of the parameters, closed under the free
   variables of their types.  [ctx] is innermost-first and a binder's type
   mentions only binders to its right, so one left-to-right pass collects them
   all. *)
let context_slice ctx params =
  let rec hlp needed acc = function
    | [] -> List.rev acc
    | ((name, ty) as binding) :: ctx2 ->
        if List.exists (var_occurs name) needed then
          hlp (ty :: needed) (binding :: acc) ctx2
        else
          hlp needed acc ctx2
  in
  hlp params [] ctx

type memo_entry = {
  memo_shape : memo_class;
  (** The declaration-level shape, which the recognized occurrence data is
      rebuilt against. *)
  memo_erasable : bool;
  (** [is_erasable_class] of the validated verdict this key produced.  A false
      bit is the whole answer -- the verdict was [CRegular] -- and it is not
      implied by the shape: [expand] demotes an [MSubset] to [CRegular] for a
      parameter-dependent indexed family. *)
}

(* Keyed on the occurrence itself -- the inductive, its actual parameters and
   the context slice those parameters are typed in -- so that the shape can be
   looked up before any constructor telescope is destructed.  The shapes
   carrying no occurrence-specific data, and every key whose verdict was
   [CRegular], are then answered from the key alone.

   The slice is part of the key, and not merely the propositional verdicts of
   the parameters themselves: binder names come verbatim from Rocq, so two
   premises of one problem can both bind a variable printed [T], one at
   [nat -> Prop] and one at [nat -> Type].  The parameter terms are then equal
   and so are their verdicts (neither [T] is a proposition), while a
   constructor field [T 0] is propositional in the one context and informative
   in the other.

   What the key does *not* record is [Defhash].  The rest of the classification
   is read from there -- the declaration itself, and, through
   [Coq_typing.check_prop], the type of every constant the key mentions.  A
   local hypothesis reaches the translation as a [$Var], which
   [Coq_convert.to_coqterm] lowers to a [Const], so a parameter that is a
   hypothesis [H] contributes its bare name to the key and its type only to
   [Defhash]; two goals of one session both binding [H], at [nat -> Prop] and
   at [nat -> Set], produce the same key and different verdicts.  A constant
   absent from [Defhash] is likewise classified as informative and would change
   verdict once premise selection admits it.  The memo is therefore valid for
   exactly one [Defhash] population and is cleared wherever that population
   changes: [Coq_transl.reinit], [Coq_transl.remove_def] and
   [Coq_transl.cleanup]. *)
let memo :
      ((string * coqterm list * (string * coqterm) list), memo_entry) Hashtbl.t =
  Hashtbl.create 257

let clear () = Hashtbl.clear memo

exception Not_classifiable

let check_prop ctx ty =
  try Coq_typing.check_prop ctx ty with _ -> raise Not_classifiable

let get_inductive name =
  if Defhash.mem name then
    match Defhash.find name with
    | (_, IndType(_, constrs, params_num), ind_ty, ind_sort) ->
        Some (constrs, params_num, ind_ty, ind_sort)
    | _ -> None
  else
    None

(* Premise selection can omit a constructor independently of its inductive, so
   this lookup fails on well-formed input.  Report it the way the case path
   always did, instead of letting the bare [Failure] surface as an unexplained
   internal bug. *)
let constructor_def cname =
  try Defhash.find cname with Failure _ ->
    raise (Hammer_errors.HammerError
             ("internal translation error: missing constructor declaration: " ^ cname))

let constructor_index_data params params_num cname =
  let (target, targs, cargs) =
    Coq_typing.destruct_type_app (coqdef_type (constructor_def cname))
  in
  let param_formals = Hhlib.take params_num cargs in
  let instantiate_params tm = subst_params param_formals params tm in
  let patterns =
    match target with
    | Equal (_, rhs) -> [rhs]
    | _ -> Hhlib.drop params_num targs
  in
  let args =
    List.map
      (fun (name, ty) -> (name, instantiate_params ty))
      (Hhlib.drop params_num cargs)
  in
  (List.map instantiate_params patterns, args)

let rec telescope_length = function
  | Prod (_, _, body) -> 1 + telescope_length body
  | Let (_, (_, _, body)) -> telescope_length body
  | _ -> 0

(* The index suffix of an inductive's declared telescope [type_args],
   instantiated at the occurrence [params].  [type_args] is taken rather than
   the arity itself because [Coq_typing.get_type_args] refreshes every binder,
   so a caller that already destructed the arity must pass its own result
   instead of provoking a second, differently named one. *)
let index_formals_of type_args params params_num =
  let param_formals = Hhlib.take params_num type_args in
  List.map
    (fun (name, ty) -> (name, subst_params param_formals params ty))
    (Hhlib.drop params_num type_args)

(* The informative/propositional verdict of every position of an index
   telescope, decided left to right in the extended context.  The fording
   patterns kept by [constructor_info], the index equalities emitted for a
   case predicate and the rigid-clash pruning of case branches all key off the
   same positions, so they all read this one mask. *)
let informative_index_mask ctx index_formals =
  let rec hlp formal_ctx acc = function
    | [] -> List.rev acc
    | (name, ty) :: formals ->
        hlp ((name, ty) :: formal_ctx)
          (not (Coq_typing.check_prop formal_ctx ty) :: acc) formals
  in
  hlp ctx [] index_formals

type forded_index = {
  ford_arg : string;
  ford_arg_index : int;
  ford_index_pos : int;
  ford_value : coqterm;
}

type fording = {
  ford_solved : forded_index list;
  ford_patterns : coqterm list;
  ford_eqs : index_eqs;
}

(* The fording rule itself, shared by the guard and the case paths.  A result
   index position solves a constructor argument when the position is
   informative per [informative_index_mask], its pattern is that bare argument
   and no earlier position already solved it.  A solved argument is not
   quantified but instantiated with the corresponding entry of [replacements] --
   the index formal for the classification, the occurrence's actual index for a
   case branch -- and every other informative position contributes a residual
   equation between the index and its pattern.  The two paths must agree: a
   pattern shape forded on one side alone would give a family guard-side index
   equations that its branch equations do not match.

   [mask], [replacements] and [patterns] are walked in lockstep and the walk
   stops with the shortest of them, leaving the remaining patterns untouched.
   That is what the case path relies on for an occurrence which does not expose
   its family: it passes no indices and an empty mask, and nothing is forded.
   A caller which does require the three to align -- the classification, whose
   patterns and formals both come from the declaration -- checks that itself.

   Instantiating a solved argument reaches every pattern and every residual
   equation, not only the positions that follow it: a solved argument leaves
   the constructor telescope, so an earlier position mentioning it -- a family
   indexed by both [S n] and [n], say -- would otherwise keep a reference no
   consumer binds any more.  [simple_subst] is enough for that: the binders of
   a pattern come from the global binder refresh of [constructor_index_data],
   so none of them can capture a free variable of a replacement. *)
let ford_indices mask replacements args patterns =
  let find_arg name =
    let rec find idx = function
      | [] -> None
      | (name2, _) :: args2 -> if name = name2 then Some idx else find (idx + 1) args2
    in
    find 0 args
  in
  let rec hlp pos solved eqs seen mask replacements patterns =
    match mask, replacements, patterns with
    | keep :: mask2, value :: replacements2, pattern :: patterns2 ->
        let residual () =
          hlp (pos + 1) solved (if keep then (pos, pattern) :: eqs else eqs)
            (pattern :: seen) mask2 replacements2 patterns2
        in
        begin match pattern with
        | Var arg_name
             when keep && not (List.exists (fun s -> s.ford_arg = arg_name) solved) ->
            begin match find_arg arg_name with
            | Some arg_idx ->
                let entry =
                  { ford_arg = arg_name; ford_arg_index = arg_idx;
                    ford_index_pos = pos; ford_value = value }
                in
                let subst = simple_subst arg_name value in
                hlp (pos + 1) (entry :: solved)
                  (List.map (fun (pos2, tm) -> (pos2, subst tm)) eqs)
                  (value :: List.map subst seen)
                  mask2 replacements2
                  (List.map subst patterns2)
            | None -> residual ()
            end
        | _ -> residual ()
        end
    | _ ->
        { ford_solved = List.rev solved;
          ford_patterns = List.rev_append seen patterns;
          ford_eqs = List.rev eqs }
  in
  hlp 0 [] [] [] mask replacements patterns

(* Head reduction under the [opt_whnf_budget] fuel, resolving constants through
   [Defhash].  Every caller wants nothing but the head -- an inductive for an
   occurrence type, a constructor for a rigid-clash comparison -- and the fuel
   is what keeps a type-level function from being unfolded wholesale merely to
   answer a question about its head.  Running out is not an error: the term
   comes back unreduced, and the caller reads the head it failed to expose as
   the negative answer, which for every caller is the conservative one. *)
let budgeted_whnf tm =
  let unfold name =
    try Some (coqdef_value (Defhash.find name)) with Failure _ -> None
  in
  whnf_head ~budget:opt_whnf_budget ~unfold
    ~is_constructor:Coq_typing.is_constructor tm

(* The single notion of "exactly saturated occurrence" shared by the guard and
   the case paths.  Both must agree: a family recognized on one side of the
   sequent but not on the other would receive index equations in its guards
   without the matching branch pruning.  The normalizer is the budgeted head
   reduction of [budgeted_whnf], which is built for exposing an inductive
   head and bounded against the type-level unfolding blow-up. *)
let saturated_occurrence ty =
  match flatten_app (budgeted_whnf ty) with
  | Const indname, args ->
      begin match get_inductive indname with
      | Some (_, params_num, ind_ty, _)
           when List.length args = telescope_length ind_ty ->
          Some (indname, Hhlib.take params_num args, Hhlib.drop params_num args)
      | _ -> None
      end
  | _ -> None

let occurrence_indices indname ty =
  match indname = Hhutils.lib_ref_name "core.eq.type", ty with
  | true, Equal (_, rhs) -> Some [rhs]
  | _ ->
    match get_inductive indname with
    | Some (_, params_num, ind_ty, _) when telescope_length ind_ty <= params_num ->
        (* An index-free family is not required to expose its inductive, and
           must not be: outside a case predicate [Coq_convert] lowers the
           logical inductives to the FOL formers [$True], [$False], [&] and
           [|], and a scrutinee typed by one of them is no longer an
           application of the inductive in any syntactic sense.  It has no
           index either way, so the empty index list is the whole answer. *)
        Some []
    | Some _ ->
        begin match saturated_occurrence ty with
        | Some (name, _, indices) when name = indname -> Some indices
        | _ -> None
        end
    | None -> None

let arg_at infos idx =
  try Some (List.find (fun info -> info.arg_index = idx) infos) with Not_found -> None

(* Letouzey's non-recursive-carrier condition applies to the whole inductive
   dependency graph, not just direct self references.  Serialized declarations
   do not retain mutual-block metadata, so follow inductive occurrences through
   constructor telescopes.  The visited set also makes ordinary recursive
   carriers such as [nat] terminate without being mistaken for a cycle back to
   the refinement currently being classified. *)
let rec carrier_reaches_inductive target visited ty =
  if term_mentions_const [target] ty then
    true
  else
    match flatten_app ty with
    | Const name, args ->
       List.exists (carrier_reaches_inductive target visited) args ||
       if List.mem name visited then
         false
       else
         begin match get_inductive name with
         | None -> false
         | Some (constrs, params_num, _, _) ->
            let params = Hhlib.take params_num args in
            List.exists
              (fun cname ->
                 try
                   let (_, _, cargs) =
                     Coq_typing.destruct_type_app (coqdef_type (Defhash.find cname))
                   in
                   let cparams = Hhlib.take params_num cargs in
                   List.exists
                     (fun (_, field_ty) ->
                        let field_ty =
                          if List.length params = params_num then
                            subst_params cparams params field_ty
                          else
                            field_ty
                        in
                        carrier_reaches_inductive target (name :: visited) field_ty)
                     (Hhlib.drop params_num cargs)
                 with _ ->
                   (* A malformed or unavailable telescope cannot justify
                      refinement collapse. *)
                   true)
              constrs
         end
    | _ ->
       match ty with
       | Var _ | Const _ | SortProp | SortSet | SortType | IndType _ -> false
       | App (x, y) | Equal (x, y) ->
          carrier_reaches_inductive target visited x ||
          carrier_reaches_inductive target visited y
       | Lam (_, ty, body) | Prod (_, ty, body) | Quant (_, (_, ty, body)) ->
          carrier_reaches_inductive target visited ty ||
          carrier_reaches_inductive target visited body
       | Let (value, (_, ty, body)) ->
          carrier_reaches_inductive target visited value ||
          carrier_reaches_inductive target visited ty ||
          carrier_reaches_inductive target visited body
       | Case (_, matched, return_ty, raw_return_ty, _, branches) ->
          carrier_reaches_inductive target visited matched ||
          carrier_reaches_inductive target visited return_ty ||
          carrier_reaches_inductive target visited raw_return_ty ||
          List.exists
            (fun (_, branch) -> carrier_reaches_inductive target visited branch)
            branches
       | Cast (term, ty) ->
          carrier_reaches_inductive target visited term ||
          carrier_reaches_inductive target visited ty
       | Fix (_, _, _, _, types, bodies) ->
          List.exists (carrier_reaches_inductive target visited) types ||
          List.exists (carrier_reaches_inductive target visited) bodies

let is_solved ctor info =
  List.exists (fun (arg_idx, _) -> arg_idx = info.arg_index) ctor.ctor_solved

let residual_informative ctor =
  List.filter
    (fun info -> not info.arg_is_prop && not (is_solved ctor info))
    ctor.ctor_args

let solved_names ctor =
  List.fold_right
    (fun (arg_idx, index_pos) acc ->
       match arg_at ctor.ctor_args arg_idx with
       | Some info -> (info.arg_name, index_pos) :: acc
       | None -> raise Not_classifiable)
    ctor.ctor_solved []

let validate_subset indname ctor carrier_idx prop_indices =
  let infos = ctor.ctor_args in
  let no_erased_payload_dependencies prop_args =
    let prop_names = List.map fst prop_args in
    List.for_all
      (fun (name, ty) ->
         List.for_all
           (fun prop_name -> prop_name = name || not (var_occurs prop_name ty))
           prop_names)
      prop_args
  in
  let is_sort = function
    | SortProp | SortSet | SortType -> true
    | _ -> false
  in
  (* Refinement collapse exposes the erased carrier itself in place of the
     carrier binder, so every remaining proof payload has to stay a proposition
     once the carrier is replaced by a value of the subset type.  A proof field
     whose type applies the carrier in head position (as in a dependent record
     [{ P : A -> Prop & forall x, P x }], where the "carrier" is really a
     predicate the proof asserts) loses its propositional target under that
     substitution: the subset value is not a predicate and cannot head a Prop.
     Such an inductive is a genuine dependent pair, not a subset, so it stays on
     the ordinary (sound) path.  A carrier occurring only as an *argument* of a
     separate predicate (the ordinary [sig]/[{x | P x}] shape) is unaffected. *)
  let carrier_heads_a_proof carrier_name prop_args =
    let rec strip = function
      | Prod(_, _, body) -> strip body
      | ty -> ty
    in
    List.exists
      (fun (_, ty) ->
         match fst (flatten_app (strip ty)) with
         | Var v -> v = carrier_name
         | _ -> false)
      prop_args
  in
  match arg_at infos carrier_idx with
  | Some carrier when residual_informative ctor = [carrier] &&
                       not (is_sort carrier.arg_ty) &&
                       not (carrier_reaches_inductive indname [indname] carrier.arg_ty) ->
      let prop_args =
        List.fold_right
          (fun idx acc ->
             match arg_at infos idx with
             | Some info when info.arg_is_prop -> (info.arg_name, info.arg_ty) :: acc
             | _ -> acc)
          prop_indices []
      in
      if List.length prop_args = List.length prop_indices && prop_args <> [] &&
         no_erased_payload_dependencies prop_args &&
         not (carrier_heads_a_proof carrier.arg_name prop_args) &&
         List.for_all
           (fun (prop_name, _) -> not (var_occurs prop_name carrier.arg_ty))
           prop_args
      then
        CSubset {
          carrier_idx;
          carrier_name = carrier.arg_name;
          subset_args =
            List.map (fun info -> (info.arg_name, info.arg_ty)) ctor.ctor_args;
          prop_args;
          solved = solved_names ctor;
          index_eqs = ctor.ctor_eqs;
          index_formals = ctor.ctor_index_formals;
        }
      else
        CRegular
  | _ -> CRegular

let validate_enum ctor_infos ctor_prop_indices =
  let find_ctor name =
    try Some (List.find (fun info -> info.ctor_name = name) ctor_infos) with Not_found -> None
  in
  let one_ctor (name, prop_indices) =
    match find_ctor name with
    | None -> None
    | Some ctor ->
        let prop_tys =
          List.fold_right
            (fun idx acc ->
               match arg_at ctor.ctor_args idx with
               | Some info when info.arg_is_prop -> info.arg_ty :: acc
               | _ -> acc)
            prop_indices []
        in
        let local_arg_names = List.map (fun info -> info.arg_name) ctor.ctor_args in
        if List.length prop_tys = List.length prop_indices &&
           residual_informative ctor = [] &&
           List.for_all
             (fun prop_ty ->
                List.for_all
                  (fun arg_name -> not (var_occurs arg_name prop_ty))
                  local_arg_names)
             prop_tys
        then
          Some {
            enum_name = name;
            enum_args =
              List.map (fun info -> (info.arg_name, info.arg_ty)) ctor.ctor_args;
            enum_payloads =
              List.map2 (fun idx ty ->
                  match arg_at ctor.ctor_args idx with
                  | Some info -> (info.arg_name, ty)
                  | None -> raise Not_classifiable)
                prop_indices prop_tys;
            enum_solved = solved_names ctor;
            enum_index_eqs = ctor.ctor_eqs;
          }
        else
          None
  in
  let rec collect acc = function
    | [] -> Some (List.rev acc)
    | h :: t ->
        begin match one_ctor h with
        | Some c -> collect (c :: acc) t
        | None -> None
        end
  in
  match collect [] ctor_prop_indices, ctor_infos with
  | Some enum_constructors, ctor :: _ ->
      CEnum {
        enum_constructors;
        enum_index_formals = ctor.ctor_index_formals;
      }
  | _ -> CRegular

let instantiate_class indname ctor_infos = function
  | MEmpty -> CEmpty
  | MPropSingleton ->
      begin match ctor_infos with
      | [_] -> CPropSingleton
      | _ -> CRegular
      end
  | MSubset (carrier_idx, prop_indices) ->
      begin match ctor_infos with
      | [ctor] -> validate_subset indname ctor carrier_idx prop_indices
      | _ -> CRegular
      end
  | MEnum ctor_prop_indices -> validate_enum ctor_infos ctor_prop_indices
  | MRegular -> CRegular

let constructor_fields_depend_on_params params_num cname =
  try
    let (_, _, cargs) =
      Coq_typing.destruct_type_app (coqdef_type (Defhash.find cname))
    in
    let param_names = List.map fst (Hhlib.take params_num cargs) in
    List.exists
      (fun (_, ty) -> List.exists (fun name -> var_occurs name ty) param_names)
      (Hhlib.drop params_num cargs)
  with _ ->
    true

let classify_shape is_prop_ind has_indices ctor_infos =
  (* Singleton proof matches can be erased, and refinement/enum occurrences
     can be expanded from their residual informative arguments.  Solved
     constructor arguments remain in the retained telescope but are not
     residual data.  Anything not recognized stays on the ordinary path for
     totality. *)
  let prop_indices ctor =
    List.fold_right
      (fun info acc -> if info.arg_is_prop then info.arg_index :: acc else acc)
      ctor.ctor_args []
  in
  match ctor_infos with
  | [] -> MEmpty
  | [ctor] when is_prop_ind && List.for_all (fun info -> info.arg_is_prop) ctor.ctor_args ->
      MPropSingleton
  | _ when has_indices && not opt_dependent_types -> MRegular
  | _ when is_prop_ind -> MRegular
  | [ctor] ->
      let informative = residual_informative ctor in
      let prop_args = prop_indices ctor in
      begin match informative, prop_args with
      | [carrier], _ :: _ ->
          MSubset (carrier.arg_index, prop_args)
      | [], _ ->
          MEnum [ctor.ctor_name, prop_args]
      | _ -> MRegular
      end
  | _ ->
      if List.for_all (fun ctor -> residual_informative ctor = []) ctor_infos then
        MEnum (List.map (fun ctor -> (ctor.ctor_name, prop_indices ctor)) ctor_infos)
      else
        MRegular

let constructor_info ctx params params_num index_formals cname =
  let patterns, args = constructor_index_data params params_num cname in
  let mask =
    try informative_index_mask ctx index_formals
    with _ -> raise Not_classifiable
  in
  (* [ford_indices] stops with the shortest of its three lists; a declaration
     whose result-index patterns do not align with its own index telescope is
     malformed and must not be classified from the prefix that does align. *)
  if List.length patterns <> List.length index_formals then
    raise Not_classifiable;
  let fording = ford_indices mask (mk_vars index_formals) args patterns in
  let eqs = fording.ford_eqs in
  let apply_solved tm =
    List.fold_left
      (fun tm solved -> simple_subst solved.ford_arg solved.ford_value tm)
      tm fording.ford_solved
  in
  let args = List.map (fun (name, ty) -> (name, apply_solved ty)) args in
  let rec collect arg_ctx idx acc = function
    | [] -> List.rev acc
    | (name, ty) :: args2 ->
        let ty = simpl ty in
        let is_prop = check_prop arg_ctx ty in
        let info = { arg_index = idx; arg_name = name; arg_ty = ty; arg_is_prop = is_prop } in
        collect ((name, ty) :: arg_ctx) (idx + 1) (info :: acc) args2
  in
  let ctor_args = collect (List.rev index_formals @ ctx) 0 [] args in
  let rec erase_proofs substitutions eqs = function
    | [] -> eqs
    | info :: infos ->
        let ty = List.fold_left (fun ty (name, value) -> simple_subst name value ty)
                   info.arg_ty substitutions
        in
        if info.arg_is_prop then
          (* [destruct_type_app] globally refreshes the binders in the patterns
             and constructor telescope returned by [constructor_index_data], and
             the index formals are globally fresh too.  Consequently [ty] has no
             free name that a residual pattern binder can capture.  Preserve
             that invariant and build the analytical proof cast directly:
             [mk_proof_cast] would refresh already-safe binders and perturb the
             global fresh-name stream merely by classifying metadata. *)
          let value = Cast (Const "$Proof", ty) in
          let eqs =
            List.map (fun (pos, tm) -> (pos, simple_subst info.arg_name value tm)) eqs
          in
          erase_proofs ((info.arg_name, value) :: substitutions) eqs infos
        else
          erase_proofs substitutions eqs infos
  in
  let ctor_solved =
    List.map
      (fun solved -> (solved.ford_arg_index, solved.ford_index_pos))
      fording.ford_solved
  in
  let proof_occurs =
    List.exists
      (fun info ->
         info.arg_is_prop &&
         List.exists (fun (_, tm) -> var_occurs info.arg_name tm) eqs)
      ctor_args
  in
  {
    ctor_name = cname;
    ctor_args;
    ctor_solved;
    ctor_eqs = if proof_occurs then erase_proofs [] eqs ctor_args else eqs;
    ctor_index_formals = index_formals;
  }

let is_erasable_class = function
  | CRegular -> false
  | CEmpty | CPropSingleton | CSubset _ | CEnum _ -> true

(* The memo key of an occurrence, from its already truncated parameters. *)
let occurrence_key ctx indname params =
  (indname, params, context_slice ctx params)

(* The key [is_erasable_instance] may look up, or [None] when [classify] would
   not have keyed the occurrence at all.  The guards repeated here are the ones
   [classify] applies before building its own key, so that a lookup cannot
   answer for a key no classification ever filled. *)
let classifiable_key ctx indname params =
  match get_inductive indname with
  | Some (constrs, params_num, _, _)
       when List.length params >= params_num && List.for_all Defhash.mem constrs ->
      Some (occurrence_key ctx indname (Hhlib.take params_num params))
  | _ -> None

let classify ctx indname params =
  try
    match get_inductive indname with
    | None -> CRegular
    | Some (_, params_num, _, _) when List.length params < params_num ->
        (* A partially applied inductive is not a classifiable instance: its
           parameters are not all determined, so [constructor_info] could not
           substitute them and [check_prop] would be handed unbound formals.
           Such occurrences stay on the status-quo path. *)
        CRegular
    | Some (constrs, _, _, _) when not (List.for_all Defhash.mem constrs) ->
        (* Premise selection can omit a constructor independently of its
           inductive.  There is then no complete set of telescopes to classify,
           and an occurrence outside a match must not be turned into the
           missing-declaration error the case path reports. *)
        CRegular
    | Some (constrs, params_num, ind_ty, ind_sort) ->
        let params = Hhlib.take params_num params in
        let key = occurrence_key ctx indname params in
        (* Destructing the constructor telescopes is by far the expensive part
           of the classification, and [classify] runs at every occurrence of
           every premise type.  It is therefore reached only when the memo
           misses or when the recognized shape genuinely carries occurrence
           terms; the remaining shapes are decided from the declaration. *)
        let constructor_infos () =
          let all_formals = Coq_typing.get_type_args ind_ty in
          let index_formals = index_formals_of all_formals params params_num in
          (List.length all_formals > params_num,
           List.map (constructor_info ctx params params_num index_formals) constrs)
        in
        let expand has_indices ctor_infos shape =
          let cls = instantiate_class indname ctor_infos shape in
          (* Occurrence-level subset collapse must agree with the declaration
             axioms.  Parameter-dependent declarations cannot be classified
             uniformly (a parameter may later be instantiated by [Prop]), so
             [classify_decl] retains constructor injectivity.  For an indexed
             subset that axiom also recovers solved indices from constructor
             equality; collapsing two constructor occurrences to the same
             carrier would therefore make distinct indices equal.  Keep these
             families regular at every occurrence. *)
          match cls with
          | CSubset _ when has_indices &&
                           List.exists
                             (constructor_fields_depend_on_params params_num)
                             constrs ->
              CRegular
          | _ -> cls
        in
        begin match Hashtbl.find_opt memo key with
        | Some { memo_erasable = false; _ } ->
            (* The validated verdict was [CRegular], whatever the shape:
               [MRegular], or a shape [validate_subset]/[validate_enum] or the
               parameter-dependence demotion of [expand] rejected.  There is
               nothing to rebuild the telescopes for. *)
            CRegular
        | Some { memo_shape = MEmpty; _ } -> CEmpty
        | Some { memo_shape = MPropSingleton; _ } -> CPropSingleton
        | Some { memo_shape = (MSubset _ | MEnum _) as shape; _ } ->
            let (has_indices, ctor_infos) = constructor_infos () in
            expand has_indices ctor_infos shape
        | Some { memo_shape = MRegular; _ } -> CRegular
        | None ->
            let (has_indices, ctor_infos) = constructor_infos () in
            let is_prop_ind =
              ind_sort = SortProp || Coq_typing.check_type_target_is_prop ind_ty
            in
            let shape = classify_shape is_prop_ind has_indices ctor_infos in
            let cls = expand has_indices ctor_infos shape in
            Hashtbl.add memo key
              { memo_shape = shape; memo_erasable = is_erasable_class cls };
            cls
        end
  with Not_classifiable | Failure _ -> CRegular

(* [has_erasable_content] asks for nothing but this bit at every application
   node of every premise type, and discards the rest of the classification.
   Answering it from the memo is what keeps a [bool] or [sumbool] occurrence
   from rebuilding a constructor telescope per occurrence; only the first
   occurrence of a key runs the classification.

   The bit is memoized rather than the [CSubset]/[CEnum] record itself.  Those
   records escape into emitted terms -- guard expansion substitutes through
   [subset_args] and instantiates [enum_args] into constructor tags -- and
   their binders are globally fresh per classification, which nested guards
   over one formula rely on.  (The [constructor_formals_hash] of [Coq_transl]
   caches such a telescope, but only [Coq_typing.check_prop] ever reads it and
   nothing from it reaches an axiom.)  Returning one record twice would put the
   same binder names in two places of one formula, so the record is rebuilt and
   only the verdict is remembered. *)
let is_erasable_instance ctx indname params =
  match classifiable_key ctx indname params with
  | None -> false
  | Some key ->
      begin match Hashtbl.find_opt memo key with
      | Some entry -> entry.memo_erasable
      | None -> is_erasable_class (classify ctx indname params)
      end

let classify_decl indname =
  match get_inductive indname with
  | None -> None
  | Some (constrs, params_num, ind_ty, _) ->
      (* A formal parameter can later be instantiated by a proposition or a
         proposition-valued family.  If constructor fields mention parameters,
         their proof/content masks (and therefore subset classification) are not
         declaration invariants.  Declaration-level skips are optional, so use
         the conservative occurrence-independent subset only. *)
      if List.exists (constructor_fields_depend_on_params params_num) constrs then
        None
      else
        (try
           let formals = Hhlib.take params_num (Coq_typing.get_type_args ind_ty) in
           (* [get_type_args] refreshes every binder, so the same declaration
              yields different formal names at every call.  Those names are part
              of the memo key, through both the parameters and the context slice
              they are typed in, so keying on them would file one entry no later
              call can ever look up and re-run the classification every time.
              Rename them positionally instead: the key then depends on the
              declaration alone.  The names cannot collide -- a refreshed binder
              is [var_<name>_<id>] and a Rocq identifier holds no [$] -- and
              they stay inside the classification, which reads their types and
              returns no term built over them. *)
           let rec canonical i renaming acc = function
             | [] -> List.rev acc
             | (name, ty) :: formals2 ->
                 let name2 = "$decl_param_" ^ string_of_int i in
                 let ty2 =
                   List.fold_left
                     (fun ty (n, n2) -> simple_subst n (Var n2) ty) ty renaming
                 in
                 canonical (i + 1) ((name, name2) :: renaming)
                   ((name2, ty2) :: acc) formals2
           in
           let params = canonical 0 [] [] formals in
           let ctx = List.rev params in
           Some (classify ctx indname (mk_vars params))
         with Failure _ -> None)

(* The retained telescope of a classified constructor refers to every solved
   argument through the index formal that fords it, which only a consumer
   holding the occurrence's indices can instantiate.  A consumer holding the
   constructor's own arguments instead -- a constructor application rather than
   a typing occurrence -- needs the ordinary telescope back, with each such
   formal restored to the argument it stands for. *)
let unford_telescope index_formals solved args =
  let substitutions =
    List.map
      (fun (arg_name, index_pos) ->
         (fst (List.nth index_formals index_pos), Var arg_name))
      solved
  in
  List.map
    (fun (name, ty) ->
       (name,
        List.fold_left
          (fun ty (formal, value) -> simple_subst formal value ty)
          ty substitutions))
    args

let rec has_erasable_content ctx tm =
  let classifies_here =
    match flatten_app tm with
    | Const indname, args -> is_erasable_instance ctx indname args
    | _ -> false
  in
  classifies_here ||
  match tm with
  | Var _ | Const _ | SortProp | SortSet | SortType -> false
  | App (x, y) -> has_erasable_content ctx x || has_erasable_content ctx y
  | Lam (name, ty, body) | Prod (name, ty, body) | Quant (_, (name, ty, body)) ->
      has_erasable_content ctx ty || has_erasable_content ((name, ty) :: ctx) body
  | Let (value, (name, ty, body)) ->
      has_erasable_content ctx value || has_erasable_content ctx ty ||
      has_erasable_content ((name, ty) :: ctx) body
  | Case (_, matched_term, return_type, _, _, branches) ->
      has_erasable_content ctx matched_term || has_erasable_content ctx return_type ||
      List.exists (fun (_, branch) -> has_erasable_content ctx branch) branches
  | Cast (term, ty) -> has_erasable_content ctx term || has_erasable_content ctx ty
  | Fix (_, _, _, _, types, bodies) ->
      List.exists (has_erasable_content ctx) types || List.exists (has_erasable_content ctx) bodies
  | IndType _ -> false
  | Equal (x, y) -> has_erasable_content ctx x || has_erasable_content ctx y
