(* Classification of inductive instances for proof/content erasure.

   This module only chooses the translation path.  CPropSingleton/CEmpty cover
   proof-only matches, CSubset/CEnum cover shallow expansion of informative
   payloads, and CRegular leaves the ordinary translation unchanged. *)

open Hammer_lib
open Coqterms

type ind_class =
  | CEmpty
  | CPropSingleton
  | CSubset of { carrier_idx : int; carrier_name : string; prop_args : (string * coqterm) list }
  | CEnum of (string * coqterm list) list
  | CRegular

type arg_info = {
  arg_index : int;
  arg_name : string;
  arg_ty : coqterm;
  arg_is_prop : bool;
}

type ctor_info = {
  ctor_name : string;
  ctor_args : arg_info list;
}

type memo_class =
  | MEmpty
  | MPropSingleton
  | MSubset of int * int list
  | MEnum of (string * int list) list
  | MRegular

let memo : ((string * bool list * bool * bool list list), memo_class) Hashtbl.t = Hashtbl.create 257

let clear () = Hashtbl.clear memo

exception Not_classifiable

let check_prop ctx ty =
  try Coq_typing.check_prop ctx ty with _ -> raise Not_classifiable

let is_ex_ind name = Coq_stdnames.is_init_logic "ex" name
let is_eq_ind name = Coq_stdnames.is_init_logic "eq" name
let is_acc_ind name = Coq_stdnames.is_init_wf "Acc" name

let is_instance_dependent_decl name =
  Coq_stdnames.is_init_datatypes "prod" name ||
  Coq_stdnames.is_init_datatypes "sum" name ||
  Coq_stdnames.is_init_specif "sigT" name

let get_inductive name =
  if Defhash.mem name then
    match Defhash.find name with
    | (_, IndType(_, constrs, params_num), ind_ty, ind_sort) ->
        Some (constrs, params_num, ind_ty, ind_sort)
    | _ -> None
  else
    None

let arg_at infos idx =
  try Some (List.find (fun info -> info.arg_index = idx) infos) with Not_found -> None

let validate_subset indname infos carrier_idx prop_indices =
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
  match arg_at infos carrier_idx with
  | Some carrier when not carrier.arg_is_prop && not (is_sort carrier.arg_ty) &&
                       not (term_mentions_const [indname] carrier.arg_ty) ->
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
         List.for_all
           (fun (prop_name, _) -> not (var_occurs prop_name carrier.arg_ty))
           prop_args
      then
        CSubset { carrier_idx; carrier_name = carrier.arg_name; prop_args }
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
           List.for_all (fun info -> info.arg_is_prop) ctor.ctor_args &&
           List.for_all
             (fun prop_ty ->
                List.for_all
                  (fun arg_name -> not (var_occurs arg_name prop_ty))
                  local_arg_names)
             prop_tys
        then
          Some (name, prop_tys)
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
  match collect [] ctor_prop_indices with
  | Some ctors -> CEnum ctors
  | None -> CRegular

let instantiate_class indname ctor_infos = function
  | MEmpty -> CEmpty
  | MPropSingleton -> CPropSingleton
  | MSubset (carrier_idx, prop_indices) ->
      begin match ctor_infos with
      | [ctor] -> validate_subset indname ctor.ctor_args carrier_idx prop_indices
      | _ -> CRegular
      end
  | MEnum ctor_prop_indices -> validate_enum ctor_infos ctor_prop_indices
  | MRegular -> CRegular

let classify_shape indname is_prop_ind has_indices ctor_infos =
  (* Singleton proof matches can be erased, and refinement/enum occurrences
     can be expanded from their informative payloads.  Anything not recognized
     stays on the ordinary path for totality.

     Indexed families need their indices reflected in the generated premises.
     The current shallow expansion records constructor payloads but not result-
     index constraints, so classifying indexed families as CEnum/CSubset or
     CPropSingleton would be too weak (e.g. equality/transport could be reduced
     without requiring the source equality).  Keep them on the ordinary path
     until index constraints are represented.  [Acc] is the one indexed
     proof-singleton exception: its erasure path has a well-founded-recursion
     guardrail in the translation layer. *)
  match ctor_infos with
  | [] -> MEmpty
  | _ when is_ex_ind indname -> MRegular
  | _ when is_eq_ind indname -> MPropSingleton
  | [ctor] when is_prop_ind && List.for_all (fun info -> info.arg_is_prop) ctor.ctor_args ->
      MPropSingleton
  | _ when has_indices && not (is_acc_ind indname) -> MRegular
  | _ when is_prop_ind -> MRegular
  | [ctor] ->
      let informative = List.filter (fun info -> not info.arg_is_prop) ctor.ctor_args in
      let prop_args = List.filter (fun info -> info.arg_is_prop) ctor.ctor_args in
      begin match informative, prop_args with
      | [carrier], _ :: _ ->
          MSubset (carrier.arg_index, List.map (fun info -> info.arg_index) prop_args)
      | [], _ ->
          MEnum [ctor.ctor_name, List.map (fun info -> info.arg_index) prop_args]
      | _ -> MRegular
      end
  | _ ->
      if List.for_all (fun ctor -> List.for_all (fun info -> info.arg_is_prop) ctor.ctor_args) ctor_infos then
        MEnum
          (List.map
             (fun ctor ->
                (ctor.ctor_name, List.map (fun info -> info.arg_index) ctor.ctor_args))
             ctor_infos)
      else
        MRegular

let constructor_info ctx params params_num cname =
  let (_, _, cargs) = Coq_typing.destruct_type_app (coqdef_type (Defhash.find cname)) in
  let param_formals = Hhlib.take params_num cargs in
  let args =
    List.map
      (fun (name, ty) -> (name, subst_params param_formals params ty))
      (Hhlib.drop params_num cargs)
  in
  let rec collect ctx idx acc = function
    | [] -> List.rev acc
    | (name, ty) :: args2 ->
        let ty = simpl ty in
        let is_prop = check_prop ctx ty in
        let info = { arg_index = idx; arg_name = name; arg_ty = ty; arg_is_prop = is_prop } in
        collect ((name, ty) :: ctx) (idx + 1) (info :: acc) args2
  in
  { ctor_name = cname; ctor_args = collect ctx 0 [] args }

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
    | Some (constrs, params_num, ind_ty, ind_sort) ->
        let all_formals = Coq_typing.get_type_args ind_ty in
        let has_indices = List.length all_formals > params_num in
        let params = Hhlib.take params_num params in
        let mask = List.map (check_prop ctx) params in
        let ctor_infos = List.map (constructor_info ctx params params_num) constrs in
        let is_prop_ind =
          ind_sort = SortProp || Coq_typing.check_type_target_is_prop ind_ty
        in
        let ctor_prop_mask =
          List.map (fun ctor -> List.map (fun info -> info.arg_is_prop) ctor.ctor_args) ctor_infos
        in
        let key = (indname, mask, is_prop_ind, ctor_prop_mask) in
        let shape =
          try Hashtbl.find memo key with Not_found ->
            let shape = classify_shape indname is_prop_ind has_indices ctor_infos in
            Hashtbl.add memo key shape;
            shape
        in
        instantiate_class indname ctor_infos shape
  with Not_classifiable -> CRegular

let classify_decl indname =
  if is_instance_dependent_decl indname then
    None
  else
    match get_inductive indname with
    | None -> None
    | Some (_, params_num, ind_ty, _) ->
        let params = Hhlib.take params_num (Coq_typing.get_type_args ind_ty) in
        let ctx = List.rev params in
        Some (classify ctx indname (mk_vars params))

let is_erasable_class = function
  | CRegular -> false
  | CEmpty | CPropSingleton | CSubset _ | CEnum _ -> true

let params_for_inductive indname args =
  match get_inductive indname with
  | Some (_, params_num, _, _) -> Hhlib.take params_num args
  | None -> args

let rec has_erasable_content ctx tm =
  let classifies_here =
    match flatten_app tm with
    | Const indname, args ->
        begin match get_inductive indname with
        | Some _ -> is_erasable_class (classify ctx indname (params_for_inductive indname args))
        | None -> false
        end
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
