(* Convert hhterm to coqterm *)

open Hammer_lib
open Hh_term
open Coqterms
open Coq_transl_opts

(* Canonical names of the core logical constants, resolved through the
   registered references so that they match the names produced by
   [hhterm_of_global] on any Rocq version. *)
let logic_True = lazy (Hhutils.lib_ref_name "core.True.type")
let logic_False = lazy (Hhutils.lib_ref_name "core.False.type")
let logic_and = lazy (Hhutils.lib_ref_name "core.and.type")
let logic_or = lazy (Hhutils.lib_ref_name "core.or.type")
let logic_not = lazy (Hhutils.lib_ref_name "core.not.type")
let logic_iff = lazy (Hhutils.lib_ref_name "core.iff.type")
let logic_eq = lazy (Hhutils.lib_ref_name "core.eq.type")
let logic_ex = lazy (Hhutils.lib_ref_name "core.ex.type")
let logic_all = lazy (Hhutils.lib_ref_name "core.all")

(* A case predicate is type-level CIC data.  In particular, its scrutinee binder
   records the instantiated inductive type.  Do not lower logical
   inductives to FOL syntax while converting it, or case compilation loses the
   parameters of matches on [ex], [or], and similar propositions. *)
let preserving_case_predicate = ref false

let with_case_predicate f =
  let previous = !preserving_case_predicate in
  preserving_case_predicate := true;
  try
    let result = f () in
    preserving_case_predicate := previous;
    result
  with e ->
    preserving_case_predicate := previous;
    raise e

(***************************************************************************************)
(* Check input *)

let is_valid_name name =
  not (is_logop name) && (String.length name < 2 || String.sub name 0 2 <> "$_")
let check_name name = if not (is_valid_name name) then failwith ("check_name: " ^ name) else ()

(***************************************************************************************)
(* Convert input to coqterms *)

let to_coqsort kind =
  match kind with
  | Comb(Id "$Sort", Id "$Prop") -> SortProp
  | Comb(Id "$Sort", Id "$Type") -> SortType
  | Comb(Id "$Sort", Id "$Set") -> if opt_set_to_type then SortType else SortSet
  | _ -> SortType
(* the last case may happen with e.g.: Let U := Type. Variable A : U. Variable x : A. *)

let rec to_coqterm tm =
  let is_fix = function Comb(Id "$Fix", _) -> true | _ -> false
  and is_cofix = function Id "$CoFix" -> true | _ -> false
  in
  match tm with
  | Comb(Comb(Id "$Ind", Id name), _)
      when not !preserving_case_predicate && name = Lazy.force logic_True ->
    Const("$True")

  | Comb(Comb(Id "$Ind", Id name), _)
      when not !preserving_case_predicate && name = Lazy.force logic_False ->
    Const("$False")

  | Comb(Comb(Id "$Ind", Id name), _)
      when not !preserving_case_predicate && name = Lazy.force logic_and ->
    Const("&")

  | Comb(Comb(Id "$Ind", Id name), _)
      when not !preserving_case_predicate && name = Lazy.force logic_or ->
    Const("|")

  | Comb(Id "$Const", Id name)
      when not !preserving_case_predicate && name = Lazy.force logic_not ->
    Const("~")

  | Comb(Id "$Const", Id name)
      when not !preserving_case_predicate && name = Lazy.force logic_iff ->
    Const("<=>")

  | Comb(Comb(Id "$Ind", Id name), _)
      when not !preserving_case_predicate && opt_translate_eq && name = Lazy.force logic_eq ->
    Const("=")

  | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id name), _)),
         Comb(Comb(Id "$ConstrArray", _),
              Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id varname)), vartype), body)))
      when not !preserving_case_predicate && name = Lazy.force logic_ex ->
    Quant("?", (varname, to_coqterm vartype, to_coqterm body))

  | Comb(Comb(Id "$App", Comb(Id "$Const", Id name)),
         Comb(Comb(Id "$ConstrArray", _),
              Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id varname)), vartype), body)))
      when not !preserving_case_predicate && name = Lazy.force logic_all ->
    Quant("!", (varname, to_coqterm vartype, to_coqterm body))

  | Comb(Id "$App", Comb(Comb(Id "$Ind", Id name), _))
      when not !preserving_case_predicate && name = Lazy.force logic_ex ->
    Const("?")

  | Comb(Id "$Const", Id name)
      when not !preserving_case_predicate && name = Lazy.force logic_all ->
    Const("!")

  | Comb(Id "$Rel", Id num) ->
    Var(num)

  | Comb(Id "$Const", Id name) ->
    check_name name;
    Const(name)

  | Comb(Id "$Var", Id name) ->
    check_name name;
    Const(name)

  | Comb(Comb(Id "$App", left), args) ->
    let rec build_app left args =
      match args with
      | Comb(args2, arg) ->
        App(build_app left args2, to_coqterm arg)
      | Id "$ConstrArray" ->
        to_coqterm left
      | _ ->
        failwith "to_coqterm: build_app"
    in
    build_app left args

  | Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id varname)), vartype), body) ->
    check_name varname;
    Lam(varname, to_coqterm vartype, to_coqterm body)

  | Comb(Comb(Comb(Comb(Id "$Case", Comb(Comb(Comb(Comb(Id "$CaseInfo",
                                                   Comb(Comb(Id "$Ind", Id indname), _)),
                                                   Id npar), _ndecls_arr), nargs_arr)),
                   return_type_lam),
              matched_term), cases) ->
    let rec parse_cases cases nargs_arr acc =
      match cases, nargs_arr with
      | Id "$ConstrArray", Id "$IntArray" -> acc
      | Comb(cases2, c), Comb(nargs_arr2, Id nargs) ->
        parse_cases cases2 nargs_arr2 ((int_of_string nargs, to_coqterm c) :: acc)
      | _ -> failwith "parse_cases"
    in
    check_name indname;
    Case(indname, to_coqterm matched_term, to_coqterm return_type_lam,
         to_case_predicate return_type_lam, int_of_string npar,
         parse_cases cases nargs_arr [])

  | Comb(Comb(Comb(Comb(Id "$LetIn", Comb(Id "$Name", Id varname)), value), vartype), body) ->
    check_name varname;
    Let(to_coqterm value, (varname, to_coqterm vartype, to_coqterm body))

  | Comb(Comb(Id "$Construct", _), Id constrname) ->
    check_name constrname;
    Const(constrname)

  | Comb(Comb(Id "$Cast", trm), ty) ->
    Cast(to_coqterm trm, to_coqterm ty)

  | Comb(Comb(fix_or_cofix, Id result_index),
         Comb(Comb(Comb(Id "$PrecDeclaration", names), types), bodies))
      when
        (is_fix fix_or_cofix || is_cofix fix_or_cofix) ->
    let rec build_lst f (trm : hhterm) acc =
      match trm with
      | Comb(trm2, arg) ->
        build_lst f trm2 ((f arg) :: acc)
      | Id "$ConstrArray" | Id "$NameArray" | Id "$IntArray" ->
        acc
      | _ ->
        failwith "to_coqterm: build_lst"
    and name_to_str = function
      | Comb(Id "$Name", Id name) -> check_name name; name
      | _ -> failwith "name_to_str"
    and int_to_int = function
      | Id n -> int_of_string n
      | _ -> failwith "int_to_int"
    in
    let cft, recargs =
      match fix_or_cofix with
      | Comb(Id "$Fix", recargs) -> CoqFix, build_lst int_to_int recargs []
      | Id "$CoFix" -> CoqCoFix, []
      | _ -> failwith "to_coqterm: fix_or_cofix"
    in
    Fix(cft, int_of_string result_index, recargs,
        build_lst name_to_str names [], build_lst to_coqterm types [],
        build_lst to_coqterm bodies [])

  | Comb(Comb(Comb(Id "$Prod", Comb(Id "$Name", Id varname)), vartype), body) ->
    check_name varname;
    Prod(varname, to_coqterm vartype, to_coqterm body)

  | Comb(Id "$Sort", Id "$Prop") ->
    SortProp

  | Comb(Id "$Sort", Id "$Set") ->
    if opt_set_to_type then SortType else SortSet

  | Comb(Id "$Sort", Id "$Type") ->
    SortType

  | Comb(Comb(Id "$Ind", Id indname), _) ->
    check_name indname;
    Const(indname)

  | Comb(Comb(Comb(Id "$Proj", _), _), _) ->
     Const("unsupported__" ^ unique_id ())
  (* TODO: primitive projections not really supported *)
  | Comb(Id "$Int", _) ->
     Const("unsupported__" ^ unique_id ())
  (* TODO: primitive integers not really supported *)
  | Comb(Id "$Float", _) ->
     Const("unsupported__" ^ unique_id ())
  (* TODO: primitive floats not really supported *)
  | _ ->
     print_endline (string_of_hhterm tm);
     failwith ("to_coqterm")

and to_case_predicate tm =
  match tm with
  | Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id varname)), vartype), body) ->
     check_name varname;
     Lam(varname, with_case_predicate (fun () -> to_coqterm vartype),
         to_case_predicate body)
  | _ -> to_coqterm tm

let to_coqdef (def : hhdef) (lst : hhdef list) =
  let rec parse_constrs lst cacc =
    match lst with
    | (Comb(Comb(Id "$Construct", _), Id constrname), _, kind, ty, _) :: t ->
       parse_constrs t (constrname :: cacc)
    | _ -> List.rev cacc
  in
  match def with
  | (Comb(Comb(Id "$Ind", Id indname), Id params_num), _, kind, ty, _) ->
      let constrs = parse_constrs lst []
      in
      log 2 ("to_coqdef: " ^ indname);
      (indname, IndType(indname, constrs, int_of_string params_num),
       to_coqterm (force_hhterm ty), to_coqsort kind)
  | (Comb(Id "$Const", Id name), _, Comb(Id "$Sort", Id "$Prop"), ty, _) ->
      log 2 ("to_coqdef (omit proof): " ^ name);
      (name, Const(name), to_coqterm (force_hhterm ty), SortProp)
  | (Comb(Id "$Const", Id name), opaque, kind, ty, prf) ->
    begin
      log 2 ("to_coqdef: " ^ name);
      let prf =
        if opaque then
          Const(name)
        else
          let vp = force_hhterm prf in
          match vp with
          | Id "$Axiom" ->
             Const(name)
          | _ ->
             to_coqterm vp
      in
      (name, prf, to_coqterm (force_hhterm ty), to_coqsort kind)
    end
  | (Comb(Comb(Id "$Construct", _), Id constrname), _, kind, ty, _) ->
      log 2 ("to_coqdef: " ^ constrname);
      (constrname, Const(constrname), to_coqterm (force_hhterm ty), to_coqsort kind)
  | _ ->
      failwith ("to_coqdef: " ^ get_hhdef_name def)
