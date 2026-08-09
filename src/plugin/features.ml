open Hammer_lib
open Hh_term
open Hammer_errors

(*********************************************************************************)
(* feature options *)

let opt_feature_polarity = true

(*********************************************************************************)

(* Canonical names of the core logical constants, resolved through the
   registered references so that they match the names produced by
   [hhterm_of_global] on any Rocq version. *)
let logic_and = lazy (Hhutils.lib_ref_name "core.and.type")
let logic_or = lazy (Hhutils.lib_ref_name "core.or.type")
let logic_not = lazy (Hhutils.lib_ref_name "core.not.type")
let logic_iff = lazy (Hhutils.lib_ref_name "core.iff.type")
let logic_ex = lazy (Hhutils.lib_ref_name "core.ex.type")
let logic_all = lazy (Hhutils.lib_ref_name "core.all")

(* The module prefix of the logical constants, e.g. "Corelib.Init.Logic." *)
let logic_prefix = lazy
  (let s = Hhutils.lib_ref_name "core.False.type" in
   String.sub s 0 (String.length s - String.length "False"))

let is_logic_name c = Hhlib.string_begins_with c (Lazy.force logic_prefix)

let extract_consts (t : hhterm) : string list =
  let rec pom t acc =
    match t with
    | Id _ ->
      acc
    | Comb(Comb(Id "$Construct", x), Id c)
        when
          not (is_logic_name c) ->
      pom x (c :: acc)
    | Comb(Id x, Id c)
        when (x = "$Const" || x = "$Ind") &&
          not (is_logic_name c) ->
      (c :: acc)
    | Comb(x, y) ->
      pom y (pom x acc)
  in
  Hhlib.sort_uniq compare (pom t [])

let rec top_feature = function
  | Comb(Comb(Id "$Construct", _), Id c)
  | Comb(Comb(Id "$Ind", Id c), _)
  | Comb(Id "$Const", Id c) -> c
  | Comb(Id "$Var", Id _) -> "X"
  | Comb(Id "$Rel", Id _) -> "X"
  | Comb(Comb(Id "$App", t), _) -> top_feature t
  | _ -> ""

let extract_features (t : hhterm) : string list =
  let get_polarized c pos =
    if pos then
      c ^ "+"
    else
      c ^ "-"
  in
  let add_feature c pos acc =
    if opt_feature_polarity then
      c :: (get_polarized c pos) :: acc
    else
      c :: acc
  in
  let rec pom t pos acc =
    match t with
    | Id _ ->
      acc
    | Comb(Comb(Comb(Id "$Prod", Comb(Id "$Name", Id _)), vartype), body) ->
       pom vartype (not pos) (pom body pos acc)
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id c), _)), args)
        when c = Lazy.force logic_and || c = Lazy.force logic_or ->
       pom args pos acc
    | Comb(Comb(Id "$App", Comb(Id "$Const", Id c)), args)
        when c = Lazy.force logic_not ->
       pom args (not pos) acc
    | Comb(Comb(Id "$App", Comb(Id "$Const", Id c)), args)
        when c = Lazy.force logic_iff ->
       pom args pos (pom args (not pos) acc)
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id c), _)),
           Comb(Comb(Id "$ConstrArray", _),
                Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id _)), vartype), body)))
        when c = Lazy.force logic_ex ->
       pom vartype pos (pom body pos acc)
    | Comb(Comb(Id "$App", Comb(Id "$Const", Id c)),
           Comb(Comb(Id "$ConstrArray", _),
                Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id _)), vartype), body)))
        when c = Lazy.force logic_all ->
       pom vartype (not pos) (pom body pos acc)
    | Comb(Comb(Id "$Construct", x), Id c)
        when
          not (is_logic_name c) ->
       pom x pos (add_feature c pos acc)
    | Comb(Id x, Id c)
        when (x = "$Const" || x = "$Ind") &&
          not (is_logic_name c) ->
       add_feature c pos acc
    | Comb(Comb(Id "$App", Comb(Id "$Const", Id c)), args)
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id c), _)), args)
    | Comb(Comb(Id "$App", Comb(Id "$Var", Id c)), args)
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Construct", _), Id c)), args) ->
       let rec app_fea acc = function
         | Id "$ConstrArray" -> acc
         | Comb(moreargs, arg) ->
            begin match top_feature arg with
            | "" -> app_fea acc moreargs
            | s -> app_fea ((c ^ "-" ^ s) :: acc) moreargs
            end
         | _ ->
            failwith "impossible"
       in
       let feas = c :: app_fea [] args in
       pom args pos (List.fold_left (fun acc c -> add_feature c pos acc) acc feas)
    | Comb(x, y) ->
       pom y pos (pom x pos acc)
  in
  Hhlib.sort_uniq compare (pom t true [])

let get_def_fea_term (def : hhdef) : hhterm =
  match def with
  | (_, true, _, ty, _) ->
     Lazy.force ty
  | (_, false, _, ty, prf) ->
     Comb(Lazy.force ty, Lazy.force prf)

let get_def_features (def : hhdef) : string list =
  extract_features (get_def_fea_term def)

let get_goal_features (hyps : hhdef list) (goal : hhdef) : string list =
  let rec pom lst =
    match lst with
    | [] -> get_def_fea_term goal
    | h :: t ->
       Comb(Comb(Comb(Id "$Prod", Comb(Id "$Name", Id "$Anonymous")), get_def_fea_term h), pom t)
  in
  extract_features (pom hyps)

let get_deps (def : hhdef) : string list =
  match def with
  | (_, _, _, ty, prf) ->
    extract_consts (Comb(Lazy.force ty, Lazy.force prf))

let features_cache = Hashtbl.create 1024
let deps_cache = Hashtbl.create 1024

let cleanup () =
  Hashtbl.reset features_cache;
  Hashtbl.reset deps_cache

(* Variables must not be cached under their names: the same name may
   denote a different variable in another section or proof. *)

let get_def_features_cached (def : hhdef) : string list =
  if hhdef_is_var def then
    get_def_features def
  else
    let name = get_hhdef_name def in
    try
      Hashtbl.find features_cache name
    with Not_found ->
      let fea = get_def_features def in
      Hashtbl.add features_cache name fea;
      fea

let get_deps_cached (def : hhdef) : string list =
  if hhdef_is_var def then
    get_deps def
  else
    let name = get_hhdef_name def in
    try
      Hashtbl.find deps_cache name
    with Not_found ->
      let deps = get_deps def in
      Hashtbl.add deps_cache name deps;
      deps

(* A name is under one of [prefixes] if it begins with any of them.  Each
   filtered module is listed under both its legacy [Stdlib.*] name and its
   current [Corelib.*] (or bare) name: after the Rocq stdlib/corelib split the
   problematic definitions are emitted as e.g. [Corelib.Classes.Morphisms.Proper]
   and [Hurkens.TypeNeqSmallType.paradox], so a single legacy prefix silently
   matched nothing and the filter became a no-op. *)
let begins_with_any name prefixes =
  List.exists (fun p -> Hhlib.string_begins_with name p) prefixes

let filter_program_prefixes = ["Stdlib.Program."; "Corelib.Program."]
let filter_classes_prefixes = ["Stdlib.Classes."; "Corelib.Classes."]
let filter_hurkens_prefixes = ["Stdlib.Logic.Hurkens."; "Corelib.Logic.Hurkens."; "Hurkens."]

let is_nontrivial (def : hhdef) : bool =
  let name = get_hhdef_name def in
  name <> "" && not (is_logic_name name) &&
    (if !Opt.filter_program then not (begins_with_any name filter_program_prefixes) else true) &&
    (if !Opt.filter_classes then not (begins_with_any name filter_classes_prefixes) else true) &&
    (if !Opt.filter_hurkens then not (begins_with_any name filter_hurkens_prefixes) else true)

type selection_ctx = {
  ndefs : hhdef list;
  def_tbl : (string, hhdef) Hashtbl.t;
  occ : (string, int) Hashtbl.t Lazy.t;
  dcands : hhdef list Lazy.t;
}

let constructor_inductive (def : hhdef) : string option =
  match def with
  | (Comb(Comb(Id "$Construct",
                    Comb(Comb(Id "$Ind", Id ind), _)), Id _), _, _, _, _) ->
     Some ind
  | _ -> None

let inductive_name (def : hhdef) : string option =
  match def with
  | (Comb(Comb(Id "$Ind", Id ind), _), _, _, _, _) -> Some ind
  | _ -> None

let make_selection_ctx (hyps : hhdef list) (defs : hhdef list) (goal : hhdef) : selection_ctx =
  let ndefs = List.filter is_nontrivial defs in
  let def_tbl = Hashtbl.create (List.length ndefs) in
  List.iter
    (fun def -> Hashtbl.replace def_tbl (get_hhdef_name def) def)
    ndefs;
  let occ =
    lazy
      (let tbl = Hashtbl.create (List.length ndefs) in
       List.iter
         (fun def ->
            List.iter
              (fun name ->
                 let count =
                   match Hashtbl.find_opt tbl name with
                   | Some count -> count
                   | None -> 0
                 in
                 Hashtbl.replace tbl name (count + 1))
              (get_deps_cached def))
         ndefs;
       tbl)
  in
  let make_dcands occ =
    let seed_names =
      Hhlib.strset_from_lst
        (get_deps goal @ List.concat_map get_deps hyps)
    in
    let seed_defs =
      List.filter
        (fun def -> Hhlib.StringSet.mem (get_hhdef_name def) seed_names)
        ndefs
    in
    let constructors = Hashtbl.create 64 in
    List.iter
      (fun def ->
         match constructor_inductive def with
         | Some ind ->
            let defs =
              match Hashtbl.find_opt constructors ind with
              | Some defs -> defs
              | None -> []
            in
            Hashtbl.replace constructors ind (def :: defs)
         | None -> ())
      ndefs;
    let candidate_names = ref seed_names in
    List.iter
      (fun def ->
         match constructor_inductive def, inductive_name def with
         | Some ind, _ when Hashtbl.mem def_tbl ind ->
            candidate_names := Hhlib.StringSet.add ind !candidate_names
         | _, Some ind ->
            begin match Hashtbl.find_opt constructors ind with
            | Some defs ->
               List.iter
                 (fun def ->
                    candidate_names :=
                      Hhlib.StringSet.add (get_hhdef_name def) !candidate_names)
                 defs
            | None -> ()
            end
         | _ -> ())
      seed_defs;
    let occ = Lazy.force occ in
    let ranked =
      List.filter_map
        (fun def ->
           let name = get_hhdef_name def in
           if Hhlib.StringSet.mem name !candidate_names then
             let count =
               match Hashtbl.find_opt occ name with
               | Some count -> count
               | None -> 0
             in
             Some (count, hhterm_size (get_def_fea_term def), name, def)
           else
             None)
        ndefs
    in
    List.map
      (fun (_, _, _, def) -> def)
      (List.sort
         (fun (occ1, size1, name1, _) (occ2, size2, name2, _) ->
            let c = compare occ1 occ2 in
            if c <> 0 then c
            else
              let c = compare size1 size2 in
              if c <> 0 then c else String.compare name1 name2)
         ranked)
  in
  let rec ctx : selection_ctx =
    { ndefs; def_tbl; occ; dcands = lazy (make_dcands ctx.occ) }
  in
  ctx

let extract (ctx : selection_ctx) (hyps : hhdef list) (goal : hhdef) : string =
  Msg.info "Extracting features...";
  let fname = Opt.temp_file "predict" "" in
  let ocfea = open_out (fname ^ "fea") in
  let ocdep = open_out (fname ^ "dep") in
  let ocseq = open_out (fname ^ "seq") in
  let defs = ctx.ndefs in
  if !Opt.debug_mode then
    Msg.info ("After filtering: " ^ string_of_int (List.length defs) ^ " Coq objects.");
  let write_def def =
    let name = get_hhdef_name def in
    output_string ocseq name; output_char ocseq '\n';
    let fea = get_def_features_cached def in
    output_string ocfea name; output_char ocfea ':';
    (* For empty features output empty quotes *)
    output_char ocfea '\"';
    Hhlib.oiter (output_string ocfea) (output_string ocfea) "\", \"" fea;
    output_string ocfea "\"\n";
    let pre_deps = get_deps_cached def in
    let deps = List.filter (fun name -> Hashtbl.mem ctx.def_tbl name) pre_deps in
    output_string ocdep name; output_char ocdep ':';
    if deps <> [] then Hhlib.oiter (output_string ocdep) (output_string ocdep) " " deps;
    output_char ocdep '\n';
  in
  List.iter write_def defs;
  close_out ocfea;
  close_out ocseq;
  close_out ocdep;
  let oc = open_out (fname ^ "conj") in
  let fea = get_goal_features hyps goal in
  output_char oc '\"';
  Hhlib.oiter (output_string oc) (output_string oc) "\", \"" fea;
  output_string oc "\"\n";
  close_out oc;
  fname

let choose_given_lemmas (hyps : hhdef list) (defs : hhdef list) (lems : hhdef list) (goal : hhdef) : hhdef list =
  Msg.info "Choosing definitions...";
  let ndefs = List.filter is_nontrivial defs in
  if !Opt.debug_mode then
    Msg.info ("After filtering: " ^ string_of_int (List.length ndefs) ^ " Coq objects.");
  let names = Hhlib.strset_from_lst (List.map get_hhdef_name ndefs) in
  let filter_deps deps = List.filter (fun a -> Hhlib.StringSet.mem a names) deps in
  let choose_def def =
    get_hhdef_name def :: filter_deps (get_deps_cached def)
  in
  (* The goal and the hypotheses are local to the current proof, so
     their dependencies must not be cached under their names. *)
  let goal_deps = filter_deps (get_deps goal) in
  let hyps_deps = List.concat (List.map (fun h -> filter_deps (get_deps h)) hyps) in
  let objs =
    Hhlib.strset_from_lst
      (goal_deps @ hyps_deps @ List.concat (List.map choose_def lems))
  in
  List.filter (fun def -> Hhlib.StringSet.mem (get_hhdef_name def) objs) defs

let run_predict (ctx : selection_ctx) fname pred_num pred_method =
  let oname = Opt.temp_file ("coqhammer_out" ^ pred_method ^ string_of_int pred_num) "" in
  let cmd = !Opt.predict_path ^ " " ^ fname ^ "fea " ^ fname ^ "dep " ^
    fname ^ "seq -n " ^ string_of_int pred_num ^
    " -p " ^ pred_method ^ " " ^ Opt.stderr_redirect () ^ " < " ^ fname ^
    "conj > " ^ oname
  in
  if !Opt.debug_mode || !Opt.gs_mode = 0 then
    Msg.info ("Running dependency prediction (" ^ pred_method ^ "-" ^
                 string_of_int pred_num ^ ")...");
  if !Opt.debug_mode then
    Msg.info cmd;
  let ret = Sys.command cmd in
  if ret <> 0 then
    begin
      (* sh exits with 127 when the command cannot be found *)
      let hint =
        if ret = 127 then
          "\nThe '" ^ !Opt.predict_path ^
            "' program could not be found. Most probably it is not installed \
             or not in the PATH. Note that the PATH seen by CoqHammer may \
             differ from your shell's PATH (e.g. when Rocq is started from an \
             IDE); see the CoqHammer installation instructions."
        else
          ""
      in
      Sys.remove oname;
      raise (HammerError ("Dependency prediction failed." ^ hint ^
                            "\nPrediction command: " ^ cmd ^
                            (if !Opt.debug_mode then
                               "\nSee '" ^ Opt.error_log_file () ^ "' for the error output."
                             else "")))
    end;
  let ic = open_in oname in
  try
    let predicts =
      Str.split (Str.regexp " ")
        (try input_line ic with End_of_file ->
          close_in ic; Sys.remove oname;
          raise (HammerError "Predictor did not return advice."))
    in
    close_in ic; Sys.remove oname;
    List.filter_map (fun name -> Hashtbl.find_opt ctx.def_tbl name) predicts
  with e ->
    close_in ic; Sys.remove oname;
    raise e

let clean fname =
  if not !Opt.debug_mode then
    List.iter Sys.remove [fname; (fname ^ "fea"); (fname ^ "dep"); (fname ^ "seq");
                          (fname ^ "conj")]

let rec take n lst =
  if n <= 0 then
    []
  else
    match lst with
    | [] -> []
    | x :: xs -> x :: take (n - 1) xs

let prepare_def_slots (ctx : selection_ctx) =
  if !Opt.definition_premises > 0 then
    ignore (Lazy.force ctx.dcands)

let take_unique_defs seen n defs =
  let rec hlp seen n acc = function
    | _ when n <= 0 -> List.rev acc
    | [] -> List.rev acc
    | def :: defs2 ->
       let name = get_hhdef_name def in
       if Hhlib.StringSet.mem name seen then
         hlp seen n acc defs2
       else
         hlp (Hhlib.StringSet.add name seen) (n - 1) (def :: acc) defs2
  in
  hlp seen n [] defs

let merge_def_slots (ctx : selection_ctx) n predictions =
  let max_slots = !Opt.definition_premises in
  if n <= 0 then
    []
  else if max_slots = 0 then
    predictions
  else
    let dcands = Lazy.force ctx.dcands in
    let ceil_eighth = n / 8 + (if n mod 8 = 0 then 0 else 1) in
    let k = min (List.length dcands) (min max_slots ceil_eighth) in
    let forced = take k dcands in
    let seen = Hhlib.strset_from_lst (List.map get_hhdef_name forced) in
    forced @ take_unique_defs seen (n - k) predictions

let predict (ctx : selection_ctx) (hyps : hhdef list) (goal : hhdef) : hhdef list =
  let fname = extract ctx hyps goal in
  try
    let predicted =
      run_predict ctx fname !Opt.predictions_num !Opt.predict_method
    in
    let r = merge_def_slots ctx !Opt.predictions_num predicted in
    clean fname;
    r
  with e ->
    clean fname;
    raise e
