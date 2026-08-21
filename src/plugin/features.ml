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
     force_hhterm ty
  | (_, false, _, ty, prf) ->
     Comb(force_hhterm ty, force_hhterm prf)

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
    extract_consts (Comb(force_hhterm ty, force_hhterm prf))

let features_cache = Hashtbl.create 1024
let deps_cache = Hashtbl.create 1024
let sizes_cache = Hashtbl.create 1024

let cleanup () =
  Hashtbl.reset features_cache;
  Hashtbl.reset deps_cache;
  Hashtbl.reset sizes_cache

(* Variables must not be cached under their names: the same name may
   denote a different variable in another section or proof. *)

let cached table compute def =
  if hhdef_is_var def then
    compute def
  else
    let name = get_hhdef_name def in
    match Hashtbl.find_opt table name with
    | Some value -> value
    | None ->
       let value = compute def in
       Hashtbl.add table name value;
       value

let get_def_features_cached (def : hhdef) : string list =
  cached features_cache get_def_features def

let get_deps_cached (def : hhdef) : string list =
  cached deps_cache get_deps def

(* The size of a global's feature term is a property of its statement, like its
   features and its dependencies, so it is cached the same way.  Without that,
   the ranking below pays for it again on every goal: [extract] releases the
   converted type and body trees as soon as it has written the features it
   needed them for, and the ranking is their only later reader, so it would
   re-convert the whole candidate set each time. *)
let get_def_size_cached (def : hhdef) : int =
  cached sizes_cache (fun def -> hhterm_size (get_def_fea_term def)) def

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
  seed : Hhlib.StringSet.t Lazy.t;
  occ : (string, int) Hashtbl.t Lazy.t;
  dcands : hhdef list Lazy.t;
}

type selection_metadata = {
  def_candidates : int;
  seed_min_occ : int option;
  seed_median_occ : int option;
  forced_slots : int;
}

(* An accessible global that never occurs in another global's statement has no
   entry; that is an occurrence count of zero, not a missing measurement. *)
let occurrence_count occ name =
  match Hashtbl.find_opt occ name with
  | Some count -> count
  | None -> 0

let make_selection_ctx (hyps : hhdef list) (defs : hhdef list) (goal : hhdef) : selection_ctx =
  let ndefs = List.filter is_nontrivial defs in
  let def_tbl = Hashtbl.create (List.length ndefs) in
  List.iter
    (fun def -> Hashtbl.replace def_tbl (get_hhdef_name def) def)
    ndefs;
  let seed =
    lazy
      (Hhlib.strset_from_lst
         (get_deps goal @ List.concat_map get_deps hyps))
  in
  let occ =
    lazy
      (let tbl = Hashtbl.create (List.length ndefs) in
       List.iter
         (fun def ->
            List.iter
              (fun name ->
                 Hashtbl.replace tbl name (occurrence_count tbl name + 1))
              (get_deps_cached def))
         ndefs;
       tbl)
  in
  let make_dcands seed occ =
    let seed = Lazy.force seed in
    let seed_defs =
      List.filter
        (fun def -> Hhlib.StringSet.mem (get_hhdef_name def) seed)
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
    let candidate_names = ref seed in
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
             Some (occurrence_count occ name,
                   get_def_size_cached def, name, def)
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
  { ndefs; def_tbl; seed; occ; dcands = lazy (make_dcands seed occ) }

let get_query_features (ctx : selection_ctx) (hyps : hhdef list) (goal : hhdef) =
  let features = get_goal_features hyps goal in
  let generality = !Opt.definition_features in
  if generality = 0 then
    features
  else
    let occ = Lazy.force ctx.occ in
    let expanded =
      Hhlib.StringSet.fold
        (fun name acc ->
           match Hashtbl.find_opt ctx.def_tbl name with
           | Some def ->
              if occurrence_count occ name <= generality then
                get_deps_cached def @ acc
              else
                acc
           | None -> acc)
        (Lazy.force ctx.seed) []
    in
    Hhlib.sort_uniq String.compare (features @ expanded)

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
    (* Feature/dependency caches now hold the compact products needed by later
       predictions.  Drop the much larger converted type/body trees before
       moving to the next global; selected premises are regenerated lazily for
       translation. *)
    release_hhdef def;
  in
  List.iter write_def defs;
  close_out ocfea;
  close_out ocseq;
  close_out ocdep;
  let oc = open_out (fname ^ "conj") in
  let fea = get_query_features ctx hyps goal in
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
        (* Cleanup is left to the handler below: doing it here too would
           remove [oname] twice, and the second removal's [Sys_error] would
           replace the diagnostic. *)
        (try input_line ic with End_of_file ->
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

let definition_slot_count ctx n =
  let max_slots = !Opt.definition_premises in
  if n <= 0 || max_slots <= 0 then
    0
  else
    let ceil_eighth = n / 8 + (if n mod 8 = 0 then 0 else 1) in
    min (List.length (Lazy.force ctx.dcands)) (min max_slots ceil_eighth)

let selection_metadata ctx n =
  let occ = Lazy.force ctx.occ in
  let seed_occurrences =
    Hhlib.StringSet.fold
      (fun name counts ->
         if Hashtbl.mem ctx.def_tbl name then
           occurrence_count occ name :: counts
         else
           counts)
      (Lazy.force ctx.seed) []
    |> List.sort compare
  in
  let seed_min_occ, seed_median_occ =
    match seed_occurrences with
    | [] -> None, None
    | min_occ :: _ ->
       let middle = (List.length seed_occurrences - 1) / 2 in
       Some min_occ, Some (List.nth seed_occurrences middle)
  in
  {
    def_candidates = List.length (Lazy.force ctx.dcands);
    seed_min_occ;
    seed_median_occ;
    forced_slots = definition_slot_count ctx n;
  }

let merge_def_slots (ctx : selection_ctx) n predictions =
  if n <= 0 then
    []
  else if !Opt.definition_premises <= 0 then
    predictions
  else
    let k = definition_slot_count ctx n in
    let forced = Hhlib.take k (Lazy.force ctx.dcands) in
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
