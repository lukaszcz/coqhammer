open Hammer_lib
open Hh_term
open Hammer_errors

(*********************************************************************************)
(* feature options *)

let opt_feature_polarity = true

(*********************************************************************************)

let extract_consts (t : hhterm) : string list =
  let rec pom t acc =
    match t with
    | Id _ ->
      acc
    | Comb(Comb(Id "$Construct", x), Id c)
        when
          not (Hhlib.string_begins_with c "Coq.Init.Logic.") ->
      pom x (c :: acc)
    | Comb(Id x, Id c)
        when (x = "$Const" || x = "$Ind") &&
          not (Hhlib.string_begins_with c "Coq.Init.Logic.") ->
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
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.and"), _)), args) ->
       pom args pos acc
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.or"), _)), args) ->
       pom args pos acc
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.not"), _)), args) ->
       pom args (not pos) acc
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.iff"), _)), args) ->
       pom args pos (pom args (not pos) acc)
    | Comb(Comb(Id "$App", Comb(Comb(Id "$Ind", Id "Coq.Init.Logic.ex"), _)),
           Comb(Comb(Id "$ConstrArray", _),
                Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id _)), vartype), body))) ->
       pom vartype pos (pom body pos acc)
    | Comb(Comb(Id "$App", Comb(Id "$Const", Id "Coq.Init.Logic.all")),
           Comb(Comb(Id "$ConstrArray", _),
                Comb(Comb(Comb(Id "$Lambda", Comb(Id "$Name", Id _)), vartype), body))) ->
       pom vartype (not pos) (pom body pos acc)
    | Comb(Comb(Id "$Construct", x), Id c)
        when
          not (Hhlib.string_begins_with c "Coq.Init.Logic.") ->
       pom x pos (add_feature c pos acc)
    | Comb(Id x, Id c)
        when (x = "$Const" || x = "$Ind") &&
          not (Hhlib.string_begins_with c "Coq.Init.Logic.") ->
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

let get_def_features_cached (def : hhdef) : string list =
  let name = get_hhdef_name def in
  try
    Hashtbl.find features_cache name
  with Not_found ->
    let fea = get_def_features def in
    Hashtbl.add features_cache name fea;
    fea

let get_deps_cached (def : hhdef) : string list =
  let name = get_hhdef_name def in
  try
    Hashtbl.find deps_cache name
  with Not_found ->
    let deps = get_deps def in
    Hashtbl.add deps_cache name deps;
    deps

let is_nontrivial (def : hhdef) : bool =
  let name = get_hhdef_name def in
  name <> "" && not (Hhlib.string_begins_with name "Coq.Init.Logic.") &&
    (if !Opt.filter_program then not (Hhlib.string_begins_with name "Coq.Program.") else true) &&
    (if !Opt.filter_classes then not (Hhlib.string_begins_with name "Coq.Classes.") else true) &&
    (if !Opt.filter_hurkens then
        not (Hhlib.string_begins_with name "Coq.Logic.Hurkens.") else true)

let extract (hyps : hhdef list) (defs : hhdef list) (goal : hhdef) : string =
  Msg.info "Extracting features...";
  let fname = Filename.temp_file "predict" "" in
  let ocfea = open_out (fname ^ "fea") in
  let ocdep = open_out (fname ^ "dep") in
  let ocseq = open_out (fname ^ "seq") in
  let defs = List.filter is_nontrivial defs in
  if !Opt.debug_mode then
    Msg.info ("After filtering: " ^ string_of_int (List.length defs) ^ " Coq objects.");
  let names = Hhlib.strset_from_lst (List.map get_hhdef_name defs) in
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
    let deps = List.filter (fun a -> Hhlib.StringSet.mem a names) pre_deps in
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

let run_predict fname defs pred_num pred_method =
  let oname = Filename.temp_file ("coqhammer_out" ^ pred_method ^ string_of_int pred_num) "" in
  let cmd = !Opt.predict_path ^ " " ^ fname ^ "fea " ^ fname ^ "dep " ^
    fname ^ "seq -n " ^ string_of_int pred_num ^
    " -p " ^ pred_method ^ " 2>/dev/null < " ^ fname ^
    "conj > " ^ oname
  in
  if !Opt.debug_mode || !Opt.gs_mode = 0 then
    Msg.info ("Running dependency prediction (" ^ pred_method ^ "-" ^
                 string_of_int pred_num ^ ")...");
  if !Opt.debug_mode then
    Msg.info cmd;
  if Sys.command cmd <> 0 then
    begin
      raise (HammerError ("Dependency prediction failed.\nPrediction command: " ^ cmd))
    end;
  let ic = open_in oname in
  try
    let predicts =
      Hhlib.strset_from_lst
        (Str.split (Str.regexp " ")
           (try input_line ic with End_of_file ->
             close_in ic; Sys.remove oname;
             raise (HammerError "Predictor did not return advice.")))
    in
    close_in ic; Sys.remove oname;
    List.filter (fun def -> Hhlib.StringSet.mem (get_hhdef_name def) predicts) defs
  with e ->
    close_in ic; Sys.remove oname;
    raise e

let clean fname =
  if not !Opt.debug_mode then
    List.iter Sys.remove [fname; (fname ^ "fea"); (fname ^ "dep"); (fname ^ "seq");
                          (fname ^ "conj")]

let predict (hyps : hhdef list) (defs : hhdef list) (goal : hhdef) : hhdef list =
  let fname = extract hyps defs goal in
  try
    let r = run_predict fname defs !Opt.predictions_num !Opt.predict_method in
    clean fname;
    r
  with e ->
    clean fname;
    raise e
