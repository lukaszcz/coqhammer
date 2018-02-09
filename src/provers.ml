open Hammer_errors

(******************************************************************************)

let is_alpha = function 'A'..'Z'|'a'..'z'|'_' -> true | _ -> false

let is_good_dep s = is_alpha (String.get s 0) && not (Hhlib.string_begins_with s "_HAMMER_")

let get_deps lst = List.filter is_good_dep lst

let get_defs lst =
  List.filter is_good_dep
    (List.map (fun s -> String.sub s 6 (String.length s - 6))
       (List.filter (fun s -> Hhlib.string_begins_with s "$_def_") lst))

(******************************************************************************)

let invoke_prover prover_name cmd outfile =
  if !Opt.debug_mode then
    Msg.info cmd;
  let tm = Unix.gettimeofday ()
  in
  let ret = Sys.command cmd
  in
  if ret = 0 then
    Sys.command ("grep -q -s \"SZS status Theorem\" " ^ outfile) = 0
  else if ret <> 137 && Unix.gettimeofday () -. tm <= 1. then (* the second branch is a hack *)
    begin
      Msg.error ("Error running " ^ prover_name ^ ".");
      if !Opt.debug_mode then
        Msg.info ("Return code: " ^ string_of_int ret);
      false
    end
  else
    false

let call_eprover infile outfile =
  let tmt = string_of_int !Opt.atp_timelimit in
  let tmt2 = string_of_int (!Opt.atp_timelimit + 1) in
  let cmd =
    "htimeout " ^ tmt2 ^ " eprover -s --cpu-limit=" ^ tmt ^ " --auto-schedule -R --print-statistics -p --tstp-format \"" ^ infile ^ "\" 2>/dev/null | grep \"file[(]'\\|# SZS\" > \"" ^ outfile ^ "\""
  in
  invoke_prover "eprover" cmd outfile

let extract_eprover_data outfile =
  try
    let ic = open_in outfile
    in
    let rec pom acc =
      try
	let ln = input_line ic in
	if String.get ln 0 = '#' then
	  pom acc
	else if String.sub ln ((String.index ln ',') + 2) 5 = "axiom" then
	  let i = String.rindex ln ',' + 2 in
	  let j = String.rindex ln '\'' in
	  let name = Scanf.unescaped (String.sub ln (i + 1) (j - i - 1)) in
	  pom (name :: acc)
	else
	  pom acc
      with
      | End_of_file ->
	acc
      | Not_found | Invalid_argument(_) ->
	pom acc
    in
    let names = pom []
    in
    close_in ic;
    (get_deps names, get_defs names)
  with _ ->
    raise (HammerError "Failed to extract EProver data")

let call_z3 infile outfile =
  let tmt = string_of_int !Opt.atp_timelimit in
  let tmt2 = string_of_int (!Opt.atp_timelimit + 1) in
  let cmd =
    "htimeout " ^ tmt2 ^ " z3_tptp -c -t:" ^ tmt ^ " -file:" ^ infile ^ " 2>/dev/null > " ^ outfile
  in
  invoke_prover "z3_tptp" cmd outfile

let extract_z3_data outfile =
  try
    let ic = open_in outfile
    in
    ignore (input_line ic);
    let ln = String.trim (input_line ic) in
    let s = String.sub ln 13 (String.length ln - 2 - 13) in
    let names = List.map Scanf.unescaped (Str.split (Str.regexp "'| |'") s) in
    close_in ic;
    (get_deps names, get_defs names)
  with _ ->
    raise (HammerError "Failed to extract Z3 data")

let call_vampire infile outfile =
  let tmt = string_of_int !Opt.atp_timelimit in
  let tmt2 = string_of_int (!Opt.atp_timelimit + 1) in
  let cmd =
    "htimeout " ^ tmt2 ^ " vampire --mode casc -t " ^ tmt ^ " --proof tptp --output_axiom_names on " ^ infile ^ " 2>/dev/null | grep \"file[(]'\|% SZS\" > " ^ outfile
  in
  invoke_prover "vampire" cmd outfile

let extract_vampire_data outfile =
  try
    let ic = open_in outfile
    in
    let rec pom acc =
      try
	let ln = input_line ic in
	if String.get ln 0 = '%' then
	  pom acc
	else
	  let i = String.rindex ln ',' + 1 in
	  let j = String.rindex ln '\'' in
	  let name = Scanf.unescaped (String.sub ln (i + 1) (j - i - 1)) in
	  if name <> "HAMMER_GOAL" then
	    pom (name :: acc)
	  else
	    pom acc
      with
      | End_of_file ->
	acc
      | Not_found | Invalid_argument(_) ->
	pom acc
    in
    let names = pom []
    in
    close_in ic;
    (get_deps names, get_defs names)
  with _ ->
    raise (HammerError "Failed to extract Vampire data")

let call_cvc4 infile outfile =
	let tmt = string_of_int !Opt.atp_timelimit in
	let tmt2 = string_of_int (!Opt.atp_timelimit + 1) in
	let cmd = 
      "htimeout " ^ tmt2 ^ " cvc4 --tlimit " ^ tmt ^ " --dump-unsat-cores-full " ^ infile ^ " > " ^ outfile 
	in
	invoke_prover "cvc4" cmd outfile

let extract_cvc4_data outfile =
  try
    let ic = open_in outfile
    in
    ignore (input_line ic);
    let rec pom acc =
      try
    let ln = input_line ic in
    if ln = "(" || ln = ")" then
      pom acc
    else 
      pom (ln :: acc)
      with
      | End_of_file ->
    acc
      | Not_found | Invalid_argument(_) ->
    pom acc
    in
    let names = pom []
    in
    close_in ic;
    (get_deps names, get_defs names)
  with _ ->
    raise (HammerError "Failed to extract CVC4 data")



(******************************************************************************)

let provers = 
            [
                (Opt.vampire_enabled, "Vampire", call_vampire, extract_vampire_data);
	            (Opt.z3_enabled, "Z3", call_z3, extract_z3_data);
	            (Opt.eprover_enabled, "EProver", call_eprover, extract_eprover_data);
                (Opt.cvc4_enabled, "CVC4", call_cvc4, extract_cvc4_data)
            ]

(* TODO : add something here *)

let call_prover (enabled, pname, call, extract) fname ofname cont =
  let clean () =
    if not !Opt.debug_mode && Sys.file_exists ofname then
      Sys.remove ofname
  in
  if !enabled then
    try
      begin
	if !Opt.debug_mode || !Opt.gs_mode = 0 then
	  Msg.info ("Running " ^ pname ^ "...");
	if call fname ofname then
	  begin
	    let (deps, defs) = extract ofname in
	    clean ();
	    let n = List.length deps in
	    if n <= !Opt.max_atp_predictions then
	      (pname, (deps, defs))
	    else
	      begin
		Msg.info (pname ^ " returned too many predictions (" ^ string_of_int n ^ ")");
		cont ()
	      end
	  end
	else
	  begin
	    if !Opt.debug_mode || !Opt.gs_mode = 0 then
	      Msg.info (pname ^ " failed");
	    clean ();
	    cont ()
	  end
      end
    with e ->
      clean ();
      raise e
  else
    cont ()

let call_provers fname ofname =
  let rec pom lst =
    match lst with
    | [] -> raise (HammerFailure "ATPs failed to find a proof")
    | h :: t -> call_prover h fname ofname (fun () -> pom t)
  in
  pom provers

let call_provers_par fname ofname =
  let jobs =
    List.map
      begin fun ((_, pname, _, _) as h) _ ->
	call_prover h fname (ofname ^ "." ^ pname) (fun () -> exit 1)
      end
      provers
  in
  let time = float_of_int !Opt.atp_timelimit
  in
  match Parallel.run_parallel (fun _ -> ()) (fun _ -> ()) time jobs with
  | None -> raise (HammerFailure "ATPs failed to find a proof")
  | Some x -> x

(******************************************************************************)
(* Main functions *)

let write_atp_file fname deps1 hyps deps goal =
  let name = Hh_term.get_hhdef_name goal in
  let depnames = List.map Hh_term.get_hhdef_name (hyps @ deps1) in
  Coq_transl.remove_def name;
  List.iter (fun d -> Coq_transl.remove_def (Hh_term.get_hhdef_name d)) hyps;
  Coq_transl.reinit (goal :: hyps @ deps);
  if !Opt.debug_mode || !Opt.gs_mode = 0 then
    Msg.info ("Translating the problem to FOL...");
  Coq_transl.retranslate (name :: depnames);
  if !Opt.debug_mode then
    Msg.info ("Writing translated problem to file '" ^ fname ^ "'...");
  Coq_transl.write_problem fname name depnames

let predict deps1 hyps deps goal =
  let prn_lst lst =
    match lst with
    | [] -> ""
    | h :: t ->
      List.fold_right (fun x a -> (Hhlib.drop_prefix x "Top.") ^ ", " ^ a) t
	(Hhlib.drop_prefix h "Top.")
  in
  let fname = Filename.temp_file "coqhammer" ".p" in
  write_atp_file fname deps1 hyps deps goal;
  let ofname = fname ^ ".out" in
  let clean () =
    if not !Opt.debug_mode then
      begin
	Sys.remove fname;
	if Sys.file_exists ofname then
	  Sys.remove ofname
      end
  in
  let call = if !Opt.parallel_mode then call_provers_par else call_provers
  in
  try
    let (pname, (deps, defs)) = call fname ofname in
    Msg.info (pname ^ " succeeded\n - dependencies: " ^ prn_lst deps ^
		"\n - definitions: " ^ prn_lst defs);
    clean ();
    (deps, defs)
  with e ->
    clean ();
    raise e
