open Hammer_lib
open Hammer_errors
open Hh_term
open Atp_names

(* info about what the ATP used in the proof *)
type atp_info = {
  deps : string list; (* dependencies: lemmas, theorems *)
  defs : string list; (* definitions (non-propositional) *)
  typings : string list;
  cases : string list;
  inversions : string list;
  injections : string list;
  discrims : (string * string) list;
  types : string list; (* (co)inductive types *)
}

(******************************************************************************)

(* Raised when a line that has already been recognised as carrying a premise
   name cannot be parsed.  That is always a bug in the parser rather than a
   property of the proof, so it must reach the user instead of being skipped
   with the line: a parser that silently drops names turns its own breakage
   into what looks like a weak translation.  Failing to recognise a line as
   carrying a name at all is a different matter and stays caught, since the
   provers interleave other output with their proofs. *)
exception Parse_error of string

(* Reverse the encoding tptp_out applies to a premise name: a prime is written
   ~q, a literal tilde ~t, and every other byte outside the safe printable-ASCII
   range (notably the non-ASCII bytes of a Unicode identifier) is written ~ then
   two lowercase hex digits, so that the emitted single-quoted atom needs no
   TPTP backslash escape (which z3_tptp rejects and EProver mangles) and carries
   no byte z3_tptp refuses.  A tilde that opens no known escape is kept as-is, so
   a name that never went through the encoder passes through unchanged. *)
let hex_digit c =
  match c with
  | '0' .. '9' -> Char.code c - Char.code '0'
  | 'a' .. 'f' -> Char.code c - Char.code 'a' + 10
  | _ -> -1
let decode_thm_name s =
  let n = String.length s in
  let buf = Buffer.create n in
  let rec go i =
    if i >= n then
      Buffer.contents buf
    else if s.[i] = '~' && i + 1 < n then
      match s.[i + 1] with
      | 'q' -> Buffer.add_char buf '\''; go (i + 2)
      | 't' -> Buffer.add_char buf '~'; go (i + 2)
      | _ when i + 2 < n && hex_digit s.[i + 1] >= 0 && hex_digit s.[i + 2] >= 0 ->
          Buffer.add_char buf
            (Char.chr (hex_digit s.[i + 1] * 16 + hex_digit s.[i + 2]));
          go (i + 3)
      | _ -> Buffer.add_char buf '~'; go (i + 1)
    else
      begin
        Buffer.add_char buf s.[i];
        go (i + 1)
      end
  in
  go 0

(* Read the single-quoted atom that opens at ln.[i].  The emitted atom carries
   no backslash escape and no embedded quote, so the first quote closes it; the
   prime, encoded as ~q, is restored by decode_thm_name afterwards. *)
let read_quoted_atom ln i =
  let n = String.length ln in
  let buf = Buffer.create 32 in
  let rec scan i =
    if i >= n then
      raise (Parse_error ln)
    else if ln.[i] = '\'' then
      Buffer.contents buf
    else
      begin
        Buffer.add_char buf ln.[i];
        scan (i + 1)
      end
  in
  decode_thm_name (scan (i + 1))

(* CVC4 is asked for an unsat core rather than a proof, and prints one premise
   name per line with no enclosing term.  Like Vampire it quotes the name only
   when TPTP requires it, so a line carrying a bare lower word such as
   beq_refl is a name in full and not a line to pass over. *)
let core_atom_of_line ln =
  let s = String.trim ln in
  if s = "" then
    raise (Parse_error ln)
  else if s.[0] = '\'' then
    read_quoted_atom s 0
  else
    s

(* EProver and Vampire print a proof, where the premise name is the second
   argument of the trailing file(SOURCE, NAME).  Both forms of NAME occur:
   EProver always quotes it, while Vampire quotes only when TPTP requires it
   and writes e.g. file('...p',beq_refl) otherwise.  Reading only quoted atoms
   would take the source path for the name of every unquoted premise, and
   slicing to the last quote drops them instead. *)
let axiom_name_of_line ln =
  let n = String.length ln in
  let start =
    match String.rindex_opt ln ',' with
    | Some i -> ref (i + 1)
    | None -> raise (Parse_error ln)
  in
  while !start < n && (ln.[!start] = ' ' || ln.[!start] = '\t') do incr start done;
  if !start >= n then
    raise (Parse_error ln)
  else if ln.[!start] = '\'' then
    read_quoted_atom ln !start
  else
    let stop = ref !start in
    while !stop < n && ln.[!stop] <> ')' && ln.[!stop] <> ',' do incr stop done;
    let name = String.trim (String.sub ln !start (!stop - !start)) in
    if name = "" then raise (Parse_error ln) else name

let get_types lst =
  remove_duplicates
    (List.filter is_good_dep
       (List.map
          begin fun s ->
            try
              let s =
                if Hhlib.string_begins_with s "$_inversion_" then
                  String.sub s 12 (String.length s - 12)
                else if Hhlib.string_begins_with s "$_inj_" then
                  String.sub s 6 (String.length s - 6)
                else if Hhlib.string_begins_with s "$_discrim_" then
                  let s = String.sub s 10 (String.length s - 10) in
                  let i = String.index s '$' in
                  String.sub s 0 i
                else if Hhlib.string_begins_with s "$_case_" then
                  case_name_subject (String.sub s 7 (String.length s - 7))
                else
                  "$none"
              in
              let tgt =
                Coq_typing.get_type_app_target (Coqterms.coqdef_type (Defhash.find s))
              in
              match tgt with
              | Coqterms.Const(x) -> x
              | _ -> "$none"
            with _ ->
              "$none"
          end
          lst))

let get_atp_info names =
  { deps = get_deps names; defs = get_defs names; typings = get_typings names;
    cases = get_cases names; inversions = get_inversions names;
    injections = get_injections names; discrims = get_discrims names;
    types = get_types names }

let prn_atp_info info =
  let drop_prefixes x =
    Hhlib.drop_prefix
      (Hhlib.drop_prefix (Hhlib.drop_prefix x "Top.") "Corelib.")
      "Stdlib."
  in
  let prn_lst prompt lst =
    match lst with
    | [] -> ""
    | h :: t ->
       prompt ^
       List.fold_right (fun x a -> drop_prefixes x ^ ", " ^ a) t
         (drop_prefixes h)
  in
  let nl b =
    if b then "\n" else ""
  in
  let b1 = info.deps <> [] in
  let b2 = b1 || info.defs <> [] in
  let b3 = b2 || info.inversions <> [] in
  prn_lst "- dependencies: " info.deps ^
    prn_lst (nl b1 ^ "- definitions: ") info.defs ^
    prn_lst (nl b2 ^ "- inversions: ") info.inversions ^
    prn_lst (nl b3 ^ "- cases: ") info.cases

module StringMap = Map.Make(String)

let get_atp_deps deps =
  let deps_map =
    List.fold_left (fun a x -> StringMap.add (get_hhdef_name x) x a) StringMap.empty deps
  in
  fun info ->
    List.map (fun x -> StringMap.find x deps_map)
      (List.sort_uniq Stdlib.compare
         (List.filter (fun x -> StringMap.mem x deps_map)
            (info.deps @ info.defs @ info.typings @ info.types)))

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
        begin
          Msg.info ("Return code: " ^ string_of_int ret);
          Msg.info ("See '" ^ Opt.error_log_file () ^ "' for the error output.")
        end;
      false
    end
  else
    false

let call_eprover infile outfile =
  let tmt = string_of_int !Opt.atp_timelimit in
  let tmt2 = string_of_int (!Opt.atp_timelimit + 1) in
  let cmd =
    "htimeout " ^ tmt2 ^ " eprover -s --cpu-limit=" ^ tmt ^ " --auto-schedule -R --print-statistics -p --tstp-format \"" ^ infile ^ "\" " ^ Opt.stderr_redirect () ^ " | grep \"file[(]'\\|# SZS\" > \"" ^ outfile ^ "\""
  in
  invoke_prover "eprover" cmd outfile

let extract_eprover_data outfile =
  try
    let ic = open_in outfile
    in
    let names =
      Fun.protect ~finally:(fun () -> close_in_noerr ic)
        begin fun () ->
          let rec pom acc =
            try
              let ln = input_line ic in
              if String.get ln 0 = '#' then
                pom acc
              else if String.sub ln ((String.index ln ',') + 2) 5 = "axiom" then
                pom (axiom_name_of_line ln :: acc)
              else
                pom acc
            with
            | End_of_file ->
               acc
            (* One unreadable name must not discard the rest of a found proof. *)
            | Not_found | Invalid_argument(_) ->
               pom acc
          in
          pom []
        end
    in
    get_atp_info names
  with
  | Parse_error ln ->
     raise (HammerError
              ("Failed to parse a premise name in EProver output: " ^ ln))
  | _ ->
    raise (HammerError "Failed to extract EProver data")

type z3_binary = Z3Tptp | Z3

let z3_binary = ref Z3Tptp

let z3_name = function
  | Z3Tptp -> "z3_tptp"
  | Z3 -> "z3"

let z3_call_args bin infile =
  let tmt = string_of_int !Opt.atp_timelimit in
  match bin with
  | Z3Tptp -> "-c -t:" ^ tmt ^ " -file:" ^ Filename.quote infile
  | Z3 ->
     "-tptp -t:" ^ string_of_int (!Opt.atp_timelimit * 1000) ^
       " " ^ Filename.quote infile

let call_z3 infile outfile =
  let tmt2 = string_of_int (!Opt.atp_timelimit + 1) in
  let bin = !z3_binary in
  let cmd =
    "htimeout " ^ tmt2 ^ " " ^ z3_name bin ^ " " ^ z3_call_args bin infile ^
      " " ^ Opt.stderr_redirect () ^ " > " ^ Filename.quote outfile
  in
  invoke_prover (z3_name bin) cmd outfile

let extract_z3_data outfile =
  try
    let ic = open_in outfile
    in
    let names =
      Fun.protect ~finally:(fun () -> close_in_noerr ic)
        begin fun () ->
          ignore (input_line ic);
          let ln = String.trim (input_line ic) in
          let s = String.sub ln 13 (String.length ln - 2 - 13) in
          List.map decode_thm_name (Str.split (Str.regexp "'| |'") s)
        end
    in
    get_atp_info names
  with
  | Parse_error ln ->
     raise (HammerError
              ("Failed to parse a premise name in Z3 output: " ^ ln))
  | _ ->
    raise (HammerError "Failed to extract Z3 data")

let call_vampire infile outfile =
  let tmt = string_of_int !Opt.atp_timelimit in
  let tmt2 = string_of_int (!Opt.atp_timelimit + 1) in
  let cmd =
    "htimeout " ^ tmt2 ^ " vampire --mode casc -t " ^ tmt ^ " --proof tptp --output_axiom_names on " ^ infile ^ " " ^ Opt.stderr_redirect () ^ " | grep \"file[(]'\\|% SZS\" > " ^ outfile
  in
  invoke_prover "vampire" cmd outfile

let extract_vampire_data outfile =
  try
    let ic = open_in outfile
    in
    let names =
      Fun.protect ~finally:(fun () -> close_in_noerr ic)
        begin fun () ->
          let rec pom acc =
            try
              let ln = input_line ic in
              if String.get ln 0 = '%' then
                pom acc
              else
                let name = axiom_name_of_line ln in
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
          pom []
        end
    in
    get_atp_info names
  with
  | Parse_error ln ->
     raise (HammerError
              ("Failed to parse a premise name in Vampire output: " ^ ln))
  | _ ->
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
    let ic = open_in outfile in
    let names =
      Fun.protect ~finally:(fun () -> close_in_noerr ic)
        begin fun () ->
          let rec pom acc =
            try
              let ln = input_line ic in
              if (String.get ln 0 = '%') then
                pom acc
              else
                let name = core_atom_of_line ln in
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
          pom []
        end
    in
    get_atp_info names
  with
  | Parse_error ln ->
     raise (HammerError
              ("Failed to parse a premise name in CVC4 output: " ^ ln))
  | _ ->
    raise (HammerError "Failed to extract CVC4 data")

(******************************************************************************)

let provers = [(Opt.vampire_enabled, "Vampire", call_vampire, extract_vampire_data);
               (Opt.z3_enabled, "Z3", call_z3, extract_z3_data);
               (Opt.eprover_enabled, "EProver", call_eprover, extract_eprover_data);
               (Opt.cvc4_enabled, "CVC4", call_cvc4, extract_cvc4_data)]

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
            let info = extract ofname in
            clean ();
            (pname, info)
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
  (* Allocate the debug log in the parent so that the forked workers
     below all append to the same file. *)
  if !Opt.debug_mode then
    ignore (Opt.error_log_file ());
  let jobs =
    List.map
      begin fun ((_, pname, _, _) as h) _ ->
        call_prover h fname (ofname ^ "." ^ pname) (fun () -> Unix._exit 1)
      end
      provers
  in
  let time = float_of_int !Opt.atp_timelimit
  in
  match Parallel.run_parallel (fun _ -> ()) (fun _ -> ()) time jobs with
  | None, _ -> raise (HammerFailure "ATPs failed to find a proof")
  | Some x, _ -> x

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

let minimize info hyps deps goal =
  if !Opt.debug_mode then
    Msg.info (prn_atp_info info);
  Msg.info "Minimizing dependencies...";
  let get_atp_deps = get_atp_deps deps
  in
  let rec pom pname1 info =
    let fname = Opt.temp_file "coqhammer" ".p" in
    write_atp_file fname (get_atp_deps info) hyps deps goal;
    let ofname = fname ^ ".out" in
    let clean () =
      if not !Opt.debug_mode then
        begin
          if Sys.file_exists fname then
            Sys.remove fname;
          if Sys.file_exists ofname then
            Sys.remove ofname
        end
    in
    let jobs =
      List.map
        begin fun ((_, pname, _, _) as h) _ ->
          if pname <> pname1 then
            begin
              let (pname2, info2) =
                call_prover h fname (ofname ^ "." ^ pname) (fun () -> Unix._exit 1)
              in
              if List.length info2.deps < List.length info.deps ||
                List.length info2.defs < List.length info.defs
              then
                (pname2, info2)
              else
                Unix._exit 1
            end
          else
            Unix._exit 1
        end
        provers
    in
    let time = (float_of_int !Opt.atp_timelimit)
    in
    match Parallel.run_parallel (fun _ -> ()) (fun _ -> ()) time jobs with
    | None, _ ->
       begin
         if !Opt.debug_mode then
           begin
             if pname1 = "" then
               Msg.info "Minimization failed"
             else
               Msg.info "Minimization succeeded"
           end;
         clean ();
         info
       end
    | Some (pname2, info2), _ -> clean (); pom pname2 info2
  in
  pom "" info

let predict deps1 hyps deps goal =
  let fname = Opt.temp_file "coqhammer" ".p" in
  write_atp_file fname deps1 hyps deps goal;
  let ofname = fname ^ ".out" in
  let clean () =
    if not !Opt.debug_mode then
      begin
        if Sys.file_exists fname then
          Sys.remove fname;
        if Sys.file_exists ofname then
          Sys.remove ofname
      end
  in
  let call = if !Opt.parallel_mode then call_provers_par else call_provers
  in
  try
    let (pname, info) = call fname ofname in
    clean ();
    (pname, info)
  with e ->
    clean ();
    raise e

(******************************************************************************)

let detect_eprover () =
  if Sys.command "eprover --version 2>&1 >/dev/null" = 0 then
    begin
      Msg.info "Eprover found";
      true
    end
  else
    begin
      Msg.info "Eprover not found";
      Opt.eprover_enabled := false;
      false
    end

let detect_vampire () =
  if Sys.command "vampire --version 2>&1 >/dev/null" = 0 then
    begin
      Msg.info "Vampire found";
      true
    end
  else
    begin
      Msg.info "Vampire not found";
      Opt.vampire_enabled := false;
      false
    end

let command_succeeds cmd =
  Sys.command (cmd ^ " >/dev/null 2>&1") = 0

let z3_supports_tptp bin =
  let fname = Opt.temp_file "coqhammer-z3-detect" ".p" in
  try
    let oc = open_out fname in
    output_string oc "fof(coqhammer_z3_detect, conjecture, $true).\n";
    close_out oc;
    let ret =
      Sys.command
        (z3_name bin ^ " " ^ z3_call_args bin fname ^ " >/dev/null 2>&1")
    in
    Sys.remove fname;
    ret = 0
  with _ ->
    begin
      try Sys.remove fname with _ -> ()
    end;
    false

let detect_z3 () =
  if command_succeeds "z3_tptp -h" then
    begin
      z3_binary := Z3Tptp;
      Msg.info "Z3 found (z3_tptp)";
      true
    end
  else if command_succeeds "z3 -h" && z3_supports_tptp Z3 then
    begin
      z3_binary := Z3;
      Msg.info "Z3 found (z3 with TPTP support)";
      true
    end
  else
    begin
      Msg.info "Z3 not found";
      Opt.z3_enabled := false;
      false
    end

let detect_cvc4 () =
  if Sys.command "cvc4 --version 2>&1 >/dev/null" = 0 then
    begin
      Msg.info "CVC4 found";
      true
    end
  else
    begin
      Msg.info "CVC4 not found";
      Opt.cvc4_enabled := false;
      false
    end

let detect () =
  let b1 = detect_eprover ()
  and b2 = detect_vampire ()
  and b3 = detect_z3 ()
  and b4 = detect_cvc4 ()
  in
  b1 || b2 || b3 || b4
