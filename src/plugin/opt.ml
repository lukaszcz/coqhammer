open Goptions

let predictions_num = ref 1024

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"Predictions"];
      optread=(fun ()->Some !predictions_num);
      optwrite=
   (function
        None -> predictions_num := 128
      |	Some i -> predictions_num := (max i 16))}
  in
  declare_int_option gdopt

let sauto_timelimit = ref 1

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"SAutoLimit"];
      optread=(fun ()->Some !sauto_timelimit);
      optwrite=
   (function
        None -> sauto_timelimit := 1
      |	Some i -> sauto_timelimit := (max i 0))}
  in
  declare_int_option gdopt

let atp_timelimit = ref 20

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"ATPLimit"];
      optread=(fun ()->Some !atp_timelimit);
      optwrite=
   (function
        None -> atp_timelimit := 10
      |	Some i -> atp_timelimit := (max i 0))}
  in
  declare_int_option gdopt

let reconstr_timelimit = ref 5

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"ReconstrLimit"];
      optread=(fun ()->Some !reconstr_timelimit);
      optwrite=
   (function
        None -> reconstr_timelimit := 10
      |	Some i -> reconstr_timelimit := (max i 0))}
  in
  declare_int_option gdopt

let reconstr_retries = ref 3

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"ReconstrRetries"];
      optread=(fun ()->Some !reconstr_retries);
      optwrite=
   (function
        None -> reconstr_retries := 3
      | Some i -> reconstr_retries := (max i 0))}
  in
  declare_int_option gdopt

let minimize_threshold = ref 8

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"MinimizationThreshold"];
      optread=(fun ()->Some !minimize_threshold);
      optwrite=
   (function
        None -> minimize_threshold := 0
      |	Some i -> minimize_threshold := (max i 0))}
  in
  declare_int_option gdopt

let gs_mode = ref 8

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"GSMode"];
      optread=(fun ()->Some !gs_mode);
      optwrite=
   (function
        None -> gs_mode := 16
      |	Some i -> gs_mode := i)}
  in
  declare_int_option gdopt

let eprover_enabled = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"Eprover"];
      optread=(fun () -> !eprover_enabled);
      optwrite=(fun b -> eprover_enabled := b)}
  in
  declare_bool_option gdopt

let vampire_enabled = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"Vampire"];
      optread=(fun () -> !vampire_enabled);
      optwrite=(fun b -> vampire_enabled := b)}
  in
  declare_bool_option gdopt

let z3_enabled = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"Z3"];
      optread=(fun () -> !z3_enabled);
      optwrite=(fun b -> z3_enabled := b)}
  in
  declare_bool_option gdopt

let cvc4_enabled = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"CVC4"];
      optread=(fun () -> !cvc4_enabled);
      optwrite=(fun b -> cvc4_enabled := b)}
  in
  declare_bool_option gdopt

let predict_path = ref "predict"

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"PredictPath"];
      optread=(fun () -> !predict_path);
      optwrite=(fun s -> predict_path := s)}
  in
  declare_string_option gdopt

let predict_method = ref "knn"

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"PredictMethod"];
      optread=(fun () -> !predict_method);
      optwrite=
        begin fun s ->
          if s = "knn" || s = "nbayes" || s = "rforest" then
            predict_method := s
          else
            Msg.error "Invalid method. Available predict methods: knn, nbayes."
        end}
  in
  declare_string_option gdopt

let parallel_mode = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"Parallel"];
      optread=(fun () -> !parallel_mode);
      optwrite=(fun b -> parallel_mode := b)}
  in
  declare_bool_option gdopt

let debug_mode = ref false

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"Debug"];
      optread=(fun () -> !debug_mode);
      optwrite=(fun b -> debug_mode := b)}
  in
  declare_bool_option gdopt

(* Target directory for the files written by [Hammer_dump]. Unset by
   default, in which case COQHAMMER_DUMP_DIR may redirect relative dump
   names. Setting the option, even to the empty string, overrides the
   environment; an empty configured directory writes relative names
   verbatim (i.e. relative to the current directory), as users expect. *)
let dump_directory_unset = "<unset>"
let dump_directory = ref ""
let dump_directory_is_set = ref false

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"Dump";"Directory"];
      optread=(fun () -> if !dump_directory_is_set then !dump_directory else dump_directory_unset);
      optwrite=
        (fun s ->
           if s = dump_directory_unset then
             dump_directory_is_set := false
           else
             begin
               dump_directory := s;
               dump_directory_is_set := true
             end)}
  in
  declare_string_option gdopt

(* Resolve the path of a [Hammer_dump] file: a relative name is placed in
   the configured dump directory (the Hammer Dump Directory option, or the
   COQHAMMER_DUMP_DIR environment variable when the option is unset);
   otherwise (and always for absolute names) the name is used unchanged. *)
let resolve_dump_path fname =
  let dir =
    if !dump_directory_is_set then
      !dump_directory
    else
      match Sys.getenv_opt "COQHAMMER_DUMP_DIR" with Some d -> d | None -> ""
  in
  if dir <> "" && Filename.is_relative fname then
    Filename.concat dir fname
  else
    fname

(* Per-invocation temporary directory. All temporary files created
   during a single hammer/predict invocation are placed inside a fresh,
   private directory (see [temp_file]) which is removed as a whole when
   the invocation finishes -- even on interruption or when an ATP worker
   is killed mid-run. This makes cleanup deterministic and race-free: no
   process globs over the shared temp directory, so concurrent hammer
   invocations never delete each other's files. In debug mode no such
   directory is used, so the intermediate files are left in the system
   temp directory for inspection. *)

let temp_dir_ref = ref None

(* Create a temporary file for the current invocation. When an
   invocation directory is active the file is placed inside it;
   otherwise (e.g. in debug mode, or outside any invocation) it falls
   back to the system temp directory. *)
let temp_file prefix suffix =
  match !temp_dir_ref with
  | Some dir -> Filename.temp_file ~temp_dir:dir prefix suffix
  | None -> Filename.temp_file prefix suffix

(* Remove a (flat) invocation directory together with its contents. *)
let remove_temp_dir dir =
  (try
     Array.iter
       (fun f -> try Sys.remove (Filename.concat dir f) with _ -> ())
       (Sys.readdir dir)
   with _ -> ());
  (try Sys.rmdir dir with _ -> ())

(* Run [f] with a fresh invocation directory active, removing it (and
   everything left inside it) afterwards. In debug mode, or when a
   directory is already active (nested call), [f] is run as-is. *)
let with_temp_dir (f : unit -> 'a) : 'a =
  if !debug_mode || !temp_dir_ref <> None then
    f ()
  else
    begin
      let base = Filename.temp_file "coqhammer" "" in
      Sys.remove base;
      Sys.mkdir base 0o700;
      temp_dir_ref := Some base;
      Fun.protect
        ~finally:(fun () -> temp_dir_ref := None; remove_temp_dir base)
        f
    end

let error_log_file_ref = ref None

(* Path of the log file collecting the stderr of external commands (the
   predictor and the ATPs) in debug mode. A fresh, user-owned temporary
   file with safe permissions is created on first use, so the
   redirection cannot be diverted to a pre-existing attacker-controlled
   path in the shared temp directory. *)
let error_log_file () =
  match !error_log_file_ref with
  | Some f -> f
  | None ->
     let f = Filename.temp_file "coqhammer_error" ".log" in
     error_log_file_ref := Some f;
     f

(* Shell redirection for the stderr of external commands: in debug mode
   the error output is kept in the error log file so that configuration
   problems can be diagnosed; otherwise it is discarded. *)
let stderr_redirect () =
  if !debug_mode then
    "2>> " ^ Filename.quote (error_log_file ())
  else
    "2>/dev/null"

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"ClosureGuards"];
      optread=(fun () -> !Coq_transl_opts.opt_closure_guards);
      optwrite=(fun b -> Coq_transl_opts.opt_closure_guards := b)}
  in
  declare_bool_option gdopt

let filter_program = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"FilterProgram"];
      optread=(fun () -> !filter_program);
      optwrite=(fun b -> filter_program := b)}
  in
  declare_bool_option gdopt

let filter_classes = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"FilterClasses"];
      optread=(fun () -> !filter_classes);
      optwrite=(fun b -> filter_classes := b)}
  in
  declare_bool_option gdopt

let filter_hurkens = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"FilterHurkens"];
      optread=(fun () -> !filter_hurkens);
      optwrite=(fun b -> filter_hurkens := b)}
  in
  declare_bool_option gdopt

let search_blacklist = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"Blacklist"];
      optread=(fun () -> !search_blacklist);
      optwrite=(fun b -> search_blacklist := b)}
  in
  declare_bool_option gdopt

let clear_unused = ref true

let _ =
  let gdopt=
    { optdepr=None;
      optstage = Interp;
      optkey=["Hammer";"ClearUnused"];
      optread=(fun () -> !clear_unused);
      optwrite=(fun b -> clear_unused := b)}
  in
  declare_bool_option gdopt

module FilterSet = Set.Make(Names.ModPath)

module HammerFilter = struct
  type t = Names.ModPath.t
  module Set = FilterSet
  let encode env = Nametab.locate_module
  let check_local _ _ = ()
  let discharge x = x
  let subst = Mod_subst.subst_mp
  let printer m = Names.DirPath.print (Libnames.dirpath_of_path (Nametab.path_of_module m))
  let key = ["Hammer"; "Filter"]
  let title = "Hammer Filter"
  let member_message m b =
    Pp.app (printer m)
      (if b then Pp.str " present" else Pp.str "absent")
end

module HammerFilterTable = MakeRefTable(HammerFilter)
