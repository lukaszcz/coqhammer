open Hammer_lib
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

(* Per-invocation temporary directories live under a private 0700
   [coqhammer-<uid>] directory in the system temporary directory. Each
   [inv-<pid>-<random>] directory is created atomically with [mkdir] and
   is removed when its hammer/predict invocation finishes. Once per
   process, stale invocation directories whose creator is dead (or whose
   mtime is more than 24 hours old, as a backstop for pid reuse) are
   removed. The sweep is confined to the private per-user parent and only
   considers names of that form, so concurrent invocations do not delete
   each other's files. In debug mode no invocation directory is used, so
   intermediate files are left in the system temporary directory for
   inspection. *)

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

let temp_parent_dir () =
  let dir =
    Filename.concat (Filename.get_temp_dir_name ())
      ("coqhammer-" ^ string_of_int (Unix.geteuid ()))
  in
  (try Sys.mkdir dir 0o700 with Sys_error _ -> ());
  let unsafe () =
    raise (Hammer_errors.HammerError
             ("unsafe temporary directory: " ^ dir ^
                " (expected a directory owned by the current user with \
                 permissions 0700; remove it or run 'chmod 700' on it)"))
  in
  let st =
    try Unix.lstat dir with Unix.Unix_error _ -> unsafe ()
  in
  if st.Unix.st_kind <> Unix.S_DIR || st.Unix.st_uid <> Unix.geteuid ()
     || st.Unix.st_perm land 0o777 <> 0o700
  then
    unsafe ();
  dir

let make_temp_dir parent =
  let rng =
    Random.State.make
      [| Unix.getpid (); int_of_float (Unix.gettimeofday () *. 1e6) |]
  in
  let rec go attempts =
    if attempts = 0 then
      raise
        (Hammer_errors.HammerError "cannot create a temporary directory");
    let name =
      Filename.concat parent
        (Printf.sprintf "inv-%d-%06x" (Unix.getpid ())
           (Random.State.int rng 0x1000000))
    in
    try
      Sys.mkdir name 0o700;
      name
    with Sys_error _ -> go (attempts - 1)
  in
  go 100

let parse_inv_pid entry =
  let prefix = "inv-" in
  let prefix_len = String.length prefix in
  if String.length entry <= prefix_len
     || String.sub entry 0 prefix_len <> prefix
  then
    None
  else
    match String.index_from_opt entry prefix_len '-' with
    | None -> None
    | Some separator ->
       if separator = prefix_len || separator = String.length entry - 1 then
         None
       else
         match
           int_of_string_opt
             (String.sub entry prefix_len (separator - prefix_len))
         with
         | Some pid when pid > 0 -> Some pid
         | _ -> None

let swept_temp_dirs = ref false

let sweep_stale_temp_dirs parent =
  if not !swept_temp_dirs then
    begin
      swept_temp_dirs := true;
      try
        Array.iter
          (fun entry ->
             try
               match parse_inv_pid entry with
               | None -> ()
               | Some pid ->
                  let dir = Filename.concat parent entry in
                  let st = Unix.lstat dir in
                  if st.Unix.st_kind = Unix.S_DIR then
                    begin
                      let dead =
                        try
                          Unix.kill pid 0;
                          false
                        with
                        | Unix.Unix_error (Unix.ESRCH, _, _) -> true
                        | _ -> false
                      in
                      let ancient = Unix.time () -. st.Unix.st_mtime > 86400. in
                      if dead || ancient then remove_temp_dir dir
                    end
             with _ -> ())
          (Sys.readdir parent)
      with _ -> ()
    end

(* Run [f] with a fresh invocation directory active, removing it (and
   everything left inside it) afterwards. In debug mode, or when a
   directory is already active (nested call), [f] is run as-is. *)
let with_temp_dir (f : unit -> 'a) : 'a =
  if !debug_mode || !temp_dir_ref <> None then
    f ()
  else
    begin
      let parent = temp_parent_dir () in
      let base = make_temp_dir parent in
      sweep_stale_temp_dirs parent;
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
