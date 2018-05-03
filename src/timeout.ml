(* Proofview.tclTIMEOUT is incorrect because of a bug in OCaml runtime
   (a random thread receives the SIGALRM signal instead of the thread
   which set it up using Unix.alarm). This file contains a more
   correct version, but it may still fail to work sometimes. *)
   
let my_timeout n f e =
  let killed = ref false in
  let exited = ref false in
  let watchdog () =
    let rec kill_main_thread () =
      try
        while not !killed do
          exited := true;
          Control.interrupt := true;
          Msg.error "Coq/OCaml bug: timeout failed!";
          Unix.sleep 1
        done
      with Sys.Break ->
        begin
          prerr_endline "OCaml bug: Sys.Break in watchdog";
          kill_main_thread ()
        end
    in
    Unix.sleep (n + 1);
    kill_main_thread ()
  in
  (* This will fail if the main thread loops without executing
     operations which allow switching to the watchdog thread. *)
  let _ = Thread.create watchdog ()
  in
  let timeout_handler _ = raise e in
  let psh = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
  let _ = Unix.alarm n in
  let restore_timeout () =
    let _ = Unix.alarm 0 in
    Sys.set_signal Sys.sigalrm psh
  in
  try
    let res = f () in
    killed := true;
    restore_timeout ();
    res
  with
  | Sys.Break ->
     let () = killed := true in
     restore_timeout ();
     (** Just in case, it could be a regular Ctrl+C *)
     if not !exited then raise Sys.Break
     else raise e
  | e ->
     let () = killed := true in
     let e = Backtrace.add_backtrace e in
     restore_timeout ();
     Exninfo.iraise e
	 

let tclTIMEOUT n t =
  Proofview.tclTIMEOUT n t

