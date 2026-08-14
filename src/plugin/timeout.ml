(* Proofview.tclTIMEOUT is incorrect because of a bug in OCaml
   runtime. This file contains a timeout implementation based on
   Unix.fork and Unix.sleep. See:

   https://caml.inria.fr/mantis/view.php?id=7709
   https://caml.inria.fr/mantis/view.php?id=4127
   https://github.com/coq/coq/issues/7430
   https://github.com/coq/coq/issues/7408

*)

(* The [Hammer_lib] modules ([Hhpartac] here) must be reached through
   the pack: only the pack's interface is installed with
   coq-hammer-tactics, and the dune library is wrapped. *)
open Hammer_lib

(* ptimeout implements timeout using fork and sleep *)
let ptimeout n tac =
  let pid = Unix.fork () in
  if pid = 0 then
    (* the worker; see the comment on [Hhpartac.detach_child] (issue #180) *)
    Hhpartac.worker n tac
  else
    begin
      let pid2 = Unix.fork () in
      if pid2 = 0 then
        begin (* The watchdog.  Unlike in [Hhpartac.partac], signalling
                 the worker from here is essentially safe: the parent
                 blocks in [waitpid] on that single worker, so while
                 the watchdog lives the worker is unreaped and its pid
                 cannot be recycled.  (The exception is the instant
                 between the parent reaping the worker and SIGTERMing
                 the watchdog, which would have to coincide with the
                 timeout expiring.) *)
          Hhpartac.detach_child ();
          (try
             Unix.sleep n;
             Unix.kill pid Sys.sigterm
           with _ -> ());
          Unix._exit 0
        end;
      (* Watchdog first: see [Hhpartac.kill_children]. *)
      let live = ref [pid2; pid] in
      let res =
        try
          let (_, status) = Hhpartac.restart_on_eintr (Unix.waitpid []) pid in
          live := List.filter (fun p -> p <> pid) !live;
          Hhpartac.kill_children live;
          match status with
          | Unix.WEXITED 0 -> `Success
          | _ when Hhpartac.killed_by_sigint status ->
             (* The worker has the default SIGINT behaviour, so this
                means Ctrl-C: the user's interrupt must not be turned
                into a mere Tac_Timeout failure. *)
             `Interrupted
          | _ -> `Timeout
        with
        | e when CErrors.noncritical e ->
           Hhpartac.kill_children live; `Timeout
        | e ->
           (* Sys.Break in particular: do not swallow the user's
              interrupt; clean up and let it propagate. *)
           let e = Exninfo.capture e in
           Hhpartac.kill_children live;
           Exninfo.iraise e
      in
      match res with
      | `Success -> tac
      | `Interrupted -> raise Sys.Break
      | `Timeout -> Proofview.tclZERO Logic_monad.Tac_Timeout
    end
