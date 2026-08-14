(* Proofview.tclTIMEOUT is incorrect because of a bug in OCaml
   runtime. This file contains a timeout implementation based on
   Unix.fork and Unix.sleep. See:

   https://caml.inria.fr/mantis/view.php?id=7709
   https://caml.inria.fr/mantis/view.php?id=4127
   https://github.com/coq/coq/issues/7430
   https://github.com/coq/coq/issues/7408

*)

(* ptimeout implements timeout using fork and sleep *)
let ptimeout n tac =
  let pid = Unix.fork () in
  if pid = 0 then
    begin (* the worker *)
      (* See the comment on [Hhpartac.detach_child] (issue #180). *)
      Hhpartac.detach_child ();
      Proofview.tclOR
        (Proofview.tclBIND tac (fun _ -> Unix._exit 0))
        (fun _ -> Unix._exit 1)
    end
  else
    begin
      let pid2 = Unix.fork () in
      if pid2 = 0 then
        begin (* the watchdog *)
          Hhpartac.detach_child ();
          (try
             Unix.sleep n;
             Unix.kill pid Sys.sigterm
           with _ -> ());
          Unix._exit 0
        end;
      let clean_watchdog () =
        ignore (try Unix.kill pid2 Sys.sigterm with _ -> ());
        (try ignore (Unix.waitpid [] pid2) with _ -> ())
      in
      let clean_all () =
        (* Watchdog first: while it lives it may SIGTERM the worker's
           pid, which must not happen after that pid has been reaped
           (and possibly recycled). *)
        clean_watchdog ();
        ignore (try Unix.kill pid Sys.sigterm with _ -> ());
        (try ignore (Unix.waitpid [] pid) with _ -> ())
      in
      let res =
        try
          let (_, status) = Unix.waitpid [] pid
          in
          match status with
          | Unix.WEXITED 0 -> clean_watchdog (); `Success
          | Unix.WSIGNALED s when s = Sys.sigint ->
             (* The worker has the default SIGINT behaviour, so this
                means Ctrl-C: the user's interrupt must not be turned
                into a mere Tac_Timeout failure. *)
             clean_watchdog (); `Interrupted
          | _ -> clean_watchdog (); `Timeout
        with
        | e when CErrors.noncritical e ->
           clean_all (); `Timeout
        | e ->
           (* Sys.Break in particular: do not swallow the user's
              interrupt; clean up and let it propagate. *)
           let e = Exninfo.capture e in
           clean_all ();
           Exninfo.iraise e
      in
      match res with
      | `Success -> tac
      | `Interrupted -> raise Sys.Break
      | `Timeout -> Proofview.tclZERO Logic_monad.Tac_Timeout
    end
