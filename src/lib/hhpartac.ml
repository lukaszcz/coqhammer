(* Parallel invocation of tactics *)

(* Forked children must never touch the toplevel's standard descriptors:
   under an IDE (coqtop -emacs, coqidetop) stdin/stdout carry the prover
   protocol, and a child that escapes into the read-eval-print loop starts
   competing with the parent for those channels, desynchronizing the UI
   from the kernel (issue #180).  This can actually happen: on Ctrl-C the
   toplevel's [Sys.catch_break] handler raises [Sys.Break] in every
   process of the terminal's foreground group, including our forks, and
   [Proofview.tclOR] does not catch critical exceptions, so a worker
   unwinds past [Unix._exit] into [Coqloop].  Detaching the descriptors
   makes any such escape harmless (the REPL reads EOF and exits), and
   restoring the default SIGINT behaviour makes Ctrl-C simply kill the
   child. *)
let detach_child () =
  Sys.set_signal Sys.sigint Sys.Signal_default;
  (* A child that still escapes past [Unix._exit] (a critical exception
     unwinding into the toplevel loop, which then reads EOF from
     /dev/null and exits normally) must report failure, not success:
     legitimate terminations use [Unix._exit], which bypasses
     [at_exit].  Exiting immediately here also prevents flushing of
     inherited channel buffers (the concern of PR #229) on any
     remaining [Stdlib.exit] path. *)
  at_exit (fun () -> Unix._exit 2);
  (* An exception must never escape from a freshly forked child. *)
  try
    let devnull = Unix.openfile "/dev/null" [Unix.O_RDWR] 0o600 in
    Unix.dup2 devnull Unix.stdin;
    Unix.dup2 devnull Unix.stdout;
    Unix.dup2 devnull Unix.stderr;
    Unix.close devnull
  with _ -> ()

let partac time lst0 cont =
  let rec pom lst pids =
    match lst with
    | [] ->
       let pid2 = Unix.fork () in
       if pid2 = 0 then
         begin (* the watchdog *)
           detach_child ();
           begin
             try
               if time > 0 then
                 begin
                   Unix.sleep time;
                   List.iter (fun i -> try Unix.kill i Sys.sigterm with _ -> ()) pids
                 end
             with _ -> ()
           end;
           Unix._exit 0
         end
       else
         let cleaned = ref false in
         let clean () =
           (* Idempotent: [clean] may be reached again when an exception
              is raised from [cont] after a normal cleanup; the pids may
              have been reaped and recycled by then, so they must not be
              killed twice. *)
           if not !cleaned then
             begin
               cleaned := true;
               (* Kill and reap the watchdog first: while it lives it
                  may SIGTERM a worker pid, which must not happen after
                  that pid has been reaped (and possibly recycled). *)
               ignore (try Unix.kill pid2 Sys.sigterm with _ -> ());
               (try ignore (Unix.waitpid [] pid2) with _ -> ());
               List.iter (fun i -> try Unix.kill i Sys.sigterm with _ -> ()) pids;
               List.iter (fun i -> try ignore (Unix.waitpid [] i) with _ -> ()) pids
             end
         in
         let n = List.length lst0 in
         let rec wait k =
           if k = 0 then
               begin
                 clean ();
                 cont (-1) (Proofview.tclZERO Logic_monad.Tac_Timeout)
               end
           else
             let (pid, status) = Unix.wait () in
             let interrupted =
               (* The children have the default SIGINT behaviour, so a
                  child killed by SIGINT means Ctrl-C: propagate the
                  interrupt instead of racing with the parent's own
                  pending [Sys.Break] (losing that race would turn the
                  user's interrupt into a mere tactic failure). *)
               match status with
               | Unix.WSIGNALED s -> s = Sys.sigint
               | _ -> false
             in
             if interrupted then
               begin
                 clean ();
                 raise Sys.Break
               end
             else if pid = pid2 && time > 0 then
               begin
                 clean ();
                 cont (-1) (Proofview.tclZERO Logic_monad.Tac_Timeout)
               end
             else if List.mem pid pids then
               match status with
               | Unix.WEXITED 0 ->
                  begin
                    clean ();
                    let i = n - Hhlib.index pid pids - 1 in
                    cont i (List.nth lst0 i)
                  end
               | _ -> wait (k - 1)
             else
               wait k
         in
         (* [Unix.wait] is interrupted by Ctrl-C ([Sys.Break]); the
            children must be killed and reaped before the interrupt
            propagates, or they are leaked. *)
         (try wait n
          with e ->
            let e = Exninfo.capture e in
            clean ();
            Exninfo.iraise e)
    | tac :: t ->
       let pid = Unix.fork () in
       if pid = 0 then
         begin (* a worker *)
           detach_child ();
           Proofview.tclOR
             (Proofview.tclBIND tac (fun _ -> Unix._exit 0))
             (fun _ -> Unix._exit 1)
         end
       else
         pom t (pid :: pids)
  in
  pom lst0 []
