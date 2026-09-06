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
  (* An exception must never escape from a freshly forked child; and a
     child whose descriptors could not be detached would keep the
     toplevel's protocol channels, recreating the hazard above, so
     abort it outright (its exit status reports a failed tactic). *)
  try
    let devnull = Unix.openfile "/dev/null" [Unix.O_RDWR] 0o600 in
    Unix.dup2 devnull Unix.stdin;
    Unix.dup2 devnull Unix.stdout;
    Unix.dup2 devnull Unix.stderr;
    (* [openfile] returns the lowest free descriptor: if a standard
       descriptor was closed at fork time, [devnull] IS that
       descriptor, and closing it would undo its own redirection. *)
    if devnull <> Unix.stdin && devnull <> Unix.stdout && devnull <> Unix.stderr
    then Unix.close devnull
  with _ -> Unix._exit 2

(* The body of a forked worker: detach from the toplevel, run the
   tactic, and report success or failure through the exit status.
   When [time > 0] the worker also arms a SIGALRM deadline slightly
   beyond the timeout: the parent normally kills it earlier, so the
   alarm only bounds the lifetime of a worker orphaned by a parent
   that died without cleaning up -- and a worker signalling itself
   cannot hit a recycled pid. *)
let worker time tac =
  detach_child ();
  if time > 0 then
    begin
      Sys.set_signal Sys.sigalrm Sys.Signal_default;
      (* [min ... (max_int - 5)] keeps [time + 5] from overflowing
         [int].  [Unix.alarm] truncates its argument to a 32-bit
         [unsigned int], so the deadline is exact up to about 2^32
         seconds (~136 years) -- far beyond any real time limit. *)
      ignore (Unix.alarm (min time (max_int - 5) + 5))
    end;
  Proofview.tclOR
    (Proofview.tclBIND tac (fun _ -> Unix._exit 0))
    (fun _ -> Unix._exit 1)

(* Restart [f x] when interrupted by a signal whose OCaml handler
   returns normally: the kernel then fails the underlying system call
   with EINTR, which must not be confused with a real error (or,
   worse, a timeout).  A handler that raises instead -- as
   [Sys.catch_break]'s does with [Sys.Break] on Ctrl-C -- propagates
   out of [f] as usual. *)
let rec restart_on_eintr f x =
  try f x with Unix.Unix_error (Unix.EINTR, _, _) -> restart_on_eintr f x

let killed_by_sigint status =
  match status with
  | Unix.WSIGNALED s -> s = Sys.sigint
  | _ -> false

(* SIGTERM and reap the child processes still listed in [live],
   removing each pid as it is reaped.  A pid leaves [live] only when
   reaped, and only reaped pids can be recycled by the kernel, so no
   signal is ever sent to a pid that may denote an unrelated process.
   This also makes the cleanup idempotent and re-entrant: if it is
   itself interrupted -- an asynchronous [Sys.Break] arriving during
   [kill] or [waitpid] must propagate rather than be swallowed
   together with the user's interrupt -- running it again finishes the
   job.  Watchdog processes must precede workers in [live]: a watchdog
   is then reaped -- hence provably no longer signalling anybody --
   before the worker pids it holds are reaped and become recyclable. *)
let kill_children live =
  List.iter
    (fun pid -> try Unix.kill pid Sys.sigterm with Unix.Unix_error _ -> ())
    !live;
  List.iter
    (fun pid ->
      (try ignore (restart_on_eintr (Unix.waitpid []) pid)
       with Unix.Unix_error (Unix.ECHILD, _, _) -> ());
      live := List.filter (fun p -> p <> pid) !live)
    !live

let partac time lst0 cont =
  let rec pom lst pids =
    match lst with
    | [] ->
       let pid2 = Unix.fork () in
       if pid2 = 0 then
         begin (* The watchdog: a pure timer.  It must not signal the
                  worker pids itself: it only holds a fork-time
                  snapshot of them, and by the time it fires some may
                  have been reaped by the parent -- and recycled by
                  the kernel, so the signal could hit an unrelated
                  process.  The parent, which knows which pids are
                  still live, does the killing when [Unix.wait]
                  returns the watchdog. *)
           detach_child ();
           (try if time > 0 then Unix.sleep time with _ -> ());
           Unix._exit 0
         end
       else
         (* Watchdog first: see [kill_children]. *)
         let live = ref (pid2 :: pids) in
         let clean () = kill_children live in
         let n = List.length lst0 in
         let rec wait k =
           if k = 0 then
               begin
                 clean ();
                 cont (-1) (Proofview.tclZERO Logic_monad.Tac_Timeout)
               end
           else
             let (pid, status) = restart_on_eintr Unix.wait () in
             live := List.filter (fun p -> p <> pid) !live;
             (* The children have the default SIGINT behaviour, so a
                child killed by SIGINT means Ctrl-C: propagate the
                interrupt instead of racing with the parent's own
                pending [Sys.Break] (losing that race would turn the
                user's interrupt into a mere tactic failure). *)
             if killed_by_sigint status then
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
         worker time tac
       else
         pom t (pid :: pids)
  in
  pom lst0 []
