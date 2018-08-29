(* Parallel invocation of tactics *)

let partac n lst0 cont =
  let rec pom lst pids =
    match lst with
    | [] ->
       let pid2 = Unix.fork () in
       if pid2 = 0 then
         begin (* the watchdog *)
           if n > 0 then
             begin
               Unix.sleep n;
               List.iter (fun i -> try Unix.kill i Sys.sigterm with _ -> ()) pids
             end;
           exit 0
         end
       else
         let rec wait k pids =
           let clean () =
             List.iter (fun i -> try Unix.kill i Sys.sigterm with _ -> ()) pids;
             ignore (try Unix.kill pid2 Sys.sigterm with _ -> ())
           in
           match pids with
           | [] ->
              begin
                clean ();
                cont (-1) (Proofview.tclZERO Proofview.Timeout)
              end
           | pid :: t ->
              begin
                try
                  let (_, status) = Unix.waitpid [] pid
                  in
                  match status with
                  | Unix.WEXITED 0 -> clean (); cont k (List.nth lst0 k)
                  | _ -> wait (k + 1) t
                with
                | _ -> wait (k + 1) t
              end
         in
         wait 0 (List.rev pids)
    | tac :: t ->
       let pid = Unix.fork () in
       if pid = 0 then
         begin (* a worker *)
           Proofview.tclOR
             (Proofview.tclBIND tac (fun _ -> exit 0))
             (fun _ -> exit 1)
         end
       else
         pom t (pid :: pids)
  in
  pom lst0 []
