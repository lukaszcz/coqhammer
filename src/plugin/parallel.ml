(* Parallel function invocation (for Unix) *)

type ('a, 'b) sum = Inl of 'a | Inr of 'b | Err of int

let run_parallel (progress_fn : 'a -> unit) (sec_fn : unit -> unit)
    time (lst : (('a -> unit) -> 'b) list) =
  let piper, pipew = Unix.pipe () in
  let start f =
    let pid = Unix.fork () in
    let oc = Unix.out_channel_of_descr pipew in
    if pid = 0 then
      begin
        try
          Unix.close piper;
          let progress_sub_fn a =
            output_value oc (Inl a); flush oc
          in
          let ret = f progress_sub_fn in
          output_value oc (Inr ret);
          flush oc;
          Unix._exit 0
        with _ ->
          try output_value oc (Err (Unix.getpid ())); flush oc; Unix._exit 0
          with _ -> Unix._exit 0
      end;
    pid
  in
  let subprocesses = ref (List.mapi (fun pos f -> (start f, pos)) lst) in
  let clean () =
    List.iter (fun (pid, _) -> try Unix.kill pid Sys.sigterm with _ -> ()) !subprocesses;
    Unix.close piper;
    List.iter (fun (pid, _) -> try ignore (Unix.waitpid [] pid) with _ -> ()) !subprocesses;
    List.iter (fun (pid, _) -> try Unix.kill pid Sys.sigkill with _ -> ()) !subprocesses;
  in
  (* This is an over-approximation: a child which reported failure and exited
     remains here until [clean] unless its [Err] message was also received.
     Callers must give explicit failure reports precedence over membership in
     this list. *)
  let unfinished () = List.map snd !subprocesses in
  try
    Unix.close pipew;
    let rec select desc time =
      if time <= 0. then 0. else
        let (r, _, _) = Unix.select [desc] [] [] 1. in
        if r <> [] then time else (sec_fn (); select desc (time -. 1.))
    in
    Unix.set_nonblock piper;
    let inc = Unix.in_channel_of_descr piper in
    let remove pid =
      subprocesses := List.filter (fun (child_pid, _) -> child_pid <> pid) !subprocesses;
      ignore (Unix.waitpid [] pid)
    in
    let rec drain () =
      try
        match input_value inc with
        | Inl pr -> progress_fn pr; drain ()
        | Inr _ -> drain ()
        | Err pid -> remove pid; drain ()
      with Sys_blocked_io | Unix.Unix_error _ | End_of_file -> ()
    in
    let rec ret time =
      if !subprocesses = [] then None else
        let interp time = function
          | Inl pr -> progress_fn pr; ret time
          | Inr value -> drain (); Some value
          | Err pid -> remove pid; ret time
        in
        try interp time (input_value inc) with Sys_blocked_io | Unix.Unix_error _ ->
          let ntime = select piper time in
          if ntime > 0. then interp ntime (input_value inc) else None
    in
    let ret = ret time in
    let unfinished = unfinished () in
    clean ();
    (ret, unfinished)
  with
  | End_of_file ->
     let unfinished = unfinished () in
     clean (); (None, unfinished)
  | e ->
     clean (); raise e
