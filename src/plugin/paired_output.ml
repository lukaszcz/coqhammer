type file_id = int * int

type temporary = {
  path : string;
  id : file_id;
  channel : out_channel;
}

let id_of_stats stats = stats.Unix.st_dev, stats.Unix.st_ino

let file_id path =
  try Some (id_of_stats (Unix.lstat path)) with
  | Unix.Unix_error (Unix.ENOENT, _, _) -> None

let unlink_if_owned path ids =
  match file_id path with
  | Some id when List.mem id ids -> Unix.unlink path
  | _ -> ()

(* Cleanup runs with an exception already propagating, so one leftover that
   cannot be removed must neither replace that exception nor stop the removals
   that follow it. *)
let ignore_errors f = try f () with _ -> ()

let make_temporary target =
  let dir = Filename.dirname target in
  let path, channel =
    Filename.open_temp_file ~perms:0o666 ~temp_dir:dir
      ".coqhammer-pair-" ".tmp"
  in
  try
    let id = id_of_stats (Unix.fstat (Unix.descr_of_out_channel channel)) in
    { path; id; channel }
  with e ->
    close_out_noerr channel;
    (try Unix.unlink path with _ -> ());
    raise e

let ensure_absent path =
  match file_id path with
  | None -> ()
  | Some _ -> failwith ("paired output target appeared during publication: " ^ path)

let write ~commit_path ~write_commit ~companion_path ~write_companion =
  let stale_commit = file_id commit_path in
  let stale_companion = file_id companion_path in
  (* [Stdlib.] because Rocq's own [Option] shadows the standard one here. *)
  let commit_ids = ref (Stdlib.Option.to_list stale_commit) in
  let companion_ids = ref (Stdlib.Option.to_list stale_companion) in
  let temporaries = ref [] in
  let cleanup () =
    (* Close every channel before unlinking any of them, so no removal races a
       still-open handle on platforms that refuse one. *)
    List.iter (fun temporary -> close_out_noerr temporary.channel) !temporaries;
    List.iter
      (fun temporary ->
         ignore_errors (fun () -> unlink_if_owned temporary.path [temporary.id]))
      !temporaries;
    ignore_errors (fun () -> unlink_if_owned commit_path !commit_ids);
    ignore_errors (fun () -> unlink_if_owned companion_path !companion_ids)
  in
  try
    (* A retry must not leave an old pair looking like the result of this run
       if creating or writing its replacement subsequently fails.  Should the
       first removal raise, [cleanup] reattempts the second. *)
    unlink_if_owned commit_path !commit_ids;
    unlink_if_owned companion_path !companion_ids;
    ensure_absent commit_path;
    ensure_absent companion_path;
    let commit = make_temporary commit_path in
    temporaries := commit :: !temporaries;
    let companion = make_temporary companion_path in
    temporaries := companion :: !temporaries;
    write_commit commit.channel;
    close_out commit.channel;
    write_companion companion.channel;
    close_out companion.channel;
    (* The problem/commit file is the publication marker. The pre-rename
       absence checks avoid silently replacing a concurrently published file;
       gen-atp's per-goal paths exclude a same-target race between the checks
       and renames. *)
    ensure_absent companion_path;
    companion_ids := companion.id :: !companion_ids;
    Unix.rename companion.path companion_path;
    ensure_absent commit_path;
    commit_ids := commit.id :: !commit_ids;
    Unix.rename commit.path commit_path
  with e ->
    cleanup ();
    raise e
