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

let id_mem id ids = List.exists ((=) id) ids

let unlink_if_owned path ids =
  match file_id path with
  | Some id when id_mem id ids -> Unix.unlink path
  | _ -> ()

let attempt_all actions =
  let error = ref None in
  List.iter
    (fun action ->
       try action () with e ->
         match !error with
         | None -> error := Some e
         | Some _ -> ())
    actions;
  match !error with
  | Some e -> raise e
  | None -> ()

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

let option_to_list = function
  | Some value -> [value]
  | None -> []

let write ~commit_path ~write_commit ~companion_path ~write_companion =
  let stale_commit = file_id commit_path in
  let stale_companion = file_id companion_path in
  let commit_ids = ref (option_to_list stale_commit) in
  let companion_ids = ref (option_to_list stale_companion) in
  let temporaries = ref [] in
  let cleanup () =
    List.iter (fun temporary -> close_out_noerr temporary.channel) !temporaries;
    attempt_all
      (List.map
         (fun temporary () -> unlink_if_owned temporary.path [temporary.id])
         !temporaries @
       [ (fun () -> unlink_if_owned commit_path !commit_ids);
         (fun () -> unlink_if_owned companion_path !companion_ids) ])
  in
  try
    (* A retry must not leave an old pair looking like the result of this run
       if creating or writing its replacement subsequently fails. *)
    attempt_all
      [ (fun () -> unlink_if_owned commit_path !commit_ids);
        (fun () -> unlink_if_owned companion_path !companion_ids) ];
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
    (try cleanup () with _ -> ());
    raise e
