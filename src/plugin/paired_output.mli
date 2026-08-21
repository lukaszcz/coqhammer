(* Publish a commit file and its companion as one logical output pair.
   Both writers receive unique temporary files in their targets' directories.
   The companion is renamed first and the commit file last, so consumers may
   treat the commit file's appearance as indicating a complete pair.

   Targets are assumed to have one writer, as gen-atp guarantees by assigning
   each goal and predictor/budget configuration its own paths. Identity checks
   prevent cleanup from removing a target replaced by a different writer. *)
val write :
  commit_path:string ->
  write_commit:(out_channel -> unit) ->
  companion_path:string ->
  write_companion:(out_channel -> unit) ->
  unit
