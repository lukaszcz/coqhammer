exception Injected

let fail message = raise (Failure message)

let assert_true condition message = if not condition then fail message

let write_string path contents =
  let oc = open_out path in
  output_string oc contents;
  close_out oc

let read_string path =
  let ic = open_in path in
  let contents = really_input_string ic (in_channel_length ic) in
  close_in ic;
  contents

let has_pair_temporary dir =
  Array.exists
    (fun name ->
       let prefix = ".coqhammer-pair-" in
       let suffix = ".tmp" in
       let length = String.length name in
       length >= String.length prefix + String.length suffix &&
       String.sub name 0 (String.length prefix) = prefix &&
       String.sub name (length - String.length suffix) (String.length suffix) = suffix)
    (Sys.readdir dir)

let expect_failure f =
  try
    f ();
    fail "expected paired output to fail"
  with
  | Injected -> ()
  | Unix.Unix_error _ -> ()
  | Sys_error _ -> ()
  | Failure message when message <> "expected paired output to fail" -> ()

let assert_clean dir problem metadata =
  assert_true (not (Sys.file_exists problem)) "problem survived failed publication";
  assert_true (not (Sys.file_exists metadata)) "metadata survived failed publication";
  assert_true (not (has_pair_temporary dir)) "paired-output temporary survived"

let publish problem metadata write_problem write_metadata =
  Paired_output.write
    ~commit_path:problem ~write_commit:write_problem
    ~companion_path:metadata ~write_companion:write_metadata

let () =
  let marker = Filename.temp_file "paired-output-test-" "" in
  Sys.remove marker;
  Sys.mkdir marker 0o700;
  let problem = Filename.concat marker "goal.p" in
  let metadata = Filename.concat marker "goal.meta" in
  let output contents oc = output_string oc contents in
  Fun.protect
    ~finally:(fun () ->
      Array.iter
        (fun name ->
           let path = Filename.concat marker name in
           try Sys.remove path with Sys_error _ -> try Sys.rmdir path with Sys_error _ -> ())
        (Sys.readdir marker);
      Sys.rmdir marker)
    (fun () ->
      write_string problem "stale problem";
      write_string metadata "stale metadata";
      publish problem metadata (output "problem") (output "metadata\n");
      assert_true (read_string problem = "problem") "wrong published problem";
      assert_true (read_string metadata = "metadata\n") "wrong published metadata";
      assert_true (not (has_pair_temporary marker)) "temporary survived successful publication";

      Sys.remove problem;
      Sys.remove metadata;
      let child = Unix.fork () in
      if child = 0 then begin
        ignore (Unix.umask 0o027);
        try
          publish problem metadata (output "problem") (output "metadata");
          Unix._exit 0
        with _ ->
          Unix._exit 1
      end;
      let _, status = Unix.waitpid [] child in
      assert_true (status = Unix.WEXITED 0) "permission test child failed";
      let permissions path = (Unix.stat path).Unix.st_perm land 0o777 in
      assert_true (permissions problem = 0o640)
        "problem did not retain open_out permissions";
      assert_true (permissions metadata = 0o640)
        "metadata did not retain open_out permissions";

      Sys.remove problem;
      Sys.remove metadata;
      expect_failure (fun () ->
        publish problem metadata (output "problem")
          (fun oc ->
             output_string oc "metadata";
             write_string problem "other problem";
             write_string metadata "other metadata"));
      assert_true (read_string problem = "other problem")
        "cleanup removed another writer's problem";
      assert_true (read_string metadata = "other metadata")
        "cleanup removed another writer's metadata";
      assert_true (not (has_pair_temporary marker))
        "temporary survived a publication conflict";

      write_string problem "stale problem";
      write_string metadata "stale metadata";
      expect_failure (fun () -> publish problem metadata (fun _ -> raise Injected) (output "metadata"));
      assert_clean marker problem metadata;

      write_string problem "stale problem";
      write_string metadata "stale metadata";
      expect_failure (fun () -> publish problem metadata (output "problem") (fun _ -> raise Injected));
      assert_clean marker problem metadata;

      expect_failure (fun () ->
        publish problem metadata
          (fun oc -> output_string oc "problem"; Unix.close (Unix.descr_of_out_channel oc))
          (output "metadata"));
      assert_clean marker problem metadata;

      expect_failure (fun () ->
        publish problem metadata (output "problem")
          (fun oc ->
             output_string oc "metadata";
             Array.iter
               (fun name ->
                  let path = Filename.concat marker name in
                  if String.length name >= 18 &&
                     String.sub name 0 16 = ".coqhammer-pair-" &&
                     Filename.check_suffix name ".tmp" &&
                     read_string path = "problem"
                  then Sys.remove path)
               (Sys.readdir marker)));
      assert_clean marker problem metadata;

      let missing_problem = Filename.concat marker "missing/goal.p" in
      let missing_metadata = Filename.concat marker "missing/goal.meta" in
      expect_failure (fun () ->
        publish missing_problem missing_metadata (output "problem") (output "metadata"));
      assert_true (not (Sys.file_exists missing_problem)) "problem survived failed open";
      assert_true (not (Sys.file_exists missing_metadata)) "metadata survived failed open";

      print_endline "paired output tests passed")
