(* Diagnostic counters for lifted symbols.

   Lifting mints one symbol per occurrence shape, so one Coq object reached at
   two shapes gets two unrelated names.  Sharing those lifts across
   instantiation is worth its risk only where the splitting actually happens,
   and that is a question about corpora rather than about the code: these
   counters answer it by reporting, per lift kind, how many symbols the
   translation minted and how many of them a link equation would relate.

   The counters are collected only when COQHAMMER_LIFT_STATS names a directory;
   otherwise every entry point here is a no-op, so a default build pays
   nothing.  Each process writes its own file, since problem generation
   compiles many files in parallel and appending to a shared one would
   interleave. *)

let out_dir =
  match Sys.getenv_opt "COQHAMMER_LIFT_STATS" with
  | Some dir when dir <> "" -> dir
  | _ -> ""

let enabled () = out_dir <> ""

let counters : (string, int) Hashtbl.t = Hashtbl.create 64

(* Counters other modules own.  Registering a source rather than pushing values
   keeps this module free of dependencies on the modules it reports on, which
   is what lets it sit below them. *)
let sources : (unit -> (string * int) list) list ref = ref []

let add name n =
  if enabled () then
    let old = try Hashtbl.find counters name with Not_found -> 0 in
    Hashtbl.replace counters name (old + n)

let count name = add name 1

let add_source f =
  if enabled () then
    sources := f :: !sources

let collect () =
  let acc = Hashtbl.fold (fun name n acc -> (name, n) :: acc) counters [] in
  let acc =
    List.fold_left (fun acc source -> source () @ acc) acc !sources
  in
  List.sort (fun (x, _) (y, _) -> String.compare x y) acc

let dump () =
  if enabled () then
    try
      let fname = Filename.concat out_dir ("lift-stats-" ^ string_of_int (Unix.getpid ()) ^ ".txt") in
      let oc = open_out fname in
      Fun.protect ~finally:(fun () -> close_out_noerr oc)
        begin fun () ->
          List.iter (fun (name, n) -> output_string oc (name ^ "=" ^ string_of_int n ^ "\n")) (collect ())
        end
    with _ ->
      (* A diagnostic that aborts the translation it measures is worse than no
         diagnostic; an unwritable directory is the user's problem to notice in
         the empty aggregate. *)
      ()

let () = if enabled () then at_exit dump
