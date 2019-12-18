(* The program to fix "Require" statements in Coq source code *)

let remove_trailing_dot s =
  let len = String.length s in
  if len > 0 && String.get s (len - 1) = '.' then
    String.sub s 0 (len - 1)
  else
    s

let process_file fname =
  let rec pom ic oc =
    let rec hlp prefix lst =
      match lst with
      | file :: lst2 ->
         let from =
           if Sys.file_exists (file ^ ".v") then
             "From " ^ Sys.argv.(1) ^ " "
           else
             ""
         in
         output_string oc (from ^ prefix ^ file ^ ".\n");
         hlp prefix lst2
      | [] ->
         ()
    in
    let s = String.trim (input_line ic) in
    begin
      let words = Str.split (Str.regexp "[ ]+") (remove_trailing_dot s) in
      match words with
      | "Require" :: "Import" :: lst -> hlp "Require Import " lst
      | "Require" :: "Export" :: lst -> hlp "Require Export " lst
      | "Require" :: lst -> hlp "Require " lst
      | _ -> output_string oc (s ^ "\n")
    end;
    pom ic oc
  in
  let ofname = Filename.temp_file "fixreqs" ".v"
  in
  let ic = open_in fname
  and oc = open_out ofname
  in
  try
    pom ic oc
  with End_of_file ->
    close_in ic;
    close_out oc;
    ignore (Sys.command ("mv " ^ ofname ^ " " ^ fname))

let rec process_dir dir =
  let entries = Sys.readdir dir in
  Sys.chdir dir;
  Array.iter
    begin fun fname ->
      if Sys.is_directory fname then
        process_dir fname
      else if Filename.check_suffix fname ".v" then
        process_file fname
      else
        ()
    end
    entries;
  Sys.chdir ".."

;;

if Array.length Sys.argv <> 2 then
  prerr_endline "usage: fixreqs prefix"
else
  process_dir "."
