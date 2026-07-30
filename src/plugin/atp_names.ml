open Hammer_lib

let is_alpha = function 'A'..'Z'|'a'..'z'|'_' -> true | _ -> false

let is_good_dep s = String.length s > 0 && is_alpha (String.get s 0) && not (Hhlib.string_begins_with s "_HAMMER_")

let remove_duplicates = Hhlib.sort_uniq Stdlib.compare

let get_deps lst = List.filter is_good_dep lst

let strip_dollar_suffix s =
  try
    let i = String.index s '$' in
    if i > 0 then String.sub s 0 i else s
  with Not_found -> s

let case_name_subject s =
  let rec peel s =
    if Hhlib.string_begins_with s "$_case_" then
      peel (String.sub s 7 (String.length s - 7))
    else
      s
  in
  let s = peel s in
  try
    let i = String.index s '$' in
    if i > 0 then String.sub s 0 i else "$none"
  with Not_found -> "$none"

(* Keep the names carrying [prefix], strip it, and recover the constant behind
   each one with [subject]. *)
let get_prefixed prefix subject lst =
  let n = String.length prefix in
  List.filter is_good_dep
    (List.map (fun s -> subject (String.sub s n (String.length s - n)))
       (List.filter (fun s -> Hhlib.string_begins_with s prefix) lst))

let get_defs lst =
  remove_duplicates (get_prefixed "$_def_" strip_dollar_suffix lst)

let get_typings lst =
  remove_duplicates (get_prefixed "$_typeof_" strip_dollar_suffix lst)

let get_cases lst =
  remove_duplicates (get_prefixed "$_case_" case_name_subject lst)

let get_inversions lst = get_prefixed "$_inversion_" (fun s -> s) lst

let get_injections lst = get_prefixed "$_inj_" (fun s -> s) lst

let get_discrims lst =
  List.filter (fun (x, y) -> is_good_dep x && is_good_dep y)
    (List.map
       begin fun s ->
         let s = String.sub s 10 (String.length s - 10) in
         let i = String.index s '$' in
         let s1 = String.sub s 0 i
         and s2 = String.sub s (i + 1) (String.length s - i - 1)
         in
         (s1, s2)
       end
       (List.filter (fun s -> Hhlib.string_begins_with s "$_discrim_") lst))
