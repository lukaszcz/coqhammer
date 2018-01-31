
(* Escape characters not accepted by the TPTP format. *)
let escape_to_hex s =
  let n = ref 0 in
  for i = 0 to String.length s - 1 do
    n := !n + (match String.unsafe_get s i with
     'a'|'b'|'c'|'d'|'e'|'f'|'g'|'h'|'i'|'j'|'k'|'l'|'m'|'n'|'o'|'p'|'q'|'r'|'s'|'t'|'u'|'v'|'w'|'x'|'y'|'z'
    |'A'|'B'|'C'|'D'|'E'|'F'|'G'|'H'|'I'|'J'|'K'|'L'|'M'|'N'|'O'|'P'|'Q'|'R'|'S'|'T'|'U'|'V'|'W'|'X'|'Y'|'Z'
    |'0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9' -> 1
    |'_' -> 2 | _ -> 3)
  done;
  if !n = String.length s then s else begin
    let s' = String.create !n in
    n := 0;
    for i = 0 to String.length s - 1 do begin
      match String.unsafe_get s i with
      ('a'|'b'|'c'|'d'|'e'|'f'|'g'|'h'|'i'|'j'|'k'|'l'|'m'|'n'|'o'|'p'|'q'|'r'|'s'|'t'|'u'|'v'|'w'|'x'|'y'|'z'
      |'A'|'B'|'C'|'D'|'E'|'F'|'G'|'H'|'I'|'J'|'K'|'L'|'M'|'N'|'O'|'P'|'Q'|'R'|'S'|'T'|'U'|'V'|'W'|'X'|'Y'|'Z'
      |'0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9' as c) -> String.unsafe_set s' !n c
      | '_' -> String.unsafe_set s' !n '_'; incr n; String.unsafe_set s' !n '_'
      | c -> let c = Char.code c in
             String.unsafe_set s' !n '_'; incr n;
             String.unsafe_set s' !n (Printf.sprintf "%x" (c / 16)).[0]; incr n;
             String.unsafe_set s' !n (Printf.sprintf "%x" (c mod 16)).[0]
    end; incr n; done;
    s'
  end
;;

let is_primed name =
  name.[0] = '\'' && name.[String.length name - 1] = '\''
let add_prime s = 
  if is_primed s then s else "\'" ^ s ^ "\'"

let remove_prime name =
  try 
  if is_primed name
  then 
    let n = String.length name in
    Str.last_chars (Str.first_chars name (n - 1)) (n- 2) 
  else name
  with _ -> name

let is_lowercase c =
  let i = Char.code c in i >= Char.code 'a' && i <= Char.code 'z'
let is_uppercase c =
  let i = Char.code c in i >= Char.code 'A' && i <= Char.code 'Z'
let is_letter c =
  (is_lowercase c) or (is_uppercase c)

(* 
   This should not modify the names of the original theorems 
   since these symbols are already escaped in the first export.
   A problem may arise if a hollight name
   contains one of the escape sequence which does not happen 
   since we use a limited number of hollight theorems for our translation
   '$or' is escaped to '|dollar|or'
*)

let escape_special s =
  let s1 = Str.global_replace (Str.regexp_string "\\") "|bslash|" s in
  let s2 = Str.global_replace (Str.regexp_string "/") "|slash|" s1 in
  let s3 = Str.global_replace (Str.regexp_string "$") "|dollar|" s2 in
  s3

let escape_special_thm s =
  Str.global_replace (Str.regexp_string "'") "\\'"
    (Str.global_replace (Str.regexp_string "\\") "\\\\" s)

let escape_all s = add_prime (escape_special (remove_prime s))

let escape_var s = "V" ^ escape_to_hex s
let escape_const s = escape_all s
let escape_thm s = escape_all s
