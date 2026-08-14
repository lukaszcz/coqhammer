type hhterm =
   Id of string (* may be a constant or variable *)
 | Comb of hhterm * hhterm

type hhterm_thunk = {
  ht_make : unit -> hhterm;
  mutable ht_value : hhterm option;
}

type hhdef =
  hhterm (* "name" term; use get_hhdef_name to extract the name string *) *
    bool (* is opaque? *) *
    hhterm (* kind; Comb(Id "$Sort", Id "$Prop") if type is a proposition *) *
    hhterm_thunk (* type *) *
    hhterm_thunk (* term: definiens (value or proof term) *)

let delay_hhterm make = { ht_make = make; ht_value = None }

let force_hhterm thunk =
  match thunk.ht_value with
  | Some value -> value
  | None ->
     let value = thunk.ht_make () in
     thunk.ht_value <- Some value;
     value

let release_hhdef ((_, _, _, ty, term) : hhdef) =
  ty.ht_value <- None;
  term.ht_value <- None

let get_hhterm_name (c : hhterm) : string =
  match c with
  | Comb(Comb(Id "$Construct", _), Id constrname) ->
    constrname
  | Comb(Id "$Const", Id name) ->
    name
  | Comb(Comb(Id "$Ind", Id indname), _) ->
    indname
  | Comb(Id "$Var", Id name) ->
    name
  | _ ->
    ""

let get_hhdef_name ((c, _, _, _, _) : hhdef) : string =
  get_hhterm_name c

let hhdef_is_opaque ((_, opaque, _, _, _) : hhdef) : bool =
  opaque

let rec hhterm_size (t : hhterm) : int =
  match t with
  | Id _ -> 1
  | Comb (x, y) -> 1 + hhterm_size x + hhterm_size y

(* A variable (a section variable or a local hypothesis) is not a
   global object: its name may denote something else in another
   context. *)
let hhdef_is_var ((c, _, _, _, _) : hhdef) : bool =
  match c with
  | Comb(Id "$Var", Id _) -> true
  | _ -> false

let rec string_of_hhterm t =
  match t with
  | Id(s) -> s
  | Comb(x, y) -> string_of_hhterm x ^ " @ (" ^ string_of_hhterm y ^ ")"
