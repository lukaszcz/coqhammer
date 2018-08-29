open Coqterms

type namesubst = (string (* new name *) * string (* old name *)) list

(* takes a context and term and returns them in canonical form, along
   with a list of free variable substitutions made. *)
val canonical : coqcontext -> coqterm -> coqcontext * coqterm * namesubst

(* a hash table for coqterms which hashes up to alpha-equivalence *)
type coqterms_hash = (coqcontext * coqterm, coqterm) Hashtbl.t

val create : unit -> coqterms_hash
val clear : coqterms_hash -> unit
val find_or_insert : coqterms_hash -> coqcontext -> coqterm -> (coqcontext -> coqterm -> coqterm) -> coqterm
