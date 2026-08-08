open Coqterms

type namesubst = (string (* new name *) * string (* old name *)) list

(* takes a context and term and returns them in canonical form, along
   with a list of free variable substitutions made. *)
val canonical : coqcontext -> coqterm -> coqcontext * coqterm * namesubst

(* [match_instance cctx_s ctm_s cctx_i ctm_i] treats the canonical variables
   bound by [cctx_s] as pattern variables and returns their images, in the
   canonical order [v_CANONICAL_0 .. v_CANONICAL_(k-1)] with
   [k = List.length cctx_s], such that substituting them into [ctm_s] yields
   [ctm_i] syntactically.  The match is capture-free: every image is
   well-scoped in [cctx_i], which is enforced rather than assumed -- a match
   whose images would not be is reported as no match, so a caller may close the
   link equation over [cctx_i] without checking.  A schema term which is a bare
   pattern variable is rejected. *)
val match_instance : coqcontext -> coqterm -> coqcontext -> coqterm ->
  coqterm list option

(* A link between a newly minted lift and an already registered one.  With
   [ll_new_is_schema = false] the partner is the schema: [ll_subst] has length
   [List.length ll_ctx] and its terms live in the new canonical context, so the
   caller may emit, closed over the new context's variables,
   [new_symbol(new_vars) = ll_name(ll_subst)].  With [ll_new_is_schema = true]
   the new lift is the schema: [ll_subst] has the length of the new context and
   its terms live in [ll_ctx], so the caller may emit, closed over [ll_ctx]'s
   variables, [ll_name(vars of ll_ctx) = new_symbol(ll_subst)].

   [ll_tm] is the partner's canonical term.  Matching is syntactic on unerased
   [coqterm]s while the translated arity of a lift depends on which of its
   binders erase, so the caller must compare the two terms' binder erasure
   before emitting anything -- see [add_link_axiom]. *)
type lift_link = {
  ll_name : string;
  ll_ctx : coqcontext;
  ll_tm : coqterm;
  ll_new_is_schema : bool;
  ll_subst : coqterm list;
}

(* [register_lift kind symbol cctx ctm] records a minted lift.  Lifts
   registered under different kinds ("type", "lam", "case", "fix") are never
   linked. *)
val register_lift : string -> string -> coqcontext -> coqterm -> unit

(* [find_lift_link kind cctx ctm] looks for a registered lift of the same kind
   related to [(cctx, ctm)] by instantiation, preferring the direction in which
   the partner is the more general term.  At most one link is returned. *)
val find_lift_link : string -> coqcontext -> coqterm -> lift_link option

(* empties every registry; does not touch the counters *)
val clear_lifts : unit -> unit

type lift_counters = {
  lc_registered : int;      (* register_lift calls *)
  lc_queried : int;         (* find_lift_link calls *)
  lc_linked_fwd : int;      (* links found with the partner as schema *)
  lc_linked_rev : int;      (* links found with the new lift as schema *)
  lc_attempts : int;        (* candidate match attempts *)
  lc_filtered : int;        (* examined entries rejected by the constant/size pre-filters *)
  lc_truncated : int;       (* find_lift_link calls that stopped at a cap,
                               leaving entries unexamined *)
  lc_noconst_dropped : int; (* entries dropped from the capped constant-free list *)
}

val counters : string -> lift_counters
val all_counters : unit -> (string * lift_counters) list
val reset_counters : unit -> unit

type 'a lift_fun = (coqterm -> coqterm) -> ('a -> 'a)

(* a hash table for coqterms which hashes up to alpha-equivalence; 'a
   = f coqterm for some functor f; the second element of the pair is
   the functor lifting function (fmap) *)
type 'a coqterms_hash = (string * coqcontext * coqterm, 'a) Hashtbl.t * ('a lift_fun)

val create : 'a lift_fun -> 'a coqterms_hash
(* clears the table and, with it, the lift registry *)
val clear : 'a coqterms_hash -> unit
(* find_or_insert h ctx tm mk *)
val find_or_insert : 'a coqterms_hash -> coqcontext -> coqterm ->
  (coqcontext -> coqterm -> 'a) (* function creating new value, called if tm not found *) ->
  'a
(* [find_or_insert_keyed key ...] additionally separates otherwise
   alpha-equivalent entries by an occurrence-identity key. *)
val find_or_insert_keyed : string -> 'a coqterms_hash -> coqcontext -> coqterm ->
  (coqcontext -> coqterm -> 'a) ->
  'a
