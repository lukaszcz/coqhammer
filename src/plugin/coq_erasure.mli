(* Classification of inductive instances for proof/content erasure. *)

open Coqterms

(** Classification of an instantiated inductive type [I params].  The
    classification is used by the extraction-factored translation to decide which
    constructor arguments are computationally informative and which are erased
    proofs.  The classifier itself only analyses existing definitions; it emits no
    axioms and has no translation side effects. *)
type ind_class =
  | CEmpty
      (** No inhabitants are represented in the extracted program.  This covers
          ordinary empty inductives such as [False] (and future indexed-empty
          instances when the occurrence analysis can prove that no constructor
          matches). *)
  | CPropSingleton
      (** A [Prop]-sorted inductive satisfying CIC's singleton-elimination
          criterion: one constructor and all non-parameter constructor arguments
          are propositional.  Matches on such proofs may be erased to the unique
          branch.  Existentials such as [ex] are deliberately not classified this
          way because their witness is informative. *)
  | CSubset of {
      carrier_idx : int;
      (** Zero-based position, among non-parameter constructor arguments, of the
          unique informative carrier argument that remains after erasure. *)
      carrier_name : string;
      (** Binder name of the informative carrier in the instantiated constructor
          telescope.  Payload types may mention this name and guard expansion
          substitutes the guarded term for it before proposition translation. *)
      prop_args : (string * coqterm) list;
      (** Propositional payload fields dropped by program extraction.  The types
          are instantiated with the actual inductive parameters and may mention
          the carrier variable. *)
    }
      (** A [Set]/[Type]-sorted singleton with exactly one informative
          constructor argument and at least one propositional payload argument,
          e.g. [sig] or [sig2] and per-instance cases such as [prod A P] when
          [P : Prop].  Side conditions: the inductive must be non-indexed, the
          carrier type must not mention the inductive itself (Letouzey's
          non-recursive-carrier condition), and a purely informative one-field
          wrapper is kept [CRegular] instead of being collapsed. *)
  | CEnum of (string * coqterm list) list
      (** A non-indexed inductive whose constructors have only propositional
          non-parameter arguments after instantiation.  Extracted values are
          constructor tags; the listed payload formulas are the specifications
          associated with each tag (for example [sumbool A B]).  Indexed enums
          such as [reflect] stay [CRegular] until index constraints are represented
          in the shallow guard. *)
  | CRegular
      (** No erasure-specific simplification is justified.  The existing
          constructor, inversion, and typing translation remains the sound
          fallback. *)

val clear : unit -> unit
(** Clear the classification memo table. *)

val classify : coqcontext -> string -> coqterm list -> ind_class
(** [classify ctx indname params] classifies the inductive instance
    [indname params] in context [ctx].  Constructor telescopes are instantiated
    with [params], then each non-parameter argument is tested with
    [Coq_typing.check_prop].  Unknown or unsupported shapes conservatively return
    [CRegular]. *)

val classify_decl : string -> ind_class option
(** Declaration-level classification when the result is independent of a
    particular parameter instance.  This is useful for optional declaration-level
    skips: [False], [and], [eq], [Acc], [sig], [sig2], ... return their stable
    class, whereas sort-ambiguous families such as [prod], [sum], and [sigT]
    return [None] because their class depends on the actual parameters. *)

val has_erasable_content : coqcontext -> coqterm -> bool
(** [has_erasable_content ctx ty] scans [ty] for an inductive instance whose
    classification is [CEmpty], [CPropSingleton], [CSubset], or [CEnum].  The
    scan respects binders by extending [ctx]. *)
