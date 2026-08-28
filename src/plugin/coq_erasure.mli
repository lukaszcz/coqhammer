(* Classification of inductive instances for proof/content erasure. *)

open Coqterms

(** Classification of an instantiated inductive type [I params].  The
    classification is used by the extraction-factored translation to decide which
    constructor arguments are computationally informative and which are erased
    proofs.  The classifier itself only analyses existing definitions; it emits no
    axioms and has no translation side effects. *)
type index_eqs = (int * coqterm) list
(** Residual constructor equations, pairing a zero-based index position with
    its forded constructor pattern. *)

type index_formals = (string * coqterm) list
(** The declared index telescope, instantiated with occurrence parameters. *)

type enum_constructor = {
  enum_name : string;
  (** Constructor tag. *)
  enum_args : (string * coqterm) list;
  (** The instantiated, non-parameter constructor telescope in declaration order.
      Types have the solved arguments already substituted away, and provide the
      names needed to erase proof arguments when constructing the tag at an
      occurrence. *)
  enum_payloads : (string * coqterm) list;
  (** Propositional constructor arguments and their payload formulas. *)
  enum_solved : (string * int) list;
  (** Constructor argument names solved by their zero-based index position. *)
  enum_index_eqs : index_eqs;
  (** Residual equations of this constructor's forded form. *)
}
(** Forded metadata for one enumerated constructor. *)

type enum_data = {
  enum_constructors : enum_constructor list;
  (** Constructor entries in declaration order. *)
  enum_index_formals : index_formals;
  (** Common formals used by every constructor's payloads and residual patterns. *)
}
(** Forded metadata shared by an enumerated inductive instance. *)

type ind_class =
  | CEmpty
      (** No inhabitants are represented in the extracted program, as for
          ordinary empty inductives such as [False]. *)
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
      subset_args : (string * coqterm) list;
      (** The complete instantiated, non-parameter constructor telescope in
          declaration order.  Its types have the solved arguments already
          substituted away; consumers must use this retained telescope instead
          of destructing the constructor again, which would produce unrelated
          fresh binder names. *)
      prop_args : (string * coqterm) list;
      (** Propositional payload fields dropped by program extraction.  The types
          are instantiated with the actual inductive parameters and may mention
          the carrier variable. *)
      solved : (string * int) list;
      (** Constructor argument names solved by their zero-based index position. *)
      index_eqs : index_eqs;
      (** Residual equations of the constructor's forded form. *)
      index_formals : index_formals;
      (** Formals used by payloads and residual index patterns. *)
    }
      (** A [Set]/[Type]-sorted singleton with exactly one informative
          constructor argument and at least one propositional payload argument,
          e.g. [sig] or [sig2] and per-instance cases such as [prod A P] when
          [P : Prop].  Side conditions: the carrier type must not lead back to
          the inductive through another constructor telescope (Letouzey's
          non-recursive-carrier condition), and a purely informative one-field
          wrapper is kept [CRegular] instead of being collapsed. *)
  | CEnum of enum_data
      (** An inductive whose constructors have no residual informative arguments
          after instantiation.  Extracted values are constructor tags; the record
          retains the complete forded constructor metadata and the common index
          formals needed to instantiate tags, payloads, and equations at a
          saturated occurrence. *)
  | CRegular
      (** No erasure-specific simplification is justified.  The existing
          constructor, inversion, and typing translation remains the sound
          fallback. *)

val instantiate : index_formals -> coqterm list -> coqterm -> coqterm
(** [instantiate formals indices tm] substitutes the occurrence [indices]
    pointwise for the declared index [formals] in [tm].  The arities must agree. *)

val constructor_index_data :
  coqterm list -> int -> string -> coqterm list * (string * coqterm) list
(** [constructor_index_data params params_num cname] atomically returns the
    result-index patterns and instantiated non-parameter constructor telescope
    of [cname].  Both components come from the same [destruct_type_app] call, so
    their globally refreshed constructor binders correspond.  Callers needing
    both must use this helper rather than destructing the constructor separately.
    For the lowered equality target [Equal (a, b)], the patterns are [[b]]. *)

val index_formals_of : index_formals -> coqterm list -> int -> index_formals
(** [index_formals_of type_args params params_num] is the index suffix of an
    inductive's declared telescope [type_args], instantiated at the occurrence
    [params].  The destructed telescope is taken as an argument rather than the
    arity itself: [Coq_typing.get_type_args] refreshes every binder, so a
    caller that already destructed the arity must pass its own result instead
    of provoking a second, differently named one. *)

val informative_index_mask : coqcontext -> index_formals -> bool list
(** [informative_index_mask ctx index_formals] is the informative/propositional
    verdict of every position of an index telescope, decided left to right in
    the extended context.  Kept fording patterns, emitted index equalities and
    rigid-clash branch pruning all key off the same positions, so they must all
    read this one mask. *)

val saturated_occurrence : coqterm -> (string * coqterm list * coqterm list) option
(** [saturated_occurrence ty] head-normalizes [ty] and, when the result is an
    exactly saturated application of an inductive, returns that inductive's
    name, its parameters and its indices.  This is the one definition of an
    exactly saturated occurrence: the guard path and the case path must
    recognize the same occurrences, or a family would receive index equations
    in its guards without the matching branch pruning.  The normalization is
    the budgeted head reduction of [opt_whnf_budget], which exposes an
    inductive head without risking the type-level unfolding blow-up. *)

val occurrence_indices : string -> coqterm -> coqterm list option
(** [occurrence_indices indname ty] recovers the indices of [ty] as a
    [saturated_occurrence] of [indname].  An inductive declaring no index is exempt from that validation
    and always yields [Some []]: [Coq_convert] lowers the logical inductives to
    the FOL formers, so a scrutinee typed by one of them is no longer an
    application of the inductive in any syntactic sense, and it has no index to
    recover either way.  For the exact inductive registered as [core.eq.type],
    the lowered representation [Equal (a, b)] returns [Some [b]]. *)

val clear : unit -> unit
(** Clear the classification memo table. *)

val unford_telescope :
  index_formals -> (string * int) list -> (string * coqterm) list ->
  (string * coqterm) list
(** [unford_telescope index_formals solved args] restores the ordinary
    constructor telescope from a retained one.  [subset_args] and [enum_args]
    refer to every solved argument through the index formal that fords it,
    which only a consumer holding the occurrence's indices can instantiate; a
    consumer holding the constructor's own arguments instead -- a constructor
    application rather than a typing occurrence -- substitutes each such formal
    back to the argument it stands for. *)

val classify : coqcontext -> string -> coqterm list -> ind_class
(** [classify ctx indname params] classifies the inductive instance
    [indname params] in context [ctx].  Constructor telescopes are instantiated
    with [params], then each non-parameter argument is tested with
    [Coq_typing.check_prop].  Unknown or unsupported shapes conservatively return
    [CRegular]. *)

val classify_decl : string -> ind_class option
(** Declaration-level classification when the result is independent of a
    particular parameter instance.  This is useful for optional declaration-level
    skips.  Parameterized declarations whose constructor fields mention their
    parameters return [None], because later parameter instantiations may change
    the proof/content classification. *)

val has_erasable_content : coqcontext -> coqterm -> bool
(** [has_erasable_content ctx ty] scans [ty] for an inductive instance whose
    classification is [CEmpty], [CPropSingleton], [CSubset], or [CEnum].  The
    scan respects binders by extending [ctx]. *)
