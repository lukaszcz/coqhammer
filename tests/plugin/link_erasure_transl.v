(* Focused translation regression for link equations across erased binders.

   A lifted symbol names a Coq term, so when one lift's term is a syntactic
   instance of another's the translator relates them by a [$_link_] equation.
   Instance matching is syntactic on the *unerased* term, but how many
   arguments a lift's symbol takes is decided after erasure: a proof binder
   carries no term-level argument.  A schema whose lambda binder has a
   canonical variable as its type matches anything, including an instance whose
   binder is a proof -- and then the schema's binder survives translation while
   the instance's does not, so the two symbols are applied at different
   arities.

   [sch] and [inst] below are exactly that pair.  The schema lifts
   [fun _ : Z => c] with [Z] and [c] canonical, so its symbol takes its two
   context arguments and the surviving binder.  The instance lifts
   [fun _ : R => c] with [R : Prop], whose binder erases, so its symbol takes
   only its one context argument and the definition equation saturates there.
   A link between them would equate the instance applied to its context -- a
   value -- with the schema applied to two of its three arguments -- a function
   still awaiting one.  Together with the definition equations that yields
   [happ(f, x) = f] for every [f] and [x], collapsing application to a
   projection and making the problem prove anything.

   Pinned here: no link equation is emitted for such a pair.  The check is that
   the translation of [inst] contains no [$_link_] axiom at all, which is the
   whole property for this file -- these two lifts are the only candidates in
   it, and the erasure profiles are what must keep them apart. *)

From Hammer Require Import Hammer.

Parameter G : forall Z : Type, (Z -> nat) -> nat.
Parameter R : Prop.

(* The schema: the lambda's binder type is the canonical variable [Z]. *)
Definition sch (Z : Type) (c : nat) : nat := G Z (fun _ : Z => c).

(* The instance: [Z := R] with [R : Prop], so this lambda's binder is a proof
   and erases.  The schema is translated first, so it is registered by the time
   the instance looks for a partner. *)
Definition inst (c : nat) : nat := G R (fun _ : R => c).

Hammer_transl "sch".
Hammer_transl "inst".
