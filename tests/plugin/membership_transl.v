(* Focused translation regression for the membership half of a typing axiom.

   A constant whose type carries erasure-relevant content -- an enum codomain
   like [bool], a subset like [{n : nat | n = 0}] -- has its [$_typeof_] axiom
   emitted as the applied unfolding of that content, so payloads are expanded
   per occurrence instead of being lifted.  The unfolding says how the constant
   behaves once applied, but on its own it never says that the constant
   inhabits its own type.  That fact is not decoration: a premise quantifying
   over a function is guarded by exactly that membership, so [q_all] below can
   be instantiated at [f] only if [$HasType f ($_arrow elt bool)] is available.
   Pinned here: the unfolding and the membership are conjoined for a function
   into an enum and for one into a subset, and a function with no erasable
   content still gets the bare membership and nothing spurious beside it.

   The other half concerns which direction a type-unfolding axiom is stated in.
   For a *product* it must stay a one-way implication: over an empty domain the
   extensional unfolding holds vacuously of every object, so an equivalence
   would let a non-function inhabit an arrow type (commit 951862d).  Both the
   [$_arrow_N] axioms and the definition axiom of the transparent product
   [endo] are checked to be implications.  A non-product unfolding is a
   different statement -- the body of a transparent type definition, where the
   two memberships are convertible by delta and there is no domain to be empty
   -- so [elt]'s definition axiom is an equivalence, and instantiating a premise
   stated at [A] on a term typed at [elt] needs that reverse direction. *)

From Hammer Require Import Hammer.

Parameter A : Type.

(* Transparent definition of a leaf type: memberships at [elt] and at [A]
   unfold into each other. *)
Definition elt := A.

(* Erasable content in the codomain, so these two take the applied-unfolding
   branch: an enum, then a subset. *)
Parameter f : elt -> bool.
Parameter r : elt -> {n : nat | n = 0}.

(* The same shape with nothing erasable: plain membership, no unfolding. *)
Parameter g : elt -> A.

(* Transparent definition of a product, and a constant declared at it, so the
   membership is stated at the defined name and the definition axiom is what
   would unfold it. *)
Definition endo := elt -> elt.
Parameter e : endo.

(* The consumer side: this premise is usable at [f] only through the membership
   conjunct of [f]'s typing axiom. *)
Parameter Q : (elt -> bool) -> Prop.
Axiom q_all : forall k : elt -> bool, Q k.

Hammer_transl "elt".
Hammer_transl "f".
Hammer_transl "r".
Hammer_transl "g".
Hammer_transl "endo".
Hammer_transl "e".
Hammer_transl "q_all".
