(* Focused translation regression for the canonical arrow former.

   A non-dependent product with a non-Prop domain is translated structurally,
   as [$_arrow(dom, cod)], instead of being lifted to a constant minted per
   occurrence shape.  This pins that the same former is used at an instance
   occurrence (a section variable [h : X -> Y]) and inside a quantified premise
   ([map_len]'s binder [g : X -> Y] under [forall X Y]), since the whole point
   of the canonicalization is that those two unify.  Dependent products and
   Prop-domain products keep the per-occurrence [$_type_N] lifting.

   The unfolding axiom for an arrow shape must stay a one-way implication:
   an equivalence is unsound over empty domains (commit 951862d), so the
   Makefile also checks that no [$_arrow_N] axiom is an equivalence. *)

From Hammer Require Import Hammer.
From Stdlib Require Import Lists.List.

Parameter A B : Type.
Parameter f : A -> B.

Parameter P : A -> Type.
Parameter dep : forall x : A, P x.

Parameter propdom : True -> A.

Parameter nested : A -> B -> A.

(* A long arrow telescope.  Each codomain is itself an arrow, so canonicalizing
   one canonicalizes the next; the translation of the subject must therefore be
   used once and not re-run, or the work doubles at every level and a telescope
   this deep never finishes.  The Makefile bounds this file's compilation. *)
Parameter deep :
  A -> A -> A -> A -> A -> A -> A -> A -> A -> A ->
  A -> A -> A -> A -> A -> A -> A -> A -> A -> A ->
  A -> A -> A -> A -> A -> A -> A -> A -> A -> A ->
  A -> A -> A -> A -> A -> A -> A -> A -> A -> A -> A.

Lemma map_len :
  forall (X Y : Type) (g : X -> Y) (l : list X), length (map g l) = length l.
Proof.
  induction l; simpl; auto.
Qed.

(* Instance-position arrow: one canonical former, no lifted name. *)
Hammer_transl "f".

(* The same former under quantifiers, applied to the bound type variables. *)
Hammer_transl "map_len".

(* Not eligible: dependent product, and product with a Prop domain. *)
Hammer_transl "dep".
Hammer_transl "propdom".

(* Nested arrows canonicalize recursively. *)
Hammer_transl "nested".
Hammer_transl "deep".

Section ArrowGoal.

Variables (X Y : Type) (h : X -> Y).

Goal forall l, length (map h l) = length l.
  Hammer_dump "arrow_transl.p".
Abort.

End ArrowGoal.
