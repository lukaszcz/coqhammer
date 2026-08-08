(* Sanity check for the FOL translation: the core logical constants must be
   translated to genuine FOL connectives, quantifiers and equality, not left
   as uninterpreted symbols. The Makefile greps the output of Hammer_transl
   for leftover "Init.Logic." names. *)

From Hammer Require Import Hammer.

Lemma lem_transl_sanity :
  forall (P Q : nat -> Prop),
    (forall n, P n <-> Q n) ->
    (exists n, ~ P n /\ (n = 0 \/ True)) ->
    ~ (forall n, Q n) \/ ~ False.
Proof. hammer. Qed.

Hammer_transl "lem_transl_sanity".
