From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.
From Hammer Require Import Reflect.

Lemma ssrnat_eqn_eq : forall n m, eqn n m <-> n = m.
Proof.
  split; move => /eqnP; auto.
Qed.

Lemma ssrnat_leq_le : forall n m, leq n m <-> le n m.
Proof.
  split; move => /leP; auto.
Qed.

Lemma nat_eqop_eq : forall n m : nat, n == m <-> n = m.
Proof.
  split; move => /eqP; auto.
Qed.

Hint Rewrite -> ssrnat_eqn_eq : brefl_hints.
Hint Rewrite -> ssrnat_leq_le : brefl_hints.
Hint Rewrite -> nat_eqop_eq : brefl_hints.

(* TODO: Do we really want this? *)
Lemma ssrnat_multE : forall x y, Nat.mul x y = x * y.
Proof.
  rewrite multE.
  reflexivity.
Qed.

Lemma ssrnat_plusE : forall x y, Nat.add x y = x + y.
Proof.
  rewrite plusE.
  reflexivity.
Qed.

Lemma ssrnat_minusE : forall x y, Nat.sub x y = x - y.
Proof.
  rewrite minusE.
  reflexivity.
Qed.

Hint Rewrite <- ssrnat_multE : bsimpl_hints.
Hint Rewrite <- ssrnat_plusE : bsimpl_hints.
Hint Rewrite <- ssrnat_minusE : bsimpl_hints.
