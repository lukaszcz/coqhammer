From Hammer Require Import Hammer.

Hammer_version.
Hammer_objects.

Lemma lem_1 {A : Type} (P : A -> Prop) : forall x, P x -> P x.
Proof.
  hammer.
Qed.

Lemma lem_2 {A : Type} (P Q : A -> Prop) : forall x, P x \/ Q x -> Q x \/ P x.
Proof.
  hammer.
Qed.

Lemma lem_3 {A : Type} (P Q : A -> Prop) : forall x, (forall x, P x -> Q x) -> P x -> Q x.
Proof.
  hammer.
Qed.

Lemma mult_1 : forall m n k : nat, m * n + k = k + n * m.
Proof.
  hammer_features.
  hammer_transl.
  predict 16.
  hauto using (PeanoNat.Nat.mul_comm, PeanoNat.Nat.add_comm).
Qed.
