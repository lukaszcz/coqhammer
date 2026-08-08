From Hammer Require Import Hammer.

Hammer_version.
Hammer_objects.

Section Bug01.

Variable P R : nat -> Prop.
Variable Q : nat -> nat -> Prop.

Axiom R_implies_P : forall x,
  R x ->
  P x.

Axiom P_Q_trans : forall x y,
  P x ->
  Q x y ->
  P y.

Lemma bug01 : R 0 -> Q 0 1 -> P 1.
Proof.
  hammer.
Qed.

End Bug01.
