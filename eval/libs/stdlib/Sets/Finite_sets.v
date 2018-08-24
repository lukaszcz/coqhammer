From Hammer Require Import Hammer.



























Require Import Ensembles.

Section Ensembles_finis.
Variable U : Type.

Inductive Finite : Ensemble U -> Prop :=
| Empty_is_finite : Finite (Empty_set U)
| Union_is_finite :
forall A:Ensemble U,
Finite A -> forall x:U, ~ In U A x -> Finite (Add U A x).

Inductive cardinal : Ensemble U -> nat -> Prop :=
| card_empty : cardinal (Empty_set U) 0
| card_add :
forall (A:Ensemble U) (n:nat),
cardinal A n -> forall x:U, ~ In U A x -> cardinal (Add U A x) (S n).

End Ensembles_finis.

Hint Resolve Empty_is_finite Union_is_finite: sets.
Hint Resolve card_empty card_add: sets.

Require Import Constructive_sets.

Section Ensembles_finis_facts.
Variable U : Type.

Lemma cardinal_invert :
forall (X:Ensemble U) (p:nat),
cardinal U X p ->
match p with
| O => X = Empty_set U
| S n =>
exists A : _,
(exists x : _, X = Add U A x /\ ~ In U A x /\ cardinal U A n)
end.
Proof. try hammer_hook "Finite_sets" "Finite_sets.cardinal_invert". Undo.  
induction 1; simpl; auto.
exists A; exists x; auto.
Qed.

Lemma cardinal_elim :
forall (X:Ensemble U) (p:nat),
cardinal U X p ->
match p with
| O => X = Empty_set U
| S n => Inhabited U X
end.
Proof. try hammer_hook "Finite_sets" "Finite_sets.cardinal_elim". Undo.  
intros X p C; elim C; simpl; trivial with sets.
Qed.

End Ensembles_finis_facts.
