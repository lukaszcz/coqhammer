From Hammer Require Import Hammer.









Require Export Coq.Classes.SetoidTactics.

Export Morphisms.ProperNotations.



Definition Setoid_Theory := @Equivalence.
Definition Build_Setoid_Theory := @Build_Equivalence.

Definition Seq_refl A Aeq (s : Setoid_Theory A Aeq) : forall x:A, Aeq x x.
Proof. try hammer_hook "Setoid" "Setoid.Seq_refl".  
unfold Setoid_Theory in s. intros ; reflexivity.
Defined.

Definition Seq_sym A Aeq (s : Setoid_Theory A Aeq) : forall x y:A, Aeq x y -> Aeq y x.
Proof. try hammer_hook "Setoid" "Setoid.Seq_sym".  
unfold Setoid_Theory in s. intros ; symmetry ; assumption.
Defined.

Definition Seq_trans A Aeq (s : Setoid_Theory A Aeq) : forall x y z:A, Aeq x y -> Aeq y z -> Aeq x z.
Proof. try hammer_hook "Setoid" "Setoid.Seq_trans".  
unfold Setoid_Theory in s. intros ; transitivity y ; assumption.
Defined.



Ltac trans_st x :=
idtac "trans_st on Setoid_Theory is OBSOLETE";
idtac "use transitivity on Equivalence instead";
match goal with
| H : Setoid_Theory _ ?eqA |- ?eqA _ _ =>
apply (Seq_trans _ _ H) with x; auto
end.

Ltac sym_st :=
idtac "sym_st on Setoid_Theory is OBSOLETE";
idtac "use symmetry on Equivalence instead";
match goal with
| H : Setoid_Theory _ ?eqA |- ?eqA _ _ =>
apply (Seq_sym _ _ H); auto
end.

Ltac refl_st :=
idtac "refl_st on Setoid_Theory is OBSOLETE";
idtac "use reflexivity on Equivalence instead";
match goal with
| H : Setoid_Theory _ ?eqA |- ?eqA _ _ =>
apply (Seq_refl _ _ H); auto
end.

Definition gen_st : forall A : Set, Setoid_Theory _ (@eq A).
Proof. try hammer_hook "Setoid" "Setoid.gen_st".  
constructor; congruence.
Qed.

