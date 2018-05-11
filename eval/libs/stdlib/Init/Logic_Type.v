From Hammer Require Import Hammer.











Set Implicit Arguments.

Require Import Datatypes.
Require Export Logic.



Definition notT (A:Type) := A -> False.



Section identity_is_a_congruence.

Variables A B : Type.
Variable f : A -> B.

Variables x y z : A.

Lemma identity_sym : identity x y -> identity y x.
Proof. try hammer_hook "Logic_Type" "Logic_Type.identity_sym".  
destruct 1; trivial.
Defined.

Lemma identity_trans : identity x y -> identity y z -> identity x z.
Proof. try hammer_hook "Logic_Type" "Logic_Type.identity_trans".  
destruct 2; trivial.
Defined.

Lemma identity_congr : identity x y -> identity (f x) (f y).
Proof. try hammer_hook "Logic_Type" "Logic_Type.identity_congr".  
destruct 1; trivial.
Defined.

Lemma not_identity_sym : notT (identity x y) -> notT (identity y x).
Proof. try hammer_hook "Logic_Type" "Logic_Type.not_identity_sym".  
red; intros H H'; apply H; destruct H'; trivial.
Qed.

End identity_is_a_congruence.

Definition identity_ind_r :
forall (A:Type) (a:A) (P:A -> Prop), P a -> forall y:A, identity y a -> P y.
intros A x P H y H0; case identity_sym with (1 := H0); trivial.
Defined.

Definition identity_rec_r :
forall (A:Type) (a:A) (P:A -> Set), P a -> forall y:A, identity y a -> P y.
intros A x P H y H0; case identity_sym with (1 := H0); trivial.
Defined.

Definition identity_rect_r :
forall (A:Type) (a:A) (P:A -> Type), P a -> forall y:A, identity y a -> P y.
intros A x P H y H0; case identity_sym with (1 := H0); trivial.
Defined.

Hint Immediate identity_sym not_identity_sym: core.

Notation refl_id := identity_refl (compat "8.3").
Notation sym_id := identity_sym (compat "8.3").
Notation trans_id := identity_trans (compat "8.3").
Notation sym_not_id := not_identity_sym (compat "8.3").
