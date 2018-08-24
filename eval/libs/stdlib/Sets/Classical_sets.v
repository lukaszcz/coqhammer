From Hammer Require Import Hammer.



























Require Export Ensembles.
Require Export Constructive_sets.
Require Export Classical.

Section Ensembles_classical.
Variable U : Type.

Lemma not_included_empty_Inhabited :
forall A:Ensemble U, ~ Included U A (Empty_set U) -> Inhabited U A.
Proof. try hammer_hook "Classical_sets" "Classical_sets.not_included_empty_Inhabited". Undo.  
intros A NI.
elim (not_all_ex_not U (fun x:U => ~ In U A x)).
intros x H; apply Inhabited_intro with x.
apply NNPP; auto with sets.
red; intro.
apply NI; red.
intros x H'; elim (H x); trivial with sets.
Qed.

Lemma not_empty_Inhabited :
forall A:Ensemble U, A <> Empty_set U -> Inhabited U A.
Proof. try hammer_hook "Classical_sets" "Classical_sets.not_empty_Inhabited". Undo.  
intros; apply not_included_empty_Inhabited.
red; auto with sets.
Qed.

Lemma Inhabited_Setminus :
forall X Y:Ensemble U,
Included U X Y -> ~ Included U Y X -> Inhabited U (Setminus U Y X).
Proof. try hammer_hook "Classical_sets" "Classical_sets.Inhabited_Setminus". Undo.  
intros X Y I NI.
elim (not_all_ex_not U (fun x:U => In U Y x -> In U X x) NI).
intros x YX.
apply Inhabited_intro with x.
apply Setminus_intro.
apply not_imply_elim with (In U X x); trivial with sets.
auto with sets.
Qed.

Lemma Strict_super_set_contains_new_element :
forall X Y:Ensemble U,
Included U X Y -> X <> Y -> Inhabited U (Setminus U Y X).
Proof. try hammer_hook "Classical_sets" "Classical_sets.Strict_super_set_contains_new_element". Undo.  
auto 7 using Inhabited_Setminus with sets.
Qed.

Lemma Subtract_intro :
forall (A:Ensemble U) (x y:U), In U A y -> x <> y -> In U (Subtract U A x) y.
Proof. try hammer_hook "Classical_sets" "Classical_sets.Subtract_intro". Undo.  
unfold Subtract at 1; auto with sets.
Qed.
Hint Resolve Subtract_intro : sets.

Lemma Subtract_inv :
forall (A:Ensemble U) (x y:U), In U (Subtract U A x) y -> In U A y /\ x <> y.
Proof. try hammer_hook "Classical_sets" "Classical_sets.Subtract_inv". Undo.  
intros A x y H'; elim H'; auto with sets.
Qed.

Lemma Included_Strict_Included :
forall X Y:Ensemble U, Included U X Y -> Strict_Included U X Y \/ X = Y.
Proof. try hammer_hook "Classical_sets" "Classical_sets.Included_Strict_Included". Undo.  
intros X Y H'; try assumption.
elim (classic (X = Y)); auto with sets.
Qed.

Lemma Strict_Included_inv :
forall X Y:Ensemble U,
Strict_Included U X Y -> Included U X Y /\ Inhabited U (Setminus U Y X).
Proof. try hammer_hook "Classical_sets" "Classical_sets.Strict_Included_inv". Undo.  
intros X Y H'; red in H'.
split; [ tauto | idtac ].
elim H'; intros H'0 H'1; try exact H'1; clear H'.
apply Strict_super_set_contains_new_element; auto with sets.
Qed.

Lemma not_SIncl_empty :
forall X:Ensemble U, ~ Strict_Included U X (Empty_set U).
Proof. try hammer_hook "Classical_sets" "Classical_sets.not_SIncl_empty". Undo.  
intro X; red; intro H'; try exact H'.
lapply (Strict_Included_inv X (Empty_set U)); auto with sets.
intro H'0; elim H'0; intros H'1 H'2; elim H'2; clear H'0.
intros x H'0; elim H'0.
intro H'3; elim H'3.
Qed.

Lemma Complement_Complement :
forall A:Ensemble U, Complement U (Complement U A) = A.
Proof. try hammer_hook "Classical_sets" "Classical_sets.Complement_Complement". Undo.  
unfold Complement; intros; apply Extensionality_Ensembles;
auto with sets.
red; split; auto with sets.
red; intros; apply NNPP; auto with sets.
Qed.

End Ensembles_classical.

Hint Resolve Strict_super_set_contains_new_element Subtract_intro
not_SIncl_empty: sets.
