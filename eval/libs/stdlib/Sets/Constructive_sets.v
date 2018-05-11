From Hammer Require Import Hammer.



























Require Export Ensembles.

Section Ensembles_facts.
Variable U : Type.

Lemma Extension : forall B C:Ensemble U, B = C -> Same_set U B C.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Extension".  
intros B C H'; rewrite H'; auto with sets.
Qed.

Lemma Noone_in_empty : forall x:U, ~ In U (Empty_set U) x.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Noone_in_empty".  
red; destruct 1.
Qed.

Lemma Included_Empty : forall A:Ensemble U, Included U (Empty_set U) A.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Included_Empty".  
intro; red.
intros x H; elim (Noone_in_empty x); auto with sets.
Qed.

Lemma Add_intro1 :
forall (A:Ensemble U) (x y:U), In U A y -> In U (Add U A x) y.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Add_intro1".  
unfold Add at 1; auto with sets.
Qed.

Lemma Add_intro2 : forall (A:Ensemble U) (x:U), In U (Add U A x) x.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Add_intro2".  
unfold Add at 1; auto with sets.
Qed.

Lemma Inhabited_add : forall (A:Ensemble U) (x:U), Inhabited U (Add U A x).
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Inhabited_add".  
intros A x.
apply Inhabited_intro with (x := x); auto using Add_intro2 with sets.
Qed.

Lemma Inhabited_not_empty :
forall X:Ensemble U, Inhabited U X -> X <> Empty_set U.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Inhabited_not_empty".  
intros X H'; elim H'.
intros x H'0; red; intro H'1.
absurd (In U X x); auto with sets.
rewrite H'1; auto using Noone_in_empty with sets.
Qed.

Lemma Add_not_Empty : forall (A:Ensemble U) (x:U), Add U A x <> Empty_set U.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Add_not_Empty".  
intros A x; apply Inhabited_not_empty; apply Inhabited_add.
Qed.

Lemma not_Empty_Add : forall (A:Ensemble U) (x:U), Empty_set U <> Add U A x.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.not_Empty_Add".  
intros; red; intro H; generalize (Add_not_Empty A x); auto with sets.
Qed.

Lemma Singleton_inv : forall x y:U, In U (Singleton U x) y -> x = y.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Singleton_inv".  
intros x y H'; elim H'; trivial with sets.
Qed.

Lemma Singleton_intro : forall x y:U, x = y -> In U (Singleton U x) y.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Singleton_intro".  
intros x y H'; rewrite H'; trivial with sets.
Qed.

Lemma Union_inv :
forall (B C:Ensemble U) (x:U), In U (Union U B C) x -> In U B x \/ In U C x.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Union_inv".  
intros B C x H'; elim H'; auto with sets.
Qed.

Lemma Add_inv :
forall (A:Ensemble U) (x y:U), In U (Add U A x) y -> In U A y \/ x = y.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Add_inv".  
intros A x y H'; induction H'.
left; assumption.
right; apply Singleton_inv; assumption.
Qed.

Lemma Intersection_inv :
forall (B C:Ensemble U) (x:U),
In U (Intersection U B C) x -> In U B x /\ In U C x.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Intersection_inv".  
intros B C x H'; elim H'; auto with sets.
Qed.

Lemma Couple_inv : forall x y z:U, In U (Couple U x y) z -> z = x \/ z = y.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Couple_inv".  
intros x y z H'; elim H'; auto with sets.
Qed.

Lemma Setminus_intro :
forall (A B:Ensemble U) (x:U),
In U A x -> ~ In U B x -> In U (Setminus U A B) x.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Setminus_intro".  
unfold Setminus at 1; red; auto with sets.
Qed.

Lemma Strict_Included_intro :
forall X Y:Ensemble U, Included U X Y /\ X <> Y -> Strict_Included U X Y.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Strict_Included_intro".  
auto with sets.
Qed.

Lemma Strict_Included_strict : forall X:Ensemble U, ~ Strict_Included U X X.
Proof. try hammer_hook "Constructive_sets" "Constructive_sets.Strict_Included_strict".  
intro X; red; intro H'; elim H'.
intros H'0 H'1; elim H'1; auto with sets.
Qed.

End Ensembles_facts.

Hint Resolve Singleton_inv Singleton_intro Add_intro1 Add_intro2
Intersection_inv Couple_inv Setminus_intro Strict_Included_intro
Strict_Included_strict Noone_in_empty Inhabited_not_empty Add_not_Empty
not_Empty_Add Inhabited_add Included_Empty: sets.
