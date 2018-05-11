From Hammer Require Import Hammer.









Require Import Relations Setoid SetoidList List Multiset PermutSetoid Permutation Omega.

Set Implicit Arguments.



Section Perm.

Variable A : Type.
Hypothesis eq_dec : forall x y:A, {x=y} + {~ x=y}.

Notation permutation := (permutation _ eq_dec).
Notation list_contents := (list_contents _ eq_dec).



Lemma multiplicity_In :
forall l a, In a l <-> 0 < multiplicity (list_contents l) a.
Proof. try hammer_hook "PermutEq" "PermutEq.multiplicity_In".  
intros; split; intro H.
eapply In_InA, multiplicity_InA in H; eauto with typeclass_instances.
eapply multiplicity_InA, InA_alt in H as (y & -> & H); eauto with typeclass_instances.
Qed.

Lemma multiplicity_In_O :
forall l a, ~ In a l -> multiplicity (list_contents l) a = 0.
Proof. try hammer_hook "PermutEq" "PermutEq.multiplicity_In_O".  
intros l a; rewrite multiplicity_In;
destruct (multiplicity (list_contents l) a); auto.
destruct 1; auto with arith.
Qed.

Lemma multiplicity_In_S :
forall l a, In a l -> multiplicity (list_contents l) a >= 1.
Proof. try hammer_hook "PermutEq" "PermutEq.multiplicity_In_S".  
intros l a; rewrite multiplicity_In; auto.
Qed.

Lemma multiplicity_NoDup :
forall l, NoDup l <-> (forall a, multiplicity (list_contents l) a <= 1).
Proof. try hammer_hook "PermutEq" "PermutEq.multiplicity_NoDup".  
induction l.
simpl.
split; auto with arith.
intros; apply NoDup_nil.
split; simpl.
inversion_clear 1.
rewrite IHl in H1.
intros; destruct (eq_dec a a0) as [H2|H2]; simpl; auto.
subst a0.
rewrite multiplicity_In_O; auto.
intros; constructor.
rewrite multiplicity_In.
generalize (H a).
destruct (eq_dec a a) as [H0|H0].
destruct (multiplicity (list_contents l) a); auto with arith.
simpl; inversion 1.
inversion H3.
destruct H0; auto.
rewrite IHl; intros.
generalize (H a0); auto with arith.
destruct (eq_dec a a0); simpl; auto with arith.
Qed.

Lemma NoDup_permut :
forall l l', NoDup l -> NoDup l' ->
(forall x, In x l <-> In x l') -> permutation l l'.
Proof. try hammer_hook "PermutEq" "PermutEq.NoDup_permut".  
intros.
red; unfold meq; intros.
rewrite multiplicity_NoDup in H, H0.
generalize (H a) (H0 a) (H1 a); clear H H0 H1.
do 2 rewrite multiplicity_In.
destruct 3; omega.
Qed.


Lemma permut_In_In :
forall l1 l2 e, permutation l1 l2 -> In e l1 -> In e l2.
Proof. try hammer_hook "PermutEq" "PermutEq.permut_In_In".  
unfold PermutSetoid.permutation, meq; intros l1 l2 e P IN.
generalize (P e); clear P.
destruct (In_dec eq_dec e l2) as [H|H]; auto.
rewrite (multiplicity_In_O _ _ H).
intros.
generalize (multiplicity_In_S _ _ IN).
rewrite H0.
inversion 1.
Qed.

Lemma permut_cons_In :
forall l1 l2 e, permutation (e :: l1) l2 -> In e l2.
Proof. try hammer_hook "PermutEq" "PermutEq.permut_cons_In".  
intros; eapply permut_In_In; eauto.
red; auto.
Qed.


Lemma permut_nil :
forall l, permutation l nil -> l = nil.
Proof. try hammer_hook "PermutEq" "PermutEq.permut_nil".  
intro l; destruct l as [ | e l ]; trivial.
assert (In e (e::l)) by (red; auto).
intro Abs; generalize (permut_In_In _ Abs H).
inversion 1.
Qed.



Lemma permutation_Permutation :
forall l l', Permutation l l' <-> permutation l l'.
Proof. try hammer_hook "PermutEq" "PermutEq.permutation_Permutation".  
split.
induction 1.
apply permut_refl.
apply permut_cons; auto.
change (permutation (y::x::l) ((x::nil)++y::l)).
apply permut_add_cons_inside; simpl; apply permut_refl.
apply permut_trans with l'; auto.
revert l'.
induction l.
intros.
rewrite (permut_nil (permut_sym H)).
apply Permutation_refl.
intros.
destruct (In_split _ _ (permut_cons_In H)) as (h2,(t2,H1)).
subst l'.
apply Permutation_cons_app.
apply IHl.
apply permut_remove_hd with a; auto with typeclass_instances.
Qed.



Lemma permut_length_1:
forall a b, permutation (a :: nil) (b :: nil)  -> a=b.
Proof. try hammer_hook "PermutEq" "PermutEq.permut_length_1".  
intros a b; unfold PermutSetoid.permutation, meq; intro P;
generalize (P b); clear P; simpl.
destruct (eq_dec b b) as [H|H]; [ | destruct H; auto].
destruct (eq_dec a b); simpl; auto; intros; discriminate.
Qed.

Lemma permut_length_2 :
forall a1 b1 a2 b2, permutation (a1 :: b1 :: nil) (a2 :: b2 :: nil) ->
(a1=a2) /\ (b1=b2) \/ (a1=b2) /\ (a2=b1).
Proof. try hammer_hook "PermutEq" "PermutEq.permut_length_2".  
intros a1 b1 a2 b2 P.
assert (H:=permut_cons_In P).
inversion_clear H.
left; split; auto.
apply permut_length_1.
red; red; intros.
generalize (P a); clear P; simpl.
destruct (eq_dec a1 a) as [H2|H2];
destruct (eq_dec a2 a) as [H3|H3]; auto.
destruct H3; transitivity a1; auto.
destruct H2; transitivity a2; auto.
right.
inversion_clear H0; [|inversion H].
split; auto.
apply permut_length_1.
red; red; intros.
generalize (P a); clear P; simpl.
destruct (eq_dec a1 a) as [H2|H2];
destruct (eq_dec b2 a) as [H3|H3]; auto.
simpl; rewrite <- plus_n_Sm; inversion 1; auto.
destruct H3; transitivity a1; auto.
destruct H2; transitivity b2; auto.
Qed.


Lemma permut_length :
forall l1 l2, permutation l1 l2 -> length l1 = length l2.
Proof. try hammer_hook "PermutEq" "PermutEq.permut_length".  
induction l1; intros l2 H.
rewrite (permut_nil (permut_sym H)); auto.
destruct (In_split _ _ (permut_cons_In H)) as (h2,(t2,H1)).
subst l2.
rewrite app_length.
simpl; rewrite <- plus_n_Sm; f_equal.
rewrite <- app_length.
apply IHl1.
apply permut_remove_hd with a; auto with typeclass_instances.
Qed.

Variable B : Type.
Variable eqB_dec : forall x y:B, { x=y }+{ ~x=y }.



Lemma permutation_map :
forall f l1 l2, permutation l1 l2 ->
PermutSetoid.permutation _ eqB_dec (map f l1) (map f l2).
Proof. try hammer_hook "PermutEq" "PermutEq.permutation_map".  
intros f; induction l1.
intros l2 P; rewrite (permut_nil (permut_sym P)); apply permut_refl.
intros l2 P.
simpl.
destruct (In_split _ _ (permut_cons_In P)) as (h2,(t2,H1)).
subst l2.
rewrite map_app.
simpl.
apply permut_add_cons_inside.
rewrite <- map_app.
apply IHl1; auto.
apply permut_remove_hd with a; auto with typeclass_instances.
Qed.

End Perm.

