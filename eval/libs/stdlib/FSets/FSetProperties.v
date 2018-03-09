From Hammer Require Import Hammer.













Require Export FSetInterface.
Require Import DecidableTypeEx FSetFacts FSetDecide.
Set Implicit Arguments.
Unset Strict Implicit.

Hint Unfold transpose compat_op Proper respectful.
Hint Extern 1 (Equivalence _) => constructor; congruence.



Module WProperties_fun (Import E : DecidableType)(M : WSfun E).
Module Import Dec := WDecide_fun E M.
Module Import FM := Dec.F .
Import M.

Lemma In_dec : forall x s, {In x s} + {~ In x s}.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.In_dec". Restart. 
intros; generalize (mem_iff s x); case (mem x s); intuition.
Qed.

Definition Add x s s' := forall y, In y s' <-> E.eq x y \/ In y s.

Lemma Add_Equal : forall x s s', Add x s s' <-> s' [=] add x s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.Add_Equal". Restart. 
unfold Add.
split; intros.
red; intros.
rewrite H; clear H.
fsetdec.
fsetdec.
Qed.

Ltac expAdd := repeat rewrite Add_Equal.

Section BasicProperties.

Variable s s' s'' s1 s2 s3 : t.
Variable x x' : elt.

Lemma equal_refl : s[=]s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.equal_refl". Restart.  fsetdec. Qed.

Lemma equal_sym : s[=]s' -> s'[=]s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.equal_sym". Restart.  fsetdec. Qed.

Lemma equal_trans : s1[=]s2 -> s2[=]s3 -> s1[=]s3.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.equal_trans". Restart.  fsetdec. Qed.

Lemma subset_refl : s[<=]s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_refl". Restart.  fsetdec. Qed.

Lemma subset_trans : s1[<=]s2 -> s2[<=]s3 -> s1[<=]s3.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_trans". Restart.  fsetdec. Qed.

Lemma subset_antisym : s[<=]s' -> s'[<=]s -> s[=]s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_antisym". Restart.  fsetdec. Qed.

Lemma subset_equal : s[=]s' -> s[<=]s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_equal". Restart.  fsetdec. Qed.

Lemma subset_empty : empty[<=]s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_empty". Restart.  fsetdec. Qed.

Lemma subset_remove_3 : s1[<=]s2 -> remove x s1 [<=] s2.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_remove_3". Restart.  fsetdec. Qed.

Lemma subset_diff : s1[<=]s3 -> diff s1 s2 [<=] s3.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_diff". Restart.  fsetdec. Qed.

Lemma subset_add_3 : In x s2 -> s1[<=]s2 -> add x s1 [<=] s2.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_add_3". Restart.  fsetdec. Qed.

Lemma subset_add_2 : s1[<=]s2 -> s1[<=] add x s2.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_add_2". Restart.  fsetdec. Qed.

Lemma in_subset : In x s1 -> s1[<=]s2 -> In x s2.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.in_subset". Restart.  fsetdec. Qed.

Lemma double_inclusion : s1[=]s2 <-> s1[<=]s2 /\ s2[<=]s1.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.double_inclusion". Restart.  intuition fsetdec. Qed.

Lemma empty_is_empty_1 : Empty s -> s[=]empty.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.empty_is_empty_1". Restart.  fsetdec. Qed.

Lemma empty_is_empty_2 : s[=]empty -> Empty s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.empty_is_empty_2". Restart.  fsetdec. Qed.

Lemma add_equal : In x s -> add x s [=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.add_equal". Restart.  fsetdec. Qed.

Lemma add_add : add x (add x' s) [=] add x' (add x s).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.add_add". Restart.  fsetdec. Qed.

Lemma remove_equal : ~ In x s -> remove x s [=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.remove_equal". Restart.  fsetdec. Qed.

Lemma Equal_remove : s[=]s' -> remove x s [=] remove x s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.Equal_remove". Restart.  fsetdec. Qed.

Lemma add_remove : In x s -> add x (remove x s) [=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.add_remove". Restart.  fsetdec. Qed.

Lemma remove_add : ~In x s -> remove x (add x s) [=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.remove_add". Restart.  fsetdec. Qed.

Lemma singleton_equal_add : singleton x [=] add x empty.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.singleton_equal_add". Restart.  fsetdec. Qed.

Lemma remove_singleton_empty :
In x s -> remove x s [=] empty -> singleton x [=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.remove_singleton_empty". Restart.  fsetdec. Qed.

Lemma union_sym : union s s' [=] union s' s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_sym". Restart.  fsetdec. Qed.

Lemma union_subset_equal : s[<=]s' -> union s s' [=] s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_subset_equal". Restart.  fsetdec. Qed.

Lemma union_equal_1 : s[=]s' -> union s s'' [=] union s' s''.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_equal_1". Restart.  fsetdec. Qed.

Lemma union_equal_2 : s'[=]s'' -> union s s' [=] union s s''.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_equal_2". Restart.  fsetdec. Qed.

Lemma union_assoc : union (union s s') s'' [=] union s (union s' s'').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_assoc". Restart.  fsetdec. Qed.

Lemma add_union_singleton : add x s [=] union (singleton x) s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.add_union_singleton". Restart.  fsetdec. Qed.

Lemma union_add : union (add x s) s' [=] add x (union s s').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_add". Restart.  fsetdec. Qed.

Lemma union_remove_add_1 :
union (remove x s) (add x s') [=] union (add x s) (remove x s').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_remove_add_1". Restart.  fsetdec. Qed.

Lemma union_remove_add_2 : In x s ->
union (remove x s) (add x s') [=] union s s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_remove_add_2". Restart.  fsetdec. Qed.

Lemma union_subset_1 : s [<=] union s s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_subset_1". Restart.  fsetdec. Qed.

Lemma union_subset_2 : s' [<=] union s s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_subset_2". Restart.  fsetdec. Qed.

Lemma union_subset_3 : s[<=]s'' -> s'[<=]s'' -> union s s' [<=] s''.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_subset_3". Restart.  fsetdec. Qed.

Lemma union_subset_4 : s[<=]s' -> union s s'' [<=] union s' s''.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_subset_4". Restart.  fsetdec. Qed.

Lemma union_subset_5 : s[<=]s' -> union s'' s [<=] union s'' s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_subset_5". Restart.  fsetdec. Qed.

Lemma empty_union_1 : Empty s -> union s s' [=] s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.empty_union_1". Restart.  fsetdec. Qed.

Lemma empty_union_2 : Empty s -> union s' s [=] s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.empty_union_2". Restart.  fsetdec. Qed.

Lemma not_in_union : ~In x s -> ~In x s' -> ~In x (union s s').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.not_in_union". Restart.  fsetdec. Qed.

Lemma inter_sym : inter s s' [=] inter s' s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_sym". Restart.  fsetdec. Qed.

Lemma inter_subset_equal : s[<=]s' -> inter s s' [=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_subset_equal". Restart.  fsetdec. Qed.

Lemma inter_equal_1 : s[=]s' -> inter s s'' [=] inter s' s''.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_equal_1". Restart.  fsetdec. Qed.

Lemma inter_equal_2 : s'[=]s'' -> inter s s' [=] inter s s''.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_equal_2". Restart.  fsetdec. Qed.

Lemma inter_assoc : inter (inter s s') s'' [=] inter s (inter s' s'').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_assoc". Restart.  fsetdec. Qed.

Lemma union_inter_1 : inter (union s s') s'' [=] union (inter s s'') (inter s' s'').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_inter_1". Restart.  fsetdec. Qed.

Lemma union_inter_2 : union (inter s s') s'' [=] inter (union s s'') (union s' s'').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_inter_2". Restart.  fsetdec. Qed.

Lemma inter_add_1 : In x s' -> inter (add x s) s' [=] add x (inter s s').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_add_1". Restart.  fsetdec. Qed.

Lemma inter_add_2 : ~ In x s' -> inter (add x s) s' [=] inter s s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_add_2". Restart.  fsetdec. Qed.

Lemma empty_inter_1 : Empty s -> Empty (inter s s').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.empty_inter_1". Restart.  fsetdec. Qed.

Lemma empty_inter_2 : Empty s' -> Empty (inter s s').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.empty_inter_2". Restart.  fsetdec. Qed.

Lemma inter_subset_1 : inter s s' [<=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_subset_1". Restart.  fsetdec. Qed.

Lemma inter_subset_2 : inter s s' [<=] s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_subset_2". Restart.  fsetdec. Qed.

Lemma inter_subset_3 :
s''[<=]s -> s''[<=]s' -> s''[<=] inter s s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_subset_3". Restart.  fsetdec. Qed.

Lemma empty_diff_1 : Empty s -> Empty (diff s s').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.empty_diff_1". Restart.  fsetdec. Qed.

Lemma empty_diff_2 : Empty s -> diff s' s [=] s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.empty_diff_2". Restart.  fsetdec. Qed.

Lemma diff_subset : diff s s' [<=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.diff_subset". Restart.  fsetdec. Qed.

Lemma diff_subset_equal : s[<=]s' -> diff s s' [=] empty.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.diff_subset_equal". Restart.  fsetdec. Qed.

Lemma remove_diff_singleton :
remove x s [=] diff s (singleton x).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.remove_diff_singleton". Restart.  fsetdec. Qed.

Lemma diff_inter_empty : inter (diff s s') (inter s s') [=] empty.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.diff_inter_empty". Restart.  fsetdec. Qed.

Lemma diff_inter_all : union (diff s s') (inter s s') [=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.diff_inter_all". Restart.  fsetdec. Qed.

Lemma Add_add : Add x s (add x s).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.Add_add". Restart.  expAdd; fsetdec. Qed.

Lemma Add_remove : In x s -> Add x (remove x s) s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.Add_remove". Restart.  expAdd; fsetdec. Qed.

Lemma union_Add : Add x s s' -> Add x (union s s'') (union s' s'').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_Add". Restart.  expAdd; fsetdec. Qed.

Lemma inter_Add :
In x s'' -> Add x s s' -> Add x (inter s s'') (inter s' s'').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_Add". Restart.  expAdd; fsetdec. Qed.

Lemma union_Equal :
In x s'' -> Add x s s' -> union s s'' [=] union s' s''.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_Equal". Restart.  expAdd; fsetdec. Qed.

Lemma inter_Add_2 :
~In x s'' -> Add x s s' -> inter s s'' [=] inter s' s''.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.inter_Add_2". Restart.  expAdd; fsetdec. Qed.

End BasicProperties.

Hint Immediate equal_sym add_remove remove_add union_sym inter_sym: set.
Hint Resolve equal_refl equal_trans subset_refl subset_equal subset_antisym
subset_trans subset_empty subset_remove_3 subset_diff subset_add_3
subset_add_2 in_subset empty_is_empty_1 empty_is_empty_2 add_equal
remove_equal singleton_equal_add union_subset_equal union_equal_1
union_equal_2 union_assoc add_union_singleton union_add union_subset_1
union_subset_2 union_subset_3 inter_subset_equal inter_equal_1 inter_equal_2
inter_assoc union_inter_1 union_inter_2 inter_add_1 inter_add_2
empty_inter_1 empty_inter_2 empty_union_1 empty_union_2 empty_diff_1
empty_diff_2 union_Add inter_Add union_Equal inter_Add_2 not_in_union
inter_subset_1 inter_subset_2 inter_subset_3 diff_subset diff_subset_equal
remove_diff_singleton diff_inter_empty diff_inter_all Add_add Add_remove
Equal_remove add_add : set.



Lemma elements_Empty : forall s, Empty s <-> elements s = nil.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.elements_Empty". Restart. 
intros.
unfold Empty.
split; intros.
assert (forall a, ~ List.In a (elements s)).
red; intros.
apply (H a).
rewrite elements_iff.
rewrite InA_alt; exists a; auto.
destruct (elements s); auto.
elim (H0 e); simpl; auto.
red; intros.
rewrite elements_iff in H0.
rewrite InA_alt in H0; destruct H0.
rewrite H in H0; destruct H0 as (_,H0); inversion H0.
Qed.

Lemma elements_empty : elements empty = nil.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.elements_empty". Restart. 
rewrite <-elements_Empty; auto with set.
Qed.



Definition of_list (l : list elt) := List.fold_right add empty l.

Definition to_list := elements.

Lemma of_list_1 : forall l x, In x (of_list l) <-> InA E.eq x l.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.of_list_1". Restart. 
induction l; simpl; intro x.
rewrite empty_iff, InA_nil. intuition.
rewrite add_iff, InA_cons, IHl. intuition.
Qed.

Lemma of_list_2 : forall l, equivlistA E.eq (to_list (of_list l)) l.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.of_list_2". Restart. 
unfold to_list; red; intros.
rewrite <- elements_iff; apply of_list_1.
Qed.

Lemma of_list_3 : forall s, of_list (to_list s) [=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.of_list_3". Restart. 
unfold to_list; red; intros.
rewrite of_list_1; symmetry; apply elements_iff.
Qed.



Section Fold.



Lemma fold_spec_right (s:t)(A:Type)(i:A)(f : elt -> A -> A) :
fold f s i = List.fold_right f i (rev (elements s)).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_spec_right". Restart. 
rewrite fold_1. symmetry. apply fold_left_rev_right.
Qed.

Notation NoDup := (NoDupA E.eq).
Notation InA := (InA E.eq).





Theorem fold_rec :
forall (A:Type)(P : t -> A -> Type)(f : elt -> A -> A)(i:A)(s:t),
(forall s', Empty s' -> P s' i) ->
(forall x a s' s'', In x s -> ~In x s' -> Add x s' s'' ->
P s' a -> P s'' (f x a)) ->
P s (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_rec". Restart. 
intros A P f i s Pempty Pstep.
rewrite fold_spec_right. set (l:=rev (elements s)).
assert (Pstep' : forall x a s' s'', InA x l -> ~In x s' -> Add x s' s'' ->
P s' a -> P s'' (f x a)).
intros; eapply Pstep; eauto.
rewrite elements_iff, <- InA_rev; auto with *.
assert (Hdup : NoDup l) by
(unfold l; eauto using elements_3w, NoDupA_rev with *).
assert (Hsame : forall x, In x s <-> InA x l) by
(unfold l; intros; rewrite elements_iff, InA_rev; intuition).
clear Pstep; clearbody l; revert s Hsame; induction l.

intros s Hsame; simpl.
apply Pempty. intro x. rewrite Hsame, InA_nil; intuition.

intros s Hsame; simpl.
apply Pstep' with (of_list l); auto.
inversion_clear Hdup; rewrite of_list_1; auto.
red. intros. rewrite Hsame, of_list_1, InA_cons; intuition.
apply IHl.
intros; eapply Pstep'; eauto.
inversion_clear Hdup; auto.
exact (of_list_1 l).
Qed.



Theorem fold_rec_bis :
forall (A:Type)(P : t -> A -> Type)(f : elt -> A -> A)(i:A)(s:t),
(forall s s' a, s[=]s' -> P s a -> P s' a) ->
(P empty i) ->
(forall x a s', In x s -> ~In x s' -> P s' a -> P (add x s') (f x a)) ->
P s (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_rec_bis". Restart. 
intros A P f i s Pmorphism Pempty Pstep.
apply fold_rec; intros.
apply Pmorphism with empty; auto with set.
rewrite Add_Equal in H1; auto with set.
apply Pmorphism with (add x s'); auto with set.
Qed.

Lemma fold_rec_nodep :
forall (A:Type)(P : A -> Type)(f : elt -> A -> A)(i:A)(s:t),
P i -> (forall x a, In x s -> P a -> P (f x a)) ->
P (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_rec_nodep". Restart. 
intros; apply fold_rec_bis with (P:=fun _ => P); auto.
Qed.



Lemma fold_rec_weak :
forall (A:Type)(P : t -> A -> Type)(f : elt -> A -> A)(i:A),
(forall s s' a, s[=]s' -> P s a -> P s' a) ->
P empty i ->
(forall x a s, ~In x s -> P s a -> P (add x s) (f x a)) ->
forall s, P s (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_rec_weak". Restart. 
intros; apply fold_rec_bis; auto.
Qed.

Lemma fold_rel :
forall (A B:Type)(R : A -> B -> Type)
(f : elt -> A -> A)(g : elt -> B -> B)(i : A)(j : B)(s : t),
R i j ->
(forall x a b, In x s -> R a b -> R (f x a) (g x b)) ->
R (fold f s i) (fold g s j).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_rel". Restart. 
intros A B R f g i j s Rempty Rstep.
rewrite 2 fold_spec_right. set (l:=rev (elements s)).
assert (Rstep' : forall x a b, InA x l -> R a b -> R (f x a) (g x b)) by
(intros; apply Rstep; auto; rewrite elements_iff, <- InA_rev; auto with *).
clearbody l; clear Rstep s.
induction l; simpl; auto.
Qed.



Lemma set_induction :
forall P : t -> Type,
(forall s, Empty s -> P s) ->
(forall s s', P s -> forall x, ~In x s -> Add x s s' -> P s') ->
forall s, P s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.set_induction". Restart. 
intros. apply (@fold_rec _ (fun s _ => P s) (fun _ _ => tt) tt s); eauto.
Qed.

Lemma set_induction_bis :
forall P : t -> Type,
(forall s s', s [=] s' -> P s -> P s') ->
P empty ->
(forall x s, ~In x s -> P s -> P (add x s)) ->
forall s, P s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.set_induction_bis". Restart. 
intros.
apply (@fold_rec_bis _ (fun s _ => P s) (fun _ _ => tt) tt s); eauto.
Qed.



Lemma fold_identity : forall s, fold add s empty [=] s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_identity". Restart. 
intros.
apply fold_rec with (P:=fun s acc => acc[=]s); auto with set.
intros. rewrite H2; rewrite Add_Equal in H1; auto with set.
Qed.





Lemma fold_0 :
forall s (A : Type) (i : A) (f : elt -> A -> A),
exists l : list elt,
NoDup l /\
(forall x : elt, In x s <-> InA x l) /\
fold f s i = fold_right f i l.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_0". Restart. 
intros; exists (rev (elements s)); split.
apply NoDupA_rev; auto with *.
split; intros.
rewrite elements_iff; do 2 rewrite InA_alt.
split; destruct 1; generalize (In_rev (elements s) x0); exists x0; intuition.
apply fold_spec_right.
Qed.



Lemma fold_1 :
forall s (A : Type) (eqA : A -> A -> Prop)
(st : Equivalence eqA) (i : A) (f : elt -> A -> A),
Empty s -> eqA (fold f s i) i.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_1". Restart. 
unfold Empty; intros; destruct (fold_0 s i f) as (l,(H1, (H2, H3))).
rewrite H3; clear H3.
generalize H H2; clear H H2; case l; simpl; intros.
reflexivity.
elim (H e).
elim (H2 e); intuition.
Qed.

Lemma fold_2 :
forall s s' x (A : Type) (eqA : A -> A -> Prop)
(st : Equivalence eqA) (i : A) (f : elt -> A -> A),
compat_op E.eq eqA f ->
transpose eqA f ->
~ In x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_2". Restart. 
intros; destruct (fold_0 s i f) as (l,(Hl, (Hl1, Hl2)));
destruct (fold_0 s' i f) as (l',(Hl', (Hl'1, Hl'2))).
rewrite Hl2; rewrite Hl'2; clear Hl2 Hl'2.
apply fold_right_add with (eqA:=E.eq)(eqB:=eqA); auto with *.
rewrite <- Hl1; auto.
intros a; rewrite InA_cons; rewrite <- Hl1; rewrite <- Hl'1;
rewrite (H2 a); intuition.
Qed.



Lemma fold_1b :
forall s (A : Type)(i : A) (f : elt -> A -> A),
Empty s -> (fold f s i) = i.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_1b". Restart. 
intros.
rewrite M.fold_1.
rewrite elements_Empty in H; rewrite H; simpl; auto.
Qed.

Section Fold_More.

Variables (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA).
Variables (f:elt->A->A)(Comp:compat_op E.eq eqA f)(Ass:transpose eqA f).

Lemma fold_commutes : forall i s x,
eqA (fold f s (f x i)) (f x (fold f s i)).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_commutes". Restart. 
intros.
apply fold_rel with (R:=fun u v => eqA u (f x v)); intros.
reflexivity.
transitivity (f x0 (f x b)); auto. apply Comp; auto with *.
Qed.



Lemma fold_init : forall i i' s, eqA i i' ->
eqA (fold f s i) (fold f s i').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_init". Restart. 
intros. apply fold_rel with (R:=eqA); auto.
intros; apply Comp; auto with *.
Qed.

Lemma fold_equal :
forall i s s', s[=]s' -> eqA (fold f s i) (fold f s' i).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_equal". Restart. 
intros i s; pattern s; apply set_induction; clear s; intros.
transitivity i.
apply fold_1; auto.
symmetry; apply fold_1; auto.
rewrite <- H0; auto.
transitivity (f x (fold f s i)).
apply fold_2 with (eqA := eqA); auto.
symmetry; apply fold_2 with (eqA := eqA); auto.
unfold Add in *; intros.
rewrite <- H2; auto.
Qed.



Lemma fold_empty : forall i, fold f empty i = i.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_empty". Restart. 
intros i; apply fold_1b; auto with set.
Qed.

Lemma fold_add : forall i s x, ~In x s ->
eqA (fold f (add x s) i) (f x (fold f s i)).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_add". Restart. 
intros; apply fold_2 with (eqA := eqA); auto with set.
Qed.

Lemma add_fold : forall i s x, In x s ->
eqA (fold f (add x s) i) (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.add_fold". Restart. 
intros; apply fold_equal; auto with set.
Qed.

Lemma remove_fold_1: forall i s x, In x s ->
eqA (f x (fold f (remove x s) i)) (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.remove_fold_1". Restart. 
intros.
symmetry.
apply fold_2 with (eqA:=eqA); auto with set.
Qed.

Lemma remove_fold_2: forall i s x, ~In x s ->
eqA (fold f (remove x s) i) (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.remove_fold_2". Restart. 
intros.
apply fold_equal; auto with set.
Qed.

Lemma fold_union_inter : forall i s s',
eqA (fold f (union s s') (fold f (inter s s') i))
(fold f s (fold f s' i)).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_union_inter". Restart. 
intros; pattern s; apply set_induction; clear s; intros.
transitivity (fold f s' (fold f (inter s s') i)).
apply fold_equal; auto with set.
transitivity (fold f s' i).
apply fold_init; auto.
apply fold_1; auto with set.
symmetry; apply fold_1; auto.
rename s'0 into s''.
destruct (In_dec x s').

transitivity (fold f (union s'' s') (f x (fold f (inter s s') i))); auto with set.
apply fold_init; auto.
apply fold_2 with (eqA:=eqA); auto with set.
rewrite inter_iff; intuition.
transitivity (f x (fold f s (fold f s' i))).
transitivity (fold f (union s s') (f x (fold f (inter s s') i))).
apply fold_equal; auto.
apply equal_sym; apply union_Equal with x; auto with set.
transitivity (f x (fold f (union s s') (fold f (inter s s') i))).
apply fold_commutes; auto.
apply Comp; auto.
symmetry; apply fold_2 with (eqA:=eqA); auto.

transitivity (f x (fold f (union s s') (fold f (inter s'' s') i))).
apply fold_2 with (eqA:=eqA); auto with set.
transitivity (f x (fold f (union s s') (fold f (inter s s') i))).
apply Comp;auto.
apply fold_init;auto.
apply fold_equal;auto.
apply equal_sym; apply inter_Add_2 with x; auto with set.
transitivity (f x (fold f s (fold f s' i))).
apply Comp; auto.
symmetry; apply fold_2 with (eqA:=eqA); auto.
Qed.

Lemma fold_diff_inter : forall i s s',
eqA (fold f (diff s s') (fold f (inter s s') i)) (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_diff_inter". Restart. 
intros.
transitivity (fold f (union (diff s s') (inter s s'))
(fold f (inter (diff s s') (inter s s')) i)).
symmetry; apply fold_union_inter; auto.
transitivity (fold f s (fold f (inter (diff s s') (inter s s')) i)).
apply fold_equal; auto with set.
apply fold_init; auto.
apply fold_1; auto with set.
Qed.

Lemma fold_union: forall i s s',
(forall x, ~(In x s/\In x s')) ->
eqA (fold f (union s s') i) (fold f s (fold f s' i)).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_union". Restart. 
intros.
transitivity (fold f (union s s') (fold f (inter s s') i)).
apply fold_init; auto.
symmetry; apply fold_1; auto with set.
unfold Empty; intro a; generalize (H a); set_iff; tauto.
apply fold_union_inter; auto.
Qed.

End Fold_More.

Lemma fold_plus :
forall s p, fold (fun _ => S) s p = fold (fun _ => S) s 0 + p.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.fold_plus". Restart. 
intros. apply fold_rel with (R:=fun u v => u = v + p); simpl; auto.
Qed.

End Fold.





Lemma cardinal_fold : forall s, cardinal s = fold (fun _ => S) s 0.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.cardinal_fold". Restart. 
intros; rewrite cardinal_1; rewrite M.fold_1.
symmetry; apply fold_left_length; auto.
Qed.



Lemma cardinal_0 :
forall s, exists l : list elt,
NoDupA E.eq l /\
(forall x : elt, In x s <-> InA E.eq x l) /\
cardinal s = length l.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.cardinal_0". Restart. 
intros; exists (elements s); intuition; apply cardinal_1.
Qed.

Lemma cardinal_1 : forall s, Empty s -> cardinal s = 0.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.cardinal_1". Restart. 
intros; rewrite cardinal_fold; apply fold_1; auto.
Qed.

Lemma cardinal_2 :
forall s s' x, ~ In x s -> Add x s s' -> cardinal s' = S (cardinal s).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.cardinal_2". Restart. 
intros; do 2 rewrite cardinal_fold.
change S with ((fun _ => S) x).
apply fold_2; auto.
Qed.



Lemma cardinal_Empty : forall s, Empty s <-> cardinal s = 0.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.cardinal_Empty". Restart. 
intros.
rewrite elements_Empty, M.cardinal_1.
destruct (elements s); intuition; discriminate.
Qed.

Lemma cardinal_inv_1 : forall s, cardinal s = 0 -> Empty s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.cardinal_inv_1". Restart. 
intros; rewrite cardinal_Empty; auto.
Qed.
Hint Resolve cardinal_inv_1.

Lemma cardinal_inv_2 :
forall s n, cardinal s = S n -> { x : elt | In x s }.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.cardinal_inv_2". Restart. 
intros; rewrite M.cardinal_1 in H.
generalize (elements_2 (s:=s)).
destruct (elements s); try discriminate.
exists e; auto.
Qed.

Lemma cardinal_inv_2b :
forall s, cardinal s <> 0 -> { x : elt | In x s }.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.cardinal_inv_2b". Restart. 
intro; generalize (@cardinal_inv_2 s); destruct cardinal;
[intuition|eauto].
Qed.



Lemma Equal_cardinal : forall s s', s[=]s' -> cardinal s = cardinal s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.Equal_cardinal". Restart. 
symmetry.
remember (cardinal s) as n; symmetry in Heqn; revert s s' Heqn H.
induction n; intros.
apply cardinal_1; rewrite <- H; auto.
destruct (cardinal_inv_2 Heqn) as (x,H2).
revert Heqn.
rewrite (cardinal_2 (s:=remove x s) (s':=s) (x:=x)); auto with set.
rewrite (cardinal_2 (s:=remove x s') (s':=s') (x:=x)); eauto with set.
Qed.

Add Morphism cardinal with signature (Equal ==> Logic.eq) as cardinal_m.
Proof.
exact Equal_cardinal.
Qed.

Hint Resolve Add_add Add_remove Equal_remove cardinal_inv_1 Equal_cardinal.



Lemma empty_cardinal : cardinal empty = 0.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.empty_cardinal". Restart. 
rewrite cardinal_fold; apply fold_1; auto with set.
Qed.

Hint Immediate empty_cardinal cardinal_1 : set.

Lemma singleton_cardinal : forall x, cardinal (singleton x) = 1.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.singleton_cardinal". Restart. 
intros.
rewrite (singleton_equal_add x).
replace 0 with (cardinal empty); auto with set.
apply cardinal_2 with x; auto with set.
Qed.

Hint Resolve singleton_cardinal: set.

Lemma diff_inter_cardinal :
forall s s', cardinal (diff s s') + cardinal (inter s s') = cardinal s .
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.diff_inter_cardinal". Restart. 
intros; do 3 rewrite cardinal_fold.
rewrite <- fold_plus.
apply fold_diff_inter with (eqA:=@Logic.eq nat); auto.
Qed.

Lemma union_cardinal:
forall s s', (forall x, ~(In x s/\In x s')) ->
cardinal (union s s')=cardinal s+cardinal s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_cardinal". Restart. 
intros; do 3 rewrite cardinal_fold.
rewrite <- fold_plus.
apply fold_union; auto.
Qed.

Lemma subset_cardinal :
forall s s', s[<=]s' -> cardinal s <= cardinal s' .
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_cardinal". Restart. 
intros.
rewrite <- (diff_inter_cardinal s' s).
rewrite (inter_sym s' s).
rewrite (inter_subset_equal H); auto with arith.
Qed.

Lemma subset_cardinal_lt :
forall s s' x, s[<=]s' -> In x s' -> ~In x s -> cardinal s < cardinal s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.subset_cardinal_lt". Restart. 
intros.
rewrite <- (diff_inter_cardinal s' s).
rewrite (inter_sym s' s).
rewrite (inter_subset_equal H).
generalize (@cardinal_inv_1 (diff s' s)).
destruct (cardinal (diff s' s)).
intro H2; destruct (H2 Logic.eq_refl x).
set_iff; auto.
intros _.
change (0 + cardinal s < S n + cardinal s).
apply Plus.plus_lt_le_compat; auto with arith.
Qed.

Theorem union_inter_cardinal :
forall s s', cardinal (union s s') + cardinal (inter s s')  = cardinal s  + cardinal s' .
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_inter_cardinal". Restart. 
intros.
do 4 rewrite cardinal_fold.
do 2 rewrite <- fold_plus.
apply fold_union_inter with (eqA:=@Logic.eq nat); auto.
Qed.

Lemma union_cardinal_inter :
forall s s', cardinal (union s s') = cardinal s + cardinal s' - cardinal (inter s s').
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_cardinal_inter". Restart. 
intros.
rewrite <- union_inter_cardinal.
rewrite Plus.plus_comm.
auto with arith.
Qed.

Lemma union_cardinal_le :
forall s s', cardinal (union s s') <= cardinal s  + cardinal s'.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.union_cardinal_le". Restart. 
intros; generalize (union_inter_cardinal s s').
intros; rewrite <- H; auto with arith.
Qed.

Lemma add_cardinal_1 :
forall s x, In x s -> cardinal (add x s) = cardinal s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.add_cardinal_1". Restart. 
auto with set.
Qed.

Lemma add_cardinal_2 :
forall s x, ~In x s -> cardinal (add x s) = S (cardinal s).
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.add_cardinal_2". Restart. 
intros.
do 2 rewrite cardinal_fold.
change S with ((fun _ => S) x);
apply fold_add with (eqA:=@Logic.eq nat); auto.
Qed.

Lemma remove_cardinal_1 :
forall s x, In x s -> S (cardinal (remove x s)) = cardinal s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.remove_cardinal_1". Restart. 
intros.
do 2 rewrite cardinal_fold.
change S with ((fun _ =>S) x).
apply remove_fold_1 with (eqA:=@Logic.eq nat); auto.
Qed.

Lemma remove_cardinal_2 :
forall s x, ~In x s -> cardinal (remove x s) = cardinal s.
Proof. hammer_hook "FSetProperties" "FSetProperties.WProperties_fun.remove_cardinal_2". Restart. 
auto with set.
Qed.

Hint Resolve subset_cardinal union_cardinal add_cardinal_1 add_cardinal_2.

End WProperties_fun.



Module WProperties (M:WS) := WProperties_fun M.E M.
Module Properties := WProperties.




Module OrdProperties (M:S).
Module ME:=OrderedTypeFacts(M.E).
Module Import P := Properties M.
Import FM.
Import M.E.
Import M.


Lemma sort_equivlistA_eqlistA : forall l l' : list elt,
sort E.lt l -> sort E.lt l' -> equivlistA E.eq l l' -> eqlistA E.eq l l'.
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.sort_equivlistA_eqlistA". Restart. 
apply SortA_equivlistA_eqlistA; eauto with *.
Qed.

Definition gtb x y := match E.compare x y with GT _ => true | _ => false end.
Definition leb x := fun y => negb (gtb x y).

Definition elements_lt x s := List.filter (gtb x) (elements s).
Definition elements_ge x s := List.filter (leb x) (elements s).

Lemma gtb_1 : forall x y, gtb x y = true <-> E.lt y x.
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.gtb_1". Restart. 
intros; unfold gtb; destruct (E.compare x y); intuition; try discriminate; ME.order.
Qed.

Lemma leb_1 : forall x y, leb x y = true <-> ~E.lt y x.
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.leb_1". Restart. 
intros; unfold leb, gtb; destruct (E.compare x y); intuition; try discriminate; ME.order.
Qed.

Lemma gtb_compat : forall x, Proper (E.eq==>Logic.eq) (gtb x).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.gtb_compat". Restart. 
red; intros x a b H.
generalize (gtb_1 x a)(gtb_1 x b); destruct (gtb x a); destruct (gtb x b); auto.
intros.
symmetry; rewrite H1.
apply ME.eq_lt with a; auto.
rewrite <- H0; auto.
intros.
rewrite H0.
apply ME.eq_lt with b; auto.
rewrite <- H1; auto.
Qed.

Lemma leb_compat : forall x, Proper (E.eq==>Logic.eq) (leb x).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.leb_compat". Restart. 
red; intros x a b H; unfold leb.
f_equal; apply gtb_compat; auto.
Qed.
Hint Resolve gtb_compat leb_compat.

Lemma elements_split : forall x s,
elements s = elements_lt x s ++ elements_ge x s.
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.elements_split". Restart. 
unfold elements_lt, elements_ge, leb; intros.
eapply (@filter_split _ E.eq _ E.lt); auto with *.
intros.
rewrite gtb_1 in H.
assert (~E.lt y x).
unfold gtb in *; destruct (E.compare x y); intuition;
try discriminate; ME.order.
ME.order.
Qed.

Lemma elements_Add : forall s s' x, ~In x s -> Add x s s' ->
eqlistA E.eq (elements s') (elements_lt x s ++ x :: elements_ge x s).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.elements_Add". Restart. 
intros; unfold elements_ge, elements_lt.
apply sort_equivlistA_eqlistA; auto with set.
apply (@SortA_app _ E.eq); auto with *.
apply (@filter_sort _ E.eq); auto with *.
constructor; auto.
apply (@filter_sort _ E.eq); auto with *.
rewrite ME.Inf_alt by (apply (@filter_sort _ E.eq); eauto with *).
intros.
rewrite filter_InA in H1; auto with *; destruct H1.
rewrite leb_1 in H2.
rewrite <- elements_iff in H1.
assert (~E.eq x y).
contradict H; rewrite H; auto.
ME.order.
intros.
rewrite filter_InA in H1; auto with *; destruct H1.
rewrite gtb_1 in H3.
inversion_clear H2.
ME.order.
rewrite filter_InA in H4; auto with *; destruct H4.
rewrite leb_1 in H4.
ME.order.
red; intros a.
rewrite InA_app_iff, InA_cons, !filter_InA, <-elements_iff,
leb_1, gtb_1, (H0 a) by auto with *.
intuition.
destruct (E.compare a x); intuition.
fold (~E.lt a x); auto with *.
Qed.

Definition Above x s := forall y, In y s -> E.lt y x.
Definition Below x s := forall y, In y s -> E.lt x y.

Lemma elements_Add_Above : forall s s' x,
Above x s -> Add x s s' ->
eqlistA E.eq (elements s') (elements s ++ x::nil).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.elements_Add_Above". Restart. 
intros.
apply sort_equivlistA_eqlistA; auto with *.
apply (@SortA_app _ E.eq); auto with *.
intros.
inversion_clear H2.
rewrite <- elements_iff in H1.
apply ME.lt_eq with x; auto.
inversion H3.
red; intros a.
rewrite InA_app_iff, InA_cons, InA_nil by auto with *.
do 2 rewrite <- elements_iff; rewrite (H0 a); intuition.
Qed.

Lemma elements_Add_Below : forall s s' x,
Below x s -> Add x s s' ->
eqlistA E.eq (elements s') (x::elements s).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.elements_Add_Below". Restart. 
intros.
apply sort_equivlistA_eqlistA; auto with *.
change (sort E.lt ((x::nil) ++ elements s)).
apply (@SortA_app _ E.eq); auto with *.
intros.
inversion_clear H1.
rewrite <- elements_iff in H2.
apply ME.eq_lt with x; auto.
inversion H3.
red; intros a.
rewrite InA_cons.
do 2 rewrite <- elements_iff; rewrite (H0 a); intuition.
Qed.



Lemma set_induction_max :
forall P : t -> Type,
(forall s : t, Empty s -> P s) ->
(forall s s', P s -> forall x, Above x s -> Add x s s' -> P s') ->
forall s : t, P s.
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.set_induction_max". Restart. 
intros; remember (cardinal s) as n; revert s Heqn; induction n; intros; auto.
case_eq (max_elt s); intros.
apply X0 with (remove e s) e; auto with set.
apply IHn.
assert (S n = S (cardinal (remove e s))).
rewrite Heqn; apply cardinal_2 with e; auto with set.
inversion H0; auto.
red; intros.
rewrite remove_iff in H0; destruct H0.
generalize (@max_elt_2 s e y H H0); ME.order.

assert (H0:=max_elt_3 H).
rewrite cardinal_Empty in H0; rewrite H0 in Heqn; inversion Heqn.
Qed.

Lemma set_induction_min :
forall P : t -> Type,
(forall s : t, Empty s -> P s) ->
(forall s s', P s -> forall x, Below x s -> Add x s s' -> P s') ->
forall s : t, P s.
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.set_induction_min". Restart. 
intros; remember (cardinal s) as n; revert s Heqn; induction n; intros; auto.
case_eq (min_elt s); intros.
apply X0 with (remove e s) e; auto with set.
apply IHn.
assert (S n = S (cardinal (remove e s))).
rewrite Heqn; apply cardinal_2 with e; auto with set.
inversion H0; auto.
red; intros.
rewrite remove_iff in H0; destruct H0.
generalize (@min_elt_2 s e y H H0); ME.order.

assert (H0:=min_elt_3 H).
rewrite cardinal_Empty in H0; auto; rewrite H0 in Heqn; inversion Heqn.
Qed.



Lemma fold_3 :
forall s s' x (A : Type) (eqA : A -> A -> Prop)
(st : Equivalence eqA) (i : A) (f : elt -> A -> A),
compat_op E.eq eqA f ->
Above x s -> Add x s s' -> eqA (fold f s' i) (f x (fold f s i)).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.fold_3". Restart. 
intros.
rewrite 2 fold_spec_right.
change (f x (fold_right f i (rev (elements s)))) with
(fold_right f i (rev (x::nil)++rev (elements s))).
apply (@fold_right_eqlistA E.t E.eq A eqA st); auto.
rewrite <- distr_rev.
apply eqlistA_rev.
apply elements_Add_Above; auto.
Qed.

Lemma fold_4 :
forall s s' x (A : Type) (eqA : A -> A -> Prop)
(st : Equivalence eqA) (i : A) (f : elt -> A -> A),
compat_op E.eq eqA f ->
Below x s -> Add x s s' -> eqA (fold f s' i) (fold f s (f x i)).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.fold_4". Restart. 
intros.
rewrite 2 M.fold_1.
set (g:=fun (a : A) (e : elt) => f e a).
change (eqA (fold_left g (elements s') i) (fold_left g (x::elements s) i)).
unfold g.
rewrite <- 2 fold_left_rev_right.
apply (@fold_right_eqlistA E.t E.eq A eqA st); auto.
apply eqlistA_rev.
apply elements_Add_Below; auto.
Qed.



Section FoldOpt.
Variables (A:Type)(eqA:A->A->Prop)(st:Equivalence eqA).
Variables (f:elt->A->A)(Comp:compat_op E.eq eqA f).

Lemma fold_equal :
forall i s s', s[=]s' -> eqA (fold f s i) (fold f s' i).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.fold_equal". Restart. 
intros. rewrite 2 fold_spec_right.
apply (@fold_right_eqlistA E.t E.eq A eqA st); auto.
apply eqlistA_rev.
apply sort_equivlistA_eqlistA; auto with set.
red; intro a; do 2 rewrite <- elements_iff; auto.
Qed.

Lemma add_fold : forall i s x, In x s ->
eqA (fold f (add x s) i) (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.add_fold". Restart. 
intros; apply fold_equal; auto with set.
Qed.

Lemma remove_fold_2: forall i s x, ~In x s ->
eqA (fold f (remove x s) i) (fold f s i).
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.remove_fold_2". Restart. 
intros.
apply fold_equal; auto with set.
Qed.

End FoldOpt.



Lemma choose_equal : forall s s', Equal s s' ->
match choose s, choose s' with
| Some x, Some x' => E.eq x x'
| None, None => True
| _, _ => False
end.
Proof. hammer_hook "FSetProperties" "FSetProperties.OrdProperties.choose_equal". Restart. 
intros s s' H;
generalize (@choose_1 s)(@choose_2 s)
(@choose_1 s')(@choose_2 s')(@choose_3 s s');
destruct (choose s); destruct (choose s'); simpl; intuition.
apply H5 with e; rewrite <-H; auto.
apply H5 with e; rewrite H; auto.
Qed.

End OrdProperties.
