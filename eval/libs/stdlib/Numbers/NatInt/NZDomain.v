From Hammer Require Import Hammer.









Require Export NumPrelude NZAxioms.
Require Import NZBase NZOrder NZAddOrder Plus Minus.



Local Notation "f ^ n" := (fun x => nat_rect _ x (fun _ => f) n).

Instance nat_rect_wd n {A} (R:relation A) :
Proper (R==>(R==>R)==>R) (fun x f => nat_rect (fun _ => _) x (fun _ => f) n).
Proof. try hammer_hook "NZDomain" "NZDomain.nat_rect_wd".  
intros x y eq_xy f g eq_fg; induction n; [assumption | now apply eq_fg].
Qed.

Module NZDomainProp (Import NZ:NZDomainSig').
Include NZBaseProp NZ.





Lemma itersucc_or_itersucc n m : exists k, n == (S^k) m \/ m == (S^k) n.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.itersucc_or_itersucc".  
revert n.
apply central_induction with (z:=m).
{ intros x y eq_xy; apply ex_iff_morphism.
intros n; apply or_iff_morphism.
+ split; intros; etransitivity; try eassumption; now symmetry.
+ split; intros; (etransitivity; [eassumption|]); [|symmetry];
(eapply nat_rect_wd; [eassumption|apply succ_wd]).
}
exists 0%nat. now left.
intros n. split; intros [k [L|R]].
exists (Datatypes.S k). left. now apply succ_wd.
destruct k as [|k].
simpl in R. exists 1%nat. left. now apply succ_wd.
rewrite nat_rect_succ_r in R. exists k. now right.
destruct k as [|k]; simpl in L.
exists 1%nat. now right.
apply succ_inj in L. exists k. now left.
exists (Datatypes.S k). right. now rewrite nat_rect_succ_r.
Qed.



Lemma succ_swap_pred : forall k n m, n == (S^k) m -> m == (P^k) n.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.succ_swap_pred".  
induction k.
simpl; auto with *.
simpl; intros. apply pred_wd in H. rewrite pred_succ in H. apply IHk in H; auto.
rewrite <- nat_rect_succ_r in H; auto.
Qed.



Lemma itersucc_or_iterpred : forall n m, exists k, n == (S^k) m \/ n == (P^k) m.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.itersucc_or_iterpred".  
intros n m. destruct (itersucc_or_itersucc n m) as (k,[H|H]).
exists k; left; auto.
exists k; right. apply succ_swap_pred; auto.
Qed.



Lemma itersucc0_or_iterpred0 :
forall n, exists p:nat, n == (S^p) 0 \/ n == (P^p) 0.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.itersucc0_or_iterpred0".  
intros n. exact (itersucc_or_iterpred n 0).
Qed.



Definition initial n := forall m, n ~= S m.

Lemma initial_alt : forall n, initial n <-> S (P n) ~= n.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.initial_alt".  
split. intros Bn EQ. symmetry in EQ. destruct (Bn _ EQ).
intros NEQ m EQ. apply NEQ. rewrite EQ, pred_succ; auto with *.
Qed.

Lemma initial_alt2 : forall n, initial n <-> ~exists m, n == S m.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.initial_alt2".   firstorder. Qed.



Section InitialExists.
Hypothesis init : t.
Hypothesis Initial : initial init.



Lemma initial_unique : forall m, initial m -> m == init.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.initial_unique".  
intros m Im. destruct (itersucc_or_itersucc init m) as (p,[H|H]).
destruct p. now simpl in *. destruct (Initial _ H).
destruct p. now simpl in *. destruct (Im _ H).
Qed.



Lemma initial_ancestor : forall m, exists p, m == (S^p) init.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.initial_ancestor".  
intros m. destruct (itersucc_or_itersucc init m) as (p,[H|H]).
destruct p; simpl in *; auto. exists O; auto with *. destruct (Initial _ H).
exists p; auto.
Qed.





Section SuccPred.
Hypothesis eq_decidable : forall n m, n==m \/ n~=m.
Lemma succ_pred_approx : forall n, ~initial n -> S (P n) == n.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.succ_pred_approx".  
intros n NB. rewrite initial_alt in NB.
destruct (eq_decidable (S (P n)) n); auto.
elim NB; auto.
Qed.
End SuccPred.
End InitialExists.



Section InitialDontExists.

Hypothesis succ_onto : forall n, exists m, n == S m.

Lemma succ_onto_gives_succ_pred : forall n, S (P n) == n.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.succ_onto_gives_succ_pred".  
intros n. destruct (succ_onto n) as (m,H). rewrite H, pred_succ; auto with *.
Qed.

Lemma succ_onto_pred_injective : forall n m, P n == P m -> n == m.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.succ_onto_pred_injective".  
intros n m. intros H; apply succ_wd in H.
rewrite !succ_onto_gives_succ_pred in H; auto.
Qed.

End InitialDontExists.









Lemma bi_induction_pred :
forall A : t -> Prop, Proper (eq==>iff) A ->
A 0 -> (forall n, A n -> A (S n)) -> (forall n, A n -> A (P n)) ->
forall n, A n.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.bi_induction_pred".  
intros. apply bi_induction; auto.
clear n. intros n; split; auto.
intros G; apply H2 in G. rewrite pred_succ in G; auto.
Qed.

Lemma central_induction_pred :
forall A : t -> Prop, Proper (eq==>iff) A -> forall n0,
A n0 -> (forall n, A n -> A (S n)) -> (forall n, A n -> A (P n)) ->
forall n, A n.
Proof. try hammer_hook "NZDomain" "NZDomain.NZDomainProp.central_induction_pred".  
intros.
assert (A 0).
destruct (itersucc_or_iterpred 0 n0) as (k,[Hk|Hk]); rewrite Hk; clear Hk.
clear H2. induction k; simpl in *; auto.
clear H1. induction k; simpl in *; auto.
apply bi_induction_pred; auto.
Qed.

End NZDomainProp.



Module NZOfNat (Import NZ:NZDomainSig').

Definition ofnat (n : nat) : t := (S^n) 0.
Notation "[ n ]" := (ofnat n) (at level 7) : ofnat.
Local Open Scope ofnat.

Lemma ofnat_zero : [O] == 0.
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNat.ofnat_zero".  
reflexivity.
Qed.

Lemma ofnat_succ : forall n, [Datatypes.S n] == succ [n].
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNat.ofnat_succ".  
now unfold ofnat.
Qed.

Lemma ofnat_pred : forall n, n<>O -> [Peano.pred n] == P [n].
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNat.ofnat_pred".  
unfold ofnat. destruct n. destruct 1; auto.
intros _. simpl. symmetry. apply pred_succ.
Qed.



End NZOfNat.




Module NZOfNatOrd (Import NZ:NZOrdSig').
Include NZOfNat NZ.
Include NZBaseProp NZ <+ NZOrderProp NZ.
Local Open Scope ofnat.

Theorem ofnat_S_gt_0 :
forall n : nat, 0 < [Datatypes.S n].
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOrd.ofnat_S_gt_0".  
unfold ofnat.
intros n; induction n as [| n IH]; simpl in *.
apply lt_succ_diag_r.
apply lt_trans with (S 0). apply lt_succ_diag_r. now rewrite <- succ_lt_mono.
Qed.

Theorem ofnat_S_neq_0 :
forall n : nat, 0 ~= [Datatypes.S n].
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOrd.ofnat_S_neq_0".  
intros. apply lt_neq, ofnat_S_gt_0.
Qed.

Lemma ofnat_injective : forall n m, [n]==[m] -> n = m.
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOrd.ofnat_injective".  
induction n as [|n IH]; destruct m; auto.
intros H; elim (ofnat_S_neq_0 _ H).
intros H; symmetry in H; elim (ofnat_S_neq_0 _ H).
intros. f_equal. apply IH. now rewrite <- succ_inj_wd.
Qed.

Lemma ofnat_eq : forall n m, [n]==[m] <-> n = m.
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOrd.ofnat_eq".  
split. apply ofnat_injective. intros; now subst.
Qed.



Lemma ofnat_lt : forall n m : nat, [n]<[m] <-> (n<m)%nat.
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOrd.ofnat_lt".  
induction n as [|n IH]; destruct m; repeat rewrite ofnat_zero; split.
intro H; elim (lt_irrefl _ H).
inversion 1.
auto with arith.
intros; apply ofnat_S_gt_0.
intro H; elim (lt_asymm _ _ H); apply ofnat_S_gt_0.
inversion 1.
rewrite !ofnat_succ, <- succ_lt_mono, IH; auto with arith.
rewrite !ofnat_succ, <- succ_lt_mono, IH; auto with arith.
Qed.

Lemma ofnat_le : forall n m : nat, [n]<=[m] <-> (n<=m)%nat.
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOrd.ofnat_le".  
intros. rewrite lt_eq_cases, ofnat_lt, ofnat_eq.
split.
destruct 1; subst; auto with arith.
apply Lt.le_lt_or_eq.
Qed.

End NZOfNatOrd.




Module NZOfNatOps (Import NZ:NZAxiomsSig').
Include NZOfNat NZ.
Local Open Scope ofnat.

Lemma ofnat_add_l : forall n m, [n]+m == (S^n) m.
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOps.ofnat_add_l".  
induction n; intros.
apply add_0_l.
rewrite ofnat_succ, add_succ_l. simpl. now f_equiv.
Qed.

Lemma ofnat_add : forall n m, [n+m] == [n]+[m].
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOps.ofnat_add".  
intros. rewrite ofnat_add_l.
induction n; simpl. reflexivity.
now f_equiv.
Qed.

Lemma ofnat_mul : forall n m, [n*m] == [n]*[m].
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOps.ofnat_mul".  
induction n; simpl; intros.
symmetry. apply mul_0_l.
rewrite plus_comm.
rewrite ofnat_add, mul_succ_l.
now f_equiv.
Qed.

Lemma ofnat_sub_r : forall n m, n-[m] == (P^m) n.
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOps.ofnat_sub_r".  
induction m; simpl; intros.
apply sub_0_r.
rewrite sub_succ_r. now f_equiv.
Qed.

Lemma ofnat_sub : forall n m, m<=n -> [n-m] == [n]-[m].
Proof. try hammer_hook "NZDomain" "NZDomain.NZOfNatOps.ofnat_sub".  
intros n m H. rewrite ofnat_sub_r.
revert n H. induction m. intros.
rewrite <- minus_n_O. now simpl.
intros.
destruct n.
inversion H.
rewrite nat_rect_succ_r.
simpl.
etransitivity. apply IHm. auto with arith.
eapply nat_rect_wd; [symmetry;apply pred_succ|apply pred_wd].
Qed.

End NZOfNatOps.
