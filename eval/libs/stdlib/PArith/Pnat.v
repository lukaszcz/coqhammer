From Hammer Require Import Hammer.










Require Import BinPos PeanoNat.





Local Open Scope positive_scope.
Local Open Scope nat_scope.

Module Pos2Nat.
Import Pos.



Lemma inj_succ p : to_nat (succ p) = S (to_nat p).
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_succ". Undo.  
unfold to_nat. rewrite iter_op_succ. trivial.
apply Nat.add_assoc.
Qed.

Theorem inj_add p q : to_nat (p + q) = to_nat p + to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_add". Undo.  
revert q. induction p using peano_ind; intros q.
now rewrite add_1_l, inj_succ.
now rewrite add_succ_l, !inj_succ, IHp.
Qed.

Theorem inj_mul p q : to_nat (p * q) = to_nat p * to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_mul". Undo.  
revert q. induction p using peano_ind; simpl; intros; trivial.
now rewrite mul_succ_l, inj_add, IHp, inj_succ.
Qed.



Lemma inj_1 : to_nat 1 = 1.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_1". Undo.  
reflexivity.
Qed.

Lemma inj_xO p : to_nat (xO p) = 2 * to_nat p.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_xO". Undo.  
exact (inj_mul 2 p).
Qed.

Lemma inj_xI p : to_nat (xI p) = S (2 * to_nat p).
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_xI". Undo.  
now rewrite xI_succ_xO, inj_succ, inj_xO.
Qed.



Lemma is_succ : forall p, exists n, to_nat p = S n.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.is_succ". Undo.  
induction p using peano_ind.
now exists 0.
destruct IHp as (n,Hn). exists (S n). now rewrite inj_succ, Hn.
Qed.



Lemma is_pos p : 0 < to_nat p.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.is_pos". Undo.  
destruct (is_succ p) as (n,->). auto with arith.
Qed.



Theorem id p : of_nat (to_nat p) = p.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.id". Undo.  
induction p using peano_ind. trivial.
rewrite inj_succ. rewrite <- IHp at 2.
now destruct (is_succ p) as (n,->).
Qed.



Lemma inj p q : to_nat p = to_nat q -> p = q.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj". Undo.  
intros H. now rewrite <- (id p), <- (id q), H.
Qed.

Lemma inj_iff p q : to_nat p = to_nat q <-> p = q.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_iff". Undo.  
split. apply inj. intros; now subst.
Qed.



Lemma inj_compare p q : (p ?= q)%positive = (to_nat p ?= to_nat q).
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_compare". Undo.  
revert q. induction p as [ |p IH] using peano_ind; intros q.
- destruct (succ_pred_or q) as [Hq|Hq]; [now subst|].
rewrite <- Hq, lt_1_succ, inj_succ, inj_1, Nat.compare_succ.
symmetry. apply Nat.compare_lt_iff, is_pos.
- destruct (succ_pred_or q) as [Hq|Hq]; [subst|].
rewrite compare_antisym, lt_1_succ, inj_succ. simpl.
symmetry. apply Nat.compare_gt_iff, is_pos.
now rewrite <- Hq, 2 inj_succ, compare_succ_succ, IH.
Qed.



Lemma inj_lt p q : (p < q)%positive <-> to_nat p < to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_lt". Undo.  
unfold lt. now rewrite inj_compare, Nat.compare_lt_iff.
Qed.

Lemma inj_le p q : (p <= q)%positive <-> to_nat p <= to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_le". Undo.  
unfold le. now rewrite inj_compare, Nat.compare_le_iff.
Qed.

Lemma inj_gt p q : (p > q)%positive <-> to_nat p > to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_gt". Undo.  
unfold gt. now rewrite inj_compare, Nat.compare_gt_iff.
Qed.

Lemma inj_ge p q : (p >= q)%positive <-> to_nat p >= to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_ge". Undo.  
unfold ge. now rewrite inj_compare, Nat.compare_ge_iff.
Qed.



Theorem inj_sub p q : (q < p)%positive ->
to_nat (p - q) = to_nat p - to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_sub". Undo.  
intro H. apply Nat.add_cancel_r with (to_nat q).
rewrite Nat.sub_add.
now rewrite <- inj_add, sub_add.
now apply Nat.lt_le_incl, inj_lt.
Qed.

Theorem inj_sub_max p q :
to_nat (p - q) = Nat.max 1 (to_nat p - to_nat q).
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_sub_max". Undo.  
destruct (ltb_spec q p).
-
rewrite <- inj_sub by trivial.
now destruct (is_succ (p - q)) as (m,->).
-
rewrite sub_le by trivial.
apply inj_le, Nat.sub_0_le in H. now rewrite H.
Qed.

Theorem inj_pred p : (1 < p)%positive ->
to_nat (pred p) = Nat.pred (to_nat p).
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_pred". Undo.  
intros. now rewrite <- Pos.sub_1_r, inj_sub, Nat.sub_1_r.
Qed.

Theorem inj_pred_max p :
to_nat (pred p) = Nat.max 1 (Peano.pred (to_nat p)).
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_pred_max". Undo.  
rewrite <- Pos.sub_1_r, <- Nat.sub_1_r. apply inj_sub_max.
Qed.



Lemma inj_min p q :
to_nat (min p q) = Nat.min (to_nat p) (to_nat q).
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_min". Undo.  
unfold min. rewrite inj_compare.
case Nat.compare_spec; intros H; symmetry.
- apply Nat.min_l. now rewrite H.
- now apply Nat.min_l, Nat.lt_le_incl.
- now apply Nat.min_r, Nat.lt_le_incl.
Qed.

Lemma inj_max p q :
to_nat (max p q) = Nat.max (to_nat p) (to_nat q).
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_max". Undo.  
unfold max. rewrite inj_compare.
case Nat.compare_spec; intros H; symmetry.
- apply Nat.max_r. now rewrite H.
- now apply Nat.max_r, Nat.lt_le_incl.
- now apply Nat.max_l, Nat.lt_le_incl.
Qed.

Theorem inj_iter :
forall p {A} (f:A->A) (x:A),
Pos.iter f x p = nat_rect _ x (fun _ => f) (to_nat p).
Proof. try hammer_hook "Pnat" "Pnat.Pos2Nat.inj_iter". Undo.  
induction p using peano_ind.
- trivial.
- intros. rewrite inj_succ, iter_succ.
simpl. f_equal. apply IHp.
Qed.

End Pos2Nat.

Module Nat2Pos.



Theorem id (n:nat) : n<>0 -> Pos.to_nat (Pos.of_nat n) = n.
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.id". Undo.  
induction n as [|n H]; trivial. now destruct 1.
intros _. simpl Pos.of_nat. destruct n. trivial.
rewrite Pos2Nat.inj_succ. f_equal. now apply H.
Qed.

Theorem id_max (n:nat) : Pos.to_nat (Pos.of_nat n) = max 1 n.
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.id_max". Undo.  
destruct n. trivial. now rewrite id.
Qed.



Lemma inj (n m : nat) : n<>0 -> m<>0 -> Pos.of_nat n = Pos.of_nat m -> n = m.
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj". Undo.  
intros Hn Hm H. now rewrite <- (id n), <- (id m), H.
Qed.

Lemma inj_iff (n m : nat) : n<>0 -> m<>0 ->
(Pos.of_nat n = Pos.of_nat m <-> n = m).
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj_iff". Undo.  
split. now apply inj. intros; now subst.
Qed.



Lemma inj_succ (n:nat) : n<>0 -> Pos.of_nat (S n) = Pos.succ (Pos.of_nat n).
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj_succ". Undo.  
intro H. apply Pos2Nat.inj. now rewrite Pos2Nat.inj_succ, !id.
Qed.

Lemma inj_pred (n:nat) : Pos.of_nat (pred n) = Pos.pred (Pos.of_nat n).
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj_pred". Undo.  
destruct n as [|[|n]]; trivial. simpl. now rewrite Pos.pred_succ.
Qed.

Lemma inj_add (n m : nat) : n<>0 -> m<>0 ->
Pos.of_nat (n+m) = (Pos.of_nat n + Pos.of_nat m)%positive.
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj_add". Undo.  
intros Hn Hm. apply Pos2Nat.inj.
rewrite Pos2Nat.inj_add, !id; trivial.
intros H. destruct n. now destruct Hn. now simpl in H.
Qed.

Lemma inj_mul (n m : nat) : n<>0 -> m<>0 ->
Pos.of_nat (n*m) = (Pos.of_nat n * Pos.of_nat m)%positive.
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj_mul". Undo.  
intros Hn Hm. apply Pos2Nat.inj.
rewrite Pos2Nat.inj_mul, !id; trivial.
intros H. apply Nat.mul_eq_0 in H. destruct H. now elim Hn. now elim Hm.
Qed.

Lemma inj_compare (n m : nat) : n<>0 -> m<>0 ->
(n ?= m) = (Pos.of_nat n ?= Pos.of_nat m)%positive.
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj_compare". Undo.  
intros Hn Hm. rewrite Pos2Nat.inj_compare, !id; trivial.
Qed.

Lemma inj_sub (n m : nat) : m<>0 ->
Pos.of_nat (n-m) = (Pos.of_nat n - Pos.of_nat m)%positive.
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj_sub". Undo.  
intros Hm.
apply Pos2Nat.inj.
rewrite Pos2Nat.inj_sub_max.
rewrite (id m) by trivial. rewrite !id_max.
destruct n, m; trivial.
Qed.

Lemma inj_min (n m : nat) :
Pos.of_nat (min n m) = Pos.min (Pos.of_nat n) (Pos.of_nat m).
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj_min". Undo.  
destruct n as [|n]. simpl. symmetry. apply Pos.min_l, Pos.le_1_l.
destruct m as [|m]. simpl. symmetry. apply Pos.min_r, Pos.le_1_l.
unfold Pos.min. rewrite <- inj_compare by easy.
case Nat.compare_spec; intros H; f_equal;
apply Nat.min_l || apply Nat.min_r.
rewrite H; auto. now apply Nat.lt_le_incl. now apply Nat.lt_le_incl.
Qed.

Lemma inj_max (n m : nat) :
Pos.of_nat (max n m) = Pos.max (Pos.of_nat n) (Pos.of_nat m).
Proof. try hammer_hook "Pnat" "Pnat.Nat2Pos.inj_max". Undo.  
destruct n as [|n]. simpl. symmetry. apply Pos.max_r, Pos.le_1_l.
destruct m as [|m]. simpl. symmetry. apply Pos.max_l, Pos.le_1_l.
unfold Pos.max. rewrite <- inj_compare by easy.
case Nat.compare_spec; intros H; f_equal;
apply Nat.max_l || apply Nat.max_r.
rewrite H; auto. now apply Nat.lt_le_incl. now apply Nat.lt_le_incl.
Qed.

End Nat2Pos.




Module Pos2SuccNat.



Theorem id_succ p : Pos.of_succ_nat (Pos.to_nat p) = Pos.succ p.
Proof. try hammer_hook "Pnat" "Pnat.Pos2SuccNat.id_succ". Undo.  
rewrite Pos.of_nat_succ, <- Pos2Nat.inj_succ. apply Pos2Nat.id.
Qed.



Theorem pred_id p : Pos.pred (Pos.of_succ_nat (Pos.to_nat p)) = p.
Proof. try hammer_hook "Pnat" "Pnat.Pos2SuccNat.pred_id". Undo.  
now rewrite id_succ, Pos.pred_succ.
Qed.

End Pos2SuccNat.

Module SuccNat2Pos.



Theorem id_succ (n:nat) : Pos.to_nat (Pos.of_succ_nat n) = S n.
Proof. try hammer_hook "Pnat" "Pnat.SuccNat2Pos.id_succ". Undo.  
rewrite Pos.of_nat_succ. now apply Nat2Pos.id.
Qed.

Theorem pred_id (n:nat) : pred (Pos.to_nat (Pos.of_succ_nat n)) = n.
Proof. try hammer_hook "Pnat" "Pnat.SuccNat2Pos.pred_id". Undo.  
now rewrite id_succ.
Qed.



Lemma inj (n m : nat) : Pos.of_succ_nat n = Pos.of_succ_nat m -> n = m.
Proof. try hammer_hook "Pnat" "Pnat.SuccNat2Pos.inj". Undo.  
intro H. apply (f_equal Pos.to_nat) in H. rewrite !id_succ in H.
now injection H.
Qed.

Lemma inj_iff (n m : nat) : Pos.of_succ_nat n = Pos.of_succ_nat m <-> n = m.
Proof. try hammer_hook "Pnat" "Pnat.SuccNat2Pos.inj_iff". Undo.  
split. apply inj. intros; now subst.
Qed.



Theorem inv n p : Pos.to_nat p = S n -> Pos.of_succ_nat n = p.
Proof. try hammer_hook "Pnat" "Pnat.SuccNat2Pos.inv". Undo.  
intros H. apply Pos2Nat.inj. now rewrite id_succ.
Qed.



Lemma inj_succ n : Pos.of_succ_nat (S n) = Pos.succ (Pos.of_succ_nat n).
Proof. try hammer_hook "Pnat" "Pnat.SuccNat2Pos.inj_succ". Undo.  
apply Pos2Nat.inj. now rewrite Pos2Nat.inj_succ, !id_succ.
Qed.

Lemma inj_compare n m :
(n ?= m) = (Pos.of_succ_nat n ?= Pos.of_succ_nat m)%positive.
Proof. try hammer_hook "Pnat" "Pnat.SuccNat2Pos.inj_compare". Undo.  
rewrite Pos2Nat.inj_compare, !id_succ; trivial.
Qed.



End SuccNat2Pos.



Notation Psucc_S := Pos2Nat.inj_succ (compat "8.3").
Notation Pplus_plus := Pos2Nat.inj_add (compat "8.3").
Notation Pmult_mult := Pos2Nat.inj_mul (compat "8.3").
Notation Pcompare_nat_compare := Pos2Nat.inj_compare (compat "8.3").
Notation nat_of_P_xH := Pos2Nat.inj_1 (compat "8.3").
Notation nat_of_P_xO := Pos2Nat.inj_xO (compat "8.3").
Notation nat_of_P_xI := Pos2Nat.inj_xI (compat "8.3").
Notation nat_of_P_is_S := Pos2Nat.is_succ (compat "8.3").
Notation nat_of_P_pos := Pos2Nat.is_pos (compat "8.3").
Notation nat_of_P_inj_iff := Pos2Nat.inj_iff (compat "8.3").
Notation nat_of_P_inj := Pos2Nat.inj (compat "8.3").
Notation Plt_lt := Pos2Nat.inj_lt (compat "8.3").
Notation Pgt_gt := Pos2Nat.inj_gt (compat "8.3").
Notation Ple_le := Pos2Nat.inj_le (compat "8.3").
Notation Pge_ge := Pos2Nat.inj_ge (compat "8.3").
Notation Pminus_minus := Pos2Nat.inj_sub (compat "8.3").
Notation iter_nat_of_P := @Pos2Nat.inj_iter (compat "8.3").

Notation nat_of_P_of_succ_nat := SuccNat2Pos.id_succ (compat "8.3").
Notation P_of_succ_nat_of_P := Pos2SuccNat.id_succ (compat "8.3").

Notation nat_of_P_succ_morphism := Pos2Nat.inj_succ (compat "8.3").
Notation nat_of_P_plus_morphism := Pos2Nat.inj_add (compat "8.3").
Notation nat_of_P_mult_morphism := Pos2Nat.inj_mul (compat "8.3").
Notation nat_of_P_compare_morphism := Pos2Nat.inj_compare (compat "8.3").
Notation lt_O_nat_of_P := Pos2Nat.is_pos (compat "8.3").
Notation ZL4 := Pos2Nat.is_succ (compat "8.3").
Notation nat_of_P_o_P_of_succ_nat_eq_succ := SuccNat2Pos.id_succ (compat "8.3").
Notation P_of_succ_nat_o_nat_of_P_eq_succ := Pos2SuccNat.id_succ (compat "8.3").
Notation pred_o_P_of_succ_nat_o_nat_of_P_eq_id := Pos2SuccNat.pred_id (compat "8.3").

Lemma nat_of_P_minus_morphism p q :
Pos.compare_cont Eq p q = Gt ->
Pos.to_nat (p - q) = Pos.to_nat p - Pos.to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.nat_of_P_minus_morphism". Undo.  exact ((fun H => Pos2Nat.inj_sub p q (Pos.gt_lt _ _ H))). Qed.

Lemma nat_of_P_lt_Lt_compare_morphism p q :
Pos.compare_cont Eq p q = Lt -> Pos.to_nat p < Pos.to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.nat_of_P_lt_Lt_compare_morphism". Undo.  exact ((proj1 (Pos2Nat.inj_lt p q))). Qed.

Lemma nat_of_P_gt_Gt_compare_morphism p q :
Pos.compare_cont Eq p q = Gt -> Pos.to_nat p > Pos.to_nat q.
Proof. try hammer_hook "Pnat" "Pnat.nat_of_P_gt_Gt_compare_morphism". Undo.  exact ((proj1 (Pos2Nat.inj_gt p q))). Qed.

Lemma nat_of_P_lt_Lt_compare_complement_morphism p q :
Pos.to_nat p < Pos.to_nat q -> Pos.compare_cont Eq p q = Lt.
Proof. try hammer_hook "Pnat" "Pnat.nat_of_P_lt_Lt_compare_complement_morphism". Undo.  exact ((proj2 (Pos2Nat.inj_lt p q))). Qed.

Definition nat_of_P_gt_Gt_compare_complement_morphism p q :
Pos.to_nat p > Pos.to_nat q -> Pos.compare_cont Eq p q = Gt.
Proof. try hammer_hook "Pnat" "Pnat.nat_of_P_gt_Gt_compare_complement_morphism". Undo.  exact ((proj2 (Pos2Nat.inj_gt p q))). Qed.



Section ObsoletePmultNat.

Lemma Pmult_nat_mult : forall p n,
Pmult_nat p n = Pos.to_nat p * n.
Proof. try hammer_hook "Pnat" "Pnat.Pmult_nat_mult". Undo.  
induction p; intros n; unfold Pos.to_nat; simpl.
f_equal. rewrite 2 IHp. rewrite <- Nat.mul_assoc.
f_equal. simpl. now rewrite Nat.add_0_r.
rewrite 2 IHp. rewrite <- Nat.mul_assoc.
f_equal. simpl. now rewrite Nat.add_0_r.
simpl. now rewrite Nat.add_0_r.
Qed.

Lemma Pmult_nat_succ_morphism :
forall p n, Pmult_nat (Pos.succ p) n = n + Pmult_nat p n.
Proof. try hammer_hook "Pnat" "Pnat.Pmult_nat_succ_morphism". Undo.  
intros. now rewrite !Pmult_nat_mult, Pos2Nat.inj_succ.
Qed.

Theorem Pmult_nat_l_plus_morphism :
forall p q n, Pmult_nat (p + q) n = Pmult_nat p n + Pmult_nat q n.
Proof. try hammer_hook "Pnat" "Pnat.Pmult_nat_l_plus_morphism". Undo.  
intros. rewrite !Pmult_nat_mult, Pos2Nat.inj_add. apply Nat.mul_add_distr_r.
Qed.

Theorem Pmult_nat_plus_carry_morphism :
forall p q n, Pmult_nat (Pos.add_carry p q) n = n + Pmult_nat (p + q) n.
Proof. try hammer_hook "Pnat" "Pnat.Pmult_nat_plus_carry_morphism". Undo.  
intros. now rewrite Pos.add_carry_spec, Pmult_nat_succ_morphism.
Qed.

Lemma Pmult_nat_r_plus_morphism :
forall p n, Pmult_nat p (n + n) = Pmult_nat p n + Pmult_nat p n.
Proof. try hammer_hook "Pnat" "Pnat.Pmult_nat_r_plus_morphism". Undo.  
intros. rewrite !Pmult_nat_mult. apply Nat.mul_add_distr_l.
Qed.

Lemma ZL6 : forall p, Pmult_nat p 2 = Pos.to_nat p + Pos.to_nat p.
Proof. try hammer_hook "Pnat" "Pnat.ZL6". Undo.  
intros. rewrite Pmult_nat_mult, Nat.mul_comm. simpl. now rewrite Nat.add_0_r.
Qed.

Lemma le_Pmult_nat : forall p n, n <= Pmult_nat p n.
Proof. try hammer_hook "Pnat" "Pnat.le_Pmult_nat". Undo.  
intros. rewrite Pmult_nat_mult.
apply Nat.le_trans with (1*n). now rewrite Nat.mul_1_l.
apply Nat.mul_le_mono_r. apply Pos2Nat.is_pos.
Qed.

End ObsoletePmultNat.
