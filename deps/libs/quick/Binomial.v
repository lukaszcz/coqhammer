From Hammer Require Import Hammer.









Require Import Rbase.
Require Import Rfunctions.
Require Import PartSum.
Local Open Scope R_scope.

Definition C (n p:nat) : R :=
INR (fact n) / (INR (fact p) * INR (fact (n - p))).

Lemma pascal_step1 : forall n i:nat, (i <= n)%nat -> C n i = C n (n - i).
Proof. hammer_hook "Binomial" "Binomial.pascal_step1".
intros; unfold C; replace (n - (n - i))%nat with i.
rewrite Rmult_comm.
reflexivity.
apply plus_minus; rewrite plus_comm; apply le_plus_minus; assumption.
Qed.

Lemma pascal_step2 :
forall n i:nat,
(i <= n)%nat -> C (S n) i = INR (S n) / INR (S n - i) * C n i.
Proof. hammer_hook "Binomial" "Binomial.pascal_step2".
intros; unfold C; replace (S n - i)%nat with (S (n - i)).
cut (forall n:nat, fact (S n) = (S n * fact n)%nat).
intro; repeat rewrite H0.
unfold Rdiv; repeat rewrite mult_INR; repeat rewrite Rinv_mult_distr.
ring.
apply INR_fact_neq_0.
apply INR_fact_neq_0.
apply not_O_INR; discriminate.
apply INR_fact_neq_0.
apply INR_fact_neq_0.
apply prod_neq_R0.
apply not_O_INR; discriminate.
apply INR_fact_neq_0.
intro; reflexivity.
apply minus_Sn_m; assumption.
Qed.

Lemma pascal_step3 :
forall n i:nat, (i < n)%nat -> C n (S i) = INR (n - i) / INR (S i) * C n i.
Proof. hammer_hook "Binomial" "Binomial.pascal_step3".
intros; unfold C.
cut (forall n:nat, fact (S n) = (S n * fact n)%nat).
intro.
cut ((n - i)%nat = S (n - S i)).
intro.
pattern (n - i)%nat at 2; rewrite H1.
repeat rewrite H0; unfold Rdiv; repeat rewrite mult_INR;
repeat rewrite Rinv_mult_distr.
rewrite <- H1; rewrite (Rmult_comm (/ INR (n - i)));
repeat rewrite Rmult_assoc; rewrite (Rmult_comm (INR (n - i)));
repeat rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
ring.
apply not_O_INR; apply minus_neq_O; assumption.
apply not_O_INR; discriminate.
apply INR_fact_neq_0.
apply INR_fact_neq_0.
apply prod_neq_R0; [ apply not_O_INR; discriminate | apply INR_fact_neq_0 ].
apply not_O_INR; discriminate.
apply INR_fact_neq_0.
apply prod_neq_R0; [ apply not_O_INR; discriminate | apply INR_fact_neq_0 ].
apply INR_fact_neq_0.
rewrite minus_Sn_m.
simpl; reflexivity.
apply lt_le_S; assumption.
intro; reflexivity.
Qed.


Lemma pascal :
forall n i:nat, (i < n)%nat -> C n i + C n (S i) = C (S n) (S i).
Proof. hammer_hook "Binomial" "Binomial.pascal".
intros.
rewrite pascal_step3; [ idtac | assumption ].
replace (C n i + INR (n - i) / INR (S i) * C n i) with
(C n i * (1 + INR (n - i) / INR (S i))); [ idtac | ring ].
replace (1 + INR (n - i) / INR (S i)) with (INR (S n) / INR (S i)).
rewrite pascal_step1.
rewrite Rmult_comm; replace (S i) with (S n - (n - i))%nat.
rewrite <- pascal_step2.
apply pascal_step1.
apply le_trans with n.
apply le_minusni_n.
apply lt_le_weak; assumption.
apply le_n_Sn.
apply le_minusni_n.
apply lt_le_weak; assumption.
rewrite <- minus_Sn_m.
cut ((n - (n - i))%nat = i).
intro; rewrite H0; reflexivity.
symmetry ; apply plus_minus.
rewrite plus_comm; rewrite le_plus_minus_r.
reflexivity.
apply lt_le_weak; assumption.
apply le_minusni_n; apply lt_le_weak; assumption.
apply lt_le_weak; assumption.
unfold Rdiv.
repeat rewrite S_INR.
rewrite minus_INR.
cut (INR i + 1 <> 0).
intro.
apply Rmult_eq_reg_l with (INR i + 1); [ idtac | assumption ].
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
do 2 rewrite (Rmult_comm (INR i + 1)).
repeat rewrite Rmult_assoc.
rewrite <- Rinv_l_sym; [ idtac | assumption ].
ring.
rewrite <- S_INR.
apply not_O_INR; discriminate.
apply lt_le_weak; assumption.
Qed.
