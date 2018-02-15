From Hammer Require Import Hammer.









Require Import ZArith_base.
Require Export Wf_nat.
Require Import Omega.
Local Open Scope Z_scope.





Definition Zwf (c x y:Z) := c <= y /\ x < y.



Section wf_proof.

Variable c : Z.



Let f (z:Z) := Z.abs_nat (z - c).

Lemma Zwf_well_founded : well_founded (Zwf c).
red; intros.
assert (forall (n:nat) (a:Z), (f a < n)%nat \/ a < c -> Acc (Zwf c) a).
clear a; simple induction n; intros.

case H; intros.
case (lt_n_O (f a)); auto.
apply Acc_intro; unfold Zwf; intros.
assert False; omega || contradiction.

case H0; clear H0; intro; auto.
apply Acc_intro; intros.
apply H.
unfold Zwf in H1.
case (Z.le_gt_cases c y); intro; auto with zarith.
left.
red in H0.
apply lt_le_trans with (f a); auto with arith.
unfold f.
apply Zabs2Nat.inj_lt; omega.
apply (H (S (f a))); auto.
Qed.

End wf_proof.

Hint Resolve Zwf_well_founded: datatypes.




Definition Zwf_up (c x y:Z) := y < x <= c.



Section wf_proof_up.

Variable c : Z.



Let f (z:Z) := Z.abs_nat (c - z).

Lemma Zwf_up_well_founded : well_founded (Zwf_up c).
Proof. hammer_hook "Zwf" "Zwf.Zwf_up_well_founded". Restart. 
apply well_founded_lt_compat with (f := f).
unfold Zwf_up, f.
intros.
apply Zabs2Nat.inj_lt; try (apply Z.le_0_sub; intuition).
now apply Z.sub_lt_mono_l.
Qed.

End wf_proof_up.

Hint Resolve Zwf_up_well_founded: datatypes.
