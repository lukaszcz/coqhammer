From Hammer Require Import Hammer.











Require Import PeanoNat.

Local Open Scope nat_scope.



Notation plus_0_l := Nat.add_0_l (compat "8.4").
Notation plus_0_r := Nat.add_0_r (compat "8.4").
Notation plus_comm := Nat.add_comm (compat "8.4").
Notation plus_assoc := Nat.add_assoc (compat "8.4").

Notation plus_permute := Nat.add_shuffle3 (compat "8.4").

Definition plus_Snm_nSm : forall n m, S n + m = n + S m :=
Peano.plus_n_Sm.

Lemma plus_assoc_reverse n m p : n + m + p = n + (m + p).
Proof. hammer_hook "Plus" "Plus.plus_assoc_reverse". Restart. 
symmetry. apply Nat.add_assoc.
Qed.



Lemma plus_reg_l n m p : p + n = p + m -> n = m.
Proof. hammer_hook "Plus" "Plus.plus_reg_l". Restart. 
apply Nat.add_cancel_l.
Qed.

Lemma plus_le_reg_l n m p : p + n <= p + m -> n <= m.
Proof. hammer_hook "Plus" "Plus.plus_le_reg_l". Restart. 
apply Nat.add_le_mono_l.
Qed.

Lemma plus_lt_reg_l n m p : p + n < p + m -> n < m.
Proof. hammer_hook "Plus" "Plus.plus_lt_reg_l". Restart. 
apply Nat.add_lt_mono_l.
Qed.



Lemma plus_le_compat_l n m p : n <= m -> p + n <= p + m.
Proof. hammer_hook "Plus" "Plus.plus_le_compat_l". Restart. 
apply Nat.add_le_mono_l.
Qed.

Lemma plus_le_compat_r n m p : n <= m -> n + p <= m + p.
Proof. hammer_hook "Plus" "Plus.plus_le_compat_r". Restart. 
apply Nat.add_le_mono_r.
Qed.

Lemma plus_lt_compat_l n m p : n < m -> p + n < p + m.
Proof. hammer_hook "Plus" "Plus.plus_lt_compat_l". Restart. 
apply Nat.add_lt_mono_l.
Qed.

Lemma plus_lt_compat_r n m p : n < m -> n + p < m + p.
Proof. hammer_hook "Plus" "Plus.plus_lt_compat_r". Restart. 
apply Nat.add_lt_mono_r.
Qed.

Lemma plus_le_compat n m p q : n <= m -> p <= q -> n + p <= m + q.
Proof. hammer_hook "Plus" "Plus.plus_le_compat". Restart. 
apply Nat.add_le_mono.
Qed.

Lemma plus_le_lt_compat n m p q : n <= m -> p < q -> n + p < m + q.
Proof. hammer_hook "Plus" "Plus.plus_le_lt_compat". Restart. 
apply Nat.add_le_lt_mono.
Qed.

Lemma plus_lt_le_compat n m p q : n < m -> p <= q -> n + p < m + q.
Proof. hammer_hook "Plus" "Plus.plus_lt_le_compat". Restart. 
apply Nat.add_lt_le_mono.
Qed.

Lemma plus_lt_compat n m p q : n < m -> p < q -> n + p < m + q.
Proof. hammer_hook "Plus" "Plus.plus_lt_compat". Restart. 
apply Nat.add_lt_mono.
Qed.

Lemma le_plus_l n m : n <= n + m.
Proof. hammer_hook "Plus" "Plus.le_plus_l". Restart. 
apply Nat.le_add_r.
Qed.

Lemma le_plus_r n m : m <= n + m.
Proof. hammer_hook "Plus" "Plus.le_plus_r". Restart. 
rewrite Nat.add_comm. apply Nat.le_add_r.
Qed.

Theorem le_plus_trans n m p : n <= m -> n <= m + p.
Proof. hammer_hook "Plus" "Plus.le_plus_trans". Restart. 
intros. now rewrite <- Nat.le_add_r.
Qed.

Theorem lt_plus_trans n m p : n < m -> n < m + p.
Proof. hammer_hook "Plus" "Plus.lt_plus_trans". Restart. 
intros. apply Nat.lt_le_trans with m. trivial. apply Nat.le_add_r.
Qed.



Lemma plus_is_O n m : n + m = 0 -> n = 0 /\ m = 0.
Proof. hammer_hook "Plus" "Plus.plus_is_O". Restart. 
destruct n; now split.
Qed.

Definition plus_is_one m n :
m + n = 1 -> {m = 0 /\ n = 1} + {m = 1 /\ n = 0}.
Proof. hammer_hook "Plus" "Plus.plus_is_one". Restart. 
destruct m as [| m]; auto.
destruct m; auto.
discriminate.
Defined.



Notation plus_permute_2_in_4 := Nat.add_shuffle1 (compat "8.4").





Fixpoint tail_plus n m : nat :=
match n with
| O => m
| S n => tail_plus n (S m)
end.

Lemma plus_tail_plus : forall n m, n + m = tail_plus n m.
Proof. hammer_hook "Plus" "Plus.plus_tail_plus". Restart. 
induction n as [| n IHn]; simpl; auto.
intro m; rewrite <- IHn; simpl; auto.
Qed.



Lemma succ_plus_discr n m : n <> S (m+n).
Proof. hammer_hook "Plus" "Plus.succ_plus_discr". Restart. 
apply Nat.succ_add_discr.
Qed.

Lemma n_SSn n : n <> S (S n).
Proof. hammer_hook "Plus" "Plus.n_SSn". Restart. exact ((succ_plus_discr n 1)). Qed.

Lemma n_SSSn n : n <> S (S (S n)).
Proof. hammer_hook "Plus" "Plus.n_SSSn". Restart. exact ((succ_plus_discr n 2)). Qed.

Lemma n_SSSSn n : n <> S (S (S (S n))).
Proof. hammer_hook "Plus" "Plus.n_SSSSn". Restart. exact ((succ_plus_discr n 3)). Qed.




Hint Immediate plus_comm : arith.
Hint Resolve plus_assoc plus_assoc_reverse : arith.
Hint Resolve plus_le_compat_l plus_le_compat_r : arith.
Hint Resolve le_plus_l le_plus_r le_plus_trans : arith.
Hint Immediate lt_plus_trans : arith.
Hint Resolve plus_lt_compat_l plus_lt_compat_r : arith.



Require Import Le Lt.
