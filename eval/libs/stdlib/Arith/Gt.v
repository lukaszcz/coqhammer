From Hammer Require Import Hammer.











Require Import PeanoNat Le Lt Plus.
Local Open Scope nat_scope.



Theorem gt_Sn_O n : S n > 0.
Proof. try hammer_hook "Gt" "Gt.gt_Sn_O".  exact (Nat.lt_0_succ _). Qed.

Theorem gt_Sn_n n : S n > n.
Proof. try hammer_hook "Gt" "Gt.gt_Sn_n".  exact (Nat.lt_succ_diag_r _). Qed.

Theorem gt_n_S n m : n > m -> S n > S m.
Proof. try hammer_hook "Gt" "Gt.gt_n_S".  
apply Nat.succ_lt_mono.
Qed.

Lemma gt_S_n n m : S m > S n -> m > n.
Proof. try hammer_hook "Gt" "Gt.gt_S_n".  
apply Nat.succ_lt_mono.
Qed.

Theorem gt_S n m : S n > m -> n > m \/ m = n.
Proof. try hammer_hook "Gt" "Gt.gt_S".  
intro. now apply Nat.lt_eq_cases, Nat.succ_le_mono.
Qed.

Lemma gt_pred n m : m > S n -> pred m > n.
Proof. try hammer_hook "Gt" "Gt.gt_pred".  
apply Nat.lt_succ_lt_pred.
Qed.



Lemma gt_irrefl n : ~ n > n.
Proof. try hammer_hook "Gt" "Gt.gt_irrefl".  exact (Nat.lt_irrefl _). Qed.



Lemma gt_asym n m : n > m -> ~ m > n.
Proof. try hammer_hook "Gt" "Gt.gt_asym".  exact (Nat.lt_asymm _ _). Qed.



Lemma le_not_gt n m : n <= m -> ~ n > m.
Proof. try hammer_hook "Gt" "Gt.le_not_gt".  
apply Nat.le_ngt.
Qed.

Lemma gt_not_le n m : n > m -> ~ n <= m.
Proof. try hammer_hook "Gt" "Gt.gt_not_le".  
apply Nat.lt_nge.
Qed.

Theorem le_S_gt n m : S n <= m -> m > n.
Proof. try hammer_hook "Gt" "Gt.le_S_gt".  
apply Nat.le_succ_l.
Qed.

Lemma gt_S_le n m : S m > n -> n <= m.
Proof. try hammer_hook "Gt" "Gt.gt_S_le".  
apply Nat.succ_le_mono.
Qed.

Lemma gt_le_S n m : m > n -> S n <= m.
Proof. try hammer_hook "Gt" "Gt.gt_le_S".  
apply Nat.le_succ_l.
Qed.

Lemma le_gt_S n m : n <= m -> S m > n.
Proof. try hammer_hook "Gt" "Gt.le_gt_S".  
apply Nat.succ_le_mono.
Qed.



Theorem le_gt_trans n m p : m <= n -> m > p -> n > p.
Proof. try hammer_hook "Gt" "Gt.le_gt_trans".  
intros. now apply Nat.lt_le_trans with m.
Qed.

Theorem gt_le_trans n m p : n > m -> p <= m -> n > p.
Proof. try hammer_hook "Gt" "Gt.gt_le_trans".  
intros. now apply Nat.le_lt_trans with m.
Qed.

Lemma gt_trans n m p : n > m -> m > p -> n > p.
Proof. try hammer_hook "Gt" "Gt.gt_trans".  
intros. now apply Nat.lt_trans with m.
Qed.

Theorem gt_trans_S n m p : S n > m -> m > p -> n > p.
Proof. try hammer_hook "Gt" "Gt.gt_trans_S".  
intros. apply Nat.lt_le_trans with m; trivial. now apply Nat.succ_le_mono.
Qed.



Theorem gt_0_eq n : n > 0 \/ 0 = n.
Proof. try hammer_hook "Gt" "Gt.gt_0_eq".  
destruct n; [now right | left; apply Nat.lt_0_succ].
Qed.



Lemma plus_gt_reg_l n m p : p + n > p + m -> n > m.
Proof. try hammer_hook "Gt" "Gt.plus_gt_reg_l".  
apply Nat.add_lt_mono_l.
Qed.

Lemma plus_gt_compat_l n m p : n > m -> p + n > p + m.
Proof. try hammer_hook "Gt" "Gt.plus_gt_compat_l".  
apply Nat.add_lt_mono_l.
Qed.



Hint Resolve gt_Sn_O gt_Sn_n gt_n_S : arith.
Hint Immediate gt_S_n gt_pred : arith.
Hint Resolve gt_irrefl gt_asym : arith.
Hint Resolve le_not_gt gt_not_le : arith.
Hint Immediate le_S_gt gt_S_le : arith.
Hint Resolve gt_le_S le_gt_S : arith.
Hint Resolve gt_trans_S le_gt_trans gt_le_trans: arith.
Hint Resolve plus_gt_compat_l: arith.


Notation gt_O_eq := gt_0_eq (only parsing).

