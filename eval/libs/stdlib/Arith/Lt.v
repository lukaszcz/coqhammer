From Hammer Require Import Hammer.











Require Import PeanoNat.

Local Open Scope nat_scope.



Notation lt_irrefl := Nat.lt_irrefl (compat "8.4").

Hint Resolve lt_irrefl: arith.



Theorem lt_le_S n m : n < m -> S n <= m.
Proof. try hammer_hook "Lt" "Lt.lt_le_S".  
apply Nat.le_succ_l.
Qed.

Theorem lt_n_Sm_le n m : n < S m -> n <= m.
Proof. try hammer_hook "Lt" "Lt.lt_n_Sm_le".  
apply Nat.lt_succ_r.
Qed.

Theorem le_lt_n_Sm n m : n <= m -> n < S m.
Proof. try hammer_hook "Lt" "Lt.le_lt_n_Sm".  
apply Nat.lt_succ_r.
Qed.

Hint Immediate lt_le_S: arith.
Hint Immediate lt_n_Sm_le: arith.
Hint Immediate le_lt_n_Sm: arith.

Theorem le_not_lt n m : n <= m -> ~ m < n.
Proof. try hammer_hook "Lt" "Lt.le_not_lt".  
apply Nat.le_ngt.
Qed.

Theorem lt_not_le n m : n < m -> ~ m <= n.
Proof. try hammer_hook "Lt" "Lt.lt_not_le".  
apply Nat.lt_nge.
Qed.

Hint Immediate le_not_lt lt_not_le: arith.



Notation lt_asym := Nat.lt_asymm (compat "8.4").



Notation lt_0_Sn := Nat.lt_0_succ (compat "8.4").
Notation lt_n_0 := Nat.nlt_0_r (compat "8.4").

Theorem neq_0_lt n : 0 <> n -> 0 < n.
Proof. try hammer_hook "Lt" "Lt.neq_0_lt".  
intros. now apply Nat.neq_0_lt_0, Nat.neq_sym.
Qed.

Theorem lt_0_neq n : 0 < n -> 0 <> n.
Proof. try hammer_hook "Lt" "Lt.lt_0_neq".  
intros. now apply Nat.neq_sym, Nat.neq_0_lt_0.
Qed.

Hint Resolve lt_0_Sn lt_n_0 : arith.
Hint Immediate neq_0_lt lt_0_neq: arith.



Notation lt_n_Sn := Nat.lt_succ_diag_r (compat "8.4").
Notation lt_S := Nat.lt_lt_succ_r (compat "8.4").

Theorem lt_n_S n m : n < m -> S n < S m.
Proof. try hammer_hook "Lt" "Lt.lt_n_S".  
apply Nat.succ_lt_mono.
Qed.

Theorem lt_S_n n m : S n < S m -> n < m.
Proof. try hammer_hook "Lt" "Lt.lt_S_n".  
apply Nat.succ_lt_mono.
Qed.

Hint Resolve lt_n_Sn lt_S lt_n_S : arith.
Hint Immediate lt_S_n : arith.



Lemma S_pred n m : m < n -> n = S (pred n).
Proof. try hammer_hook "Lt" "Lt.S_pred".  
intros. symmetry. now apply Nat.lt_succ_pred with m.
Qed.

Lemma lt_pred n m : S n < m -> n < pred m.
Proof. try hammer_hook "Lt" "Lt.lt_pred".  
apply Nat.lt_succ_lt_pred.
Qed.

Lemma lt_pred_n_n n : 0 < n -> pred n < n.
Proof. try hammer_hook "Lt" "Lt.lt_pred_n_n".  
intros. now apply Nat.lt_pred_l, Nat.neq_0_lt_0.
Qed.

Hint Immediate lt_pred: arith.
Hint Resolve lt_pred_n_n: arith.



Notation lt_trans := Nat.lt_trans (compat "8.4").
Notation lt_le_trans := Nat.lt_le_trans (compat "8.4").
Notation le_lt_trans := Nat.le_lt_trans (compat "8.4").

Hint Resolve lt_trans lt_le_trans le_lt_trans: arith.



Notation le_lt_or_eq_iff := Nat.lt_eq_cases (compat "8.4").

Theorem le_lt_or_eq n m : n <= m -> n < m \/ n = m.
Proof. try hammer_hook "Lt" "Lt.le_lt_or_eq".  
apply Nat.lt_eq_cases.
Qed.

Notation lt_le_weak := Nat.lt_le_incl (compat "8.4").

Hint Immediate lt_le_weak: arith.



Notation le_or_lt := Nat.le_gt_cases (compat "8.4").

Theorem nat_total_order n m : n <> m -> n < m \/ m < n.
Proof. try hammer_hook "Lt" "Lt.nat_total_order".  
apply Nat.lt_gt_cases.
Qed.


Notation lt_O_Sn := lt_0_Sn (only parsing).
Notation neq_O_lt := neq_0_lt (only parsing).
Notation lt_O_neq := lt_0_neq (only parsing).
Notation lt_n_O := lt_n_0 (only parsing).




Require Import Le.
