From Hammer Require Import Hammer.











Require Import PeanoNat.

Require Export Plus Minus Le Lt.

Local Open Scope nat_scope.





Notation mult_0_l := Nat.mul_0_l (compat "8.4").
Notation mult_0_r := Nat.mul_0_r (compat "8.4").



Notation mult_1_l := Nat.mul_1_l (compat "8.4").
Notation mult_1_r := Nat.mul_1_r (compat "8.4").

Hint Resolve mult_1_l mult_1_r: arith.



Notation mult_comm := Nat.mul_comm (compat "8.4").

Hint Resolve mult_comm: arith.



Notation mult_plus_distr_r :=
Nat.mul_add_distr_r (compat "8.4").

Notation mult_plus_distr_l :=
Nat.mul_add_distr_l (compat "8.4").

Notation mult_minus_distr_r :=
Nat.mul_sub_distr_r (compat "8.4").

Notation mult_minus_distr_l :=
Nat.mul_sub_distr_l (compat "8.4").

Hint Resolve mult_plus_distr_r: arith.
Hint Resolve mult_minus_distr_r: arith.
Hint Resolve mult_minus_distr_l: arith.



Notation mult_assoc := Nat.mul_assoc (compat "8.4").

Lemma mult_assoc_reverse n m p : n * m * p = n * (m * p).
Proof. try hammer_hook "Mult" "Mult.mult_assoc_reverse".  
symmetry. apply Nat.mul_assoc.
Qed.

Hint Resolve mult_assoc_reverse: arith.
Hint Resolve mult_assoc: arith.



Lemma mult_is_O n m : n * m = 0 -> n = 0 \/ m = 0.
Proof. try hammer_hook "Mult" "Mult.mult_is_O".  
apply Nat.eq_mul_0.
Qed.

Lemma mult_is_one n m : n * m = 1 -> n = 1 /\ m = 1.
Proof. try hammer_hook "Mult" "Mult.mult_is_one".  
apply Nat.eq_mul_1.
Qed.



Notation mult_succ_l := Nat.mul_succ_l (compat "8.4").
Notation mult_succ_r := Nat.mul_succ_r (compat "8.4").



Lemma mult_O_le n m : m = 0 \/ n <= m * n.
Proof. try hammer_hook "Mult" "Mult.mult_O_le".  
destruct m; [left|right]; simpl; trivial using Nat.le_add_r.
Qed.
Hint Resolve mult_O_le: arith.

Lemma mult_le_compat_l n m p : n <= m -> p * n <= p * m.
Proof. try hammer_hook "Mult" "Mult.mult_le_compat_l".  
apply Nat.mul_le_mono_nonneg_l, Nat.le_0_l.
Qed.
Hint Resolve mult_le_compat_l: arith.

Lemma mult_le_compat_r n m p : n <= m -> n * p <= m * p.
Proof. try hammer_hook "Mult" "Mult.mult_le_compat_r".  
apply Nat.mul_le_mono_nonneg_r, Nat.le_0_l.
Qed.

Lemma mult_le_compat n m p q : n <= m -> p <= q -> n * p <= m * q.
Proof. try hammer_hook "Mult" "Mult.mult_le_compat".  
intros. apply Nat.mul_le_mono_nonneg; trivial; apply Nat.le_0_l.
Qed.

Lemma mult_S_lt_compat_l n m p : m < p -> S n * m < S n * p.
Proof. try hammer_hook "Mult" "Mult.mult_S_lt_compat_l".  
apply Nat.mul_lt_mono_pos_l, Nat.lt_0_succ.
Qed.

Hint Resolve mult_S_lt_compat_l: arith.

Lemma mult_lt_compat_l n m p : n < m -> 0 < p -> p * n < p * m.
Proof. try hammer_hook "Mult" "Mult.mult_lt_compat_l".  
intros. now apply Nat.mul_lt_mono_pos_l.
Qed.

Lemma mult_lt_compat_r n m p : n < m -> 0 < p -> n * p < m * p.
Proof. try hammer_hook "Mult" "Mult.mult_lt_compat_r".  
intros. now apply Nat.mul_lt_mono_pos_r.
Qed.

Lemma mult_S_le_reg_l n m p : S n * m <= S n * p -> m <= p.
Proof. try hammer_hook "Mult" "Mult.mult_S_le_reg_l".  
apply Nat.mul_le_mono_pos_l, Nat.lt_0_succ.
Qed.



Theorem odd_even_lem p q : 2 * p + 1 <> 2 * q.
Proof. try hammer_hook "Mult" "Mult.odd_even_lem".  
intro. apply (Nat.Even_Odd_False (2*q)).
- now exists q.
- now exists p.
Qed.






Fixpoint mult_acc (s:nat) m n : nat :=
match n with
| O => s
| S p => mult_acc (tail_plus m s) m p
end.

Lemma mult_acc_aux : forall n m p, m + n * p = mult_acc m p n.
Proof. try hammer_hook "Mult" "Mult.mult_acc_aux".  
induction n as [| n IHn]; simpl; auto.
intros. rewrite Nat.add_assoc, IHn. f_equal.
rewrite Nat.add_comm. apply plus_tail_plus.
Qed.

Definition tail_mult n m := mult_acc 0 m n.

Lemma mult_tail_mult : forall n m, n * m = tail_mult n m.
Proof. try hammer_hook "Mult" "Mult.mult_tail_mult".  
intros; unfold tail_mult; rewrite <- mult_acc_aux; auto.
Qed.



Ltac tail_simpl :=
repeat rewrite <- plus_tail_plus; repeat rewrite <- mult_tail_mult;
simpl.
