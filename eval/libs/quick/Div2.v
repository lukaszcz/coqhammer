From Hammer Require Import Hammer.











Require Import PeanoNat Even.

Local Open Scope nat_scope.

Implicit Type n : nat.



Notation div2 := Nat.div2.



Lemma ind_0_1_SS :
forall P:nat -> Prop,
P 0 -> P 1 -> (forall n, P n -> P (S (S n))) -> forall n, P n.
Proof. try hammer_hook "Div2" "Div2.ind_0_1_SS". Undo.
intros P H0 H1 H2.
fix 1.
destruct n as [|[|n]].
- exact H0.
- exact H1.
- apply H2, ind_0_1_SS.
Qed.



Lemma lt_div2 n : 0 < n -> div2 n < n.
Proof. try hammer_hook "Div2" "Div2.lt_div2". Undo.   apply Nat.lt_div2. Qed.

Hint Resolve lt_div2: arith.



Lemma even_div2 n : even n -> div2 n = div2 (S n).
Proof. try hammer_hook "Div2" "Div2.even_div2". Undo.
rewrite Even.even_equiv. intros (p,->).
rewrite Nat.div2_succ_double. apply Nat.div2_double.
Qed.

Lemma odd_div2 n : odd n -> S (div2 n) = div2 (S n).
Proof. try hammer_hook "Div2" "Div2.odd_div2". Undo.
rewrite Even.odd_equiv. intros (p,->).
rewrite Nat.add_1_r, Nat.div2_succ_double.
simpl. f_equal. symmetry. apply Nat.div2_double.
Qed.

Lemma div2_even n : div2 n = div2 (S n) -> even n.
Proof. try hammer_hook "Div2" "Div2.div2_even". Undo.
destruct (even_or_odd n) as [Ev|Od]; trivial.
apply odd_div2 in Od. rewrite <- Od. intro Od'.
elim (n_Sn _ Od').
Qed.

Lemma div2_odd n : S (div2 n) = div2 (S n) -> odd n.
Proof. try hammer_hook "Div2" "Div2.div2_odd". Undo.
destruct (even_or_odd n) as [Ev|Od]; trivial.
apply even_div2 in Ev. rewrite <- Ev. intro Ev'.
symmetry in Ev'. elim (n_Sn _ Ev').
Qed.

Hint Resolve even_div2 div2_even odd_div2 div2_odd: arith.

Lemma even_odd_div2 n :
(even n <-> div2 n = div2 (S n)) /\
(odd n <-> S (div2 n) = div2 (S n)).
Proof. try hammer_hook "Div2" "Div2.even_odd_div2". Undo.
split; split; auto using div2_odd, div2_even, odd_div2, even_div2.
Qed.





Notation double := Nat.double.

Hint Unfold double Nat.double: arith.

Lemma double_S n : double (S n) = S (S (double n)).
Proof. try hammer_hook "Div2" "Div2.double_S". Undo.
apply Nat.add_succ_r.
Qed.

Lemma double_plus n m : double (n + m) = double n + double m.
Proof. try hammer_hook "Div2" "Div2.double_plus". Undo.
apply Nat.add_shuffle1.
Qed.

Hint Resolve double_S: arith.

Lemma even_odd_double n :
(even n <-> n = double (div2 n)) /\ (odd n <-> n = S (double (div2 n))).
Proof. try hammer_hook "Div2" "Div2.even_odd_double". Undo.
revert n. fix 1. destruct n as [|[|n]].
-
split; split; auto with arith. inversion 1.
-
split; split; auto with arith. inversion_clear 1. inversion H0.
-
destruct (even_odd_double n) as ((Ev,Ev'),(Od,Od')).
split; split; simpl div2; rewrite ?double_S.
+ inversion_clear 1. inversion_clear H0. auto.
+ injection 1. auto with arith.
+ inversion_clear 1. inversion_clear H0. auto.
+ injection 1. auto with arith.
Qed.



Lemma even_double n : even n -> n = double (div2 n).
Proof. try hammer_hook "Div2" "Div2.even_double". Undo.  exact (proj1 (proj1 (even_odd_double n))). Qed.

Lemma double_even n : n = double (div2 n) -> even n.
Proof. try hammer_hook "Div2" "Div2.double_even". Undo.  exact (proj2 (proj1 (even_odd_double n))). Qed.

Lemma odd_double n : odd n -> n = S (double (div2 n)).
Proof. try hammer_hook "Div2" "Div2.odd_double". Undo.  exact (proj1 (proj2 (even_odd_double n))). Qed.

Lemma double_odd n : n = S (double (div2 n)) -> odd n.
Proof. try hammer_hook "Div2" "Div2.double_odd". Undo.  exact (proj2 (proj2 (even_odd_double n))). Qed.

Hint Resolve even_double double_even odd_double double_odd: arith.



Lemma even_2n : forall n, even n -> {p : nat | n = double p}.
Proof. try hammer_hook "Div2" "Div2.even_2n". Undo.
intros n H. exists (div2 n). auto with arith.
Defined.

Lemma odd_S2n : forall n, odd n -> {p : nat | n = S (double p)}.
Proof. try hammer_hook "Div2" "Div2.odd_S2n". Undo.
intros n H. exists (div2 n). auto with arith.
Defined.



Lemma div2_double n : div2 (2*n) = n.
Proof. try hammer_hook "Div2" "Div2.div2_double". Undo.   apply Nat.div2_double. Qed.

Lemma div2_double_plus_one n : div2 (S (2*n)) = n.
Proof. try hammer_hook "Div2" "Div2.div2_double_plus_one". Undo.   apply Nat.div2_succ_double. Qed.
