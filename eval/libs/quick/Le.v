From Hammer Require Import Hammer.











Require Import PeanoNat.

Local Open Scope nat_scope.



Notation le_refl := Nat.le_refl.
Notation le_trans := Nat.le_trans.
Notation le_antisym := Nat.le_antisymm.

Hint Resolve le_trans: arith.
Hint Immediate le_antisym: arith.



Notation le_0_n := Nat.le_0_l.
Notation le_Sn_0 := Nat.nle_succ_0.

Lemma le_n_0_eq n : n <= 0 -> 0 = n.
Proof. try hammer_hook "Le" "Le.le_n_0_eq". Undo.
intros. symmetry. now apply Nat.le_0_r.
Qed.





Theorem le_n_S : forall n m, n <= m -> S n <= S m.
Proof. try hammer_hook "Le" "Le.le_n_S". Undo.  exact (Peano.le_n_S). Qed.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof. try hammer_hook "Le" "Le.le_S_n". Undo.  exact (Peano.le_S_n). Qed.

Notation le_n_Sn := Nat.le_succ_diag_r.
Notation le_Sn_n := Nat.nle_succ_diag_l.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof. try hammer_hook "Le" "Le.le_Sn_le". Undo.  exact (Nat.lt_le_incl). Qed.

Hint Resolve le_0_n le_Sn_0: arith.
Hint Resolve le_n_S le_n_Sn le_Sn_n : arith.
Hint Immediate le_n_0_eq le_Sn_le le_S_n : arith.



Notation le_pred_n := Nat.le_pred_l.
Notation le_pred := Nat.pred_le_mono.

Hint Resolve le_pred_n: arith.



Lemma le_elim_rel :
forall P:nat -> nat -> Prop,
(forall p, P 0 p) ->
(forall p (q:nat), p <= q -> P p q -> P (S p) (S q)) ->
forall n m, n <= m -> P n m.
Proof. try hammer_hook "Le" "Le.le_elim_rel". Undo.
intros P H0 HS.
induction n; trivial.
intros m Le. elim Le; auto with arith.
Qed.


Notation le_O_n := le_0_n (only parsing).
Notation le_Sn_O := le_Sn_0 (only parsing).
Notation le_n_O_eq := le_n_0_eq (only parsing).
