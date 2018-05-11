From Hammer Require Import Hammer.











Local Open Scope nat_scope.

Notation not_eq_sym := not_eq_sym (only parsing).

Implicit Types m n p q : nat.

Require Import Arith_base.
Require Import Peano_dec.
Require Import Compare_dec.

Definition le_or_le_S := le_le_S_dec.

Definition Pcompare := gt_eq_gt_dec.

Lemma le_dec : forall n m, {n <= m} + {m <= n}.
Proof. try hammer_hook "Compare" "Compare.le_dec".  exact (le_ge_dec). Qed.

Definition lt_or_eq n m := {m > n} + {n = m}.

Lemma le_decide : forall n m, n <= m -> lt_or_eq n m.
Proof. try hammer_hook "Compare" "Compare.le_decide".  exact (le_lt_eq_dec). Qed.

Lemma le_le_S_eq : forall n m, n <= m -> S n <= m \/ n = m.
Proof. try hammer_hook "Compare" "Compare.le_le_S_eq".  exact (le_lt_or_eq). Qed.


Lemma discrete_nat :
forall n m, n < m -> S n = m \/ (exists r : nat, m = S (S (n + r))).
Proof. try hammer_hook "Compare" "Compare.discrete_nat".  
intros m n H.
lapply (lt_le_S m n); auto with arith.
intro H'; lapply (le_lt_or_eq (S m) n); auto with arith.
induction 1; auto with arith.
right; exists (n - S (S m)); simpl.
rewrite (plus_comm m (n - S (S m))).
rewrite (plus_n_Sm (n - S (S m)) m).
rewrite (plus_n_Sm (n - S (S m)) (S m)).
rewrite (plus_comm (n - S (S m)) (S (S m))); auto with arith.
Qed.

Require Export Wf_nat.

Require Export Min Max.
