From Hammer Require Import Hammer.











Require Export ZAddOrder.

Module Type ZMulOrderProp (Import Z : ZAxiomsMiniSig').
Include ZAddOrderProp Z.

Theorem mul_lt_mono_nonpos :
forall n m p q, m <= 0 -> n < m -> q <= 0 -> p < q ->  m * q < n * p.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.mul_lt_mono_nonpos". Undo.  
intros n m p q H1 H2 H3 H4.
apply le_lt_trans with (m * p).
apply mul_le_mono_nonpos_l; [assumption | now apply lt_le_incl].
apply -> mul_lt_mono_neg_r; [assumption | now apply lt_le_trans with q].
Qed.

Theorem mul_le_mono_nonpos :
forall n m p q, m <= 0 -> n <= m -> q <= 0 -> p <= q ->  m * q <= n * p.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.mul_le_mono_nonpos". Undo.  
intros n m p q H1 H2 H3 H4.
apply le_trans with (m * p).
now apply mul_le_mono_nonpos_l.
apply mul_le_mono_nonpos_r; [now apply le_trans with q | assumption].
Qed.

Theorem mul_nonpos_nonpos : forall n m, n <= 0 -> m <= 0 -> 0 <= n * m.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.mul_nonpos_nonpos". Undo.  
intros n m H1 H2.
rewrite <- (mul_0_l m). now apply mul_le_mono_nonpos_r.
Qed.

Theorem mul_nonneg_nonpos : forall n m, 0 <= n -> m <= 0 -> n * m <= 0.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.mul_nonneg_nonpos". Undo.  
intros n m H1 H2.
rewrite <- (mul_0_l m). now apply mul_le_mono_nonpos_r.
Qed.

Theorem mul_nonpos_nonneg : forall n m, n <= 0 -> 0 <= m -> n * m <= 0.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.mul_nonpos_nonneg". Undo.  
intros; rewrite mul_comm; now apply mul_nonneg_nonpos.
Qed.

Notation mul_pos := lt_0_mul (only parsing).

Theorem lt_mul_0 :
forall n m, n * m < 0 <-> n < 0 /\ m > 0 \/ n > 0 /\ m < 0.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.lt_mul_0". Undo.  
intros n m; split; [intro H | intros [[H1 H2] | [H1 H2]]].
destruct (lt_trichotomy n 0) as [H1 | [H1 | H1]];
[| rewrite H1 in H; rewrite mul_0_l in H; false_hyp H lt_irrefl |];
(destruct (lt_trichotomy m 0) as [H2 | [H2 | H2]];
[| rewrite H2 in H; rewrite mul_0_r in H; false_hyp H lt_irrefl |]);
try (left; now split); try (right; now split).
assert (H3 : n * m > 0) by now apply mul_neg_neg.
exfalso; now apply (lt_asymm (n * m) 0).
assert (H3 : n * m > 0) by now apply mul_pos_pos.
exfalso; now apply (lt_asymm (n * m) 0).
now apply mul_neg_pos. now apply mul_pos_neg.
Qed.

Notation mul_neg := lt_mul_0 (only parsing).

Theorem le_0_mul :
forall n m, 0 <= n * m -> 0 <= n /\ 0 <= m \/ n <= 0 /\ m <= 0.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.le_0_mul". Undo.  
assert (R : forall n, 0 == n <-> n == 0) by (intros; split; apply eq_sym).
intros n m. repeat rewrite lt_eq_cases. repeat rewrite R.
rewrite lt_0_mul, eq_mul_0.
pose proof (lt_trichotomy n 0); pose proof (lt_trichotomy m 0). tauto.
Qed.

Notation mul_nonneg := le_0_mul (only parsing).

Theorem le_mul_0 :
forall n m, n * m <= 0 -> 0 <= n /\ m <= 0 \/ n <= 0 /\ 0 <= m.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.le_mul_0". Undo.  
assert (R : forall n, 0 == n <-> n == 0) by (intros; split; apply eq_sym).
intros n m. repeat rewrite lt_eq_cases. repeat rewrite R.
rewrite lt_mul_0, eq_mul_0.
pose proof (lt_trichotomy n 0); pose proof (lt_trichotomy m 0). tauto.
Qed.

Notation mul_nonpos := le_mul_0 (only parsing).

Notation le_0_square := square_nonneg (only parsing).

Theorem nlt_square_0 : forall n, ~ n * n < 0.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.nlt_square_0". Undo.  
intros n H. apply lt_nge in H. apply H. apply square_nonneg.
Qed.

Theorem square_lt_mono_nonpos : forall n m, n <= 0 -> m < n -> n * n < m * m.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.square_lt_mono_nonpos". Undo.  
intros n m H1 H2. now apply mul_lt_mono_nonpos.
Qed.

Theorem square_le_mono_nonpos : forall n m, n <= 0 -> m <= n -> n * n <= m * m.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.square_le_mono_nonpos". Undo.  
intros n m H1 H2. now apply mul_le_mono_nonpos.
Qed.

Theorem square_lt_simpl_nonpos : forall n m, m <= 0 -> n * n < m * m -> m < n.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.square_lt_simpl_nonpos". Undo.  
intros n m H1 H2. destruct (le_gt_cases n 0); [|order].
destruct (lt_ge_cases m n) as [LE|GT]; trivial.
apply square_le_mono_nonpos in GT; order.
Qed.

Theorem square_le_simpl_nonpos : forall n m, m <= 0 -> n * n <= m * m -> m <= n.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.square_le_simpl_nonpos". Undo.  
intros n m H1 H2. destruct (le_gt_cases n 0); [|order].
destruct (le_gt_cases m n) as [LE|GT]; trivial.
apply square_lt_mono_nonpos in GT; order.
Qed.

Theorem lt_1_mul_neg : forall n m, n < -1 -> m < 0 -> 1 < n * m.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.lt_1_mul_neg". Undo.  
intros n m H1 H2. apply (mul_lt_mono_neg_r m) in H1.
apply opp_pos_neg in H2. rewrite mul_opp_l, mul_1_l in H1.
now apply lt_1_l with (- m).
assumption.
Qed.

Theorem lt_mul_m1_neg : forall n m, 1 < n -> m < 0 -> n * m < -1.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.lt_mul_m1_neg". Undo.  
intros n m H1 H2. apply (mul_lt_mono_neg_r m) in H1.
rewrite mul_1_l in H1. now apply lt_m1_r with m.
assumption.
Qed.

Theorem lt_mul_m1_pos : forall n m, n < -1 -> 0 < m -> n * m < -1.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.lt_mul_m1_pos". Undo.  
intros n m H1 H2. apply (mul_lt_mono_pos_r m) in H1.
rewrite mul_opp_l, mul_1_l in H1.
apply opp_neg_pos in H2. now apply lt_m1_r with (- m).
assumption.
Qed.

Theorem lt_1_mul_l : forall n m, 1 < n ->
n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.lt_1_mul_l". Undo.  
intros n m H; destruct (lt_trichotomy m 0) as [H1 | [H1 | H1]].
left. now apply lt_mul_m1_neg.
right; left; now rewrite H1, mul_0_r.
right; right; now apply lt_1_mul_pos.
Qed.

Theorem lt_m1_mul_r : forall n m, n < -1 ->
n * m < -1 \/ n * m == 0 \/ 1 < n * m.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.lt_m1_mul_r". Undo.  
intros n m H; destruct (lt_trichotomy m 0) as [H1 | [H1 | H1]].
right; right. now apply lt_1_mul_neg.
right; left; now rewrite H1, mul_0_r.
left. now apply lt_mul_m1_pos.
Qed.

Theorem eq_mul_1 : forall n m, n * m == 1 -> n == 1 \/ n == -1.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.eq_mul_1". Undo.  
assert (F := lt_m1_0).
zero_pos_neg n.

intros m. nzsimpl. now left.

intros n Hn. rewrite <- le_succ_l, <- one_succ in Hn.
le_elim Hn; split; intros m H.
destruct (lt_1_mul_l n m) as [|[|]]; order'.
rewrite mul_opp_l, eq_opp_l in H. destruct (lt_1_mul_l n m) as [|[|]]; order'.
now left.
intros; right. now f_equiv.
Qed.

Theorem lt_mul_diag_l : forall n m, n < 0 -> (1 < m <-> n * m < n).
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.lt_mul_diag_l". Undo.  
intros n m H. stepr (n * m < n * 1) by now rewrite mul_1_r.
now apply mul_lt_mono_neg_l.
Qed.

Theorem lt_mul_diag_r : forall n m, 0 < n -> (1 < m <-> n < n * m).
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.lt_mul_diag_r". Undo.  
intros n m H. stepr (n * 1 < n * m) by now rewrite mul_1_r.
now apply mul_lt_mono_pos_l.
Qed.

Theorem le_mul_diag_l : forall n m, n < 0 -> (1 <= m <-> n * m <= n).
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.le_mul_diag_l". Undo.  
intros n m H. stepr (n * m <= n * 1) by now rewrite mul_1_r.
now apply mul_le_mono_neg_l.
Qed.

Theorem le_mul_diag_r : forall n m, 0 < n -> (1 <= m <-> n <= n * m).
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.le_mul_diag_r". Undo.  
intros n m H. stepr (n * 1 <= n * m) by now rewrite mul_1_r.
now apply mul_le_mono_pos_l.
Qed.

Theorem lt_mul_r : forall n m p, 0 < n -> 1 < p -> n < m -> n < m * p.
Proof. try hammer_hook "ZMulOrder" "ZMulOrder.ZMulOrderProp.lt_mul_r". Undo.  
intros. stepl (n * 1) by now rewrite mul_1_r.
apply mul_lt_mono_nonneg.
now apply lt_le_incl. assumption. apply le_0_1. assumption.
Qed.



Definition mul_eq_1 := eq_mul_1.

End ZMulOrderProp.

