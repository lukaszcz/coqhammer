From Hammer Require Import Hammer.











Require Export NOrder.

Module NAddOrderProp (Import N : NAxiomsMiniSig').
Include NOrderProp N.



Theorem le_add_r : forall n m, n <= n + m.
Proof. try hammer_hook "NAddOrder" "NAddOrder.NAddOrderProp.le_add_r".  
intro n; induct m.
rewrite add_0_r; now apply eq_le_incl.
intros m IH. rewrite add_succ_r; now apply le_le_succ_r.
Qed.

Theorem lt_lt_add_r : forall n m p, n < m -> n < m + p.
Proof. try hammer_hook "NAddOrder" "NAddOrder.NAddOrderProp.lt_lt_add_r".  
intros n m p H; rewrite <- (add_0_r n).
apply add_lt_le_mono; [assumption | apply le_0_l].
Qed.

Theorem lt_lt_add_l : forall n m p, n < m -> n < p + m.
Proof. try hammer_hook "NAddOrder" "NAddOrder.NAddOrderProp.lt_lt_add_l".  
intros n m p; rewrite add_comm; apply lt_lt_add_r.
Qed.

Theorem add_pos_l : forall n m, 0 < n -> 0 < n + m.
Proof. try hammer_hook "NAddOrder" "NAddOrder.NAddOrderProp.add_pos_l".  
intros; apply add_pos_nonneg. assumption. apply le_0_l.
Qed.

Theorem add_pos_r : forall n m, 0 < m -> 0 < n + m.
Proof. try hammer_hook "NAddOrder" "NAddOrder.NAddOrderProp.add_pos_r".  
intros; apply add_nonneg_pos. apply le_0_l. assumption.
Qed.

End NAddOrderProp.
