From Hammer Require Import Hammer.











Require Export ZAdd.

Module ZMulProp (Import Z : ZAxiomsMiniSig').
Include ZAddProp Z.





Theorem mul_pred_r : forall n m, n * (P m) == n * m - n.
Proof. try hammer_hook "ZMul" "ZMul.ZMulProp.mul_pred_r".  
intros n m.
rewrite <- (succ_pred m) at 2.
now rewrite mul_succ_r, <- add_sub_assoc, sub_diag, add_0_r.
Qed.

Theorem mul_pred_l : forall n m, (P n) * m == n * m - m.
Proof. try hammer_hook "ZMul" "ZMul.ZMulProp.mul_pred_l".  
intros n m; rewrite (mul_comm (P n) m), (mul_comm n m). apply mul_pred_r.
Qed.

Theorem mul_opp_l : forall n m, (- n) * m == - (n * m).
Proof. try hammer_hook "ZMul" "ZMul.ZMulProp.mul_opp_l".  
intros n m. apply add_move_0_r.
now rewrite <- mul_add_distr_r, add_opp_diag_l, mul_0_l.
Qed.

Theorem mul_opp_r : forall n m, n * (- m) == - (n * m).
Proof. try hammer_hook "ZMul" "ZMul.ZMulProp.mul_opp_r".  
intros n m; rewrite (mul_comm n (- m)), (mul_comm n m); apply mul_opp_l.
Qed.

Theorem mul_opp_opp : forall n m, (- n) * (- m) == n * m.
Proof. try hammer_hook "ZMul" "ZMul.ZMulProp.mul_opp_opp".  
intros n m; now rewrite mul_opp_l, mul_opp_r, opp_involutive.
Qed.

Theorem mul_opp_comm : forall n m, (- n) * m == n * (- m).
Proof. try hammer_hook "ZMul" "ZMul.ZMulProp.mul_opp_comm".  
intros n m. now rewrite mul_opp_l, <- mul_opp_r.
Qed.

Theorem mul_sub_distr_l : forall n m p, n * (m - p) == n * m - n * p.
Proof. try hammer_hook "ZMul" "ZMul.ZMulProp.mul_sub_distr_l".  
intros n m p. do 2 rewrite <- add_opp_r. rewrite mul_add_distr_l.
now rewrite mul_opp_r.
Qed.

Theorem mul_sub_distr_r : forall n m p, (n - m) * p == n * p - m * p.
Proof. try hammer_hook "ZMul" "ZMul.ZMulProp.mul_sub_distr_r".  
intros n m p; rewrite (mul_comm (n - m) p), (mul_comm n p), (mul_comm m p);
now apply mul_sub_distr_l.
Qed.

End ZMulProp.


