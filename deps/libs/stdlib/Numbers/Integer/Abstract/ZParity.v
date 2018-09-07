From Hammer Require Import Hammer.









Require Import Bool ZMulOrder NZParity.



Module Type ZParityProp (Import Z : ZAxiomsSig')
(Import ZP : ZMulOrderProp Z).

Include NZParityProp Z Z ZP.

Lemma odd_pred : forall n, odd (P n) = even n.
Proof. hammer_hook "ZParity" "ZParity.ZParityProp.odd_pred".  
intros. rewrite <- (succ_pred n) at 2. symmetry. apply even_succ.
Qed.

Lemma even_pred : forall n, even (P n) = odd n.
Proof. hammer_hook "ZParity" "ZParity.ZParityProp.even_pred".  
intros. rewrite <- (succ_pred n) at 2. symmetry. apply odd_succ.
Qed.

Lemma even_opp : forall n, even (-n) = even n.
Proof. hammer_hook "ZParity" "ZParity.ZParityProp.even_opp".  
assert (H : forall n, Even n -> Even (-n)).
intros n (m,H). exists (-m). rewrite mul_opp_r. now f_equiv.
intros. rewrite eq_iff_eq_true, !even_spec.
split. rewrite <- (opp_involutive n) at 2. apply H.
apply H.
Qed.

Lemma odd_opp : forall n, odd (-n) = odd n.
Proof. hammer_hook "ZParity" "ZParity.ZParityProp.odd_opp".  
intros. rewrite <- !negb_even. now rewrite even_opp.
Qed.

Lemma even_sub : forall n m, even (n-m) = Bool.eqb (even n) (even m).
Proof. hammer_hook "ZParity" "ZParity.ZParityProp.even_sub".  
intros. now rewrite <- add_opp_r, even_add, even_opp.
Qed.

Lemma odd_sub : forall n m, odd (n-m) = xorb (odd n) (odd m).
Proof. hammer_hook "ZParity" "ZParity.ZParityProp.odd_sub".  
intros. now rewrite <- add_opp_r, odd_add, odd_opp.
Qed.

End ZParityProp.
