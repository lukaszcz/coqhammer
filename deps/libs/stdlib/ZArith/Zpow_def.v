From Hammer Require Import Hammer.









Require Import BinInt Ring_theory.
Local Open Scope Z_scope.





Notation Zpower_pos := Z.pow_pos (compat "8.3").
Notation Zpower := Z.pow (compat "8.3").
Notation Zpower_0_r := Z.pow_0_r (compat "8.3").
Notation Zpower_succ_r := Z.pow_succ_r (compat "8.3").
Notation Zpower_neg_r := Z.pow_neg_r (compat "8.3").
Notation Zpower_Ppow := Pos2Z.inj_pow (compat "8.3").

Lemma Zpower_theory : power_theory 1 Z.mul (@eq Z) Z.of_N Z.pow.
Proof. hammer_hook "Zpow_def" "Zpow_def.Zpower_theory".  
constructor. intros.
destruct n;simpl;trivial.
unfold Z.pow_pos.
rewrite <- (Z.mul_1_r (pow_pos _ _ _)). generalize 1.
induction p; simpl; intros; rewrite ?IHp, ?Z.mul_assoc; trivial.
Qed.
