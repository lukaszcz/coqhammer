From Hammer Require Import Hammer.









Require Import Morphisms BinInt ZDivEucl.
Local Open Scope Z_scope.





Module ZEuclid.

Definition modulo a b := Z.modulo a (Z.abs b).
Definition div a b := (Z.sgn b) * (Z.div a (Z.abs b)).

Instance mod_wd : Proper (eq==>eq==>eq) modulo.
Proof. try hammer_hook "Zeuclid" "Zeuclid.ZEuclid.mod_wd". Undo.   congruence. Qed.
Instance div_wd : Proper (eq==>eq==>eq) div.
Proof. try hammer_hook "Zeuclid" "Zeuclid.ZEuclid.div_wd". Undo.   congruence. Qed.

Theorem div_mod a b : b<>0 -> a = b*(div a b) + modulo a b.
Proof. try hammer_hook "Zeuclid" "Zeuclid.ZEuclid.div_mod". Undo.  
intros Hb. unfold div, modulo.
rewrite Z.mul_assoc. rewrite Z.sgn_abs. apply Z.div_mod.
now destruct b.
Qed.

Lemma mod_always_pos a b : b<>0 -> 0 <= modulo a b < Z.abs b.
Proof. try hammer_hook "Zeuclid" "Zeuclid.ZEuclid.mod_always_pos". Undo.  
intros Hb. unfold modulo.
apply Z.mod_pos_bound.
destruct b; compute; trivial. now destruct Hb.
Qed.

Lemma mod_bound_pos a b : 0<=a -> 0<b -> 0 <= modulo a b < b.
Proof. try hammer_hook "Zeuclid" "Zeuclid.ZEuclid.mod_bound_pos". Undo.  
intros _ Hb. rewrite <- (Z.abs_eq b) at 3 by Z.order.
apply mod_always_pos. Z.order.
Qed.

Include ZEuclidProp Z Z Z.

End ZEuclid.
