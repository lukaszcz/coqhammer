From Hammer Require Import Hammer.









Require Import Wf_nat.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Bool.
Local Open Scope Z_scope.






Notation iter := @Z.iter (compat "8.3").

Lemma iter_nat_of_Z : forall n A f x, 0 <= n ->
Z.iter n f x = iter_nat (Z.abs_nat n) A f x.
Proof. hammer_hook "Zmisc" "Zmisc.iter_nat_of_Z". Restart. 
intros n A f x; case n; auto.
intros p _; unfold Z.iter, Z.abs_nat; apply Pos2Nat.inj_iter.
intros p abs; case abs; trivial.
Qed.
