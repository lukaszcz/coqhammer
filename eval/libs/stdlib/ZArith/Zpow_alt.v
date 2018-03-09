From Hammer Require Import Hammer.









Require Import BinInt.
Local Open Scope Z_scope.





Definition Zpower_alt n m :=
match m with
| Z0 => 1
| Zpos p => Pos.iter_op Z.mul p n
| Zneg p => 0
end.

Infix "^^" := Zpower_alt (at level 30, right associativity) : Z_scope.

Lemma Piter_mul_acc : forall f,
(forall x y:Z, (f x)*y = f (x*y)) ->
forall p k, Pos.iter f k p = (Pos.iter f 1 p)*k.
Proof. hammer_hook "Zpow_alt" "Zpow_alt.Piter_mul_acc". Restart. 
intros f Hf.
induction p; simpl; intros.
- set (g := Pos.iter f 1 p) in *. now rewrite !IHp, Hf, Z.mul_assoc.
- set (g := Pos.iter f 1 p) in *. now rewrite !IHp, Z.mul_assoc.
- now rewrite Hf, Z.mul_1_l.
Qed.

Lemma Piter_op_square : forall p a,
Pos.iter_op Z.mul p (a*a) = (Pos.iter_op Z.mul p a)*(Pos.iter_op Z.mul p a).
Proof. hammer_hook "Zpow_alt" "Zpow_alt.Piter_op_square". Restart. 
induction p; simpl; intros; trivial. now rewrite IHp, Z.mul_shuffle1.
Qed.

Lemma Zpower_equiv a b : a^^b = a^b.
Proof. hammer_hook "Zpow_alt" "Zpow_alt.Zpower_equiv". Restart. 
destruct b as [|p|p]; trivial.
unfold Zpower_alt, Z.pow, Z.pow_pos.
revert a.
induction p; simpl; intros.
- f_equal.
rewrite Piter_mul_acc.
now rewrite Piter_op_square, IHp.
intros. symmetry; apply Z.mul_assoc.
- rewrite Piter_mul_acc.
now rewrite Piter_op_square, IHp.
intros. symmetry; apply Z.mul_assoc.
- now Z.nzsimpl.
Qed.

Lemma Zpower_alt_0_r n : n^^0 = 1.
Proof. hammer_hook "Zpow_alt" "Zpow_alt.Zpower_alt_0_r". Restart.  reflexivity. Qed.

Lemma Zpower_alt_succ_r a b : 0<=b -> a^^(Z.succ b) = a * a^^b.
Proof. hammer_hook "Zpow_alt" "Zpow_alt.Zpower_alt_succ_r". Restart. 
destruct b as [|b|b]; intros Hb; simpl.
- now Z.nzsimpl.
- now rewrite Pos.add_1_r, Pos.iter_op_succ by apply Z.mul_assoc.
- now elim Hb.
Qed.

Lemma Zpower_alt_neg_r a b : b<0 -> a^^b = 0.
Proof. hammer_hook "Zpow_alt" "Zpow_alt.Zpower_alt_neg_r". Restart. 
now destruct b.
Qed.

Lemma Zpower_alt_Ppow p q : (Zpos p)^^(Zpos q) = Zpos (p^q).
Proof. hammer_hook "Zpow_alt" "Zpow_alt.Zpower_alt_Ppow". Restart. 
now rewrite Zpower_equiv, Pos2Z.inj_pow.
Qed.
