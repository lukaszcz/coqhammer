From Hammer Require Import Hammer.











Require Import Bool NAxioms NSub NParity NZPow.



Module Type NPowProp
(Import A : NAxiomsSig')
(Import B : NSubProp A)
(Import C : NParityProp A B).

Module Import Private_NZPow := Nop <+ NZPowProp A A B.

Ltac auto' := trivial; try rewrite <- neq_0_lt_0; auto using le_0_l.
Ltac wrap l := intros; apply l; auto'.

Lemma pow_succ_r' : forall a b, a^(S b) == a * a^b.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_succ_r'".   wrap pow_succ_r. Qed.



Lemma pow_0_l : forall a, a~=0 -> 0^a == 0.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_0_l".   wrap pow_0_l. Qed.

Definition pow_1_r : forall a, a^1 == a
:= pow_1_r.

Lemma pow_1_l : forall a, 1^a == 1.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_1_l".   wrap pow_1_l. Qed.

Definition pow_2_r : forall a, a^2 == a*a
:= pow_2_r.



Lemma pow_add_r : forall a b c, a^(b+c) == a^b * a^c.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_add_r".   wrap pow_add_r. Qed.

Lemma pow_mul_l : forall a b c, (a*b)^c == a^c * b^c.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_mul_l".   wrap pow_mul_l. Qed.

Lemma pow_mul_r : forall a b c, a^(b*c) == (a^b)^c.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_mul_r".   wrap pow_mul_r. Qed.



Lemma pow_eq_0 : forall a b, b~=0 -> a^b == 0 -> a == 0.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_eq_0".   intros. apply (pow_eq_0 a b); trivial. auto'. Qed.

Lemma pow_nonzero : forall a b, a~=0 -> a^b ~= 0.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_nonzero".   wrap pow_nonzero. Qed.

Lemma pow_eq_0_iff : forall a b, a^b == 0 <-> b~=0 /\ a==0.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_eq_0_iff".  
intros a b. split.
rewrite pow_eq_0_iff. intros [H |[H H']].
generalize (le_0_l b); order. split; order.
intros (Hb,Ha). rewrite Ha. now apply pow_0_l'.
Qed.



Lemma pow_lt_mono_l : forall a b c, c~=0 -> a<b -> a^c < b^c.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_lt_mono_l".   wrap pow_lt_mono_l. Qed.

Lemma pow_le_mono_l : forall a b c, a<=b -> a^c <= b^c.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_le_mono_l".   wrap pow_le_mono_l. Qed.

Lemma pow_gt_1 : forall a b, 1<a -> b~=0 -> 1<a^b.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_gt_1".   wrap pow_gt_1. Qed.

Lemma pow_lt_mono_r : forall a b c, 1<a -> b<c -> a^b < a^c.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_lt_mono_r".   wrap pow_lt_mono_r. Qed.



Lemma pow_le_mono_r : forall a b c, a~=0 -> b<=c -> a^b <= a^c.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_le_mono_r".   wrap pow_le_mono_r. Qed.

Lemma pow_le_mono : forall a b c d, a~=0 -> a<=c -> b<=d ->
a^b <= c^d.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_le_mono".   wrap pow_le_mono. Qed.

Definition pow_lt_mono : forall a b c d, 0<a<c -> 0<b<d ->
a^b < c^d
:= pow_lt_mono.



Lemma pow_inj_l : forall a b c, c~=0 -> a^c == b^c -> a == b.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_inj_l".   intros; eapply pow_inj_l; eauto; auto'. Qed.

Lemma pow_inj_r : forall a b c, 1<a -> a^b == a^c -> b == c.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_inj_r".   intros; eapply pow_inj_r; eauto; auto'. Qed.



Lemma pow_lt_mono_l_iff : forall a b c, c~=0 ->
(a<b <-> a^c < b^c).
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_lt_mono_l_iff".   wrap pow_lt_mono_l_iff. Qed.

Lemma pow_le_mono_l_iff : forall a b c, c~=0 ->
(a<=b <-> a^c <= b^c).
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_le_mono_l_iff".   wrap pow_le_mono_l_iff. Qed.

Lemma pow_lt_mono_r_iff : forall a b c, 1<a ->
(b<c <-> a^b < a^c).
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_lt_mono_r_iff".   wrap pow_lt_mono_r_iff. Qed.

Lemma pow_le_mono_r_iff : forall a b c, 1<a ->
(b<=c <-> a^b <= a^c).
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_le_mono_r_iff".   wrap pow_le_mono_r_iff. Qed.



Lemma pow_gt_lin_r : forall a b, 1<a -> b < a^b.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_gt_lin_r".   wrap pow_gt_lin_r. Qed.



Lemma pow_add_lower : forall a b c, c~=0 ->
a^c + b^c <= (a+b)^c.
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_add_lower".   wrap pow_add_lower. Qed.



Lemma pow_add_upper : forall a b c, c~=0 ->
(a+b)^c <= 2^(pred c) * (a^c + b^c).
Proof. hammer_hook "NPow" "NPow.NPowProp.pow_add_upper".   wrap pow_add_upper. Qed.



Lemma even_pow : forall a b, b~=0 -> even (a^b) = even a.
Proof. hammer_hook "NPow" "NPow.NPowProp.even_pow".  
intros a b Hb. rewrite neq_0_lt_0 in Hb.
apply lt_ind with (4:=Hb). solve_proper.
now nzsimpl.
clear b Hb. intros b Hb IH.
rewrite pow_succ_r', even_mul, IH. now destruct (even a).
Qed.

Lemma odd_pow : forall a b, b~=0 -> odd (a^b) = odd a.
Proof. hammer_hook "NPow" "NPow.NPowProp.odd_pow".  
intros. now rewrite <- !negb_even, even_pow.
Qed.

End NPowProp.
