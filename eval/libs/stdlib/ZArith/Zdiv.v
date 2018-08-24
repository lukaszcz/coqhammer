From Hammer Require Import Hammer.














Require Export ZArith_base.
Require Import Zbool Omega ZArithRing Zcomplements Setoid Morphisms.
Local Open Scope Z_scope.



Notation Zdiv_eucl_POS := Z.pos_div_eucl (compat "8.3").
Notation Zdiv_eucl := Z.div_eucl (compat "8.3").
Notation Zdiv := Z.div (compat "8.3").
Notation Zmod := Z.modulo (compat "8.3").

Notation Zdiv_eucl_eq := Z.div_eucl_eq (compat "8.3").
Notation Z_div_mod_eq_full := Z.div_mod (compat "8.3").
Notation Zmod_POS_bound := Z.pos_div_eucl_bound (compat "8.3").
Notation Zmod_pos_bound := Z.mod_pos_bound (compat "8.3").
Notation Zmod_neg_bound := Z.mod_neg_bound (compat "8.3").





Lemma Z_div_mod_POS :
forall b:Z,
b > 0 ->
forall a:positive,
let (q, r) := Z.pos_div_eucl a b in Zpos a = b * q + r /\ 0 <= r < b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_mod_POS". Undo.  
intros b Hb a. Z.swap_greater.
generalize (Z.pos_div_eucl_eq a b Hb) (Z.pos_div_eucl_bound a b Hb).
destruct Z.pos_div_eucl. rewrite Z.mul_comm. auto.
Qed.

Theorem Z_div_mod a b :
b > 0 ->
let (q, r) := Z.div_eucl a b in a = b * q + r /\ 0 <= r < b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_mod". Undo.  
Z.swap_greater. intros Hb.
assert (Hb' : b<>0) by (now destruct b).
generalize (Z.div_eucl_eq a b Hb') (Z.mod_pos_bound a b Hb).
unfold Z.modulo. destruct Z.div_eucl. auto.
Qed.



Definition Remainder r b :=  0 <= r < b \/ b < r <= 0.



Definition Remainder_alt r b :=  Z.abs r < Z.abs b /\ Z.sgn r <> - Z.sgn b.



Lemma Remainder_equiv : forall r b, Remainder r b <-> Remainder_alt r b.
Proof. try hammer_hook "Zdiv" "Zdiv.Remainder_equiv". Undo.  
intros; unfold Remainder, Remainder_alt; omega with *.
Qed.

Hint Unfold Remainder.



Theorem Z_div_mod_full a b :
b <> 0 ->
let (q, r) := Z.div_eucl a b in a = b * q + r /\ Remainder r b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_mod_full". Undo.  
intros Hb.
generalize (Z.div_eucl_eq a b Hb)
(Z.mod_pos_bound a b) (Z.mod_neg_bound a b).
unfold Z.modulo. destruct Z.div_eucl as (q,r).
intros EQ POS NEG.
split; auto.
red; destruct b.
now destruct Hb. left; now apply POS. right; now apply NEG.
Qed.



Lemma Z_mod_remainder a b : b<>0 -> Remainder (a mod b) b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_remainder". Undo.  
unfold Z.modulo; intros Hb; generalize (Z_div_mod_full a b Hb); auto.
destruct Z.div_eucl; tauto.
Qed.

Lemma Z_mod_lt a b : b > 0 -> 0 <= a mod b < b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_lt". Undo.  exact ((fun Hb => Z.mod_pos_bound a b (Z.gt_lt _ _ Hb))). Qed.

Lemma Z_mod_neg a b : b < 0 -> b < a mod b <= 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_neg". Undo.  exact ((Z.mod_neg_bound a b)). Qed.

Lemma Z_div_mod_eq a b : b > 0 -> a = b*(a/b) + (a mod b).
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_mod_eq". Undo.  
intros Hb; apply Z.div_mod; auto with zarith.
Qed.

Lemma Zmod_eq_full a b : b<>0 -> a mod b = a - (a/b)*b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_eq_full". Undo.   intros. rewrite Z.mul_comm. now apply Z.mod_eq. Qed.

Lemma Zmod_eq a b : b>0 -> a mod b = a - (a/b)*b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_eq". Undo.   intros. apply Zmod_eq_full. now destruct b. Qed.



Theorem Zdiv_eucl_exist : forall (b:Z)(Hb:b>0)(a:Z),
{qr : Z * Z | let (q, r) := qr in a = b * q + r /\ 0 <= r < b}.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_eucl_exist". Undo.  
intros b Hb a.
exists (Z.div_eucl a b).
exact (Z_div_mod a b Hb).
Qed.

Arguments Zdiv_eucl_exist : default implicits.




Theorem Zdiv_mod_unique b q1 q2 r1 r2 :
0 <= r1 < Z.abs b -> 0 <= r2 < Z.abs b ->
b*q1+r1 = b*q2+r2 -> q1=q2 /\ r1=r2.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_mod_unique". Undo.  
intros Hr1 Hr2 H. rewrite <- (Z.abs_sgn b), <- !Z.mul_assoc in H.
destruct (Z.div_mod_unique (Z.abs b) (Z.sgn b * q1) (Z.sgn b * q2) r1 r2); auto.
split; trivial.
apply Z.mul_cancel_l with (Z.sgn b); trivial.
rewrite Z.sgn_null_iff, <- Z.abs_0_iff. destruct Hr1; Z.order.
Qed.

Theorem Zdiv_mod_unique_2 :
forall b q1 q2 r1 r2:Z,
Remainder r1 b -> Remainder r2 b ->
b*q1+r1 = b*q2+r2 -> q1=q2 /\ r1=r2.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_mod_unique_2". Undo.  exact (Z.div_mod_unique). Qed.

Theorem Zdiv_unique_full:
forall a b q r, Remainder r b ->
a = b*q + r -> q = a/b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_unique_full". Undo.  exact (Z.div_unique). Qed.

Theorem Zdiv_unique:
forall a b q r, 0 <= r < b ->
a = b*q + r -> q = a/b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_unique". Undo.   intros; eapply Zdiv_unique_full; eauto. Qed.

Theorem Zmod_unique_full:
forall a b q r, Remainder r b ->
a = b*q + r ->  r = a mod b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_unique_full". Undo.  exact (Z.mod_unique). Qed.

Theorem Zmod_unique:
forall a b q r, 0 <= r < b ->
a = b*q + r -> r = a mod b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_unique". Undo.   intros; eapply Zmod_unique_full; eauto. Qed.



Lemma Zmod_0_l: forall a, 0 mod a = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_0_l". Undo.  
destruct a; simpl; auto.
Qed.

Lemma Zmod_0_r: forall a, a mod 0 = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_0_r". Undo.  
destruct a; simpl; auto.
Qed.

Lemma Zdiv_0_l: forall a, 0/a = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_0_l". Undo.  
destruct a; simpl; auto.
Qed.

Lemma Zdiv_0_r: forall a, a/0 = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_0_r". Undo.  
destruct a; simpl; auto.
Qed.

Ltac zero_or_not a :=
destruct (Z.eq_dec a 0);
[subst; rewrite ?Zmod_0_l, ?Zdiv_0_l, ?Zmod_0_r, ?Zdiv_0_r;
auto with zarith|].

Lemma Zmod_1_r: forall a, a mod 1 = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_1_r". Undo.   intros. zero_or_not a. apply Z.mod_1_r. Qed.

Lemma Zdiv_1_r: forall a, a/1 = a.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_1_r". Undo.   intros. zero_or_not a. apply Z.div_1_r. Qed.

Hint Resolve Zmod_0_l Zmod_0_r Zdiv_0_l Zdiv_0_r Zdiv_1_r Zmod_1_r
: zarith.

Lemma Zdiv_1_l: forall a, 1 < a -> 1/a = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_1_l". Undo.  exact (Z.div_1_l). Qed.

Lemma Zmod_1_l: forall a, 1 < a ->  1 mod a = 1.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_1_l". Undo.  exact (Z.mod_1_l). Qed.

Lemma Z_div_same_full : forall a:Z, a<>0 -> a/a = 1.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_same_full". Undo.  exact (Z.div_same). Qed.

Lemma Z_mod_same_full : forall a, a mod a = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_same_full". Undo.   intros. zero_or_not a. apply Z.mod_same; auto. Qed.

Lemma Z_mod_mult : forall a b, (a*b) mod b = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_mult". Undo.   intros. zero_or_not b. apply Z.mod_mul. auto. Qed.

Lemma Z_div_mult_full : forall a b:Z, b <> 0 -> (a*b)/b = a.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_mult_full". Undo.  exact (Z.div_mul). Qed.





Lemma Z_div_pos: forall a b, b > 0 -> 0 <= a -> 0 <= a/b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_pos". Undo.   intros. apply Z.div_pos; auto with zarith. Qed.

Lemma Z_div_ge0: forall a b, b > 0 -> a >= 0 -> a/b >=0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_ge0". Undo.  
intros; generalize (Z_div_pos a b H); auto with zarith.
Qed.



Lemma Z_div_lt : forall a b:Z, b >= 2 -> a > 0 -> a/b < a.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_lt". Undo.   intros. apply Z.div_lt; auto with zarith. Qed.



Theorem Zdiv_small: forall a b, 0 <= a < b -> a/b = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_small". Undo.  exact (Z.div_small). Qed.



Theorem Zmod_small: forall a n, 0 <= a < n -> a mod n = a.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_small". Undo.  exact (Z.mod_small). Qed.



Lemma Z_div_ge : forall a b c:Z, c > 0 -> a >= b -> a/c >= b/c.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_ge". Undo.   intros. apply Z.le_ge. apply Z.div_le_mono; auto with zarith. Qed.



Lemma Z_div_le : forall a b c:Z, c > 0 -> a <= b -> a/c <= b/c.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_le". Undo.   intros. apply Z.div_le_mono; auto with zarith. Qed.



Lemma Z_mult_div_ge : forall a b:Z, b > 0 -> b*(a/b) <= a.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mult_div_ge". Undo.   intros. apply Z.mul_div_le; auto with zarith. Qed.

Lemma Z_mult_div_ge_neg : forall a b:Z, b < 0 -> b*(a/b) >= a.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mult_div_ge_neg". Undo.   intros. apply Z.le_ge. apply Z.mul_div_ge; auto with zarith. Qed.



Lemma Z_div_exact_full_1 : forall a b:Z, a = b*(a/b) -> a mod b = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_exact_full_1". Undo.   intros a b. zero_or_not b. rewrite Z.div_exact; auto. Qed.

Lemma Z_div_exact_full_2 : forall a b:Z, b <> 0 -> a mod b = 0 -> a = b*(a/b).
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_exact_full_2". Undo.   intros; rewrite Z.div_exact; auto. Qed.



Theorem Zmod_le: forall a b, 0 < b -> 0 <= a -> a mod b <= a.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_le". Undo.   intros. apply Z.mod_le; auto. Qed.



Theorem Zdiv_lt_upper_bound:
forall a b q, 0 < b -> a < q*b -> a/b < q.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_lt_upper_bound". Undo.   intros a b q; rewrite Z.mul_comm; apply Z.div_lt_upper_bound. Qed.

Theorem Zdiv_le_upper_bound:
forall a b q, 0 < b -> a <= q*b -> a/b <= q.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_le_upper_bound". Undo.   intros a b q; rewrite Z.mul_comm; apply Z.div_le_upper_bound. Qed.

Theorem Zdiv_le_lower_bound:
forall a b q, 0 < b -> q*b <= a -> q <= a/b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_le_lower_bound". Undo.   intros a b q; rewrite Z.mul_comm; apply Z.div_le_lower_bound. Qed.



Lemma Zdiv_le_compat_l: forall p q r, 0 <= p -> 0 < q < r ->
p / r <= p / q.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_le_compat_l". Undo.   intros; apply Z.div_le_compat_l; auto with zarith. Qed.

Theorem Zdiv_sgn: forall a b,
0 <= Z.sgn (a/b) * Z.sgn a * Z.sgn b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_sgn". Undo.  
destruct a as [ |a|a]; destruct b as [ |b|b]; simpl; auto with zarith;
generalize (Z.div_pos (Zpos a) (Zpos b)); unfold Z.div, Z.div_eucl;
destruct Z.pos_div_eucl as (q,r); destruct r; omega with *.
Qed.



Lemma Z_mod_plus_full : forall a b c:Z, (a + b * c) mod c = a mod c.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_plus_full". Undo.   intros. zero_or_not c. apply Z.mod_add; auto. Qed.

Lemma Z_div_plus_full : forall a b c:Z, c <> 0 -> (a + b * c) / c = a / c + b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_plus_full". Undo.  exact (Z.div_add). Qed.

Theorem Z_div_plus_full_l: forall a b c : Z, b <> 0 -> (a * b + c) / b = a + c / b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_plus_full_l". Undo.  exact (Z.div_add_l). Qed.



Lemma Zdiv_opp_opp : forall a b:Z, (-a)/(-b) = a/b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_opp_opp". Undo.   intros. zero_or_not b. apply Z.div_opp_opp; auto. Qed.

Lemma Zmod_opp_opp : forall a b:Z, (-a) mod (-b) = - (a mod b).
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_opp_opp". Undo.   intros. zero_or_not b. apply Z.mod_opp_opp; auto. Qed.

Lemma Z_mod_zero_opp_full : forall a b:Z, a mod b = 0 -> (-a) mod b = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_zero_opp_full". Undo.   intros. zero_or_not b. apply Z.mod_opp_l_z; auto. Qed.

Lemma Z_mod_nz_opp_full : forall a b:Z, a mod b <> 0 ->
(-a) mod b = b - (a mod b).
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_nz_opp_full". Undo.   intros. zero_or_not b. apply Z.mod_opp_l_nz; auto. Qed.

Lemma Z_mod_zero_opp_r : forall a b:Z, a mod b = 0 -> a mod (-b) = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_zero_opp_r". Undo.   intros. zero_or_not b. apply Z.mod_opp_r_z; auto. Qed.

Lemma Z_mod_nz_opp_r : forall a b:Z, a mod b <> 0 ->
a mod (-b) = (a mod b) - b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_nz_opp_r". Undo.   intros. zero_or_not b. apply Z.mod_opp_r_nz; auto. Qed.

Lemma Z_div_zero_opp_full : forall a b:Z, a mod b = 0 -> (-a)/b = -(a/b).
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_zero_opp_full". Undo.   intros. zero_or_not b. apply Z.div_opp_l_z; auto. Qed.

Lemma Z_div_nz_opp_full : forall a b:Z, a mod b <> 0 ->
(-a)/b = -(a/b)-1.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_nz_opp_full". Undo.   intros a b. zero_or_not b. intros; rewrite Z.div_opp_l_nz; auto. Qed.

Lemma Z_div_zero_opp_r : forall a b:Z, a mod b = 0 -> a/(-b) = -(a/b).
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_zero_opp_r". Undo.   intros. zero_or_not b. apply Z.div_opp_r_z; auto. Qed.

Lemma Z_div_nz_opp_r : forall a b:Z, a mod b <> 0 ->
a/(-b) = -(a/b)-1.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_nz_opp_r". Undo.   intros a b. zero_or_not b. intros; rewrite Z.div_opp_r_nz; auto. Qed.



Lemma  Zdiv_mult_cancel_r : forall a b c:Z,
c <> 0 -> (a*c)/(b*c) = a/b.
Proof. intros. zero_or_not b. apply Z.div_mul_cancel_r; auto. Qed.

Lemma Zdiv_mult_cancel_l : forall a b c:Z,
c<>0 -> (c*a)/(c*b) = a/b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_mult_cancel_l". Undo.  
intros. rewrite (Z.mul_comm c b); zero_or_not b.
rewrite (Z.mul_comm b c). apply Z.div_mul_cancel_l; auto.
Qed.

Lemma Zmult_mod_distr_l: forall a b c,
(c*a) mod (c*b) = c * (a mod b).
Proof. try hammer_hook "Zdiv" "Zdiv.Zmult_mod_distr_l". Undo.  
intros. zero_or_not c. rewrite (Z.mul_comm c b); zero_or_not b.
rewrite (Z.mul_comm b c). apply Z.mul_mod_distr_l; auto.
Qed.

Lemma Zmult_mod_distr_r: forall a b c,
(a*c) mod (b*c) = (a mod b) * c.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmult_mod_distr_r". Undo.  
intros. zero_or_not b. rewrite (Z.mul_comm b c); zero_or_not c.
rewrite (Z.mul_comm c b). apply Z.mul_mod_distr_r; auto.
Qed.



Theorem Zmod_mod: forall a n, (a mod n) mod n = a mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_mod". Undo.   intros. zero_or_not n. apply Z.mod_mod; auto. Qed.

Theorem Zmult_mod: forall a b n,
(a * b) mod n = ((a mod n) * (b mod n)) mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmult_mod". Undo.   intros. zero_or_not n. apply Z.mul_mod; auto. Qed.

Theorem Zplus_mod: forall a b n,
(a + b) mod n = (a mod n + b mod n) mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zplus_mod". Undo.   intros. zero_or_not n. apply Z.add_mod; auto. Qed.

Theorem Zminus_mod: forall a b n,
(a - b) mod n = (a mod n - b mod n) mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zminus_mod". Undo.  
intros.
replace (a - b) with (a + (-1) * b); auto with zarith.
replace (a mod n - b mod n) with (a mod n + (-1) * (b mod n)); auto with zarith.
rewrite Zplus_mod.
rewrite Zmult_mod.
rewrite Zplus_mod with (b:=(-1) * (b mod n)).
rewrite Zmult_mod.
rewrite Zmult_mod with (b:= b mod n).
repeat rewrite Zmod_mod; auto.
Qed.

Lemma Zplus_mod_idemp_l: forall a b n, (a mod n + b) mod n = (a + b) mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zplus_mod_idemp_l". Undo.  
intros; rewrite Zplus_mod, Zmod_mod, <- Zplus_mod; auto.
Qed.

Lemma Zplus_mod_idemp_r: forall a b n, (b + a mod n) mod n = (b + a) mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zplus_mod_idemp_r". Undo.  
intros; rewrite Zplus_mod, Zmod_mod, <- Zplus_mod; auto.
Qed.

Lemma Zminus_mod_idemp_l: forall a b n, (a mod n - b) mod n = (a - b) mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zminus_mod_idemp_l". Undo.  
intros; rewrite Zminus_mod, Zmod_mod, <- Zminus_mod; auto.
Qed.

Lemma Zminus_mod_idemp_r: forall a b n, (a - b mod n) mod n = (a - b) mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zminus_mod_idemp_r". Undo.  
intros; rewrite Zminus_mod, Zmod_mod, <- Zminus_mod; auto.
Qed.

Lemma Zmult_mod_idemp_l: forall a b n, (a mod n * b) mod n = (a * b) mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmult_mod_idemp_l". Undo.  
intros; rewrite Zmult_mod, Zmod_mod, <- Zmult_mod; auto.
Qed.

Lemma Zmult_mod_idemp_r: forall a b n, (b * (a mod n)) mod n = (b * a) mod n.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmult_mod_idemp_r". Undo.  
intros; rewrite Zmult_mod, Zmod_mod, <- Zmult_mod; auto.
Qed.



Section EqualityModulo.
Variable N:Z.

Definition eqm a b := (a mod N = b mod N).
Infix "==" := eqm (at level 70).

Lemma eqm_refl : forall a, a == a.
Proof. try hammer_hook "Zdiv" "Zdiv.eqm_refl". Undo.   unfold eqm; auto. Qed.

Lemma eqm_sym : forall a b, a == b -> b == a.
Proof. try hammer_hook "Zdiv" "Zdiv.eqm_sym". Undo.   unfold eqm; auto. Qed.

Lemma eqm_trans : forall a b c,
a == b -> b == c -> a == c.
Proof. try hammer_hook "Zdiv" "Zdiv.eqm_trans". Undo.   unfold eqm; eauto with *. Qed.

Instance eqm_setoid : Equivalence eqm.
Proof. try hammer_hook "Zdiv" "Zdiv.eqm_setoid". Undo.  
constructor; [exact eqm_refl | exact eqm_sym | exact eqm_trans].
Qed.

Instance Zplus_eqm : Proper (eqm ==> eqm ==> eqm) Z.add.
Proof. try hammer_hook "Zdiv" "Zdiv.Zplus_eqm". Undo.  
unfold eqm; repeat red; intros. rewrite Zplus_mod, H, H0, <- Zplus_mod; auto.
Qed.

Instance Zminus_eqm : Proper (eqm ==> eqm ==> eqm) Z.sub.
Proof. try hammer_hook "Zdiv" "Zdiv.Zminus_eqm". Undo.  
unfold eqm; repeat red; intros. rewrite Zminus_mod, H, H0, <- Zminus_mod; auto.
Qed.

Instance Zmult_eqm : Proper (eqm ==> eqm ==> eqm) Z.mul.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmult_eqm". Undo.  
unfold eqm; repeat red; intros. rewrite Zmult_mod, H, H0, <- Zmult_mod; auto.
Qed.

Instance Zopp_eqm : Proper (eqm ==> eqm) Z.opp.
Proof. try hammer_hook "Zdiv" "Zdiv.Zopp_eqm". Undo.  
intros x y H. change ((-x)==(-y)) with ((0-x)==(0-y)). now rewrite H.
Qed.

Lemma Zmod_eqm : forall a, (a mod N) == a.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_eqm". Undo.  
intros; exact (Zmod_mod a N).
Qed.



End EqualityModulo.

Lemma Zdiv_Zdiv : forall a b c, 0<=b -> 0<=c -> (a/b)/c = a/(b*c).
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_Zdiv". Undo.  
intros. zero_or_not b. rewrite Z.mul_comm. zero_or_not c.
rewrite Z.mul_comm. apply Z.div_div; auto with zarith.
Qed.





Theorem Zdiv_mult_le:
forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_mult_le". Undo.  
intros. zero_or_not b. apply Z.div_mul_le; auto with zarith. Qed.



Lemma Zmod_divides : forall a b, b<>0 ->
(a mod b = 0 <-> exists c, a = b*c).
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_divides". Undo.  
intros. rewrite Z.mod_divide; trivial.
split; intros (c,Hc); exists c; subst; auto with zarith.
Qed.



Lemma Zdiv2_div : forall a, Z.div2 a = a/2.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv2_div". Undo.  exact (Z.div2_div). Qed.

Lemma Zmod_odd : forall a, a mod 2 = if Z.odd a then 1 else 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_odd". Undo.  
intros a. now rewrite <- Z.bit0_odd, <- Z.bit0_mod.
Qed.

Lemma Zmod_even : forall a, a mod 2 = if Z.even a then 0 else 1.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_even". Undo.  
intros a. rewrite Zmod_odd, Zodd_even_bool. now destruct Z.even.
Qed.

Lemma Zodd_mod : forall a, Z.odd a = Zeq_bool (a mod 2) 1.
Proof. try hammer_hook "Zdiv" "Zdiv.Zodd_mod". Undo.  
intros a. rewrite Zmod_odd. now destruct Z.odd.
Qed.

Lemma Zeven_mod : forall a, Z.even a = Zeq_bool (a mod 2) 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Zeven_mod". Undo.  
intros a. rewrite Zmod_even. now destruct Z.even.
Qed.





Lemma Z_mod_same : forall a, a > 0 -> a mod a = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_same". Undo.  
intros; apply Z_mod_same_full.
Qed.

Lemma Z_div_same : forall a, a > 0 -> a/a = 1.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_same". Undo.  
intros; apply Z_div_same_full; auto with zarith.
Qed.

Lemma Z_div_plus : forall a b c:Z, c > 0 -> (a + b * c) / c = a / c + b.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_plus". Undo.  
intros; apply Z_div_plus_full; auto with zarith.
Qed.

Lemma Z_div_mult : forall a b:Z, b > 0 -> (a*b)/b = a.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_mult". Undo.  
intros; apply Z_div_mult_full; auto with zarith.
Qed.

Lemma Z_mod_plus : forall a b c:Z, c > 0 -> (a + b * c) mod c = a mod c.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_plus". Undo.  
intros; apply Z_mod_plus_full; auto with zarith.
Qed.

Lemma Z_div_exact_1 : forall a b:Z, b > 0 -> a = b*(a/b) -> a mod b = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_exact_1". Undo.  
intros; apply Z_div_exact_full_1; auto with zarith.
Qed.

Lemma Z_div_exact_2 : forall a b:Z, b > 0 -> a mod b = 0 -> a = b*(a/b).
Proof. try hammer_hook "Zdiv" "Zdiv.Z_div_exact_2". Undo.  
intros; apply Z_div_exact_full_2; auto with zarith.
Qed.

Lemma Z_mod_zero_opp : forall a b:Z, b > 0 -> a mod b = 0 -> (-a) mod b = 0.
Proof. try hammer_hook "Zdiv" "Zdiv.Z_mod_zero_opp". Undo.  
intros; apply Z_mod_zero_opp_full; auto with zarith.
Qed.



Fixpoint Zmod_POS (a : positive) (b : Z) : Z  :=
match a with
| xI a' =>
let r := Zmod_POS a' b in
let r' := (2 * r + 1) in
if r' <? b then r' else (r' - b)
| xO a' =>
let r := Zmod_POS a' b in
let r' := (2 * r) in
if r' <? b then r' else (r' - b)
| xH => if 2 <=? b then 1 else 0
end.

Definition Zmod' a b :=
match a with
| Z0 => 0
| Zpos a' =>
match b with
| Z0 => 0
| Zpos _ => Zmod_POS a' b
| Zneg b' =>
let r := Zmod_POS a' (Zpos b') in
match r  with Z0 =>  0 |  _  =>   b + r end
end
| Zneg a' =>
match b with
| Z0 => 0
| Zpos _ =>
let r := Zmod_POS a' b in
match r with Z0 =>  0 | _  =>  b - r end
| Zneg b' => - (Zmod_POS a' (Zpos b'))
end
end.


Theorem Zmod_POS_correct a b : Zmod_POS a b = snd (Z.pos_div_eucl a b).
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod_POS_correct". Undo.  
induction a as [a IH|a IH| ]; simpl; rewrite ?IH.
destruct (Z.pos_div_eucl a b) as (p,q); simpl;
case Z.ltb_spec; reflexivity.
destruct (Z.pos_div_eucl a b) as (p,q); simpl;
case Z.ltb_spec; reflexivity.
case Z.leb_spec; trivial.
Qed.

Theorem Zmod'_correct: forall a b, Zmod' a b = a mod b.
Proof. try hammer_hook "Zdiv" "Zdiv.Zmod'_correct". Undo.  
intros a b; unfold Z.modulo; case a; simpl; auto.
intros p; case b; simpl; auto.
intros p1; refine (Zmod_POS_correct _ _); auto.
intros p1; rewrite Zmod_POS_correct; auto.
case (Z.pos_div_eucl p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
intros p; case b; simpl; auto.
intros p1; rewrite Zmod_POS_correct; auto.
case (Z.pos_div_eucl p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
intros p1; rewrite Zmod_POS_correct; simpl; auto.
case (Z.pos_div_eucl p (Zpos p1)); auto.
Qed.




Theorem Zdiv_eucl_extended :
forall b:Z,
b <> 0 ->
forall a:Z,
{qr : Z * Z | let (q, r) := qr in a = b * q + r /\ 0 <= r < Z.abs b}.
Proof. try hammer_hook "Zdiv" "Zdiv.Zdiv_eucl_extended". Undo.  
intros b Hb a.
destruct (Z_le_gt_dec 0 b) as [Hb'|Hb'].
- assert (Hb'' : b > 0) by omega.
rewrite Z.abs_eq; [ apply Zdiv_eucl_exist; assumption | assumption ].
- assert (Hb'' : - b > 0) by omega.
destruct (Zdiv_eucl_exist Hb'' a) as ((q,r),[]).
exists (- q, r).
split.
+ rewrite <- Z.mul_opp_comm; assumption.
+ rewrite Z.abs_neq; [ assumption | omega ].
Qed.

Arguments Zdiv_eucl_extended : default implicits.



Require Import PeanoNat.

Lemma div_Zdiv (n m: nat): m <> O ->
Z.of_nat (n / m) = Z.of_nat n / Z.of_nat m.
Proof. try hammer_hook "Zdiv" "Zdiv.div_Zdiv". Undo.  
intros.
apply (Zdiv_unique _ _ _ (Z.of_nat (n mod m))).
split. auto with zarith.
now apply inj_lt, Nat.mod_upper_bound.
rewrite <- Nat2Z.inj_mul, <- Nat2Z.inj_add.
now apply inj_eq, Nat.div_mod.
Qed.

Lemma mod_Zmod (n m: nat): m <> O ->
Z.of_nat (n mod m) = (Z.of_nat n) mod (Z.of_nat m).
Proof. try hammer_hook "Zdiv" "Zdiv.mod_Zmod". Undo.  
intros.
apply (Zmod_unique _ _ (Z.of_nat n / Z.of_nat m)).
split. auto with zarith.
now apply inj_lt, Nat.mod_upper_bound.
rewrite <- div_Zdiv, <- Nat2Z.inj_mul, <- Nat2Z.inj_add by trivial.
now apply inj_eq, Nat.div_mod.
Qed.
