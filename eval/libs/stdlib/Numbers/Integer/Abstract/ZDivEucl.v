From Hammer Require Import Hammer.









Require Import ZAxioms ZMulOrder ZSgnAbs NZDiv.



Module Type EuclidSpec (Import A : ZAxiomsSig')(Import B : DivMod A).
Axiom mod_always_pos : forall a b, b ~= 0 -> 0 <= B.modulo a b < abs b.
End EuclidSpec.

Module Type ZEuclid (Z:ZAxiomsSig) := NZDiv.NZDiv Z <+ EuclidSpec Z.

Module ZEuclidProp
(Import A : ZAxiomsSig')
(Import B : ZMulOrderProp A)
(Import C : ZSgnAbsProp A B)
(Import D : ZEuclid A).


Infix "/" := D.div : euclid.
Infix "mod" := D.modulo : euclid.
Local Open Scope euclid.

Module Import Private_NZDiv := Nop <+ NZDivProp A D B.



Lemma mod_eq :
forall a b, b~=0 -> a mod b == a - b*(a/b).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_eq".  
intros.
rewrite <- add_move_l.
symmetry. now apply div_mod.
Qed.

Ltac pos_or_neg a :=
let LT := fresh "LT" in
let LE := fresh "LE" in
destruct (le_gt_cases 0 a) as [LE|LT]; [|rewrite <- opp_pos_neg in LT].



Theorem div_mod_unique : forall b q1 q2 r1 r2 : t,
0<=r1<abs b -> 0<=r2<abs b ->
b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_mod_unique".  
intros b q1 q2 r1 r2 Hr1 Hr2 EQ.
pos_or_neg b.
rewrite abs_eq in * by trivial.
apply div_mod_unique with b; trivial.
rewrite abs_neq' in * by auto using lt_le_incl.
rewrite eq_sym_iff. apply div_mod_unique with (-b); trivial.
rewrite 2 mul_opp_l.
rewrite add_move_l, sub_opp_r.
rewrite <-add_assoc.
symmetry. rewrite add_move_l, sub_opp_r.
now rewrite (add_comm r2), (add_comm r1).
Qed.

Theorem div_unique:
forall a b q r, 0<=r<abs b -> a == b*q + r -> q == a/b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_unique".  
intros a b q r Hr EQ.
assert (Hb : b~=0).
pos_or_neg b.
rewrite abs_eq in Hr; intuition; order.
rewrite <- opp_0, eq_opp_r. rewrite abs_neq' in Hr; intuition; order.
destruct (div_mod_unique b q (a/b) r (a mod b)); trivial.
now apply mod_always_pos.
now rewrite <- div_mod.
Qed.

Theorem mod_unique:
forall a b q r, 0<=r<abs b -> a == b*q + r -> r == a mod b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_unique".  
intros a b q r Hr EQ.
assert (Hb : b~=0).
pos_or_neg b.
rewrite abs_eq in Hr; intuition; order.
rewrite <- opp_0, eq_opp_r. rewrite abs_neq' in Hr; intuition; order.
destruct (div_mod_unique b q (a/b) r (a mod b)); trivial.
now apply mod_always_pos.
now rewrite <- div_mod.
Qed.



Lemma div_opp_r : forall a b, b~=0 -> a/(-b) == -(a/b).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_opp_r".  
intros. symmetry.
apply div_unique with (a mod b).
rewrite abs_opp; now apply mod_always_pos.
rewrite mul_opp_opp; now apply div_mod.
Qed.

Lemma mod_opp_r : forall a b, b~=0 -> a mod (-b) == a mod b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_opp_r".  
intros. symmetry.
apply mod_unique with (-(a/b)).
rewrite abs_opp; now apply mod_always_pos.
rewrite mul_opp_opp; now apply div_mod.
Qed.

Lemma div_opp_l_z : forall a b, b~=0 -> a mod b == 0 ->
(-a)/b == -(a/b).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_opp_l_z".  
intros a b Hb Hab. symmetry.
apply div_unique with (-(a mod b)).
rewrite Hab, opp_0. split; [order|].
pos_or_neg b; [rewrite abs_eq | rewrite abs_neq']; order.
now rewrite mul_opp_r, <-opp_add_distr, <-div_mod.
Qed.

Lemma div_opp_l_nz : forall a b, b~=0 -> a mod b ~= 0 ->
(-a)/b == -(a/b)-sgn b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_opp_l_nz".  
intros a b Hb Hab. symmetry.
apply div_unique with (abs b -(a mod b)).
rewrite lt_sub_lt_add_l.
rewrite <- le_add_le_sub_l. nzsimpl.
rewrite <- (add_0_l (abs b)) at 2.
rewrite <- add_lt_mono_r.
destruct (mod_always_pos a b); intuition order.
rewrite <- 2 add_opp_r, mul_add_distr_l, 2 mul_opp_r.
rewrite sgn_abs.
rewrite add_shuffle2, add_opp_diag_l; nzsimpl.
rewrite <-opp_add_distr, <-div_mod; order.
Qed.

Lemma mod_opp_l_z : forall a b, b~=0 -> a mod b == 0 ->
(-a) mod b == 0.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_opp_l_z".  
intros a b Hb Hab. symmetry.
apply mod_unique with (-(a/b)).
split; [order|now rewrite abs_pos].
now rewrite <-opp_0, <-Hab, mul_opp_r, <-opp_add_distr, <-div_mod.
Qed.

Lemma mod_opp_l_nz : forall a b, b~=0 -> a mod b ~= 0 ->
(-a) mod b == abs b - (a mod b).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_opp_l_nz".  
intros a b Hb Hab. symmetry.
apply mod_unique with (-(a/b)-sgn b).
rewrite lt_sub_lt_add_l.
rewrite <- le_add_le_sub_l. nzsimpl.
rewrite <- (add_0_l (abs b)) at 2.
rewrite <- add_lt_mono_r.
destruct (mod_always_pos a b); intuition order.
rewrite <- 2 add_opp_r, mul_add_distr_l, 2 mul_opp_r.
rewrite sgn_abs.
rewrite add_shuffle2, add_opp_diag_l; nzsimpl.
rewrite <-opp_add_distr, <-div_mod; order.
Qed.

Lemma div_opp_opp_z : forall a b, b~=0 -> a mod b == 0 ->
(-a)/(-b) == a/b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_opp_opp_z".  
intros. now rewrite div_opp_r, div_opp_l_z, opp_involutive.
Qed.

Lemma div_opp_opp_nz : forall a b, b~=0 -> a mod b ~= 0 ->
(-a)/(-b) == a/b + sgn(b).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_opp_opp_nz".  
intros. rewrite div_opp_r, div_opp_l_nz by trivial.
now rewrite opp_sub_distr, opp_involutive.
Qed.

Lemma mod_opp_opp_z : forall a b, b~=0 -> a mod b == 0 ->
(-a) mod (-b) == 0.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_opp_opp_z".  
intros. now rewrite mod_opp_r, mod_opp_l_z.
Qed.

Lemma mod_opp_opp_nz : forall a b, b~=0 -> a mod b ~= 0 ->
(-a) mod (-b) == abs b - a mod b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_opp_opp_nz".  
intros. now rewrite mod_opp_r, mod_opp_l_nz.
Qed.



Lemma div_same : forall a, a~=0 -> a/a == 1.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_same".  
intros. symmetry. apply div_unique with 0.
split; [order|now rewrite abs_pos].
now nzsimpl.
Qed.

Lemma mod_same : forall a, a~=0 -> a mod a == 0.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_same".  
intros.
rewrite mod_eq, div_same by trivial. nzsimpl. apply sub_diag.
Qed.



Theorem div_small: forall a b, 0<=a<b -> a/b == 0.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_small".   exact div_small. Qed.



Theorem mod_small: forall a b, 0<=a<b -> a mod b == a.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_small".   exact mod_small. Qed.



Lemma div_0_l: forall a, a~=0 -> 0/a == 0.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_0_l".  
intros. pos_or_neg a. apply div_0_l; order.
apply opp_inj. rewrite <- div_opp_r, opp_0 by trivial. now apply div_0_l.
Qed.

Lemma mod_0_l: forall a, a~=0 -> 0 mod a == 0.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_0_l".  
intros; rewrite mod_eq, div_0_l; now nzsimpl.
Qed.

Lemma div_1_r: forall a, a/1 == a.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_1_r".  
intros. symmetry. apply div_unique with 0.
assert (H:=lt_0_1); rewrite abs_pos; intuition; order.
now nzsimpl.
Qed.

Lemma mod_1_r: forall a, a mod 1 == 0.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_1_r".  
intros. rewrite mod_eq, div_1_r; nzsimpl; auto using sub_diag.
apply neq_sym, lt_neq; apply lt_0_1.
Qed.

Lemma div_1_l: forall a, 1<a -> 1/a == 0.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_1_l".   exact div_1_l. Qed.

Lemma mod_1_l: forall a, 1<a -> 1 mod a == 1.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_1_l".   exact mod_1_l. Qed.

Lemma div_mul : forall a b, b~=0 -> (a*b)/b == a.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_mul".  
intros. symmetry. apply div_unique with 0.
split; [order|now rewrite abs_pos].
nzsimpl; apply mul_comm.
Qed.

Lemma mod_mul : forall a b, b~=0 -> (a*b) mod b == 0.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_mul".  
intros. rewrite mod_eq, div_mul by trivial. rewrite mul_comm; apply sub_diag.
Qed.

Theorem div_unique_exact a b q: b~=0 -> a == b*q -> q == a/b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_unique_exact".  
intros Hb H. rewrite H, mul_comm. symmetry. now apply div_mul.
Qed.





Theorem mod_le: forall a b, 0<=a -> b~=0 -> a mod b <= a.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_le".  
intros. pos_or_neg b. apply mod_le; order.
rewrite <- mod_opp_r by trivial. apply mod_le; order.
Qed.

Theorem div_pos : forall a b, 0<=a -> 0<b -> 0<= a/b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_pos".   exact div_pos. Qed.

Lemma div_str_pos : forall a b, 0<b<=a -> 0 < a/b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_str_pos".   exact div_str_pos. Qed.

Lemma div_small_iff : forall a b, b~=0 -> (a/b==0 <-> 0<=a<abs b).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_small_iff".  
intros a b Hb.
split.
intros EQ.
rewrite (div_mod a b Hb), EQ; nzsimpl.
now apply mod_always_pos.
intros. pos_or_neg b.
apply div_small.
now rewrite <- (abs_eq b).
apply opp_inj; rewrite opp_0, <- div_opp_r by trivial.
apply div_small.
rewrite <- (abs_neq' b) by order. trivial.
Qed.

Lemma mod_small_iff : forall a b, b~=0 -> (a mod b == a <-> 0<=a<abs b).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_small_iff".  
intros.
rewrite <- div_small_iff, mod_eq by trivial.
rewrite sub_move_r, <- (add_0_r a) at 1. rewrite add_cancel_l.
rewrite eq_sym_iff, eq_mul_0. tauto.
Qed.



Lemma div_lt : forall a b, 0<a -> 1<b -> a/b < a.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_lt".   exact div_lt. Qed.



Lemma div_le_mono : forall a b c, 0<c -> a<=b -> a/c <= b/c.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_le_mono".  
intros a b c Hc Hab.
rewrite lt_eq_cases in Hab. destruct Hab as [LT|EQ];
[|rewrite EQ; order].
rewrite <- lt_succ_r.
rewrite (mul_lt_mono_pos_l c) by order.
nzsimpl.
rewrite (add_lt_mono_r _ _ (a mod c)).
rewrite <- div_mod by order.
apply lt_le_trans with b; trivial.
rewrite (div_mod b c) at 1 by order.
rewrite <- add_assoc, <- add_le_mono_l.
apply le_trans with (c+0).
nzsimpl; destruct (mod_always_pos b c); try order.
rewrite abs_eq in *; order.
rewrite <- add_le_mono_l. destruct (mod_always_pos a c); order.
Qed.



Lemma mul_div_le : forall a b, b~=0 -> b*(a/b) <= a.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mul_div_le".  
intros.
rewrite (div_mod a b) at 2; trivial.
rewrite <- (add_0_r (b*(a/b))) at 1.
rewrite <- add_le_mono_l.
now destruct (mod_always_pos a b).
Qed.



Lemma mul_succ_div_gt: forall a b, 0<b -> a < b*(S (a/b)).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mul_succ_div_gt".  
intros.
nzsimpl.
rewrite (div_mod a b) at 1; try order.
rewrite <- add_lt_mono_l.
destruct (mod_always_pos a b). order.
rewrite abs_eq in *; order.
Qed.

Lemma mul_pred_div_gt: forall a b, b<0 -> a < b*(P (a/b)).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mul_pred_div_gt".  
intros a b Hb.
rewrite mul_pred_r, <- add_opp_r.
rewrite (div_mod a b) at 1; try order.
rewrite <- add_lt_mono_l.
destruct (mod_always_pos a b). order.
rewrite <- opp_pos_neg in Hb. rewrite abs_neq' in *; order.
Qed.





Lemma div_exact : forall a b, b~=0 -> (a == b*(a/b) <-> a mod b == 0).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_exact".  
intros.
rewrite (div_mod a b) at 1; try order.
rewrite <- (add_0_r (b*(a/b))) at 2.
apply add_cancel_l.
Qed.



Theorem div_lt_upper_bound:
forall a b q, 0<b -> a < b*q -> a/b < q.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_lt_upper_bound".  
intros.
rewrite (mul_lt_mono_pos_l b) by trivial.
apply le_lt_trans with a; trivial.
apply mul_div_le; order.
Qed.

Theorem div_le_upper_bound:
forall a b q, 0<b -> a <= b*q -> a/b <= q.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_le_upper_bound".  
intros.
rewrite <- (div_mul q b) by order.
apply div_le_mono; trivial. now rewrite mul_comm.
Qed.

Theorem div_le_lower_bound:
forall a b q, 0<b -> b*q <= a -> q <= a/b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_le_lower_bound".  
intros.
rewrite <- (div_mul q b) by order.
apply div_le_mono; trivial. now rewrite mul_comm.
Qed.



Lemma div_le_compat_l: forall p q r, 0<=p -> 0<q<=r -> p/r <= p/q.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_le_compat_l".   exact div_le_compat_l. Qed.



Lemma mod_add : forall a b c, c~=0 ->
(a + b * c) mod c == a mod c.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_add".  
intros.
symmetry.
apply mod_unique with (a/c+b); trivial.
now apply mod_always_pos.
rewrite mul_add_distr_l, add_shuffle0, <- div_mod by order.
now rewrite mul_comm.
Qed.

Lemma div_add : forall a b c, c~=0 ->
(a + b * c) / c == a / c + b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_add".  
intros.
apply (mul_cancel_l _ _ c); try order.
apply (add_cancel_r _ _ ((a+b*c) mod c)).
rewrite <- div_mod, mod_add by order.
rewrite mul_add_distr_l, add_shuffle0, <- div_mod by order.
now rewrite mul_comm.
Qed.

Lemma div_add_l: forall a b c, b~=0 ->
(a * b + c) / b == a + c / b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_add_l".  
intros a b c. rewrite (add_comm _ c), (add_comm a).
now apply div_add.
Qed.





Lemma div_mul_cancel_r : forall a b c, b~=0 -> 0<c ->
(a*c)/(b*c) == a/b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_mul_cancel_r".  
intros.
symmetry.
apply div_unique with ((a mod b)*c).

rewrite abs_mul, (abs_eq c) by order.
rewrite <-(mul_0_l c), <-mul_lt_mono_pos_r, <-mul_le_mono_pos_r by trivial.
now apply mod_always_pos.

rewrite (div_mod a b) at 1 by order.
rewrite mul_add_distr_r.
rewrite add_cancel_r.
rewrite <- 2 mul_assoc. now rewrite (mul_comm c).
Qed.

Lemma div_mul_cancel_l : forall a b c, b~=0 -> 0<c ->
(c*a)/(c*b) == a/b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_mul_cancel_l".  
intros. rewrite !(mul_comm c); now apply div_mul_cancel_r.
Qed.

Lemma mul_mod_distr_l: forall a b c, b~=0 -> 0<c ->
(c*a) mod (c*b) == c * (a mod b).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mul_mod_distr_l".  
intros.
rewrite <- (add_cancel_l _ _ ((c*b)* ((c*a)/(c*b)))).
rewrite <- div_mod.
rewrite div_mul_cancel_l by trivial.
rewrite <- mul_assoc, <- mul_add_distr_l, mul_cancel_l by order.
apply div_mod; order.
rewrite <- neq_mul_0; intuition; order.
Qed.

Lemma mul_mod_distr_r: forall a b c, b~=0 -> 0<c ->
(a*c) mod (b*c) == (a mod b) * c.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mul_mod_distr_r".  
intros. rewrite !(mul_comm _ c); now rewrite mul_mod_distr_l.
Qed.




Theorem mod_mod: forall a n, n~=0 ->
(a mod n) mod n == a mod n.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_mod".  
intros. rewrite mod_small_iff by trivial.
now apply mod_always_pos.
Qed.

Lemma mul_mod_idemp_l : forall a b n, n~=0 ->
((a mod n)*b) mod n == (a*b) mod n.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mul_mod_idemp_l".  
intros a b n Hn. symmetry.
rewrite (div_mod a n) at 1 by order.
rewrite add_comm, (mul_comm n), (mul_comm _ b).
rewrite mul_add_distr_l, mul_assoc.
rewrite mod_add by trivial.
now rewrite mul_comm.
Qed.

Lemma mul_mod_idemp_r : forall a b n, n~=0 ->
(a*(b mod n)) mod n == (a*b) mod n.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mul_mod_idemp_r".  
intros. rewrite !(mul_comm a). now apply mul_mod_idemp_l.
Qed.

Theorem mul_mod: forall a b n, n~=0 ->
(a * b) mod n == ((a mod n) * (b mod n)) mod n.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mul_mod".  
intros. now rewrite mul_mod_idemp_l, mul_mod_idemp_r.
Qed.

Lemma add_mod_idemp_l : forall a b n, n~=0 ->
((a mod n)+b) mod n == (a+b) mod n.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.add_mod_idemp_l".  
intros a b n Hn. symmetry.
rewrite (div_mod a n) at 1 by order.
rewrite <- add_assoc, add_comm, mul_comm.
now rewrite mod_add.
Qed.

Lemma add_mod_idemp_r : forall a b n, n~=0 ->
(a+(b mod n)) mod n == (a+b) mod n.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.add_mod_idemp_r".  
intros. rewrite !(add_comm a). now apply add_mod_idemp_l.
Qed.

Theorem add_mod: forall a b n, n~=0 ->
(a+b) mod n == (a mod n + b mod n) mod n.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.add_mod".  
intros. now rewrite add_mod_idemp_l, add_mod_idemp_r.
Qed.



Lemma div_div : forall a b c, 0<b -> c~=0 ->
(a/b)/c == a/(b*c).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_div".  
intros a b c Hb Hc.
apply div_unique with (b*((a/b) mod c) + a mod b).

rewrite abs_mul.
destruct (mod_always_pos (a/b) c), (mod_always_pos a b); try order.
split.
apply add_nonneg_nonneg; trivial.
apply mul_nonneg_nonneg; order.
apply lt_le_trans with (b*((a/b) mod c) + abs b).
now rewrite <- add_lt_mono_l.
rewrite (abs_eq b) by order.
now rewrite <- mul_succ_r, <- mul_le_mono_pos_l, le_succ_l.

rewrite (div_mod a b) at 1 by order.
rewrite add_assoc, add_cancel_r.
rewrite <- mul_assoc, <- mul_add_distr_l, mul_cancel_l by order.
apply div_mod; order.
Qed.



Lemma mod_mul_r : forall a b c, 0<b -> c~=0 ->
a mod (b*c) == a mod b + b*((a/b) mod c).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_mul_r".  
intros a b c Hb Hc.
apply add_cancel_l with (b*c*(a/(b*c))).
rewrite <- div_mod by (apply neq_mul_0; split; order).
rewrite <- div_div by trivial.
rewrite add_assoc, add_shuffle0, <- mul_assoc, <- mul_add_distr_l.
rewrite <- div_mod by order.
apply div_mod; order.
Qed.



Theorem div_mul_le:
forall a b c, 0<=a -> 0<b -> 0<=c -> c*(a/b) <= (c*a)/b.
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.div_mul_le".   exact div_mul_le. Qed.



Lemma mod_divides : forall a b, b~=0 ->
(a mod b == 0 <-> (b|a)).
Proof. try hammer_hook "ZDivEucl" "ZDivEucl.ZEuclidProp.mod_divides".  
intros a b Hb. split.
intros Hab. exists (a/b). rewrite mul_comm.
rewrite (div_mod a b Hb) at 1. rewrite Hab; now nzsimpl.
intros (c,Hc). rewrite Hc. now apply mod_mul.
Qed.

End ZEuclidProp.
