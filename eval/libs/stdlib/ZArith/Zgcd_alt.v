From Hammer Require Import Hammer.















Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zdiv.
Require Import Znumtheory.
Require Import Omega.

Open Scope Z_scope.



Fixpoint Zgcdn (n:nat) : Z -> Z -> Z := fun a b =>
match n with
| O => 1
| S n => match a with
| Z0 => Z.abs b
| Zpos _ => Zgcdn n (Z.modulo b a) a
| Zneg a => Zgcdn n (Z.modulo b (Zpos a)) (Zpos a)
end
end.

Definition Zgcd_bound (a:Z) :=
match a with
| Z0 => S O
| Zpos p => let n := Pos.size_nat p in (n+n)%nat
| Zneg p => let n := Pos.size_nat p in (n+n)%nat
end.

Definition Zgcd_alt a b := Zgcdn (Zgcd_bound a) a b.



Lemma Zgcdn_pos : forall n a b,
0 <= Zgcdn n a b.
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcdn_pos".  
induction n.
simpl; auto with zarith.
destruct a; simpl; intros; auto with zarith; auto.
Qed.

Lemma Zgcd_alt_pos : forall a b, 0 <= Zgcd_alt a b.
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcd_alt_pos".  
intros; unfold Z.gcd; apply Zgcdn_pos; auto.
Qed.





Lemma Zgcdn_linear_bound : forall n a b,
Z.abs a < Z.of_nat n -> Zis_gcd a b (Zgcdn n a b).
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcdn_linear_bound".  
induction n.
simpl; intros.
exfalso; generalize (Z.abs_nonneg a); omega.
destruct a; intros; simpl;
[ generalize (Zis_gcd_0_abs b); intuition | | ];
unfold Z.modulo;
generalize (Z_div_mod b (Zpos p) (eq_refl Gt));
destruct (Z.div_eucl b (Zpos p)) as (q,r);
intros (H0,H1);
rewrite Nat2Z.inj_succ in H; simpl Z.abs in H;
(assert (H2: Z.abs r < Z.of_nat n) by
(rewrite Z.abs_eq; auto with zarith));
assert (IH:=IHn r (Zpos p) H2); clear IHn;
simpl in IH |- *;
rewrite H0.
apply Zis_gcd_for_euclid2; auto.
apply Zis_gcd_minus; apply Zis_gcd_sym.
apply Zis_gcd_for_euclid2; auto.
Qed.



Fixpoint fibonacci (n:nat) : Z :=
match n with
| O => 1
| S O => 1
| S (S n as p) => fibonacci p + fibonacci n
end.

Lemma fibonacci_pos : forall n, 0 <= fibonacci n.
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.fibonacci_pos".  
enough (forall N n, (n<N)%nat -> 0<=fibonacci n) by eauto.
induction N.
inversion 1.
intros.
destruct n.
simpl; auto with zarith.
destruct n.
simpl; auto with zarith.
change (0 <= fibonacci (S n) + fibonacci n).
generalize (IHN n) (IHN (S n)); omega.
Qed.

Lemma fibonacci_incr :
forall n m, (n<=m)%nat -> fibonacci n <= fibonacci m.
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.fibonacci_incr".  
induction 1.
auto with zarith.
apply Z.le_trans with (fibonacci m); auto.
clear.
destruct m.
simpl; auto with zarith.
change (fibonacci (S m) <= fibonacci (S m)+fibonacci m).
generalize (fibonacci_pos m); omega.
Qed.



Lemma Zgcdn_worst_is_fibonacci : forall n a b,
0 < a < b ->
Zis_gcd a b (Zgcdn (S n) a b) ->
Zgcdn n a b <> Zgcdn (S n) a b ->
fibonacci (S n) <= a /\
fibonacci (S (S n)) <= b.
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcdn_worst_is_fibonacci".  
induction n.
intros [|a|a]; intros; simpl; omega.
intros [|a|a] b (Ha,Ha'); [simpl; omega | | easy ].
remember (S n) as m.
rewrite Heqm at 2. simpl Zgcdn.
unfold Z.modulo; generalize (Z_div_mod b (Zpos a) eq_refl).
destruct (Z.div_eucl b (Zpos a)) as (q,r).
intros (EQ,(Hr,Hr')).
Z.le_elim Hr.
-
replace (fibonacci (S (S m))) with (fibonacci (S m) + fibonacci m) by auto.
intros.
destruct (IHn r (Zpos a) (conj Hr Hr')); auto.
+ assert (EQ' : r = Zpos a * (-q) + b) by (rewrite EQ; ring).
rewrite EQ' at 1.
apply Zis_gcd_sym.
apply Zis_gcd_for_euclid2; auto.
apply Zis_gcd_sym; auto.
+ split; auto.
rewrite EQ.
apply Z.add_le_mono; auto.
apply Z.le_trans with (Zpos a * 1); auto.
now rewrite Z.mul_1_r.
apply Z.mul_le_mono_nonneg_l; auto with zarith.
change 1 with (Z.succ 0). apply Z.le_succ_l.
destruct q; auto with zarith.
assert (Zpos a * Zneg p < 0) by now compute. omega.
-
clear IHn EQ Hr'; intros _.
subst r; simpl; rewrite Heqm.
destruct n.
+ simpl. omega.
+ now destruct 1.
Qed.



Lemma Zgcdn_ok_before_fibonacci : forall n a b,
0 < a < b -> a < fibonacci (S n) ->
Zis_gcd a b (Zgcdn n a b).
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcdn_ok_before_fibonacci".  
destruct a; [ destruct 1; exfalso; omega | | destruct 1; discriminate].
cut (forall k n b,
k = (S (Pos.to_nat p) - n)%nat ->
0 < Zpos p < b -> Zpos p < fibonacci (S n) ->
Zis_gcd (Zpos p) b (Zgcdn n (Zpos p) b)).
destruct 2; eauto.
clear n; induction k.
intros.
assert (Pos.to_nat p < n)%nat by omega.
apply Zgcdn_linear_bound.
simpl.
generalize (inj_le _ _ H2).
rewrite Nat2Z.inj_succ.
rewrite positive_nat_Z; auto.
omega.
intros.
generalize (Zgcdn_worst_is_fibonacci n (Zpos p) b H0); intros.
assert (Zis_gcd (Zpos p) b (Zgcdn (S n) (Zpos p) b)).
apply IHk; auto.
omega.
replace (fibonacci (S (S n))) with (fibonacci (S n)+fibonacci n) by auto.
generalize (fibonacci_pos n); omega.
replace (Zgcdn n (Zpos p) b) with (Zgcdn (S n) (Zpos p) b); auto.
generalize (H2 H3); clear H2 H3; omega.
Qed.



Lemma Zgcd_bound_fibonacci :
forall a, 0 < a -> a < fibonacci (Zgcd_bound a).
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcd_bound_fibonacci".  
destruct a; [omega| | intro H; discriminate].
intros _.
induction p; [ | | compute; auto ];
simpl Zgcd_bound in *;
rewrite plus_comm; simpl plus;
set (n:= (Pos.size_nat p+Pos.size_nat p)%nat) in *; simpl;
assert (n <> O) by (unfold n; destruct p; simpl; auto).

destruct n as [ |m]; [elim H; auto| ].
generalize (fibonacci_pos m); rewrite Pos2Z.inj_xI; omega.

destruct n as [ |m]; [elim H; auto| ].
generalize (fibonacci_pos m); rewrite Pos2Z.inj_xO; omega.
Qed.



Lemma Zgcd_bound_opp a : Zgcd_bound (-a) = Zgcd_bound a.
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcd_bound_opp".  
now destruct a.
Qed.

Lemma Zgcdn_opp n a b : Zgcdn n (-a) b = Zgcdn n a b.
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcdn_opp".  
induction n; simpl; auto.
destruct a; simpl; auto.
Qed.

Lemma Zgcdn_is_gcd_pos n a b : (Zgcd_bound (Zpos a) <= n)%nat ->
Zis_gcd (Zpos a) b (Zgcdn n (Zpos a) b).
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcdn_is_gcd_pos".  
intros.
generalize (Zgcd_bound_fibonacci (Zpos a)).
simpl Zgcd_bound in *.
remember (Pos.size_nat a+Pos.size_nat a)%nat as m.
assert (1 < m)%nat.
{ rewrite Heqm; destruct a; simpl; rewrite 1?plus_comm;
auto with arith. }
destruct m as [ |m]; [inversion H0; auto| ].
destruct n as [ |n]; [inversion H; auto| ].
simpl Zgcdn.
unfold Z.modulo.
generalize (Z_div_mod b (Zpos a) (eq_refl Gt)).
destruct (Z.div_eucl b (Zpos a)) as (q,r).
intros (->,(H1,H2)) H3.
apply Zis_gcd_for_euclid2.
Z.le_elim H1.
+ apply Zgcdn_ok_before_fibonacci; auto.
apply Z.lt_le_trans with (fibonacci (S m));
[ omega | apply fibonacci_incr; auto].
+ subst r; simpl.
destruct m as [ |m]; [exfalso; omega| ].
destruct n as [ |n]; [exfalso; omega| ].
simpl; apply Zis_gcd_sym; apply Zis_gcd_0.
Qed.

Lemma Zgcdn_is_gcd n a b :
(Zgcd_bound a <= n)%nat -> Zis_gcd a b (Zgcdn n a b).
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcdn_is_gcd".  
destruct a.
- simpl; intros.
destruct n; [exfalso; omega | ].
simpl; generalize (Zis_gcd_0_abs b); intuition.
- apply Zgcdn_is_gcd_pos.
- rewrite <- Zgcd_bound_opp, <- Zgcdn_opp.
intros. apply Zis_gcd_minus, Zis_gcd_sym. simpl Z.opp.
now apply Zgcdn_is_gcd_pos.
Qed.

Lemma Zgcd_is_gcd :
forall a b, Zis_gcd a b (Zgcd_alt a b).
Proof. try hammer_hook "Zgcd_alt" "Zgcd_alt.Zgcd_is_gcd".  
unfold Zgcd_alt; intros; apply Zgcdn_is_gcd; auto.
Qed.


