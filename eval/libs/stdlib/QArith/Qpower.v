From Hammer Require Import Hammer.









Require Import Zpow_facts Qfield Qreduction.

Lemma Qpower_positive_1 : forall n, Qpower_positive 1 n == 1.
Proof. hammer_hook "Qpower" "Qpower.Qpower_positive_1". Restart. 
induction n;
simpl; try rewrite IHn; reflexivity.
Qed.

Lemma Qpower_1 : forall n, 1^n == 1.
Proof. hammer_hook "Qpower" "Qpower.Qpower_1". Restart. 
intros [|n|n]; simpl; try rewrite Qpower_positive_1; reflexivity.
Qed.

Lemma Qpower_positive_0 : forall n, Qpower_positive 0 n == 0.
Proof. hammer_hook "Qpower" "Qpower.Qpower_positive_0". Restart. 
induction n;
simpl; try rewrite IHn; reflexivity.
Qed.

Lemma Qpower_0 : forall n, (n<>0)%Z -> 0^n == 0.
Proof. hammer_hook "Qpower" "Qpower.Qpower_0". Restart. 
intros [|n|n] Hn; try (elim Hn; reflexivity); simpl;
rewrite Qpower_positive_0; reflexivity.
Qed.

Lemma Qpower_not_0_positive : forall a n, ~a==0 -> ~Qpower_positive a n == 0.
Proof. hammer_hook "Qpower" "Qpower.Qpower_not_0_positive". Restart. 
intros a n X H.
apply X; clear X.
induction n; simpl in *; try assumption;
destruct (Qmult_integral _ _ H);
try destruct (Qmult_integral _ _ H0); auto.
Qed.

Lemma Qpower_pos_positive : forall p n, 0 <= p -> 0 <= Qpower_positive p n.
Proof. hammer_hook "Qpower" "Qpower.Qpower_pos_positive". Restart. 
intros p n Hp.
induction n; simpl; repeat apply Qmult_le_0_compat;assumption.
Qed.

Lemma Qpower_pos : forall p n, 0 <= p -> 0 <= p^n.
Proof. hammer_hook "Qpower" "Qpower.Qpower_pos". Restart. 
intros p [|n|n] Hp; simpl; try discriminate;
try apply Qinv_le_0_compat;  apply Qpower_pos_positive; assumption.
Qed.

Lemma Qmult_power_positive  : forall a b n, Qpower_positive (a*b) n == (Qpower_positive a n)*(Qpower_positive b n).
Proof. hammer_hook "Qpower" "Qpower.Qmult_power_positive". Restart. 
induction n;
simpl; repeat rewrite IHn; ring.
Qed.

Lemma Qmult_power : forall a b n, (a*b)^n == a^n*b^n.
Proof. hammer_hook "Qpower" "Qpower.Qmult_power". Restart. 
intros a b [|n|n]; simpl;
try rewrite Qmult_power_positive;
try rewrite Qinv_mult_distr;
reflexivity.
Qed.

Lemma Qinv_power_positive  : forall a n, Qpower_positive (/a) n == /(Qpower_positive a n).
Proof. hammer_hook "Qpower" "Qpower.Qinv_power_positive". Restart. 
induction n;
simpl; repeat (rewrite IHn || rewrite Qinv_mult_distr); reflexivity.
Qed.

Lemma Qinv_power : forall a n, (/a)^n == /a^n.
Proof. hammer_hook "Qpower" "Qpower.Qinv_power". Restart. 
intros a [|n|n]; simpl;
try rewrite Qinv_power_positive;
reflexivity.
Qed.

Lemma Qdiv_power : forall a b n, (a/b)^n == (a^n/b^n).
Proof. hammer_hook "Qpower" "Qpower.Qdiv_power". Restart. 
unfold Qdiv.
intros a b n.
rewrite Qmult_power.
rewrite Qinv_power.
reflexivity.
Qed.

Lemma Qinv_power_n : forall n p, (1#p)^n == /(inject_Z ('p))^n.
Proof. hammer_hook "Qpower" "Qpower.Qinv_power_n". Restart. 
intros n p.
rewrite Qmake_Qdiv.
rewrite Qdiv_power.
rewrite Qpower_1.
unfold Qdiv.
ring.
Qed.

Lemma Qpower_plus_positive : forall a n m, Qpower_positive a (n+m) == (Qpower_positive a n)*(Qpower_positive a m).
Proof. hammer_hook "Qpower" "Qpower.Qpower_plus_positive". Restart. 
intros a n m.
unfold Qpower_positive.
apply pow_pos_add.
apply Q_Setoid.
apply Qmult_comp.
apply Qmult_assoc.
Qed.

Lemma Qpower_opp : forall a n, a^(-n) == /a^n.
Proof. hammer_hook "Qpower" "Qpower.Qpower_opp". Restart. 
intros a [|n|n]; simpl; try reflexivity.
symmetry; apply Qinv_involutive.
Qed.

Lemma Qpower_minus_positive : forall a (n m:positive),
(m < n)%positive ->
Qpower_positive a (n-m)%positive == (Qpower_positive a n)/(Qpower_positive a m).
Proof. hammer_hook "Qpower" "Qpower.Qpower_minus_positive". Restart. 
intros a n m H.
destruct (Qeq_dec a 0) as [EQ|NEQ].
- now rewrite EQ, !Qpower_positive_0.
- rewrite <- (Qdiv_mult_l (Qpower_positive a (n - m)) (Qpower_positive a m)) by
(now apply Qpower_not_0_positive).
f_equiv.
rewrite <- Qpower_plus_positive.
now rewrite Pos.sub_add.
Qed.

Lemma Qpower_plus : forall a n m, ~a==0 -> a^(n+m) == a^n*a^m.
Proof. hammer_hook "Qpower" "Qpower.Qpower_plus". Restart. 
intros a [|n|n] [|m|m] H; simpl; try ring;
try rewrite Qpower_plus_positive;
try apply Qinv_mult_distr; try reflexivity;
rewrite ?Z.pos_sub_spec;
case Pos.compare_spec; intros H0; simpl; subst;
try rewrite Qpower_minus_positive;
try (field; try split; apply Qpower_not_0_positive);
assumption.
Qed.

Lemma Qpower_plus' : forall a n m, (n+m <> 0)%Z -> a^(n+m) == a^n*a^m.
Proof. hammer_hook "Qpower" "Qpower.Qpower_plus'". Restart. 
intros a n m H.
destruct (Qeq_dec a 0)as [X|X].
rewrite X.
rewrite Qpower_0 by assumption.
destruct n; destruct m; try (elim H; reflexivity);
simpl; repeat rewrite Qpower_positive_0; ring_simplify;
reflexivity.
apply Qpower_plus.
assumption.
Qed.

Lemma Qpower_mult_positive : forall a n m,
Qpower_positive a (n*m) == Qpower_positive (Qpower_positive a n) m.
Proof. hammer_hook "Qpower" "Qpower.Qpower_mult_positive". Restart. 
intros a n m.
induction n using Pos.peano_ind.
reflexivity.
rewrite Pos.mul_succ_l.
rewrite <- Pos.add_1_l.
do 2 rewrite Qpower_plus_positive.
rewrite IHn.
rewrite Qmult_power_positive.
reflexivity.
Qed.

Lemma Qpower_mult : forall a n m, a^(n*m) ==  (a^n)^m.
Proof. hammer_hook "Qpower" "Qpower.Qpower_mult". Restart. 
intros a [|n|n] [|m|m]; simpl;
try rewrite Qpower_positive_1;
try rewrite Qpower_mult_positive;
try rewrite Qinv_power_positive;
try rewrite Qinv_involutive;
try reflexivity.
Qed.

Lemma Zpower_Qpower : forall (a n:Z), (0<=n)%Z -> inject_Z (a^n) == (inject_Z a)^n.
Proof. hammer_hook "Qpower" "Qpower.Zpower_Qpower". Restart. 
intros a [|n|n] H;[reflexivity| |elim H; reflexivity].
induction n using Pos.peano_ind.
replace (a^1)%Z with a by ring.
ring.
rewrite Pos2Z.inj_succ.
unfold Z.succ.
rewrite Zpower_exp; auto with *; try discriminate.
rewrite Qpower_plus' by discriminate.
rewrite <- IHn by discriminate.
replace (a^'n*a^1)%Z with (a^'n*a)%Z by ring.
ring_simplify.
reflexivity.
Qed.

Lemma Qsqr_nonneg : forall a, 0 <= a^2.
Proof. hammer_hook "Qpower" "Qpower.Qsqr_nonneg". Restart. 
intros a.
destruct (Qlt_le_dec 0 a) as [A|A].
apply (Qmult_le_0_compat a a);
(apply Qlt_le_weak; assumption).
setoid_replace (a^2) with ((-a)*(-a)) by ring.
rewrite Qle_minus_iff in A.
setoid_replace (0+ - a) with (-a) in A by ring.
apply Qmult_le_0_compat; assumption.
Qed.

Theorem Qpower_decomp p x y :
Qpower_positive (x#y) p = x ^ Zpos p # (y ^ p).
Proof. hammer_hook "Qpower" "Qpower.Qpower_decomp". Restart. 
induction p; intros; simpl Qpower_positive; rewrite ?IHp.
-
unfold Qmult, Qnum, Qden. f_equal.
+ now rewrite <- Z.pow_twice_r, <- Z.pow_succ_r.
+ apply Pos2Z.inj; rewrite !Pos2Z.inj_mul, !Pos2Z.inj_pow.
now rewrite <- Z.pow_twice_r, <- Z.pow_succ_r.
-
unfold Qmult, Qnum, Qden. f_equal.
+ now rewrite <- Z.pow_twice_r.
+ apply Pos2Z.inj; rewrite !Pos2Z.inj_mul, !Pos2Z.inj_pow.
now rewrite <- Z.pow_twice_r.
-
now rewrite Z.pow_1_r, Pos.pow_1_r.
Qed.
