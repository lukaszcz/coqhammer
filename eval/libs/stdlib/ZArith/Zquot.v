From Hammer Require Import Hammer.









Require Import Nnat ZArith_base ROmega ZArithRing Zdiv Morphisms.

Local Open Scope Z_scope.



Notation Ndiv_Zquot := N2Z.inj_quot (compat "8.3").
Notation Nmod_Zrem := N2Z.inj_rem (compat "8.3").
Notation Z_quot_rem_eq := Z.quot_rem' (compat "8.3").
Notation Zrem_lt := Z.rem_bound_abs (compat "8.3").
Notation Zquot_unique := Z.quot_unique (compat "8.3").
Notation Zrem_unique := Z.rem_unique (compat "8.3").
Notation Zrem_1_r := Z.rem_1_r (compat "8.3").
Notation Zquot_1_r := Z.quot_1_r (compat "8.3").
Notation Zrem_1_l := Z.rem_1_l (compat "8.3").
Notation Zquot_1_l := Z.quot_1_l (compat "8.3").
Notation Z_quot_same := Z.quot_same (compat "8.3").
Notation Z_quot_mult := Z.quot_mul (compat "8.3").
Notation Zquot_small := Z.quot_small (compat "8.3").
Notation Zrem_small := Z.rem_small (compat "8.3").
Notation Zquot2_quot := Zquot2_quot (compat "8.3").



Lemma Zquot_0_r a : a ÷ 0 = 0.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_0_r".   now destruct a. Qed.

Lemma Zrem_0_r a : Z.rem a 0 = a.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_0_r".   now destruct a. Qed.



Lemma Zrem_0_l a : Z.rem 0 a = 0.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_0_l".   now destruct a. Qed.

Lemma Zquot_0_l a : 0÷a = 0.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_0_l".   now destruct a. Qed.

Hint Resolve Zrem_0_l Zrem_0_r Zquot_0_l Zquot_0_r Z.quot_1_r Z.rem_1_r
: zarith.

Ltac zero_or_not a :=
destruct (Z.eq_decidable a 0) as [->|?];
[rewrite ?Zquot_0_l, ?Zrem_0_l, ?Zquot_0_r, ?Zrem_0_r;
auto with zarith|].

Lemma Z_rem_same a : Z.rem a a = 0.
Proof. try hammer_hook "Zquot" "Zquot.Z_rem_same".   zero_or_not a. now apply Z.rem_same. Qed.

Lemma Z_rem_mult a b : Z.rem (a*b) b = 0.
Proof. try hammer_hook "Zquot" "Zquot.Z_rem_mult".   zero_or_not b. now apply Z.rem_mul. Qed.





Theorem Zquot_opp_l a b : (-a)÷b = -(a÷b).
Proof. try hammer_hook "Zquot" "Zquot.Zquot_opp_l".   zero_or_not b. now apply Z.quot_opp_l. Qed.

Theorem Zquot_opp_r a b : a÷(-b) = -(a÷b).
Proof. try hammer_hook "Zquot" "Zquot.Zquot_opp_r".   zero_or_not b. now apply Z.quot_opp_r. Qed.

Theorem Zrem_opp_l a b : Z.rem (-a) b = -(Z.rem a b).
Proof. try hammer_hook "Zquot" "Zquot.Zrem_opp_l".   zero_or_not b. now apply Z.rem_opp_l. Qed.

Theorem Zrem_opp_r a b : Z.rem a (-b) = Z.rem a b.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_opp_r".   zero_or_not b. now apply Z.rem_opp_r. Qed.

Theorem Zquot_opp_opp a b : (-a)÷(-b) = a÷b.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_opp_opp".   zero_or_not b. now apply Z.quot_opp_opp. Qed.

Theorem Zrem_opp_opp a b : Z.rem (-a) (-b) = -(Z.rem a b).
Proof. try hammer_hook "Zquot" "Zquot.Zrem_opp_opp".   zero_or_not b. now apply Z.rem_opp_opp. Qed.



Theorem Zrem_sgn a b : 0 <= Z.sgn (Z.rem a b) * Z.sgn a.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_sgn".  
zero_or_not b.
- apply Z.square_nonneg.
- zero_or_not (Z.rem a b).
rewrite Z.rem_sign_nz; trivial. apply Z.square_nonneg.
Qed.



Theorem Zrem_sgn2 a b : 0 <= (Z.rem a b) * a.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_sgn2".  
zero_or_not b.
- apply Z.square_nonneg.
- now apply Z.rem_sign_mul.
Qed.



Theorem Zrem_lt_pos a b : 0<=a -> b<>0 -> 0 <= Z.rem a b < Z.abs b.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_lt_pos".  
intros; generalize (Z.rem_nonneg a b) (Z.rem_bound_abs a b);
romega with *.
Qed.

Theorem Zrem_lt_neg a b : a<=0 -> b<>0 -> -Z.abs b < Z.rem a b <= 0.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_lt_neg".  
intros; generalize (Z.rem_nonpos a b) (Z.rem_bound_abs a b);
romega with *.
Qed.

Theorem Zrem_lt_pos_pos a b : 0<=a -> 0<b -> 0 <= Z.rem a b < b.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_lt_pos_pos".  
intros; generalize (Zrem_lt_pos a b); romega with *.
Qed.

Theorem Zrem_lt_pos_neg a b : 0<=a -> b<0 -> 0 <= Z.rem a b < -b.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_lt_pos_neg".  
intros; generalize (Zrem_lt_pos a b); romega with *.
Qed.

Theorem Zrem_lt_neg_pos a b : a<=0 -> 0<b -> -b < Z.rem a b <= 0.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_lt_neg_pos".  
intros; generalize (Zrem_lt_neg a b); romega with *.
Qed.

Theorem Zrem_lt_neg_neg a b : a<=0 -> b<0 -> b < Z.rem a b <= 0.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_lt_neg_neg".  
intros; generalize (Zrem_lt_neg a b); romega with *.
Qed.




Definition Remainder a b r :=
(0 <= a /\ 0 <= r < Z.abs b) \/ (a <= 0 /\ -Z.abs b < r <= 0).

Definition Remainder_alt a b r :=
Z.abs r < Z.abs b /\ 0 <= r * a.

Lemma Remainder_equiv : forall a b r,
Remainder a b r <-> Remainder_alt a b r.
Proof. try hammer_hook "Zquot" "Zquot.Remainder_equiv".  
unfold Remainder, Remainder_alt; intuition.
- romega with *.
- romega with *.
- rewrite <-(Z.mul_opp_opp). apply Z.mul_nonneg_nonneg; romega.
- assert (0 <= Z.sgn r * Z.sgn a).
{ rewrite <-Z.sgn_mul, Z.sgn_nonneg; auto. }
destruct r; simpl Z.sgn in *; romega with *.
Qed.

Theorem Zquot_mod_unique_full a b q r :
Remainder a b r -> a = b*q + r -> q = a÷b /\ r = Z.rem a b.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_mod_unique_full".  
destruct 1 as [(H,H0)|(H,H0)]; intros.
apply Zdiv_mod_unique with b; auto.
apply Zrem_lt_pos; auto.
romega with *.
rewrite <- H1; apply Z.quot_rem'.

rewrite <- (Z.opp_involutive a).
rewrite Zquot_opp_l, Zrem_opp_l.
generalize (Zdiv_mod_unique b (-q) (-a÷b) (-r) (Z.rem (-a) b)).
generalize (Zrem_lt_pos (-a) b).
rewrite <-Z.quot_rem', Z.mul_opp_r, <-Z.opp_add_distr, <-H1.
romega with *.
Qed.

Theorem Zquot_unique_full a b q r :
Remainder a b r -> a = b*q + r -> q = a÷b.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_unique_full".  
intros; destruct (Zquot_mod_unique_full a b q r); auto.
Qed.

Theorem Zrem_unique_full a b q r :
Remainder a b r -> a = b*q + r -> r = Z.rem a b.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_unique_full".  
intros; destruct (Zquot_mod_unique_full a b q r); auto.
Qed.





Lemma Z_quot_pos a b : 0 <= a -> 0 <= b -> 0 <= a÷b.
Proof. try hammer_hook "Zquot" "Zquot.Z_quot_pos".   intros. zero_or_not b. apply Z.quot_pos; auto with zarith. Qed.



Lemma Z_quot_lt a b : 0 < a -> 2 <= b -> a÷b < a.
Proof. try hammer_hook "Zquot" "Zquot.Z_quot_lt".   intros. apply Z.quot_lt; auto with zarith. Qed.



Lemma Z_quot_monotone a b c : 0<=c -> a<=b -> a÷c <= b÷c.
Proof. try hammer_hook "Zquot" "Zquot.Z_quot_monotone".   intros. zero_or_not c. apply Z.quot_le_mono; auto with zarith. Qed.



Lemma Z_mult_quot_le a b : 0 <= a -> 0 <= b*(a÷b) <= a.
Proof. try hammer_hook "Zquot" "Zquot.Z_mult_quot_le".   intros. zero_or_not b. apply Z.mul_quot_le; auto with zarith. Qed.

Lemma Z_mult_quot_ge a b : a <= 0 -> a <= b*(a÷b) <= 0.
Proof. try hammer_hook "Zquot" "Zquot.Z_mult_quot_ge".   intros. zero_or_not b. apply Z.mul_quot_ge; auto with zarith. Qed.



Lemma Z_quot_exact_full a b : a = b*(a÷b) <-> Z.rem a b = 0.
Proof. try hammer_hook "Zquot" "Zquot.Z_quot_exact_full".   intros. zero_or_not b. intuition. apply Z.quot_exact; auto. Qed.



Theorem Zrem_le a b : 0 <= a -> 0 <= b -> Z.rem a b <= a.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_le".   intros. zero_or_not b. apply Z.rem_le; auto with zarith. Qed.



Theorem Zquot_le_upper_bound:
forall a b q, 0 < b -> a <= q*b -> a÷b <= q.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_le_upper_bound".   intros a b q; rewrite Z.mul_comm; apply Z.quot_le_upper_bound. Qed.

Theorem Zquot_lt_upper_bound:
forall a b q, 0 <= a -> 0 < b -> a < q*b -> a÷b < q.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_lt_upper_bound".   intros a b q; rewrite Z.mul_comm; apply Z.quot_lt_upper_bound. Qed.

Theorem Zquot_le_lower_bound:
forall a b q, 0 < b -> q*b <= a -> q <= a÷b.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_le_lower_bound".   intros a b q; rewrite Z.mul_comm; apply Z.quot_le_lower_bound. Qed.

Theorem Zquot_sgn: forall a b,
0 <= Z.sgn (a÷b) * Z.sgn a * Z.sgn b.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_sgn".  
destruct a as [ |a|a]; destruct b as [ |b|b]; simpl; auto with zarith;
unfold Z.quot; simpl; destruct N.pos_div_eucl; simpl; destruct n; simpl; auto with zarith.
Qed.





Lemma Z_rem_plus : forall a b c:Z,
0 <= (a+b*c) * a ->
Z.rem (a + b * c) c = Z.rem a c.
Proof. try hammer_hook "Zquot" "Zquot.Z_rem_plus".   intros. zero_or_not c. apply Z.rem_add; auto with zarith. Qed.

Lemma Z_quot_plus : forall a b c:Z,
0 <= (a+b*c) * a -> c<>0 ->
(a + b * c) ÷ c = a ÷ c + b.
Proof. try hammer_hook "Zquot" "Zquot.Z_quot_plus".   intros. apply Z.quot_add; auto with zarith. Qed.

Theorem Z_quot_plus_l: forall a b c : Z,
0 <= (a*b+c)*c -> b<>0 ->
b<>0 -> (a * b + c) ÷ b = a + c ÷ b.
Proof. try hammer_hook "Zquot" "Zquot.Z_quot_plus_l".   intros. apply Z.quot_add_l; auto with zarith. Qed.



Lemma Zquot_mult_cancel_r : forall a b c:Z,
c<>0 -> (a*c)÷(b*c) = a÷b.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_mult_cancel_r".   intros. zero_or_not b. apply Z.quot_mul_cancel_r; auto. Qed.

Lemma Zquot_mult_cancel_l : forall a b c:Z,
c<>0 -> (c*a)÷(c*b) = a÷b.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_mult_cancel_l".  
intros. rewrite (Z.mul_comm c b). zero_or_not b.
rewrite (Z.mul_comm b c). apply Z.quot_mul_cancel_l; auto.
Qed.

Lemma Zmult_rem_distr_l: forall a b c,
Z.rem (c*a) (c*b) = c * (Z.rem a b).
Proof. try hammer_hook "Zquot" "Zquot.Zmult_rem_distr_l".  
intros. zero_or_not c. rewrite (Z.mul_comm c b). zero_or_not b.
rewrite (Z.mul_comm b c). apply Z.mul_rem_distr_l; auto.
Qed.

Lemma Zmult_rem_distr_r: forall a b c,
Z.rem (a*c) (b*c) = (Z.rem a b) * c.
Proof. try hammer_hook "Zquot" "Zquot.Zmult_rem_distr_r".  
intros. zero_or_not b. rewrite (Z.mul_comm b c). zero_or_not c.
rewrite (Z.mul_comm c b). apply Z.mul_rem_distr_r; auto.
Qed.



Theorem Zrem_rem: forall a n, Z.rem (Z.rem a n) n = Z.rem a n.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_rem".   intros. zero_or_not n. apply Z.rem_rem; auto. Qed.

Theorem Zmult_rem: forall a b n,
Z.rem (a * b) n = Z.rem (Z.rem a n * Z.rem b n) n.
Proof. try hammer_hook "Zquot" "Zquot.Zmult_rem".   intros. zero_or_not n. apply Z.mul_rem; auto. Qed.



Theorem Zplus_rem: forall a b n,
0 <= a * b ->
Z.rem (a + b) n = Z.rem (Z.rem a n + Z.rem b n) n.
Proof. try hammer_hook "Zquot" "Zquot.Zplus_rem".   intros. zero_or_not n. apply Z.add_rem; auto. Qed.

Lemma Zplus_rem_idemp_l: forall a b n,
0 <= a * b ->
Z.rem (Z.rem a n + b) n = Z.rem (a + b) n.
Proof. try hammer_hook "Zquot" "Zquot.Zplus_rem_idemp_l".   intros. zero_or_not n. apply Z.add_rem_idemp_l; auto. Qed.

Lemma Zplus_rem_idemp_r: forall a b n,
0 <= a*b ->
Z.rem (b + Z.rem a n) n = Z.rem (b + a) n.
Proof. try hammer_hook "Zquot" "Zquot.Zplus_rem_idemp_r".  
intros. zero_or_not n. apply Z.add_rem_idemp_r; auto.
rewrite Z.mul_comm; auto.
Qed.

Lemma Zmult_rem_idemp_l: forall a b n, Z.rem (Z.rem a n * b) n = Z.rem (a * b) n.
Proof. try hammer_hook "Zquot" "Zquot.Zmult_rem_idemp_l".   intros. zero_or_not n. apply Z.mul_rem_idemp_l; auto. Qed.

Lemma Zmult_rem_idemp_r: forall a b n, Z.rem (b * Z.rem a n) n = Z.rem (b * a) n.
Proof. try hammer_hook "Zquot" "Zquot.Zmult_rem_idemp_r".   intros. zero_or_not n. apply Z.mul_rem_idemp_r; auto. Qed.



Lemma Zquot_Zquot : forall a b c, (a÷b)÷c = a÷(b*c).
Proof. try hammer_hook "Zquot" "Zquot.Zquot_Zquot".  
intros. zero_or_not b. rewrite Z.mul_comm. zero_or_not c.
rewrite Z.mul_comm. apply Z.quot_quot; auto.
Qed.



Theorem Zquot_mult_le:
forall a b c, 0<=a -> 0<=b -> 0<=c -> c*(a÷b) <= (c*a)÷b.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_mult_le".   intros. zero_or_not b. apply Z.quot_mul_le; auto with zarith. Qed.



Lemma Zrem_divides : forall a b,
Z.rem a b = 0 <-> exists c, a = b*c.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_divides".  
intros. zero_or_not b. firstorder.
rewrite Z.rem_divide; trivial.
split; intros (c,Hc); exists c; subst; auto with zarith.
Qed.



Lemma Zquot2_odd_remainder : forall a,
Remainder a 2 (if Z.odd a then Z.sgn a else 0).
Proof. try hammer_hook "Zquot" "Zquot.Zquot2_odd_remainder".  
intros [ |p|p]. simpl.
left. simpl. auto with zarith.
left. destruct p; simpl; auto with zarith.
right. destruct p; simpl; split; now auto with zarith.
Qed.

Lemma Zrem_odd : forall a, Z.rem a 2 = if Z.odd a then Z.sgn a else 0.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_odd".  
intros. symmetry.
apply Zrem_unique_full with (Z.quot2 a).
apply Zquot2_odd_remainder.
apply Zquot2_odd_eqn.
Qed.

Lemma Zrem_even : forall a, Z.rem a 2 = if Z.even a then 0 else Z.sgn a.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_even".  
intros a. rewrite Zrem_odd, Zodd_even_bool. now destruct Z.even.
Qed.

Lemma Zeven_rem : forall a, Z.even a = Z.eqb (Z.rem a 2) 0.
Proof. try hammer_hook "Zquot" "Zquot.Zeven_rem".  
intros a. rewrite Zrem_even.
destruct a as [ |p|p]; trivial; now destruct p.
Qed.

Lemma Zodd_rem : forall a, Z.odd a = negb (Z.eqb (Z.rem a 2) 0).
Proof. try hammer_hook "Zquot" "Zquot.Zodd_rem".  
intros a. rewrite Zrem_odd.
destruct a as [ |p|p]; trivial; now destruct p.
Qed.





Theorem Zquotrem_Zdiv_eucl_pos : forall a b:Z, 0 <= a -> 0 < b ->
a÷b = a/b /\ Z.rem a b = a mod b.
Proof. try hammer_hook "Zquot" "Zquot.Zquotrem_Zdiv_eucl_pos".  
intros.
apply Zdiv_mod_unique with b.
apply Zrem_lt_pos; auto with zarith.
rewrite Z.abs_eq; auto with *; apply Z_mod_lt; auto with *.
rewrite <- Z_div_mod_eq; auto with *.
symmetry; apply Z.quot_rem; auto with *.
Qed.

Theorem Zquot_Zdiv_pos : forall a b, 0 <= a -> 0 <= b ->
a÷b = a/b.
Proof. try hammer_hook "Zquot" "Zquot.Zquot_Zdiv_pos".  
intros a b Ha Hb. Z.le_elim Hb.
- generalize (Zquotrem_Zdiv_eucl_pos a b Ha Hb); intuition.
- subst; now rewrite Zquot_0_r, Zdiv_0_r.
Qed.

Theorem Zrem_Zmod_pos : forall a b, 0 <= a -> 0 < b ->
Z.rem a b = a mod b.
Proof. try hammer_hook "Zquot" "Zquot.Zrem_Zmod_pos".  
intros a b Ha Hb; generalize (Zquotrem_Zdiv_eucl_pos a b Ha Hb);
intuition.
Qed.



Theorem Zrem_Zmod_zero : forall a b, b<>0 ->
(Z.rem a b = 0 <-> a mod b = 0).
Proof. try hammer_hook "Zquot" "Zquot.Zrem_Zmod_zero".  
intros.
rewrite Zrem_divides, Zmod_divides; intuition.
Qed.
