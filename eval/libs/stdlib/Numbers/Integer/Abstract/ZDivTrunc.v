From Hammer Require Import Hammer.









Require Import ZAxioms ZMulOrder ZSgnAbs NZDiv.



Module Type ZQuotProp
(Import A : ZAxiomsSig')
(Import B : ZMulOrderProp A)
(Import C : ZSgnAbsProp A B).



Module Import Private_Div.
Module Quot2Div <: NZDiv A.
Definition div := quot.
Definition modulo := A.rem.
Definition div_wd := quot_wd.
Definition mod_wd := rem_wd.
Definition div_mod := quot_rem.
Definition mod_bound_pos := rem_bound_pos.
End Quot2Div.
Module NZQuot := Nop <+ NZDivProp A Quot2Div B.
End Private_Div.

Ltac pos_or_neg a :=
let LT := fresh "LT" in
let LE := fresh "LE" in
destruct (le_gt_cases 0 a) as [LE|LT]; [|rewrite <- opp_pos_neg in LT].



Lemma rem_eq :
forall a b, b~=0 -> a rem b == a - b*(a÷b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_eq". Undo.  
intros.
rewrite <- add_move_l.
symmetry. now apply quot_rem.
Qed.



Lemma rem_opp_opp : forall a b, b ~= 0 -> (-a) rem (-b) == - (a rem b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_opp_opp". Undo.   intros. now rewrite rem_opp_r, rem_opp_l. Qed.

Lemma quot_opp_l : forall a b, b ~= 0 -> (-a)÷b == -(a÷b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_opp_l". Undo.  
intros.
rewrite <- (mul_cancel_l _ _ b) by trivial.
rewrite <- (add_cancel_r _ _ ((-a) rem b)).
now rewrite <- quot_rem, rem_opp_l, mul_opp_r, <- opp_add_distr, <- quot_rem.
Qed.

Lemma quot_opp_r : forall a b, b ~= 0 -> a÷(-b) == -(a÷b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_opp_r". Undo.  
intros.
assert (-b ~= 0) by (now rewrite eq_opp_l, opp_0).
rewrite <- (mul_cancel_l _ _ (-b)) by trivial.
rewrite <- (add_cancel_r _ _ (a rem (-b))).
now rewrite <- quot_rem, rem_opp_r, mul_opp_opp, <- quot_rem.
Qed.

Lemma quot_opp_opp : forall a b, b ~= 0 -> (-a)÷(-b) == a÷b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_opp_opp". Undo.   intros. now rewrite quot_opp_r, quot_opp_l, opp_involutive. Qed.



Theorem quot_rem_unique : forall b q1 q2 r1 r2 : t,
(0<=r1<b \/ b<r1<=0) -> (0<=r2<b \/ b<r2<=0) ->
b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_rem_unique". Undo.  
intros b q1 q2 r1 r2 Hr1 Hr2 EQ.
destruct Hr1; destruct Hr2; try (intuition; order).
apply NZQuot.div_mod_unique with b; trivial.
rewrite <- (opp_inj_wd r1 r2).
apply NZQuot.div_mod_unique with (-b); trivial.
rewrite <- opp_lt_mono, opp_nonneg_nonpos; tauto.
rewrite <- opp_lt_mono, opp_nonneg_nonpos; tauto.
now rewrite 2 mul_opp_l, <- 2 opp_add_distr, opp_inj_wd.
Qed.

Theorem quot_unique:
forall a b q r, 0<=a -> 0<=r<b -> a == b*q + r -> q == a÷b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_unique". Undo.   intros; now apply NZQuot.div_unique with r. Qed.

Theorem rem_unique:
forall a b q r, 0<=a -> 0<=r<b -> a == b*q + r -> r == a rem b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_unique". Undo.   intros; now apply NZQuot.mod_unique with q. Qed.



Lemma quot_same : forall a, a~=0 -> a÷a == 1.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_same". Undo.  
intros. pos_or_neg a. apply NZQuot.div_same; order.
rewrite <- quot_opp_opp by trivial. now apply NZQuot.div_same.
Qed.

Lemma rem_same : forall a, a~=0 -> a rem a == 0.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_same". Undo.  
intros. rewrite rem_eq, quot_same by trivial. nzsimpl. apply sub_diag.
Qed.



Theorem quot_small: forall a b, 0<=a<b -> a÷b == 0.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_small". Undo.   exact NZQuot.div_small. Qed.



Theorem rem_small: forall a b, 0<=a<b -> a rem b == a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_small". Undo.   exact NZQuot.mod_small. Qed.



Lemma quot_0_l: forall a, a~=0 -> 0÷a == 0.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_0_l". Undo.  
intros. pos_or_neg a. apply NZQuot.div_0_l; order.
rewrite <- quot_opp_opp, opp_0 by trivial. now apply NZQuot.div_0_l.
Qed.

Lemma rem_0_l: forall a, a~=0 -> 0 rem a == 0.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_0_l". Undo.  
intros; rewrite rem_eq, quot_0_l; now nzsimpl.
Qed.

Lemma quot_1_r: forall a, a÷1 == a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_1_r". Undo.  
intros. pos_or_neg a. now apply NZQuot.div_1_r.
apply opp_inj. rewrite <- quot_opp_l. apply NZQuot.div_1_r; order.
intro EQ; symmetry in EQ; revert EQ; apply lt_neq, lt_0_1.
Qed.

Lemma rem_1_r: forall a, a rem 1 == 0.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_1_r". Undo.  
intros. rewrite rem_eq, quot_1_r; nzsimpl; auto using sub_diag.
intro EQ; symmetry in EQ; revert EQ; apply lt_neq; apply lt_0_1.
Qed.

Lemma quot_1_l: forall a, 1<a -> 1÷a == 0.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_1_l". Undo.   exact NZQuot.div_1_l. Qed.

Lemma rem_1_l: forall a, 1<a -> 1 rem a == 1.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_1_l". Undo.   exact NZQuot.mod_1_l. Qed.

Lemma quot_mul : forall a b, b~=0 -> (a*b)÷b == a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_mul". Undo.  
intros. pos_or_neg a; pos_or_neg b. apply NZQuot.div_mul; order.
rewrite <- quot_opp_opp, <- mul_opp_r by order. apply NZQuot.div_mul; order.
rewrite <- opp_inj_wd, <- quot_opp_l, <- mul_opp_l by order.
apply NZQuot.div_mul; order.
rewrite <- opp_inj_wd, <- quot_opp_r, <- mul_opp_opp by order.
apply NZQuot.div_mul; order.
Qed.

Lemma rem_mul : forall a b, b~=0 -> (a*b) rem b == 0.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_mul". Undo.  
intros. rewrite rem_eq, quot_mul by trivial. rewrite mul_comm; apply sub_diag.
Qed.

Theorem quot_unique_exact a b q: b~=0 -> a == b*q -> q == a÷b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_unique_exact". Undo.  
intros Hb H. rewrite H, mul_comm. symmetry. now apply quot_mul.
Qed.



Lemma rem_nonneg : forall a b, b~=0 -> 0 <= a -> 0 <= a rem b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_nonneg". Undo.  
intros. pos_or_neg b. destruct (rem_bound_pos a b); order.
rewrite <- rem_opp_r; trivial.
destruct (rem_bound_pos a (-b)); trivial.
Qed.

Lemma rem_nonpos : forall a b, b~=0 -> a <= 0 -> a rem b <= 0.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_nonpos". Undo.  
intros a b Hb Ha.
apply opp_nonneg_nonpos. apply opp_nonneg_nonpos in Ha.
rewrite <- rem_opp_l by trivial. now apply rem_nonneg.
Qed.

Lemma rem_sign_mul : forall a b, b~=0 -> 0 <= (a rem b) * a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_sign_mul". Undo.  
intros a b Hb. destruct (le_ge_cases 0 a).
apply mul_nonneg_nonneg; trivial. now apply rem_nonneg.
apply mul_nonpos_nonpos; trivial. now apply rem_nonpos.
Qed.

Lemma rem_sign_nz : forall a b, b~=0 -> a rem b ~= 0 ->
sgn (a rem b) == sgn a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_sign_nz". Undo.  
intros a b Hb H. destruct (lt_trichotomy 0 a) as [LT|[EQ|LT]].
rewrite 2 sgn_pos; try easy.
generalize (rem_nonneg a b Hb (lt_le_incl _ _ LT)). order.
now rewrite <- EQ, rem_0_l, sgn_0.
rewrite 2 sgn_neg; try easy.
generalize (rem_nonpos a b Hb (lt_le_incl _ _ LT)). order.
Qed.

Lemma rem_sign : forall a b, a~=0 -> b~=0 -> sgn (a rem b) ~= -sgn a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_sign". Undo.  
intros a b Ha Hb H.
destruct (eq_decidable (a rem b) 0) as [EQ|NEQ].
apply Ha, sgn_null_iff, opp_inj. now rewrite <- H, opp_0, EQ, sgn_0.
apply Ha, sgn_null_iff. apply eq_mul_0_l with 2; try order'. nzsimpl'.
apply add_move_0_l. rewrite <- H. symmetry. now apply rem_sign_nz.
Qed.



Lemma rem_abs_l : forall a b, b ~= 0 -> (abs a) rem b == abs (a rem b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_abs_l". Undo.  
intros a b Hb. destruct (le_ge_cases 0 a) as [LE|LE].
rewrite 2 abs_eq; try easy. now apply rem_nonneg.
rewrite 2 abs_neq, rem_opp_l; try easy. now apply rem_nonpos.
Qed.

Lemma rem_abs_r : forall a b, b ~= 0 -> a rem (abs b) == a rem b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_abs_r". Undo.  
intros a b Hb. destruct (le_ge_cases 0 b).
now rewrite abs_eq. now rewrite abs_neq, ?rem_opp_r.
Qed.

Lemma rem_abs : forall a b,  b ~= 0 -> (abs a) rem (abs b) == abs (a rem b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_abs". Undo.  
intros. now rewrite rem_abs_r, rem_abs_l.
Qed.

Lemma quot_abs_l : forall a b, b ~= 0 -> (abs a)÷b == (sgn a)*(a÷b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_abs_l". Undo.  
intros a b Hb. destruct (lt_trichotomy 0 a) as [LT|[EQ|LT]].
rewrite abs_eq, sgn_pos by order. now nzsimpl.
rewrite <- EQ, abs_0, quot_0_l; trivial. now nzsimpl.
rewrite abs_neq, quot_opp_l, sgn_neg by order.
rewrite mul_opp_l. now nzsimpl.
Qed.

Lemma quot_abs_r : forall a b, b ~= 0 -> a÷(abs b) == (sgn b)*(a÷b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_abs_r". Undo.  
intros a b Hb. destruct (lt_trichotomy 0 b) as [LT|[EQ|LT]].
rewrite abs_eq, sgn_pos by order. now nzsimpl.
order.
rewrite abs_neq, quot_opp_r, sgn_neg by order.
rewrite mul_opp_l. now nzsimpl.
Qed.

Lemma quot_abs : forall a b, b ~= 0 -> (abs a)÷(abs b) == abs (a÷b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_abs". Undo.  
intros a b Hb.
pos_or_neg a; [rewrite (abs_eq a)|rewrite (abs_neq a)];
try apply opp_nonneg_nonpos; try order.
pos_or_neg b; [rewrite (abs_eq b)|rewrite (abs_neq b)];
try apply opp_nonneg_nonpos; try order.
rewrite abs_eq; try easy. apply NZQuot.div_pos; order.
rewrite <- abs_opp, <- quot_opp_r, abs_eq; try easy.
apply NZQuot.div_pos; order.
pos_or_neg b; [rewrite (abs_eq b)|rewrite (abs_neq b)];
try apply opp_nonneg_nonpos; try order.
rewrite <- (abs_opp (_÷_)), <- quot_opp_l, abs_eq; try easy.
apply NZQuot.div_pos; order.
rewrite <- (quot_opp_opp a b), abs_eq; try easy.
apply NZQuot.div_pos; order.
Qed.



Lemma rem_bound_abs :
forall a b, b~=0 -> abs (a rem b) < abs b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_bound_abs". Undo.  
intros. rewrite <- rem_abs; trivial.
apply rem_bound_pos. apply abs_nonneg. now apply abs_pos.
Qed.





Theorem rem_le: forall a b, 0<=a -> 0<b -> a rem b <= a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_le". Undo.   exact NZQuot.mod_le. Qed.

Theorem quot_pos : forall a b, 0<=a -> 0<b -> 0<= a÷b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_pos". Undo.   exact NZQuot.div_pos. Qed.

Lemma quot_str_pos : forall a b, 0<b<=a -> 0 < a÷b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_str_pos". Undo.   exact NZQuot.div_str_pos. Qed.

Lemma quot_small_iff : forall a b, b~=0 -> (a÷b==0 <-> abs a < abs b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_small_iff". Undo.  
intros. pos_or_neg a; pos_or_neg b.
rewrite NZQuot.div_small_iff; try order. rewrite 2 abs_eq; intuition; order.
rewrite <- opp_inj_wd, opp_0, <- quot_opp_r, NZQuot.div_small_iff by order.
rewrite (abs_eq a), (abs_neq' b); intuition; order.
rewrite <- opp_inj_wd, opp_0, <- quot_opp_l, NZQuot.div_small_iff by order.
rewrite (abs_neq' a), (abs_eq b); intuition; order.
rewrite <- quot_opp_opp, NZQuot.div_small_iff by order.
rewrite (abs_neq' a), (abs_neq' b); intuition; order.
Qed.

Lemma rem_small_iff : forall a b, b~=0 -> (a rem b == a <-> abs a < abs b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_small_iff". Undo.  
intros. rewrite rem_eq, <- quot_small_iff by order.
rewrite sub_move_r, <- (add_0_r a) at 1. rewrite add_cancel_l.
rewrite eq_sym_iff, eq_mul_0. tauto.
Qed.



Lemma quot_lt : forall a b, 0<a -> 1<b -> a÷b < a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_lt". Undo.   exact NZQuot.div_lt. Qed.



Lemma quot_le_mono : forall a b c, 0<c -> a<=b -> a÷c <= b÷c.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_le_mono". Undo.  
intros. pos_or_neg a. apply NZQuot.div_le_mono; auto.
pos_or_neg b. apply le_trans with 0.
rewrite <- opp_nonneg_nonpos, <- quot_opp_l by order.
apply quot_pos; order.
apply quot_pos; order.
rewrite opp_le_mono in *. rewrite <- 2 quot_opp_l by order.
apply NZQuot.div_le_mono; intuition; order.
Qed.



Lemma mul_quot_le : forall a b, 0<=a -> b~=0 -> 0 <= b*(a÷b) <= a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_quot_le". Undo.  
intros. pos_or_neg b.
split.
apply mul_nonneg_nonneg; [|apply quot_pos]; order.
apply NZQuot.mul_div_le; order.
rewrite <- mul_opp_opp, <- quot_opp_r by order.
split.
apply mul_nonneg_nonneg; [|apply quot_pos]; order.
apply NZQuot.mul_div_le; order.
Qed.

Lemma mul_quot_ge : forall a b, a<=0 -> b~=0 -> a <= b*(a÷b) <= 0.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_quot_ge". Undo.  
intros.
rewrite <- opp_nonneg_nonpos, opp_le_mono, <-mul_opp_r, <-quot_opp_l by order.
rewrite <- opp_nonneg_nonpos in *.
destruct (mul_quot_le (-a) b); tauto.
Qed.



Lemma mul_succ_quot_gt: forall a b, 0<=a -> 0<b -> a < b*(S (a÷b)).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_succ_quot_gt". Undo.   exact NZQuot.mul_succ_div_gt. Qed.



Lemma mul_pred_quot_lt: forall a b, a<=0 -> 0<b -> b*(P (a÷b)) < a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_pred_quot_lt". Undo.  
intros.
rewrite opp_lt_mono, <- mul_opp_r, opp_pred, <- quot_opp_l by order.
rewrite <- opp_nonneg_nonpos in *.
now apply mul_succ_quot_gt.
Qed.

Lemma mul_pred_quot_gt: forall a b, 0<=a -> b<0 -> a < b*(P (a÷b)).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_pred_quot_gt". Undo.  
intros.
rewrite <- mul_opp_opp, opp_pred, <- quot_opp_r by order.
rewrite <- opp_pos_neg in *.
now apply mul_succ_quot_gt.
Qed.

Lemma mul_succ_quot_lt: forall a b, a<=0 -> b<0 -> b*(S (a÷b)) < a.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_succ_quot_lt". Undo.  
intros.
rewrite opp_lt_mono, <- mul_opp_l, <- quot_opp_opp by order.
rewrite <- opp_nonneg_nonpos, <- opp_pos_neg in *.
now apply mul_succ_quot_gt.
Qed.



Lemma quot_exact : forall a b, b~=0 -> (a == b*(a÷b) <-> a rem b == 0).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_exact". Undo.  
intros. rewrite rem_eq by order. rewrite sub_move_r; nzsimpl; tauto.
Qed.



Theorem quot_lt_upper_bound:
forall a b q, 0<=a -> 0<b -> a < b*q -> a÷b < q.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_lt_upper_bound". Undo.   exact NZQuot.div_lt_upper_bound. Qed.

Theorem quot_le_upper_bound:
forall a b q, 0<b -> a <= b*q -> a÷b <= q.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_le_upper_bound". Undo.  
intros.
rewrite <- (quot_mul q b) by order.
apply quot_le_mono; trivial. now rewrite mul_comm.
Qed.

Theorem quot_le_lower_bound:
forall a b q, 0<b -> b*q <= a -> q <= a÷b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_le_lower_bound". Undo.  
intros.
rewrite <- (quot_mul q b) by order.
apply quot_le_mono; trivial. now rewrite mul_comm.
Qed.



Lemma quot_le_compat_l: forall p q r, 0<=p -> 0<q<=r -> p÷r <= p÷q.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_le_compat_l". Undo.   exact NZQuot.div_le_compat_l. Qed.





Lemma rem_add : forall a b c, c~=0 -> 0 <= (a+b*c)*a ->
(a + b * c) rem c == a rem c.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_add". Undo.  
assert (forall a b c, c~=0 -> 0<=a -> 0<=a+b*c -> (a+b*c) rem c == a rem c).
intros. pos_or_neg c. apply NZQuot.mod_add; order.
rewrite <- (rem_opp_r a), <- (rem_opp_r (a+b*c)) by order.
rewrite <- mul_opp_opp in *.
apply NZQuot.mod_add; order.
intros a b c Hc Habc.
destruct (le_0_mul _ _ Habc) as [(Habc',Ha)|(Habc',Ha)]. auto.
apply opp_inj. revert Ha Habc'.
rewrite <- 2 opp_nonneg_nonpos.
rewrite <- 2 rem_opp_l, opp_add_distr, <- mul_opp_l by order. auto.
Qed.

Lemma quot_add : forall a b c, c~=0 -> 0 <= (a+b*c)*a ->
(a + b * c) ÷ c == a ÷ c + b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_add". Undo.  
intros.
rewrite <- (mul_cancel_l _ _ c) by trivial.
rewrite <- (add_cancel_r _ _ ((a+b*c) rem c)).
rewrite <- quot_rem, rem_add by trivial.
now rewrite mul_add_distr_l, add_shuffle0, <-quot_rem, mul_comm.
Qed.

Lemma quot_add_l: forall a b c, b~=0 -> 0 <= (a*b+c)*c ->
(a * b + c) ÷ b == a + c ÷ b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_add_l". Undo.  
intros a b c. rewrite add_comm, (add_comm a). now apply quot_add.
Qed.



Lemma quot_mul_cancel_r : forall a b c, b~=0 -> c~=0 ->
(a*c)÷(b*c) == a÷b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_mul_cancel_r". Undo.  
assert (Aux1 : forall a b c, 0<=a -> 0<b -> c~=0 -> (a*c)÷(b*c) == a÷b).
intros. pos_or_neg c. apply NZQuot.div_mul_cancel_r; order.
rewrite <- quot_opp_opp, <- 2 mul_opp_r. apply NZQuot.div_mul_cancel_r; order.
rewrite <- neq_mul_0; intuition order.
assert (Aux2 : forall a b c, 0<=a -> b~=0 -> c~=0 -> (a*c)÷(b*c) == a÷b).
intros. pos_or_neg b. apply Aux1; order.
apply opp_inj. rewrite <- 2 quot_opp_r, <- mul_opp_l; try order. apply Aux1; order.
rewrite <- neq_mul_0; intuition order.
intros. pos_or_neg a. apply Aux2; order.
apply opp_inj. rewrite <- 2 quot_opp_l, <- mul_opp_l; try order. apply Aux2; order.
rewrite <- neq_mul_0; intuition order.
Qed.

Lemma quot_mul_cancel_l : forall a b c, b~=0 -> c~=0 ->
(c*a)÷(c*b) == a÷b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_mul_cancel_l". Undo.  
intros. rewrite !(mul_comm c); now apply quot_mul_cancel_r.
Qed.

Lemma mul_rem_distr_r: forall a b c, b~=0 -> c~=0 ->
(a*c) rem (b*c) == (a rem b) * c.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_rem_distr_r". Undo.  
intros.
assert (b*c ~= 0) by (rewrite <- neq_mul_0; tauto).
rewrite ! rem_eq by trivial.
rewrite quot_mul_cancel_r by order.
now rewrite mul_sub_distr_r, <- !mul_assoc, (mul_comm (a÷b) c).
Qed.

Lemma mul_rem_distr_l: forall a b c, b~=0 -> c~=0 ->
(c*a) rem (c*b) == c * (a rem b).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_rem_distr_l". Undo.  
intros; rewrite !(mul_comm c); now apply mul_rem_distr_r.
Qed.



Theorem rem_rem: forall a n, n~=0 ->
(a rem n) rem n == a rem n.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.rem_rem". Undo.  
intros. pos_or_neg a; pos_or_neg n. apply NZQuot.mod_mod; order.
rewrite <- ! (rem_opp_r _ n) by trivial. apply NZQuot.mod_mod; order.
apply opp_inj. rewrite <- !rem_opp_l by order. apply NZQuot.mod_mod; order.
apply opp_inj. rewrite <- !rem_opp_opp by order. apply NZQuot.mod_mod; order.
Qed.

Lemma mul_rem_idemp_l : forall a b n, n~=0 ->
((a rem n)*b) rem n == (a*b) rem n.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_rem_idemp_l". Undo.  
assert (Aux1 : forall a b n, 0<=a -> 0<=b -> n~=0 ->
((a rem n)*b) rem n == (a*b) rem n).
intros. pos_or_neg n. apply NZQuot.mul_mod_idemp_l; order.
rewrite <- ! (rem_opp_r _ n) by order. apply NZQuot.mul_mod_idemp_l; order.
assert (Aux2 : forall a b n, 0<=a -> n~=0 ->
((a rem n)*b) rem n == (a*b) rem n).
intros. pos_or_neg b. now apply Aux1.
apply opp_inj. rewrite <-2 rem_opp_l, <-2 mul_opp_r by order.
apply Aux1; order.
intros a b n Hn. pos_or_neg a. now apply Aux2.
apply opp_inj. rewrite <-2 rem_opp_l, <-2 mul_opp_l, <-rem_opp_l by order.
apply Aux2; order.
Qed.

Lemma mul_rem_idemp_r : forall a b n, n~=0 ->
(a*(b rem n)) rem n == (a*b) rem n.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_rem_idemp_r". Undo.  
intros. rewrite !(mul_comm a). now apply mul_rem_idemp_l.
Qed.

Theorem mul_rem: forall a b n, n~=0 ->
(a * b) rem n == ((a rem n) * (b rem n)) rem n.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mul_rem". Undo.  
intros. now rewrite mul_rem_idemp_l, mul_rem_idemp_r.
Qed.



Lemma add_rem_idemp_l : forall a b n, n~=0 -> 0 <= a*b ->
((a rem n)+b) rem n == (a+b) rem n.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.add_rem_idemp_l". Undo.  
assert (Aux : forall a b n, 0<=a -> 0<=b -> n~=0 ->
((a rem n)+b) rem n == (a+b) rem n).
intros. pos_or_neg n. apply NZQuot.add_mod_idemp_l; order.
rewrite <- ! (rem_opp_r _ n) by order. apply NZQuot.add_mod_idemp_l; order.
intros a b n Hn Hab. destruct (le_0_mul _ _ Hab) as [(Ha,Hb)|(Ha,Hb)].
now apply Aux.
apply opp_inj. rewrite <-2 rem_opp_l, 2 opp_add_distr, <-rem_opp_l by order.
rewrite <- opp_nonneg_nonpos in *.
now apply Aux.
Qed.

Lemma add_rem_idemp_r : forall a b n, n~=0 -> 0 <= a*b ->
(a+(b rem n)) rem n == (a+b) rem n.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.add_rem_idemp_r". Undo.  
intros. rewrite !(add_comm a). apply add_rem_idemp_l; trivial.
now rewrite mul_comm.
Qed.

Theorem add_rem: forall a b n, n~=0 -> 0 <= a*b ->
(a+b) rem n == (a rem n + b rem n) rem n.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.add_rem". Undo.  
intros a b n Hn Hab. rewrite add_rem_idemp_l, add_rem_idemp_r; trivial.
reflexivity.
destruct (le_0_mul _ _ Hab) as [(Ha,Hb)|(Ha,Hb)];
destruct (le_0_mul _ _ (rem_sign_mul b n Hn)) as [(Hb',Hm)|(Hb',Hm)];
auto using mul_nonneg_nonneg, mul_nonpos_nonpos.
setoid_replace b with 0 by order. rewrite rem_0_l by order. nzsimpl; order.
setoid_replace b with 0 by order. rewrite rem_0_l by order. nzsimpl; order.
Qed.



Lemma quot_quot : forall a b c, b~=0 -> c~=0 ->
(a÷b)÷c == a÷(b*c).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_quot". Undo.  
assert (Aux1 : forall a b c, 0<=a -> 0<b -> c~=0 -> (a÷b)÷c == a÷(b*c)).
intros. pos_or_neg c. apply NZQuot.div_div; order.
apply opp_inj. rewrite <- 2 quot_opp_r, <- mul_opp_r; trivial.
apply NZQuot.div_div; order.
rewrite <- neq_mul_0; intuition order.
assert (Aux2 : forall a b c, 0<=a -> b~=0 -> c~=0 -> (a÷b)÷c == a÷(b*c)).
intros. pos_or_neg b. apply Aux1; order.
apply opp_inj. rewrite <- quot_opp_l, <- 2 quot_opp_r, <- mul_opp_l; trivial.
apply Aux1; trivial.
rewrite <- neq_mul_0; intuition order.
intros. pos_or_neg a. apply Aux2; order.
apply opp_inj. rewrite <- 3 quot_opp_l; try order. apply Aux2; order.
rewrite <- neq_mul_0. tauto.
Qed.

Lemma mod_mul_r : forall a b c, b~=0 -> c~=0 ->
a rem (b*c) == a rem b + b*((a÷b) rem c).
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.mod_mul_r". Undo.  
intros a b c Hb Hc.
apply add_cancel_l with (b*c*(a÷(b*c))).
rewrite <- quot_rem by (apply neq_mul_0; split; order).
rewrite <- quot_quot by trivial.
rewrite add_assoc, add_shuffle0, <- mul_assoc, <- mul_add_distr_l.
rewrite <- quot_rem by order.
apply quot_rem; order.
Qed.



Theorem quot_mul_le:
forall a b c, 0<=a -> 0<b -> 0<=c -> c*(a÷b) <= (c*a)÷b.
Proof. try hammer_hook "ZDivTrunc" "ZDivTrunc.ZQuotProp.quot_mul_le". Undo.   exact NZQuot.div_mul_le. Qed.

End ZQuotProp.

