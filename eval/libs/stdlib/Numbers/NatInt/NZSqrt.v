From Hammer Require Import Hammer.











Require Import NZAxioms NZMulOrder.



Module Type Sqrt (Import A : Typ).
Parameter Inline sqrt : t -> t.
End Sqrt.

Module Type SqrtNotation (A : Typ)(Import B : Sqrt A).
Notation "√ x" := (sqrt x) (at level 6).
End SqrtNotation.

Module Type Sqrt' (A : Typ) := Sqrt A <+ SqrtNotation A.

Module Type NZSqrtSpec (Import A : NZOrdAxiomsSig')(Import B : Sqrt' A).
Axiom sqrt_spec : forall a, 0<=a -> √a * √a <= a < S (√a) * S (√a).
Axiom sqrt_neg : forall a, a<0 -> √a == 0.
End NZSqrtSpec.

Module Type NZSqrt (A : NZOrdAxiomsSig) := Sqrt A <+ NZSqrtSpec A.
Module Type NZSqrt' (A : NZOrdAxiomsSig) := Sqrt' A <+ NZSqrtSpec A.



Module Type NZSqrtProp
(Import A : NZOrdAxiomsSig')
(Import B : NZSqrt' A)
(Import C : NZMulOrderProp A).

Local Notation "a ²" := (a*a) (at level 5, no associativity, format "a ²").



Lemma sqrt_spec_nonneg : forall b,
b² < (S b)² -> 0 <= b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_spec_nonneg".  
intros b LT.
destruct (le_gt_cases 0 b) as [Hb|Hb]; trivial. exfalso.
assert ((S b)² < b²).
rewrite mul_succ_l, <- (add_0_r b²).
apply add_lt_le_mono.
apply mul_lt_mono_neg_l; trivial. apply lt_succ_diag_r.
now apply le_succ_l.
order.
Qed.

Lemma sqrt_nonneg : forall a, 0<=√a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_nonneg".  
intros. destruct (lt_ge_cases a 0) as [Ha|Ha].
now rewrite (sqrt_neg _ Ha).
apply sqrt_spec_nonneg. destruct (sqrt_spec a Ha). order.
Qed.



Lemma sqrt_unique : forall a b, b² <= a < (S b)² -> √a == b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_unique".  
intros a b (LEb,LTb).
assert (Ha : 0<=a) by (transitivity (b²); trivial using square_nonneg).
assert (Hb : 0<=b) by (apply sqrt_spec_nonneg; order).
assert (Ha': 0<=√a) by now apply sqrt_nonneg.
destruct (sqrt_spec a Ha) as (LEa,LTa).
assert (b <= √a).
apply lt_succ_r, square_lt_simpl_nonneg; [|order].
now apply lt_le_incl, lt_succ_r.
assert (√a <= b).
apply lt_succ_r, square_lt_simpl_nonneg; [|order].
now apply lt_le_incl, lt_succ_r.
order.
Qed.



Instance sqrt_wd : Proper (eq==>eq) sqrt.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_wd".  
intros x x' Hx.
destruct (lt_ge_cases x 0) as [H|H].
rewrite 2 sqrt_neg; trivial. reflexivity.
now rewrite <- Hx.
apply sqrt_unique. rewrite Hx in *. now apply sqrt_spec.
Qed.



Lemma sqrt_spec_alt : forall a, 0<=a -> exists r,
a == (√a)² + r /\ 0 <= r <= 2*√a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_spec_alt".  
intros a Ha.
destruct (sqrt_spec _ Ha) as (LE,LT).
destruct (le_exists_sub _ _ LE) as (r & Hr & Hr').
exists r.
split. now rewrite add_comm.
split. trivial.
apply (add_le_mono_r _ _ (√a)²).
rewrite <- Hr, add_comm.
generalize LT. nzsimpl'. now rewrite lt_succ_r, add_assoc.
Qed.

Lemma sqrt_unique' : forall a b c, 0<=c<=2*b ->
a == b² + c -> √a == b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_unique'".  
intros a b c (Hc,H) EQ.
apply sqrt_unique.
rewrite EQ.
split.
rewrite <- add_0_r at 1. now apply add_le_mono_l.
nzsimpl. apply lt_succ_r.
rewrite <- add_assoc. apply add_le_mono_l.
generalize H; now nzsimpl'.
Qed.



Lemma sqrt_square : forall a, 0<=a -> √(a²) == a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_square".  
intros a Ha.
apply sqrt_unique' with 0.
split. order. apply mul_nonneg_nonneg; order'. now nzsimpl.
Qed.



Lemma sqrt_pred_square : forall a, 0<a -> √(P a²) == P a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_pred_square".  
intros a Ha.
apply sqrt_unique.
assert (EQ := lt_succ_pred 0 a Ha).
rewrite EQ. split.
apply lt_succ_r.
rewrite (lt_succ_pred 0).
assert (0 <= P a) by (now rewrite <- lt_succ_r, EQ).
assert (P a < a) by (now rewrite <- le_succ_l, EQ).
apply mul_lt_mono_nonneg; trivial.
now apply mul_pos_pos.
apply le_succ_l.
rewrite (lt_succ_pred 0). reflexivity. now apply mul_pos_pos.
Qed.



Lemma sqrt_le_mono : forall a b, a <= b -> √a <= √b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_le_mono".  
intros a b Hab.
destruct (lt_ge_cases a 0) as [Ha|Ha].
rewrite (sqrt_neg _ Ha). apply sqrt_nonneg.
assert (Hb : 0 <= b) by order.
destruct (sqrt_spec a Ha) as (LE,_).
destruct (sqrt_spec b Hb) as (_,LT).
apply lt_succ_r.
apply square_lt_simpl_nonneg; try order.
now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
Qed.



Lemma sqrt_lt_cancel : forall a b, √a < √b -> a < b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_lt_cancel".  
intros a b H.
destruct (lt_ge_cases b 0) as [Hb|Hb].
rewrite (sqrt_neg b Hb) in H; generalize (sqrt_nonneg a); order.
destruct (lt_ge_cases a 0) as [Ha|Ha]; [order|].
destruct (sqrt_spec a Ha) as (_,LT).
destruct (sqrt_spec b Hb) as (LE,_).
apply le_succ_l in H.
assert ((S (√a))² <= (√b)²).
apply mul_le_mono_nonneg; trivial.
now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
order.
Qed.



Lemma sqrt_le_square : forall a b, 0<=a -> 0<=b -> (b²<=a <-> b <= √a).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_le_square".  
intros a b Ha Hb. split; intros H.
rewrite <- (sqrt_square b); trivial.
now apply sqrt_le_mono.
destruct (sqrt_spec a Ha) as (LE,LT).
transitivity (√a)²; trivial.
now apply mul_le_mono_nonneg.
Qed.



Lemma sqrt_lt_square : forall a b, 0<=a -> 0<=b -> (a<b² <-> √a < b).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_lt_square".  
intros a b Ha Hb. split; intros H.
destruct (sqrt_spec a Ha) as (LE,_).
apply square_lt_simpl_nonneg; try order.
rewrite <- (sqrt_square b Hb) in H.
now apply sqrt_lt_cancel.
Qed.



Lemma sqrt_0 : √0 == 0.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_0".  
rewrite <- (mul_0_l 0) at 1. now apply sqrt_square.
Qed.

Lemma sqrt_1 : √1 == 1.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_1".  
rewrite <- (mul_1_l 1) at 1. apply sqrt_square. order'.
Qed.

Lemma sqrt_2 : √2 == 1.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_2".  
apply sqrt_unique' with 1. nzsimpl; split; order'. now nzsimpl'.
Qed.

Lemma sqrt_pos : forall a, 0 < √a <-> 0 < a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_pos".  
intros a. split; intros Ha. apply sqrt_lt_cancel. now rewrite sqrt_0.
rewrite <- le_succ_l, <- one_succ, <- sqrt_1. apply sqrt_le_mono.
now rewrite one_succ, le_succ_l.
Qed.

Lemma sqrt_lt_lin : forall a, 1<a -> √a<a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_lt_lin".  
intros a Ha. rewrite <- sqrt_lt_square; try order'.
rewrite <- (mul_1_r a) at 1.
rewrite <- mul_lt_mono_pos_l; order'.
Qed.

Lemma sqrt_le_lin : forall a, 0<=a -> √a<=a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_le_lin".  
intros a Ha.
destruct (le_gt_cases a 0) as [H|H].
setoid_replace a with 0 by order. now rewrite sqrt_0.
destruct (le_gt_cases a 1) as [H'|H'].
rewrite <- le_succ_l, <- one_succ in H.
setoid_replace a with 1 by order. now rewrite sqrt_1.
now apply lt_le_incl, sqrt_lt_lin.
Qed.





Lemma sqrt_mul_below : forall a b, √a * √b <= √(a*b).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_mul_below".  
intros a b.
destruct (lt_ge_cases a 0) as [Ha|Ha].
rewrite (sqrt_neg a Ha). nzsimpl. apply sqrt_nonneg.
destruct (lt_ge_cases b 0) as [Hb|Hb].
rewrite (sqrt_neg b Hb). nzsimpl. apply sqrt_nonneg.
assert (Ha':=sqrt_nonneg a).
assert (Hb':=sqrt_nonneg b).
apply sqrt_le_square; try now apply mul_nonneg_nonneg.
rewrite mul_shuffle1.
apply mul_le_mono_nonneg; try now apply mul_nonneg_nonneg.
now apply sqrt_spec.
now apply sqrt_spec.
Qed.

Lemma sqrt_mul_above : forall a b, 0<=a -> 0<=b -> √(a*b) < S (√a) * S (√b).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_mul_above".  
intros a b Ha Hb.
apply sqrt_lt_square.
now apply mul_nonneg_nonneg.
apply mul_nonneg_nonneg.
now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
now apply lt_le_incl, lt_succ_r, sqrt_nonneg.
rewrite mul_shuffle1.
apply mul_lt_mono_nonneg; trivial; now apply sqrt_spec.
Qed.





Lemma sqrt_succ_le : forall a, 0<=a -> √(S a) <= S (√a).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_succ_le".  
intros a Ha.
apply lt_succ_r.
apply sqrt_lt_square.
now apply le_le_succ_r.
apply le_le_succ_r, le_le_succ_r, sqrt_nonneg.
rewrite <- (add_1_l (S (√a))).
apply lt_le_trans with (1²+(S (√a))²).
rewrite mul_1_l, add_1_l, <- succ_lt_mono.
now apply sqrt_spec.
apply add_square_le. order'. apply le_le_succ_r, sqrt_nonneg.
Qed.

Lemma sqrt_succ_or : forall a, 0<=a -> √(S a) == S (√a) \/ √(S a) == √a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_succ_or".  
intros a Ha.
destruct (le_gt_cases (√(S a)) (√a)) as [H|H].
right. generalize (sqrt_le_mono _ _ (le_succ_diag_r a)); order.
left. apply le_succ_l in H. generalize (sqrt_succ_le a Ha); order.
Qed.

Lemma sqrt_eq_succ_iff_square : forall a, 0<=a ->
(√(S a) == S (√a) <-> exists b, 0<b /\ S a == b²).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_eq_succ_iff_square".  
intros a Ha. split.
intros EQ. exists (S (√a)).
split. apply lt_succ_r, sqrt_nonneg.
generalize (proj2 (sqrt_spec a Ha)). rewrite <- le_succ_l.
assert (Ha' : 0 <= S a) by now apply le_le_succ_r.
generalize (proj1 (sqrt_spec (S a) Ha')). rewrite EQ; order.
intros (b & Hb & H).
rewrite H. rewrite sqrt_square; try order.
symmetry.
rewrite <- (lt_succ_pred 0 b Hb). f_equiv.
rewrite <- (lt_succ_pred 0 b²) in H. apply succ_inj in H.
now rewrite H, sqrt_pred_square.
now apply mul_pos_pos.
Qed.



Lemma sqrt_add_le : forall a b, √(a+b) <= √a + √b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.sqrt_add_le".  
assert (AUX : forall a b, a<0 -> √(a+b) <= √a + √b).
intros a b Ha. rewrite (sqrt_neg a Ha). nzsimpl.
apply sqrt_le_mono.
rewrite <- (add_0_l b) at 2.
apply add_le_mono_r; order.
intros a b.
destruct (lt_ge_cases a 0) as [Ha|Ha]. now apply AUX.
destruct (lt_ge_cases b 0) as [Hb|Hb].
rewrite (add_comm a), (add_comm (√a)); now apply AUX.
assert (Ha':=sqrt_nonneg a).
assert (Hb':=sqrt_nonneg b).
rewrite <- lt_succ_r.
apply sqrt_lt_square.
now apply add_nonneg_nonneg.
now apply lt_le_incl, lt_succ_r, add_nonneg_nonneg.
destruct (sqrt_spec a Ha) as (_,LTa).
destruct (sqrt_spec b Hb) as (_,LTb).
revert LTa LTb. nzsimpl. rewrite 3 lt_succ_r.
intros LTa LTb.
assert (H:=add_le_mono _ _ _ _ LTa LTb).
etransitivity; [eexact H|]. clear LTa LTb H.
rewrite <- (add_assoc _ (√a) (√a)).
rewrite <- (add_assoc _ (√b) (√b)).
rewrite add_shuffle1.
rewrite <- (add_assoc _ (√a + √b)).
rewrite (add_shuffle1 (√a) (√b)).
apply add_le_mono_r.
now apply add_square_le.
Qed.



Lemma add_sqrt_le : forall a b, 0<=a -> 0<=b -> √a + √b <= √(2*(a+b)).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtProp.add_sqrt_le".  
intros a b Ha Hb.
assert (Ha':=sqrt_nonneg a).
assert (Hb':=sqrt_nonneg b).
apply sqrt_le_square.
apply mul_nonneg_nonneg. order'. now apply add_nonneg_nonneg.
now apply add_nonneg_nonneg.
transitivity (2*((√a)² + (√b)²)).
now apply square_add_le.
apply mul_le_mono_nonneg_l. order'.
apply add_le_mono; now apply sqrt_spec.
Qed.

End NZSqrtProp.

Module Type NZSqrtUpProp
(Import A : NZDecOrdAxiomsSig')
(Import B : NZSqrt' A)
(Import C : NZMulOrderProp A)
(Import D : NZSqrtProp A B C).



Local Notation "a ²" := (a*a) (at level 5, no associativity, format "a ²").



Definition sqrt_up a :=
match compare 0 a with
| Lt => S √(P a)
| _ => 0
end.

Local Notation "√° a" := (sqrt_up a) (at level 6, no associativity).

Lemma sqrt_up_eqn0 : forall a, a<=0 -> √°a == 0.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_eqn0".  
intros a Ha. unfold sqrt_up. case compare_spec; try order.
Qed.

Lemma sqrt_up_eqn : forall a, 0<a -> √°a == S √(P a).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_eqn".  
intros a Ha. unfold sqrt_up. case compare_spec; try order.
Qed.

Lemma sqrt_up_spec : forall a, 0<a -> (P √°a)² < a <= (√°a)².
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_spec".  
intros a Ha.
rewrite sqrt_up_eqn, pred_succ; trivial.
assert (Ha' := lt_succ_pred 0 a Ha).
rewrite <- Ha' at 3 4.
rewrite le_succ_l, lt_succ_r.
apply sqrt_spec.
now rewrite <- lt_succ_r, Ha'.
Qed.



Lemma sqrt_up_nonneg : forall a, 0<=√°a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_nonneg".  
intros. destruct (le_gt_cases a 0) as [Ha|Ha].
now rewrite sqrt_up_eqn0.
rewrite sqrt_up_eqn; trivial. apply le_le_succ_r, sqrt_nonneg.
Qed.



Instance sqrt_up_wd : Proper (eq==>eq) sqrt_up.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_wd".  
assert (Proper (eq==>eq==>Logic.eq) compare).
intros x x' Hx y y' Hy. do 2 case compare_spec; trivial; order.
intros x x' Hx; unfold sqrt_up; rewrite Hx; case compare; now rewrite ?Hx.
Qed.



Lemma sqrt_up_unique : forall a b, 0<b -> (P b)² < a <= b² -> √°a == b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_unique".  
intros a b Hb (LEb,LTb).
assert (Ha : 0<a)
by (apply le_lt_trans with (P b)²; trivial using square_nonneg).
rewrite sqrt_up_eqn; trivial.
assert (Hb' := lt_succ_pred 0 b Hb).
rewrite <- Hb'. f_equiv. apply sqrt_unique.
rewrite <- le_succ_l, <- lt_succ_r, Hb'.
rewrite (lt_succ_pred 0 a Ha). now split.
Qed.



Lemma sqrt_up_square : forall a, 0<=a -> √°(a²) == a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_square".  
intros a Ha.
le_elim Ha.
rewrite sqrt_up_eqn by (now apply mul_pos_pos).
rewrite sqrt_pred_square; trivial. apply (lt_succ_pred 0); trivial.
rewrite sqrt_up_eqn0; trivial. rewrite <- Ha. now nzsimpl.
Qed.



Lemma sqrt_up_succ_square : forall a, 0<=a -> √°(S a²) == S a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_succ_square".  
intros a Ha.
rewrite sqrt_up_eqn by (now apply lt_succ_r, mul_nonneg_nonneg).
now rewrite pred_succ, sqrt_square.
Qed.



Lemma sqrt_up_0 : √°0 == 0.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_0".  
rewrite <- (mul_0_l 0) at 1. now apply sqrt_up_square.
Qed.

Lemma sqrt_up_1 : √°1 == 1.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_1".  
rewrite <- (mul_1_l 1) at 1. apply sqrt_up_square. order'.
Qed.

Lemma sqrt_up_2 : √°2 == 2.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_2".  
rewrite sqrt_up_eqn by order'.
now rewrite two_succ, pred_succ, sqrt_1.
Qed.



Lemma le_sqrt_sqrt_up : forall a, √a <= √°a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.le_sqrt_sqrt_up".  
intros a. unfold sqrt_up. case compare_spec; intros H.
rewrite <- H, sqrt_0. order.
rewrite <- (lt_succ_pred 0 a H) at 1. apply sqrt_succ_le.
apply lt_succ_r. now rewrite (lt_succ_pred 0 a H).
now rewrite sqrt_neg.
Qed.

Lemma le_sqrt_up_succ_sqrt : forall a, √°a <= S (√a).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.le_sqrt_up_succ_sqrt".  
intros a. unfold sqrt_up.
case compare_spec; intros H; try apply le_le_succ_r, sqrt_nonneg.
rewrite <- succ_le_mono. apply sqrt_le_mono.
rewrite <- (lt_succ_pred 0 a H) at 2. apply le_succ_diag_r.
Qed.

Lemma sqrt_sqrt_up_spec : forall a, 0<=a -> (√a)² <= a <= (√°a)².
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_sqrt_up_spec".  
intros a H. split.
now apply sqrt_spec.
le_elim H.
now apply sqrt_up_spec.
now rewrite <-H, sqrt_up_0, mul_0_l.
Qed.

Lemma sqrt_sqrt_up_exact :
forall a, 0<=a -> (√a == √°a <-> exists b, 0<=b /\ a == b²).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_sqrt_up_exact".  
intros a Ha.
split. intros. exists √a.
split. apply sqrt_nonneg.
generalize (sqrt_sqrt_up_spec a Ha). rewrite <-H. destruct 1; order.
intros (b & Hb & Hb'). rewrite Hb'.
now rewrite sqrt_square, sqrt_up_square.
Qed.



Lemma sqrt_up_le_mono : forall a b, a <= b -> √°a <= √°b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_le_mono".  
intros a b H.
destruct (le_gt_cases a 0) as [Ha|Ha].
rewrite (sqrt_up_eqn0 _ Ha). apply sqrt_up_nonneg.
rewrite 2 sqrt_up_eqn by order. rewrite <- succ_le_mono.
apply sqrt_le_mono, succ_le_mono. rewrite 2 (lt_succ_pred 0); order.
Qed.



Lemma sqrt_up_lt_cancel : forall a b, √°a < √°b -> a < b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_lt_cancel".  
intros a b H.
destruct (le_gt_cases b 0) as [Hb|Hb].
rewrite (sqrt_up_eqn0 _ Hb) in H; generalize (sqrt_up_nonneg a); order.
destruct (le_gt_cases a 0) as [Ha|Ha]; [order|].
rewrite <- (lt_succ_pred 0 a Ha), <- (lt_succ_pred 0 b Hb), <- succ_lt_mono.
apply sqrt_lt_cancel, succ_lt_mono. now rewrite <- 2 sqrt_up_eqn.
Qed.



Lemma sqrt_up_lt_square : forall a b, 0<=a -> 0<=b -> (b² < a <-> b < √°a).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_lt_square".  
intros a b Ha Hb. split; intros H.
destruct (sqrt_up_spec a) as (LE,LT).
apply le_lt_trans with b²; trivial using square_nonneg.
apply square_lt_simpl_nonneg; try order. apply sqrt_up_nonneg.
apply sqrt_up_lt_cancel. now rewrite sqrt_up_square.
Qed.



Lemma sqrt_up_le_square : forall a b, 0<=a -> 0<=b -> (a <= b² <-> √°a <= b).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_le_square".  
intros a b Ha Hb. split; intros H.
rewrite <- (sqrt_up_square b Hb).
now apply sqrt_up_le_mono.
apply square_le_mono_nonneg in H; [|now apply sqrt_up_nonneg].
transitivity (√°a)²; trivial. now apply sqrt_sqrt_up_spec.
Qed.

Lemma sqrt_up_pos : forall a, 0 < √°a <-> 0 < a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_pos".  
intros a. split; intros Ha. apply sqrt_up_lt_cancel. now rewrite sqrt_up_0.
rewrite <- le_succ_l, <- one_succ, <- sqrt_up_1. apply sqrt_up_le_mono.
now rewrite one_succ, le_succ_l.
Qed.

Lemma sqrt_up_lt_lin : forall a, 2<a -> √°a < a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_lt_lin".  
intros a Ha.
rewrite sqrt_up_eqn by order'.
assert (Ha' := lt_succ_pred 2 a Ha).
rewrite <- Ha' at 2. rewrite <- succ_lt_mono.
apply sqrt_lt_lin. rewrite succ_lt_mono. now rewrite Ha', <- two_succ.
Qed.

Lemma sqrt_up_le_lin : forall a, 0<=a -> √°a<=a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_le_lin".  
intros a Ha.
le_elim Ha.
rewrite sqrt_up_eqn; trivial. apply le_succ_l.
apply le_lt_trans with (P a). apply sqrt_le_lin.
now rewrite <- lt_succ_r, (lt_succ_pred 0).
rewrite <- (lt_succ_pred 0 a) at 2; trivial. apply lt_succ_diag_r.
now rewrite <- Ha, sqrt_up_0.
Qed.





Lemma sqrt_up_mul_above : forall a b, 0<=a -> 0<=b -> √°(a*b) <= √°a * √°b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_mul_above".  
intros a b Ha Hb.
apply sqrt_up_le_square.
now apply mul_nonneg_nonneg.
apply mul_nonneg_nonneg; apply sqrt_up_nonneg.
rewrite mul_shuffle1.
apply mul_le_mono_nonneg; trivial; now apply sqrt_sqrt_up_spec.
Qed.

Lemma sqrt_up_mul_below : forall a b, 0<a -> 0<b -> (P √°a)*(P √°b) < √°(a*b).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_mul_below".  
intros a b Ha Hb.
apply sqrt_up_lt_square.
apply mul_nonneg_nonneg; order.
apply mul_nonneg_nonneg; apply lt_succ_r.
rewrite (lt_succ_pred 0); now rewrite sqrt_up_pos.
rewrite (lt_succ_pred 0); now rewrite sqrt_up_pos.
rewrite mul_shuffle1.
apply mul_lt_mono_nonneg; trivial using square_nonneg;
now apply sqrt_up_spec.
Qed.





Lemma sqrt_up_succ_le : forall a, 0<=a -> √°(S a) <= S (√°a).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_succ_le".  
intros a Ha.
apply sqrt_up_le_square.
now apply le_le_succ_r.
apply le_le_succ_r, sqrt_up_nonneg.
rewrite <- (add_1_l (√°a)).
apply le_trans with (1²+(√°a)²).
rewrite mul_1_l, add_1_l, <- succ_le_mono.
now apply sqrt_sqrt_up_spec.
apply add_square_le. order'. apply sqrt_up_nonneg.
Qed.

Lemma sqrt_up_succ_or : forall a, 0<=a -> √°(S a) == S (√°a) \/ √°(S a) == √°a.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_succ_or".  
intros a Ha.
destruct (le_gt_cases (√°(S a)) (√°a)) as [H|H].
right. generalize (sqrt_up_le_mono _ _ (le_succ_diag_r a)); order.
left. apply le_succ_l in H. generalize (sqrt_up_succ_le a Ha); order.
Qed.

Lemma sqrt_up_eq_succ_iff_square : forall a, 0<=a ->
(√°(S a) == S (√°a) <-> exists b, 0<=b /\ a == b²).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_eq_succ_iff_square".  
intros a Ha. split.
intros EQ.
le_elim Ha.
exists (√°a). split. apply sqrt_up_nonneg.
generalize (proj2 (sqrt_up_spec a Ha)).
assert (Ha' : 0 < S a) by (apply lt_succ_r; order').
generalize (proj1 (sqrt_up_spec (S a) Ha')).
rewrite EQ, pred_succ, lt_succ_r. order.
exists 0. nzsimpl. now split.
intros (b & Hb & H).
now rewrite H, sqrt_up_succ_square, sqrt_up_square.
Qed.



Lemma sqrt_up_add_le : forall a b, √°(a+b) <= √°a + √°b.
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.sqrt_up_add_le".  
assert (AUX : forall a b, a<=0 -> √°(a+b) <= √°a + √°b).
intros a b Ha. rewrite (sqrt_up_eqn0 a Ha). nzsimpl.
apply sqrt_up_le_mono.
rewrite <- (add_0_l b) at 2.
apply add_le_mono_r; order.
intros a b.
destruct (le_gt_cases a 0) as [Ha|Ha]. now apply AUX.
destruct (le_gt_cases b 0) as [Hb|Hb].
rewrite (add_comm a), (add_comm (√°a)); now apply AUX.
rewrite 2 sqrt_up_eqn; trivial.
nzsimpl. rewrite <- succ_le_mono.
transitivity (√(P a) + √b).
rewrite <- (lt_succ_pred 0 a Ha) at 1. nzsimpl. apply sqrt_add_le.
apply add_le_mono_l.
apply le_sqrt_sqrt_up.
now apply add_pos_pos.
Qed.



Lemma add_sqrt_up_le : forall a b, 0<=a -> 0<=b -> √°a + √°b <= S √°(2*(a+b)).
Proof. hammer_hook "NZSqrt" "NZSqrt.NZSqrtUpProp.add_sqrt_up_le".  
intros a b Ha Hb.
le_elim Ha.
le_elim Hb.
rewrite 3 sqrt_up_eqn; trivial.
nzsimpl. rewrite <- 2 succ_le_mono.
etransitivity; [eapply add_sqrt_le|].
apply lt_succ_r. now rewrite (lt_succ_pred 0 a Ha).
apply lt_succ_r. now rewrite (lt_succ_pred 0 b Hb).
apply sqrt_le_mono.
apply lt_succ_r. rewrite (lt_succ_pred 0).
apply mul_lt_mono_pos_l. order'.
apply add_lt_mono.
apply le_succ_l. now rewrite (lt_succ_pred 0).
apply le_succ_l. now rewrite (lt_succ_pred 0).
apply mul_pos_pos. order'. now apply add_pos_pos.
apply mul_pos_pos. order'. now apply add_pos_pos.
rewrite <- Hb, sqrt_up_0. nzsimpl. apply le_le_succ_r, sqrt_up_le_mono.
rewrite <- (mul_1_l a) at 1. apply mul_le_mono_nonneg_r; order'.
rewrite <- Ha, sqrt_up_0. nzsimpl. apply le_le_succ_r, sqrt_up_le_mono.
rewrite <- (mul_1_l b) at 1. apply mul_le_mono_nonneg_r; order'.
Qed.

End NZSqrtUpProp.
