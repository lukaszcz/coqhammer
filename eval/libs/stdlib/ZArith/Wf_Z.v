From Hammer Require Import Hammer.









Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Znat.
Require Import Zmisc.
Require Import Wf_nat.
Local Open Scope Z_scope.



Lemma Z_of_nat_complete (x : Z) :
0 <= x -> exists n : nat, x = Z.of_nat n.
Proof. hammer_hook "Wf_Z" "Wf_Z.Z_of_nat_complete". Restart. 
intros H. exists (Z.to_nat x). symmetry. now apply Z2Nat.id.
Qed.

Lemma Z_of_nat_complete_inf (x : Z) :
0 <= x -> {n : nat | x = Z.of_nat n}.
Proof. hammer_hook "Wf_Z" "Wf_Z.Z_of_nat_complete_inf". Restart. 
intros H. exists (Z.to_nat x). symmetry. now apply Z2Nat.id.
Qed.

Lemma Z_of_nat_prop :
forall P:Z -> Prop,
(forall n:nat, P (Z.of_nat n)) -> forall x:Z, 0 <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.Z_of_nat_prop". Restart. 
intros P H x Hx. now destruct (Z_of_nat_complete x Hx) as (n,->).
Qed.

Lemma Z_of_nat_set :
forall P:Z -> Set,
(forall n:nat, P (Z.of_nat n)) -> forall x:Z, 0 <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.Z_of_nat_set". Restart. 
intros P H x Hx. now destruct (Z_of_nat_complete_inf x Hx) as (n,->).
Qed.

Lemma natlike_ind :
forall P:Z -> Prop,
P 0 ->
(forall x:Z, 0 <= x -> P x -> P (Z.succ x)) ->
forall x:Z, 0 <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.natlike_ind". Restart. 
intros P Ho Hrec x Hx; apply Z_of_nat_prop; trivial.
induction n. exact Ho.
rewrite Nat2Z.inj_succ. apply Hrec; trivial using Nat2Z.is_nonneg.
Qed.

Lemma natlike_rec :
forall P:Z -> Set,
P 0 ->
(forall x:Z, 0 <= x -> P x -> P (Z.succ x)) ->
forall x:Z, 0 <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.natlike_rec". Restart. 
intros P Ho Hrec x Hx; apply Z_of_nat_set; trivial.
induction n. exact Ho.
rewrite Nat2Z.inj_succ. apply Hrec; trivial using Nat2Z.is_nonneg.
Qed.

Section Efficient_Rec.



Let R (a b:Z) := 0 <= a /\ a < b.

Let R_wf : well_founded R.
Proof. hammer_hook "Wf_Z" "Wf_Z.Efficient_Rec.R_wf". Restart. 
apply well_founded_lt_compat with Z.to_nat.
intros x y (Hx,H). apply Z2Nat.inj_lt; Z.order.
Qed.

Lemma natlike_rec2 :
forall P:Z -> Type,
P 0 ->
(forall z:Z, 0 <= z -> P z -> P (Z.succ z)) ->
forall z:Z, 0 <= z -> P z.
Proof. hammer_hook "Wf_Z" "Wf_Z.natlike_rec2". Restart. 
intros P Ho Hrec.
induction z as [z IH] using (well_founded_induction_type R_wf).
destruct z; intros Hz.
- apply Ho.
- set (y:=Z.pred (Zpos p)).
assert (LE : 0 <= y) by (unfold y; now apply Z.lt_le_pred).
assert (EQ : Zpos p = Z.succ y) by (unfold y; now rewrite Z.succ_pred).
rewrite EQ. apply Hrec, IH; trivial.
split; trivial. unfold y; apply Z.lt_pred_l.
- now destruct Hz.
Qed.



Lemma natlike_rec3 :
forall P:Z -> Type,
P 0 ->
(forall z:Z, 0 < z -> P (Z.pred z) -> P z) ->
forall z:Z, 0 <= z -> P z.
Proof. hammer_hook "Wf_Z" "Wf_Z.natlike_rec3". Restart. 
intros P Ho Hrec.
induction z as [z IH] using (well_founded_induction_type R_wf).
destruct z; intros Hz.
- apply Ho.
- assert (EQ : 0 <= Z.pred (Zpos p)) by now apply Z.lt_le_pred.
apply Hrec. easy. apply IH; trivial. split; trivial.
apply Z.lt_pred_l.
- now destruct Hz.
Qed.



Lemma Zlt_0_rec :
forall P:Z -> Type,
(forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> 0 <= x -> P x) ->
forall x:Z, 0 <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.Zlt_0_rec". Restart. 
intros P Hrec.
induction x as [x IH] using (well_founded_induction_type R_wf).
destruct x; intros Hx.
- apply Hrec; trivial. intros y (Hy,Hy').
assert (0 < 0) by now apply Z.le_lt_trans with y.
discriminate.
- apply Hrec; trivial. intros y (Hy,Hy').
apply IH; trivial. now split.
- now destruct Hx.
Defined.

Lemma Zlt_0_ind :
forall P:Z -> Prop,
(forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> 0 <= x -> P x) ->
forall x:Z, 0 <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.Zlt_0_ind". Restart.  intros; now apply Zlt_0_rec. Qed.



Lemma Z_lt_rec :
forall P:Z -> Type,
(forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> P x) ->
forall x:Z, 0 <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.Z_lt_rec". Restart. 
intros P Hrec; apply Zlt_0_rec; auto.
Qed.

Lemma Z_lt_induction :
forall P:Z -> Prop,
(forall x:Z, (forall y:Z, 0 <= y < x -> P y) -> P x) ->
forall x:Z, 0 <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.Z_lt_induction". Restart. 
intros; now apply Z_lt_rec.
Qed.



Lemma Zlt_lower_bound_rec :
forall P:Z -> Type, forall z:Z,
(forall x:Z, (forall y:Z, z <= y < x -> P y) -> z <= x -> P x) ->
forall x:Z, z <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.Zlt_lower_bound_rec". Restart. 
intros P z Hrec x Hx.
rewrite <- (Z.sub_simpl_r x z). apply Z.le_0_sub in Hx.
pattern (x - z); apply Zlt_0_rec; trivial.
clear x Hx. intros x IH Hx.
apply Hrec. intros y (Hy,Hy').
rewrite <- (Z.sub_simpl_r y z). apply IH; split.
now rewrite Z.le_0_sub.
now apply Z.lt_sub_lt_add_r.
now rewrite <- (Z.add_le_mono_r 0 x z).
Qed.

Lemma Zlt_lower_bound_ind :
forall P:Z -> Prop, forall z:Z,
(forall x:Z, (forall y:Z, z <= y < x -> P y) -> z <= x -> P x) ->
forall x:Z, z <= x -> P x.
Proof. hammer_hook "Wf_Z" "Wf_Z.Zlt_lower_bound_ind". Restart. 
intros; now apply Zlt_lower_bound_rec with z.
Qed.

End Efficient_Rec.
