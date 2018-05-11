From Hammer Require Import Hammer.









Require Import Field.
Require Import QArith.
Require Import Znumtheory.
Require Import Eqdep_dec.



Record Qc : Set := Qcmake { this :> Q ; canon : Qred this = this }.

Delimit Scope Qc_scope with Qc.
Bind Scope Qc_scope with Qc.
Arguments Qcmake this%Q _.
Open Scope Qc_scope.



Lemma Qred_identity :
forall q:Q, Z.gcd (Qnum q) (QDen q) = 1%Z -> Qred q = q.
Proof. try hammer_hook "Qcanon" "Qcanon.Qred_identity".  
intros (a,b) H; simpl in *.
rewrite <- Z.ggcd_gcd in H.
generalize (Z.ggcd_correct_divisors a ('b)).
destruct Z.ggcd as (g,(aa,bb)); simpl in *; subst.
rewrite !Z.mul_1_l. now intros (<-,<-).
Qed.

Lemma Qred_identity2 :
forall q:Q, Qred q = q -> Z.gcd (Qnum q) (QDen q) = 1%Z.
Proof. try hammer_hook "Qcanon" "Qcanon.Qred_identity2".  
intros (a,b) H; simpl in *.
generalize (Z.gcd_nonneg a ('b)) (Z.ggcd_correct_divisors a ('b)).
rewrite <- Z.ggcd_gcd.
destruct Z.ggcd as (g,(aa,bb)); simpl in *.
injection H as <- <-. intros H (_,H').
destruct g as [|g|g]; [ discriminate | | now elim H ].
destruct bb as [|b|b]; simpl in *; try discriminate.
injection H' as H'. f_equal.
apply Pos.mul_reg_r with b. now rewrite Pos.mul_1_l.
Qed.

Lemma Qred_iff : forall q:Q, Qred q = q <-> Z.gcd (Qnum q) (QDen q) = 1%Z.
Proof. try hammer_hook "Qcanon" "Qcanon.Qred_iff".  
split; intros.
apply Qred_identity2; auto.
apply Qred_identity; auto.
Qed.



Lemma Qc_is_canon : forall q q' : Qc, q == q' -> q = q'.
Proof. try hammer_hook "Qcanon" "Qcanon.Qc_is_canon".  
intros (q,hq) (q',hq') H. simpl in *.
assert (H' := Qred_complete _ _ H).
rewrite hq, hq' in H'. subst q'. f_equal.
apply eq_proofs_unicity. intros.  repeat decide equality.
Qed.
Hint Resolve Qc_is_canon.

Theorem Qc_decomp: forall q q': Qc, (q:Q) = q' -> q = q'.
Proof. try hammer_hook "Qcanon" "Qcanon.Qc_decomp".  
intros. apply Qc_is_canon. now rewrite H.
Qed.



Lemma Qred_involutive : forall q:Q, Qred (Qred q) = Qred q.
Proof. try hammer_hook "Qcanon" "Qcanon.Qred_involutive".  
intros; apply Qred_complete.
apply Qred_correct.
Qed.

Definition Q2Qc (q:Q) : Qc := Qcmake (Qred q) (Qred_involutive q).
Arguments Q2Qc q%Q.

Lemma Q2Qc_eq_iff (q q' : Q) : Q2Qc q = Q2Qc q' <-> q == q'.
Proof. try hammer_hook "Qcanon" "Qcanon.Q2Qc_eq_iff".  
split; intro H.
- now injection H as H%Qred_eq_iff.
- apply Qc_is_canon. simpl. now rewrite H.
Qed.

Notation " 0 " := (Q2Qc 0) : Qc_scope.
Notation " 1 " := (Q2Qc 1) : Qc_scope.

Definition Qcle (x y : Qc) := (x <= y)%Q.
Definition Qclt (x y : Qc) := (x < y)%Q.
Notation Qcgt := (fun x y : Qc => Qlt y x).
Notation Qcge := (fun x y : Qc => Qle y x).
Infix "<" := Qclt : Qc_scope.
Infix "<=" := Qcle : Qc_scope.
Infix ">" := Qcgt : Qc_scope.
Infix ">=" := Qcge : Qc_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : Qc_scope.
Notation "x < y < z" := (x<y/\y<z) : Qc_scope.

Definition Qccompare (p q : Qc) := (Qcompare p q).
Notation "p ?= q" := (Qccompare p q) : Qc_scope.

Lemma Qceq_alt : forall p q, (p = q) <-> (p ?= q) = Eq.
Proof. try hammer_hook "Qcanon" "Qcanon.Qceq_alt".  
unfold Qccompare.
intros; rewrite <- Qeq_alt.
split; auto. now intros <-.
Qed.

Lemma Qclt_alt : forall p q, (p<q) <-> (p?=q = Lt).
Proof. try hammer_hook "Qcanon" "Qcanon.Qclt_alt".  
intros; exact (Qlt_alt p q).
Qed.

Lemma Qcgt_alt : forall p q, (p>q) <-> (p?=q = Gt).
Proof. try hammer_hook "Qcanon" "Qcanon.Qcgt_alt".  
intros; exact (Qgt_alt p q).
Qed.

Lemma Qcle_alt : forall p q, (p<=q) <-> (p?=q <> Gt).
Proof. try hammer_hook "Qcanon" "Qcanon.Qcle_alt".  
intros; exact (Qle_alt p q).
Qed.

Lemma Qcge_alt : forall p q, (p>=q) <-> (p?=q <> Lt).
Proof. try hammer_hook "Qcanon" "Qcanon.Qcge_alt".  
intros; exact (Qge_alt p q).
Qed.



Theorem Qc_eq_dec : forall x y:Qc, {x=y} + {x<>y}.
Proof. try hammer_hook "Qcanon" "Qcanon.Qc_eq_dec".  
intros.
destruct (Qeq_dec x y) as [H|H]; auto.
right; contradict H; subst; auto with qarith.
Defined.



Definition Qcplus (x y : Qc) := Q2Qc (x+y).
Infix "+" := Qcplus : Qc_scope.
Definition Qcmult (x y : Qc) := Q2Qc (x*y).
Infix "*" := Qcmult : Qc_scope.
Definition Qcopp (x : Qc) := Q2Qc (-x).
Notation "- x" := (Qcopp x) : Qc_scope.
Definition Qcminus (x y : Qc) := x+-y.
Infix "-" := Qcminus : Qc_scope.
Definition Qcinv (x : Qc) := Q2Qc (/x).
Notation "/ x" := (Qcinv x) : Qc_scope.
Definition Qcdiv (x y : Qc) := x*/y.
Infix "/" := Qcdiv : Qc_scope.



Lemma Q_apart_0_1 : 1 <> 0.
Proof. try hammer_hook "Qcanon" "Qcanon.Q_apart_0_1".  
unfold Q2Qc.
intros H; discriminate H.
Qed.

Ltac qc := match goal with
| q:Qc |- _ => destruct q; qc
| _ => apply Qc_is_canon; simpl; rewrite !Qred_correct
end.

Opaque Qred.



Theorem Qcplus_assoc : forall x y z, x+(y+z)=(x+y)+z.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcplus_assoc".  
intros; qc; apply Qplus_assoc.
Qed.



Lemma Qcplus_0_l : forall x, 0+x = x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcplus_0_l".  
intros; qc; apply Qplus_0_l.
Qed.

Lemma Qcplus_0_r : forall x, x+0 = x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcplus_0_r".  
intros; qc; apply Qplus_0_r.
Qed.



Theorem Qcplus_comm : forall x y, x+y = y+x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcplus_comm".  
intros; qc; apply Qplus_comm.
Qed.



Lemma Qcopp_involutive : forall q, - -q = q.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcopp_involutive".  
intros; qc; apply Qopp_involutive.
Qed.

Theorem Qcplus_opp_r : forall q, q+(-q) = 0.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcplus_opp_r".  
intros; qc; apply Qplus_opp_r.
Qed.



Theorem Qcmult_assoc : forall n m p, n*(m*p)=(n*m)*p.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_assoc".  
intros; qc; apply Qmult_assoc.
Qed.



Lemma Qcmult_0_l : forall n, 0*n = 0.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_0_l".  
intros; qc; split.
Qed.

Theorem Qcmult_0_r : forall n, n*0=0.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_0_r".  
intros; qc; rewrite Qmult_comm; split.
Qed.



Lemma Qcmult_1_l : forall n, 1*n = n.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_1_l".  
intros; qc; apply Qmult_1_l.
Qed.

Theorem Qcmult_1_r : forall n, n*1=n.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_1_r".  
intros; qc; apply Qmult_1_r.
Qed.



Theorem Qcmult_comm : forall x y, x*y=y*x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_comm".  
intros; qc; apply Qmult_comm.
Qed.



Theorem Qcmult_plus_distr_r : forall x y z, x*(y+z)=(x*y)+(x*z).
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_plus_distr_r".  
intros; qc; apply Qmult_plus_distr_r.
Qed.

Theorem Qcmult_plus_distr_l : forall x y z, (x+y)*z=(x*z)+(y*z).
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_plus_distr_l".  
intros; qc; apply Qmult_plus_distr_l.
Qed.



Theorem Qcmult_integral : forall x y, x*y=0 -> x=0 \/ y=0.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_integral".  
intros.
destruct (Qmult_integral x y); try qc; auto.
injection H as H.
rewrite <- (Qred_correct (x*y)).
rewrite <- (Qred_correct 0).
rewrite H; auto with qarith.
Qed.

Theorem Qcmult_integral_l : forall x y, ~ x = 0 -> x*y = 0 -> y = 0.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_integral_l".  
intros; destruct (Qcmult_integral _ _ H0); tauto.
Qed.



Theorem Qcmult_inv_r : forall x, x<>0 -> x*(/x) = 1.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_inv_r".  
intros; qc; apply Qmult_inv_r; auto.
Qed.

Theorem Qcmult_inv_l : forall x, x<>0 -> (/x)*x = 1.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_inv_l".  
intros.
rewrite Qcmult_comm.
apply Qcmult_inv_r; auto.
Qed.

Lemma Qcinv_mult_distr : forall p q, / (p * q) = /p * /q.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcinv_mult_distr".  
intros; qc; apply Qinv_mult_distr.
Qed.

Theorem Qcdiv_mult_l : forall x y, y<>0 -> (x*y)/y = x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcdiv_mult_l".  
unfold Qcdiv.
intros.
rewrite <- Qcmult_assoc.
rewrite Qcmult_inv_r; auto.
apply Qcmult_1_r.
Qed.

Theorem Qcmult_div_r : forall x y, ~ y = 0 -> y*(x/y) = x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_div_r".  
unfold Qcdiv.
intros.
rewrite Qcmult_assoc.
rewrite Qcmult_comm.
rewrite Qcmult_assoc.
rewrite Qcmult_inv_l; auto.
apply Qcmult_1_l.
Qed.



Lemma Qcle_refl : forall x, x<=x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcle_refl".  
unfold Qcle; intros; simpl; apply Qle_refl.
Qed.

Lemma Qcle_antisym : forall x y, x<=y -> y<=x -> x=y.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcle_antisym".  
unfold Qcle; intros; simpl in *.
apply Qc_is_canon; apply Qle_antisym; auto.
Qed.

Lemma Qcle_trans : forall x y z, x<=y -> y<=z -> x<=z.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcle_trans".  
unfold Qcle; intros; eapply Qle_trans; eauto.
Qed.

Lemma Qclt_not_eq : forall x y, x<y -> x<>y.
Proof. try hammer_hook "Qcanon" "Qcanon.Qclt_not_eq".  
unfold Qclt; intros; simpl in *.
intro; destruct (Qlt_not_eq _ _ H).
subst; auto with qarith.
Qed.



Lemma Qclt_le_weak : forall x y, x<y -> x<=y.
Proof. try hammer_hook "Qcanon" "Qcanon.Qclt_le_weak".  
unfold Qcle, Qclt; intros; apply Qlt_le_weak; auto.
Qed.

Lemma Qcle_lt_trans : forall x y z, x<=y -> y<z -> x<z.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcle_lt_trans".  
unfold Qcle, Qclt; intros; eapply Qle_lt_trans; eauto.
Qed.

Lemma Qclt_le_trans : forall x y z, x<y -> y<=z -> x<z.
Proof. try hammer_hook "Qcanon" "Qcanon.Qclt_le_trans".  
unfold Qcle, Qclt; intros; eapply Qlt_le_trans; eauto.
Qed.

Lemma Qclt_trans : forall x y z, x<y -> y<z -> x<z.
Proof. try hammer_hook "Qcanon" "Qcanon.Qclt_trans".  
unfold Qclt; intros; eapply Qlt_trans; eauto.
Qed.



Lemma Qcnot_lt_le : forall x y, ~ x<y -> y<=x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcnot_lt_le".  
unfold Qcle, Qclt; intros; apply Qnot_lt_le; auto.
Qed.

Lemma Qcnot_le_lt : forall x y, ~ x<=y -> y<x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcnot_le_lt".  
unfold Qcle, Qclt; intros; apply Qnot_le_lt; auto.
Qed.

Lemma Qclt_not_le : forall x y, x<y -> ~ y<=x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qclt_not_le".  
unfold Qcle, Qclt; intros; apply Qlt_not_le; auto.
Qed.

Lemma Qcle_not_lt : forall x y, x<=y -> ~ y<x.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcle_not_lt".  
unfold Qcle, Qclt; intros; apply Qle_not_lt; auto.
Qed.

Lemma Qcle_lt_or_eq : forall x y, x<=y -> x<y \/ x=y.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcle_lt_or_eq".  
unfold Qcle, Qclt; intros x y H.
destruct (Qle_lt_or_eq _ _ H); [left|right]; trivial.
now apply Qc_is_canon.
Qed.



Lemma Qc_dec : forall x y, {x<y} + {y<x} + {x=y}.
Proof. try hammer_hook "Qcanon" "Qcanon.Qc_dec".  
unfold Qclt, Qcle; intros.
destruct (Q_dec x y) as [H|H].
left; auto.
right; apply Qc_is_canon; auto.
Defined.

Lemma Qclt_le_dec : forall x y, {x<y} + {y<=x}.
Proof. try hammer_hook "Qcanon" "Qcanon.Qclt_le_dec".  
unfold Qclt, Qcle; intros; apply Qlt_le_dec; auto.
Defined.



Lemma Qcopp_le_compat : forall p q, p<=q -> -q <= -p.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcopp_le_compat".  
unfold Qcle, Qcopp; intros; simpl in *.
repeat rewrite Qred_correct.
apply Qopp_le_compat; auto.
Qed.

Lemma Qcle_minus_iff : forall p q, p <= q <-> 0 <= q+-p.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcle_minus_iff".  
unfold Qcle, Qcminus; intros; simpl in *.
repeat rewrite Qred_correct.
apply Qle_minus_iff; auto.
Qed.

Lemma Qclt_minus_iff : forall p q, p < q <-> 0 < q+-p.
Proof. try hammer_hook "Qcanon" "Qcanon.Qclt_minus_iff".  
unfold Qclt, Qcplus, Qcopp; intros; simpl in *.
repeat rewrite Qred_correct.
apply Qlt_minus_iff; auto.
Qed.

Lemma Qcplus_le_compat :
forall x y z t, x<=y -> z<=t -> x+z <= y+t.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcplus_le_compat".  
unfold Qcplus, Qcle; intros; simpl in *.
repeat rewrite Qred_correct.
apply Qplus_le_compat; auto.
Qed.

Lemma Qcmult_le_compat_r : forall x y z, x <= y -> 0 <= z -> x*z <= y*z.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_le_compat_r".  
unfold Qcmult, Qcle; intros; simpl in *.
repeat rewrite Qred_correct.
apply Qmult_le_compat_r; auto.
Qed.

Lemma Qcmult_lt_0_le_reg_r : forall x y z, 0 <  z  -> x*z <= y*z -> x <= y.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_lt_0_le_reg_r".  
unfold Qcmult, Qcle, Qclt; intros; simpl in *.
rewrite !Qred_correct in * |-.
eapply Qmult_lt_0_le_reg_r; eauto.
Qed.

Lemma Qcmult_lt_compat_r : forall x y z, 0 < z  -> x < y -> x*z < y*z.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcmult_lt_compat_r".  
unfold Qcmult, Qclt; intros; simpl in *.
rewrite !Qred_correct in *.
eapply Qmult_lt_compat_r; eauto.
Qed.



Fixpoint Qcpower (q:Qc)(n:nat) : Qc :=
match n with
| O => 1
| S n => q * (Qcpower q n)
end.

Notation " q ^ n " := (Qcpower q n) : Qc_scope.

Lemma Qcpower_1 : forall n, 1^n = 1.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcpower_1".  
induction n; simpl; auto with qarith.
rewrite IHn; auto with qarith.
Qed.

Lemma Qcpower_0 : forall n, n<>O -> 0^n = 0.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcpower_0".  
destruct n; simpl.
destruct 1; auto.
intros.
now apply Qc_is_canon.
Qed.

Lemma Qcpower_pos : forall p n, 0 <= p -> 0 <= p^n.
Proof. try hammer_hook "Qcanon" "Qcanon.Qcpower_pos".  
induction n; simpl; auto with qarith.
easy.
intros.
apply Qcle_trans with (0*(p^n)).
easy.
apply Qcmult_le_compat_r; auto.
Qed.





Definition Qc_eq_bool (x y : Qc) :=
if Qc_eq_dec x y then true else false.

Lemma Qc_eq_bool_correct : forall x y : Qc, Qc_eq_bool x y = true -> x=y.
Proof. try hammer_hook "Qcanon" "Qcanon.Qc_eq_bool_correct".  
intros x y; unfold Qc_eq_bool; case (Qc_eq_dec x y); simpl; auto.
intros _ H; inversion H.
Qed.

Definition Qcrt : ring_theory 0 1 Qcplus Qcmult Qcminus Qcopp (eq(A:=Qc)).
Proof. try hammer_hook "Qcanon" "Qcanon.Qcrt".  
constructor.
exact Qcplus_0_l.
exact Qcplus_comm.
exact Qcplus_assoc.
exact Qcmult_1_l.
exact Qcmult_comm.
exact Qcmult_assoc.
exact Qcmult_plus_distr_l.
reflexivity.
exact Qcplus_opp_r.
Qed.

Definition Qcft :
field_theory 0%Qc 1%Qc Qcplus Qcmult Qcminus Qcopp Qcdiv Qcinv (eq(A:=Qc)).
Proof. try hammer_hook "Qcanon" "Qcanon.Qcft".  
constructor.
exact Qcrt.
exact Q_apart_0_1.
reflexivity.
exact Qcmult_inv_l.
Qed.

Add Field Qcfield : Qcft.



Example test_field : (forall x y : Qc, y<>0 -> (x/y)*y = x)%Qc.
Proof. try hammer_hook "Qcanon" "Qcanon.test_field".  
intros.
field.
auto.
Qed.
