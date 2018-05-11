From Hammer Require Import Hammer.









Require Import Rbase Equalities Orders OrdersTac.

Local Open Scope R_scope.



Lemma Req_dec : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof. try hammer_hook "ROrderedType" "ROrderedType.Req_dec".  
intros; generalize (total_order_T r1 r2) Rlt_dichotomy_converse;
intuition eauto.
Qed.

Definition Reqb r1 r2 := if Req_dec r1 r2 then true else false.
Lemma Reqb_eq : forall r1 r2, Reqb r1 r2 = true <-> r1=r2.
Proof. try hammer_hook "ROrderedType" "ROrderedType.Reqb_eq".  
intros; unfold Reqb; destruct Req_dec as [EQ|NEQ]; auto with *.
split; try discriminate. intro EQ; elim NEQ; auto.
Qed.

Module R_as_UBE <: UsualBoolEq.
Definition t := R.
Definition eq := @eq R.
Definition eqb := Reqb.
Definition eqb_eq := Reqb_eq.
End R_as_UBE.

Module R_as_DT <: UsualDecidableTypeFull := Make_UDTF R_as_UBE.













Definition Rcompare x y :=
match total_order_T x y with
| inleft (left _) => Lt
| inleft (right _) => Eq
| inright _ => Gt
end.

Lemma Rcompare_spec : forall x y, CompareSpec (x=y) (x<y) (y<x) (Rcompare x y).
Proof. try hammer_hook "ROrderedType" "ROrderedType.Rcompare_spec".  
intros. unfold Rcompare.
destruct total_order_T as [[H|H]|H]; auto.
Qed.

Module R_as_OT <: OrderedTypeFull.
Include R_as_DT.
Definition lt := Rlt.
Definition le := Rle.
Definition compare := Rcompare.

Instance lt_strorder : StrictOrder Rlt.
Proof. try hammer_hook "ROrderedType" "ROrderedType.R_as_OT.lt_strorder".   split; [ exact Rlt_irrefl | exact Rlt_trans ]. Qed.

Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) Rlt.
Proof. try hammer_hook "ROrderedType" "ROrderedType.R_as_OT.lt_compat".   repeat red; intros; subst; auto. Qed.

Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
Proof. try hammer_hook "ROrderedType" "ROrderedType.R_as_OT.le_lteq".   unfold Rle; auto with *. Qed.

Definition compare_spec := Rcompare_spec.

End R_as_OT.







Module ROrder := OTF_to_OrderTac R_as_OT.
Ltac r_order := ROrder.order.



