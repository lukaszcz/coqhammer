From Hammer Require Import Hammer.









Require Import QArith_base Orders QOrderedType GenericMinMax.



Local Open Scope Q_scope.



Definition Qmax := gmax Qcompare.
Definition Qmin := gmin Qcompare.

Module QHasMinMax <: HasMinMax Q_as_OT.
Module QMM := GenericMinMax Q_as_OT.
Definition max := Qmax.
Definition min := Qmin.
Definition max_l := QMM.max_l.
Definition max_r := QMM.max_r.
Definition min_l := QMM.min_l.
Definition min_r := QMM.min_r.
End QHasMinMax.

Module Q.



Include MinMaxProperties Q_as_OT QHasMinMax.






Lemma plus_max_distr_l : forall n m p, Qmax (p + n) (p + m) == p + Qmax n m.
Proof. try hammer_hook "Qminmax" "Qminmax.Q.plus_max_distr_l". Undo.  
intros. apply max_monotone.
intros x x' Hx; rewrite Hx; auto with qarith.
intros x x' Hx. apply Qplus_le_compat; q_order.
Qed.

Lemma plus_max_distr_r : forall n m p, Qmax (n + p) (m + p) == Qmax n m + p.
Proof. try hammer_hook "Qminmax" "Qminmax.Q.plus_max_distr_r". Undo.  
intros. rewrite (Qplus_comm n p), (Qplus_comm m p), (Qplus_comm _ p).
apply plus_max_distr_l.
Qed.

Lemma plus_min_distr_l : forall n m p, Qmin (p + n) (p + m) == p + Qmin n m.
Proof. try hammer_hook "Qminmax" "Qminmax.Q.plus_min_distr_l". Undo.  
intros. apply min_monotone.
intros x x' Hx; rewrite Hx; auto with qarith.
intros x x' Hx. apply Qplus_le_compat; q_order.
Qed.

Lemma plus_min_distr_r : forall n m p, Qmin (n + p) (m + p) == Qmin n m + p.
Proof. try hammer_hook "Qminmax" "Qminmax.Q.plus_min_distr_r". Undo.  
intros. rewrite (Qplus_comm n p), (Qplus_comm m p), (Qplus_comm _ p).
apply plus_min_distr_l.
Qed.

End Q.
