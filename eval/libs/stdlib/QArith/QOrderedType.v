From Hammer Require Import Hammer.









Require Import QArith_base Equalities Orders OrdersTac.

Local Open Scope Q_scope.



Module Q_as_DT <: DecidableTypeFull.
Definition t := Q.
Definition eq := Qeq.
Definition eq_equiv := Q_Setoid.
Definition eqb := Qeq_bool.
Definition eqb_eq := Qeq_bool_iff.

Include BackportEq.
Include HasEqBool2Dec.

End Q_as_DT.







Module Q_as_OT <: OrderedTypeFull.
Include Q_as_DT.
Definition lt := Qlt.
Definition le := Qle.
Definition compare := Qcompare.

Instance lt_strorder : StrictOrder Qlt.
Proof. try hammer_hook "QOrderedType" "QOrderedType.Q_as_OT.lt_strorder". Undo.   split; [ exact Qlt_irrefl | exact Qlt_trans ]. Qed.

Instance lt_compat : Proper (Qeq==>Qeq==>iff) Qlt.
Proof. try hammer_hook "QOrderedType" "QOrderedType.Q_as_OT.lt_compat". Undo.   auto with *. Qed.

Definition le_lteq := Qle_lteq.
Definition compare_spec := Qcompare_spec.

End Q_as_OT.




Module QOrder := OTF_to_OrderTac Q_as_OT.
Ltac q_order := QOrder.order.


