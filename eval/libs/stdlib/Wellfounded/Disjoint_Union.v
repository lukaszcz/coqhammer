From Hammer Require Import Hammer.











Require Import Relation_Operators.

Section Wf_Disjoint_Union.
Variables A B : Type.
Variable leA : A -> A -> Prop.
Variable leB : B -> B -> Prop.

Notation Le_AsB := (le_AsB A B leA leB).

Lemma acc_A_sum : forall x:A, Acc leA x -> Acc Le_AsB (inl B x).
Proof. try hammer_hook "Disjoint_Union" "Disjoint_Union.acc_A_sum". Undo.  
induction 1.
apply Acc_intro; intros y H2.
inversion_clear H2.
auto with sets.
Qed.

Lemma acc_B_sum :
well_founded leA -> forall x:B, Acc leB x -> Acc Le_AsB (inr A x).
Proof. try hammer_hook "Disjoint_Union" "Disjoint_Union.acc_B_sum". Undo.  
induction 2.
apply Acc_intro; intros y H3.
inversion_clear H3; auto with sets.
apply acc_A_sum; auto with sets.
Qed.


Lemma wf_disjoint_sum :
well_founded leA -> well_founded leB -> well_founded Le_AsB.
Proof. try hammer_hook "Disjoint_Union" "Disjoint_Union.wf_disjoint_sum". Undo.  
intros.
unfold well_founded.
destruct a as [a| b].
apply (acc_A_sum a).
apply (H a).

apply (acc_B_sum H b).
apply (H0 b).
Qed.

End Wf_Disjoint_Union.
