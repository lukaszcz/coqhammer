From Hammer Require Import Hammer.











Require Import Relation_Definitions.

Section WfInclusion.
Variable A : Type.
Variables R1 R2 : A -> A -> Prop.

Lemma Acc_incl : inclusion A R1 R2 -> forall z:A, Acc R2 z -> Acc R1 z.
Proof. try hammer_hook "Inclusion" "Inclusion.Acc_incl".  
induction 2.
apply Acc_intro; auto with sets.
Qed.

Hint Resolve Acc_incl.

Theorem wf_incl : inclusion A R1 R2 -> well_founded R2 -> well_founded R1.
Proof. try hammer_hook "Inclusion" "Inclusion.wf_incl".  
unfold well_founded; auto with sets.
Qed.

End WfInclusion.
