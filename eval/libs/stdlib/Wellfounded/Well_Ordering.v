From Hammer Require Import Hammer.











Require Import Eqdep.

Section WellOrdering.
Variable A : Type.
Variable B : A -> Type.

Inductive WO : Type :=
sup : forall (a:A) (f:B a -> WO), WO.


Inductive le_WO : WO -> WO -> Prop :=
le_sup : forall (a:A) (f:B a -> WO) (v:B a), le_WO (f v) (sup a f).

Theorem wf_WO : well_founded le_WO.
Proof. try hammer_hook "Well_Ordering" "Well_Ordering.wf_WO". Undo.  
unfold well_founded; intro.
apply Acc_intro.
elim a.
intros.
inversion H0.
apply Acc_intro.
generalize H4; generalize H1; generalize f0; generalize v.
rewrite H3.
intros.
apply (H v0 y0).
cut (f = f1).
intros E; rewrite E; auto.
symmetry .
apply (inj_pair2 A (fun a0:A => B a0 -> WO) a0 f1 f H5).
Qed.

End WellOrdering.


Section Characterisation_wf_relations.





Variable A : Type.
Variable leA : A -> A -> Prop.

Definition B (a:A) := {x : A | leA x a}.

Definition wof : well_founded leA -> A -> WO A B.
Proof. try hammer_hook "Well_Ordering" "Well_Ordering.wof". Undo.  
intros.
apply (well_founded_induction_type H (fun a:A => WO A B)); auto.
intros x H1.
apply (sup A B x).
unfold B at 1.
destruct 1 as [x0].
apply (H1 x0); auto.
Qed.

End Characterisation_wf_relations.
