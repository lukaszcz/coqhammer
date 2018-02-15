From Hammer Require Import Hammer.



























Section Ensembles.
Variable U : Type.

Definition Ensemble := U -> Prop.

Definition In (A:Ensemble) (x:U) : Prop := A x.

Definition Included (B C:Ensemble) : Prop := forall x:U, In B x -> In C x.

Inductive Empty_set : Ensemble :=.

Inductive Full_set : Ensemble :=
Full_intro : forall x:U, In Full_set x.



Inductive Singleton (x:U) : Ensemble :=
In_singleton : In (Singleton x) x.

Inductive Union (B C:Ensemble) : Ensemble :=
| Union_introl : forall x:U, In B x -> In (Union B C) x
| Union_intror : forall x:U, In C x -> In (Union B C) x.

Definition Add (B:Ensemble) (x:U) : Ensemble := Union B (Singleton x).

Inductive Intersection (B C:Ensemble) : Ensemble :=
Intersection_intro :
forall x:U, In B x -> In C x -> In (Intersection B C) x.

Inductive Couple (x y:U) : Ensemble :=
| Couple_l : In (Couple x y) x
| Couple_r : In (Couple x y) y.

Inductive Triple (x y z:U) : Ensemble :=
| Triple_l : In (Triple x y z) x
| Triple_m : In (Triple x y z) y
| Triple_r : In (Triple x y z) z.

Definition Complement (A:Ensemble) : Ensemble := fun x:U => ~ In A x.

Definition Setminus (B C:Ensemble) : Ensemble :=
fun x:U => In B x /\ ~ In C x.

Definition Subtract (B:Ensemble) (x:U) : Ensemble := Setminus B (Singleton x).

Inductive Disjoint (B C:Ensemble) : Prop :=
Disjoint_intro : (forall x:U, ~ In (Intersection B C) x) -> Disjoint B C.

Inductive Inhabited (B:Ensemble) : Prop :=
Inhabited_intro : forall x:U, In B x -> Inhabited B.

Definition Strict_Included (B C:Ensemble) : Prop := Included B C /\ B <> C.

Definition Same_set (B C:Ensemble) : Prop := Included B C /\ Included C B.



Axiom Extensionality_Ensembles : forall A B:Ensemble, Same_set A B -> A = B.

End Ensembles.

Hint Unfold In Included Same_set Strict_Included Add Setminus Subtract: sets.

Hint Resolve Union_introl Union_intror Intersection_intro In_singleton
Couple_l Couple_r Triple_l Triple_m Triple_r Disjoint_intro
Extensionality_Ensembles: sets.
