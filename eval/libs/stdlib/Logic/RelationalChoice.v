From Hammer Require Import Hammer.











Axiom relational_choice :
forall (A B : Type) (R : A->B->Prop),
(forall x : A, exists y : B, R x y) ->
exists R' : A->B->Prop,
subrelation R' R /\ forall x : A, exists! y : B, R' x y.
