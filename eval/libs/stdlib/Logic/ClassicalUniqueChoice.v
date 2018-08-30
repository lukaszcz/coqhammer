From Hammer Require Import Hammer.














Require Export Classical.

Axiom
dependent_unique_choice :
forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
(forall x : A, exists! y : B x, R x y) ->
(exists f : (forall x:A, B x), forall x:A, R x (f x)).



Theorem unique_choice :
forall (A B:Type) (R:A -> B -> Prop),
(forall x:A,  exists! y : B, R x y) ->
(exists f:A->B, forall x:A, R x (f x)).
Proof. hammer_hook "ClassicalUniqueChoice" "ClassicalUniqueChoice.unique_choice".  
intros A B.
apply (dependent_unique_choice A (fun _ => B)).
Qed.



Require Import Setoid.

Theorem classic_set_in_prop_context :
forall C:Prop, ((forall P:Prop, {P} + {~ P}) -> C) -> C.
Proof. hammer_hook "ClassicalUniqueChoice" "ClassicalUniqueChoice.classic_set_in_prop_context".  
intros C HnotEM.
set (R := fun A b => A /\ true = b \/ ~ A /\ false = b).
assert (H :  exists f : Prop -> bool, (forall A:Prop, R A (f A))).
apply unique_choice.
intro A.
destruct (classic A) as [Ha| Hnota].
exists true; split.
left; split; [ assumption | reflexivity ].
intros y [[_ Hy]| [Hna _]].
assumption.
contradiction.
exists false; split.
right; split; [ assumption | reflexivity ].
intros y [[Ha _]| [_ Hy]].
contradiction.
assumption.
destruct H as [f Hf].
apply HnotEM.
intro P.
assert (HfP := Hf P).

destruct (f P).
left.
destruct HfP as [[Ha _]| [_ Hfalse]].
assumption.
discriminate.
right.
destruct HfP as [[_ Hfalse]| [Hna _]].
discriminate.
assumption.
Qed.

Corollary not_not_classic_set :
((forall P:Prop, {P} + {~ P}) -> False) -> False.
Proof. hammer_hook "ClassicalUniqueChoice" "ClassicalUniqueChoice.not_not_classic_set".  
apply classic_set_in_prop_context.
Qed.


Notation classic_set := not_not_classic_set (only parsing).
