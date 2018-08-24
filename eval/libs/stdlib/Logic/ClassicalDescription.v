From Hammer Require Import Hammer.













Set Implicit Arguments.

Require Export Classical.
Require Export Description.
Require Import ChoiceFacts.

Local Notation inhabited A := A (only parsing).



Theorem excluded_middle_informative : forall P:Prop, {P} + {~ P}.
Proof. try hammer_hook "ClassicalDescription" "ClassicalDescription.excluded_middle_informative". Undo.  
apply
(constructive_definite_descr_excluded_middle
constructive_definite_description classic).
Qed.

Theorem classical_definite_description :
forall (A : Type) (P : A->Prop), inhabited A ->
{ x : A | (exists! x : A, P x) -> P x }.
Proof. try hammer_hook "ClassicalDescription" "ClassicalDescription.classical_definite_description". Undo.  
intros A P i.
destruct (excluded_middle_informative (exists! x, P x)) as [Hex|HnonP].
apply constructive_definite_description with (P:= fun x => (exists! x : A, P x) -> P x).
destruct Hex as (x,(Hx,Huni)).
exists x; split.
intros _; exact Hx.
firstorder.
exists i; tauto.
Qed.



Definition iota (A : Type) (i:inhabited A) (P : A->Prop) : A
:= proj1_sig (classical_definite_description P i).

Definition iota_spec (A : Type) (i:inhabited A) (P : A->Prop) :
(exists! x:A, P x) -> P (iota i P)
:= proj2_sig (classical_definite_description P i).


Theorem dependent_unique_choice :
forall (A:Type) (B:A -> Type) (R:forall x:A, B x -> Prop),
(forall x:A, exists! y : B x, R x y) ->
(exists f : (forall x:A, B x), forall x:A, R x (f x)).
Proof. try hammer_hook "ClassicalDescription" "ClassicalDescription.dependent_unique_choice". Undo.  
intros A B R H.
assert (Hexuni:forall x, exists! y, R x y).
intro x. apply H.
exists (fun x => proj1_sig (constructive_definite_description (R x) (Hexuni x))).
intro x.
apply (proj2_sig (constructive_definite_description (R x) (Hexuni x))).
Qed.

Theorem unique_choice :
forall (A B:Type) (R:A -> B -> Prop),
(forall x:A,  exists! y : B, R x y) ->
(exists f : A -> B, forall x:A, R x (f x)).
Proof. try hammer_hook "ClassicalDescription" "ClassicalDescription.unique_choice". Undo.  
intros A B.
apply dependent_unique_choice with (B:=fun _:A => B).
Qed.



Unset Implicit Arguments.

Definition dependent_description := dependent_unique_choice.
Definition description := unique_choice.
