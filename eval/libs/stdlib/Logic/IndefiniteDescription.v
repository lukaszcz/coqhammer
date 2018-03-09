From Hammer Require Import Hammer.











Require Import ChoiceFacts.

Set Implicit Arguments.

Axiom constructive_indefinite_description :
forall (A : Type) (P : A->Prop),
(exists x, P x) -> { x : A | P x }.

Lemma constructive_definite_description :
forall (A : Type) (P : A->Prop),
(exists! x, P x) -> { x : A | P x }.
Proof. hammer_hook "IndefiniteDescription" "IndefiniteDescription.constructive_definite_description". Restart. 
intros; apply constructive_indefinite_description; firstorder.
Qed.

Lemma functional_choice :
forall (A B : Type) (R:A->B->Prop),
(forall x : A, exists y : B, R x y) ->
(exists f : A->B, forall x : A, R x (f x)).
Proof. hammer_hook "IndefiniteDescription" "IndefiniteDescription.functional_choice". Restart. 
apply constructive_indefinite_descr_fun_choice.
exact constructive_indefinite_description.
Qed.
