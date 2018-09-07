From Hammer Require Import Hammer.











Require Import ChoiceFacts.

Set Implicit Arguments.

Axiom constructive_definite_description :
forall (A : Type) (P : A->Prop),
(exists! x, P x) -> { x : A | P x }.
