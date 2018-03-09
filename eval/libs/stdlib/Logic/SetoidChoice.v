From Hammer Require Import Hammer.











Require Export ClassicalChoice.
Require Export ExtensionalFunctionRepresentative.

Require Import ChoiceFacts.
Require Import ClassicalFacts.
Require Import RelationClasses.

Theorem setoid_choice :
forall A B,
forall R : A -> A -> Prop,
forall T : A -> B -> Prop,
Equivalence R ->
(forall x x' y, R x x' -> T x y -> T x' y) ->
(forall x, exists y, T x y) ->
exists f : A -> B, forall x : A, T x (f x) /\ (forall x' : A, R x x' -> f x = f x').
Proof. hammer_hook "SetoidChoice" "SetoidChoice.setoid_choice". Restart. 
apply setoid_functional_choice_first_characterization. split; [|split].
- exact choice.
- exact extensional_function_representative.
- exact classic.
Qed.

Theorem representative_choice :
forall A (R:A->A->Prop), (Equivalence R) ->
exists f : A->A, forall x : A, R x (f x) /\ forall x', R x x' -> f x = f x'.
Proof. hammer_hook "SetoidChoice" "SetoidChoice.representative_choice". Restart. 
apply setoid_fun_choice_imp_repr_fun_choice.
exact setoid_choice.
Qed.
