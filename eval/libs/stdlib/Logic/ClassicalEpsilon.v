From Hammer Require Import Hammer.














Require Export Classical.
Require Import ChoiceFacts.

Set Implicit Arguments.

Axiom constructive_indefinite_description :
forall (A : Type) (P : A->Prop),
(exists x, P x) -> { x : A | P x }.

Lemma constructive_definite_description :
forall (A : Type) (P : A->Prop),
(exists! x, P x) -> { x : A | P x }.
Proof. hammer_hook "ClassicalEpsilon" "ClassicalEpsilon.constructive_definite_description".  
intros; apply constructive_indefinite_description; firstorder.
Qed.

Theorem excluded_middle_informative : forall P:Prop, {P} + {~ P}.
Proof. hammer_hook "ClassicalEpsilon" "ClassicalEpsilon.excluded_middle_informative".  
apply
(constructive_definite_descr_excluded_middle
constructive_definite_description classic).
Qed.

Theorem classical_indefinite_description :
forall (A : Type) (P : A->Prop), inhabited A ->
{ x : A | (exists x, P x) -> P x }.
Proof. hammer_hook "ClassicalEpsilon" "ClassicalEpsilon.classical_indefinite_description".  
intros A P i.
destruct (excluded_middle_informative (exists x, P x)) as [Hex|HnonP].
apply constructive_indefinite_description
with (P:= fun x => (exists x, P x) -> P x).
destruct Hex as (x,Hx).
exists x; intros _; exact Hx.
assert {x : A | True} as (a,_).
apply constructive_indefinite_description with (P := fun _ : A => True).
destruct i as (a); firstorder.
firstorder.
Defined.



Definition epsilon (A : Type) (i:inhabited A) (P : A->Prop) : A
:= proj1_sig (classical_indefinite_description P i).

Definition epsilon_spec (A : Type) (i:inhabited A) (P : A->Prop) :
(exists x, P x) -> P (epsilon i P)
:= proj2_sig (classical_indefinite_description P i).





Lemma epsilon_inh_irrelevance :
forall (A:Type) (i j : inhabited A) (P:A->Prop),
(exists x, P x) -> epsilon i P = epsilon j P.
Proof. hammer_hook "ClassicalEpsilon" "ClassicalEpsilon.epsilon_inh_irrelevance".  
intros.
unfold epsilon, classical_indefinite_description.
destruct (excluded_middle_informative (exists x : A, P x)) as [|[]]; trivial.
Qed.

Opaque epsilon.



Theorem choice :
forall (A B : Type) (R : A->B->Prop),
(forall x : A, exists y : B, R x y) ->
(exists f : A->B, forall x : A, R x (f x)).
Proof. hammer_hook "ClassicalEpsilon" "ClassicalEpsilon.choice".  
intros A B R H.
exists (fun x => proj1_sig (constructive_indefinite_description _ (H x))).
intro x.
apply (proj2_sig (constructive_indefinite_description _ (H x))).
Qed.

