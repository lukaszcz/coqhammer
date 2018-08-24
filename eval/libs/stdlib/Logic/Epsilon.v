From Hammer Require Import Hammer.











Require Import ChoiceFacts.

Set Implicit Arguments.



Axiom epsilon_statement :
forall (A : Type) (P : A->Prop), inhabited A ->
{ x : A | (exists x, P x) -> P x }.

Lemma constructive_indefinite_description :
forall (A : Type) (P : A->Prop),
(exists x, P x) -> { x : A | P x }.
Proof. try hammer_hook "Epsilon" "Epsilon.constructive_indefinite_description". Undo.  
apply epsilon_imp_constructive_indefinite_description.
exact epsilon_statement.
Qed.

Lemma small_drinkers'_paradox :
forall (A:Type) (P:A -> Prop), inhabited A ->
exists x, (exists x, P x) -> P x.
Proof. try hammer_hook "Epsilon" "Epsilon.small_drinkers'_paradox". Undo.  
apply epsilon_imp_small_drinker.
exact epsilon_statement.
Qed.

Theorem iota_statement :
forall (A : Type) (P : A->Prop), inhabited A ->
{ x : A | (exists! x : A, P x) -> P x }.
Proof. try hammer_hook "Epsilon" "Epsilon.iota_statement". Undo.  
intros; destruct epsilon_statement with (P:=P); firstorder.
Qed.

Lemma constructive_definite_description :
forall (A : Type) (P : A->Prop),
(exists! x, P x) -> { x : A | P x }.
Proof. try hammer_hook "Epsilon" "Epsilon.constructive_definite_description". Undo.  
apply iota_imp_constructive_definite_description.
exact iota_statement.
Qed.



Definition epsilon (A : Type) (i:inhabited A) (P : A->Prop) : A
:= proj1_sig (epsilon_statement P i).

Definition epsilon_spec (A : Type) (i:inhabited A) (P : A->Prop) :
(exists x, P x) -> P (epsilon i P)
:= proj2_sig (epsilon_statement P i).



Definition iota (A : Type) (i:inhabited A) (P : A->Prop) : A
:= proj1_sig (iota_statement P i).

Definition iota_spec (A : Type) (i:inhabited A) (P : A->Prop) :
(exists! x:A, P x) -> P (iota i P)
:= proj2_sig (iota_statement P i).

