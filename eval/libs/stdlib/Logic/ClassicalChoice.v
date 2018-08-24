From Hammer Require Import Hammer.













Require Export ClassicalUniqueChoice.
Require Export RelationalChoice.
Require Import ChoiceFacts.

Set Implicit Arguments.

Definition subset (U:Type) (P Q:U->Prop) : Prop := forall x, P x -> Q x.

Theorem singleton_choice :
forall (A : Type) (P : A->Prop),
(exists x : A, P x) -> exists P' : A->Prop, subset P' P /\ exists! x, P' x.
Proof. try hammer_hook "ClassicalChoice" "ClassicalChoice.singleton_choice". Undo.  
intros A P H.
destruct (relational_choice unit A (fun _ => P) (fun _ => H)) as (R',(Hsub,HR')).
exists (R' tt); firstorder.
Qed.

Theorem choice :
forall (A B : Type) (R : A->B->Prop),
(forall x : A, exists y : B, R x y) ->
exists f : A->B, (forall x : A, R x (f x)).
Proof. try hammer_hook "ClassicalChoice" "ClassicalChoice.choice". Undo.  
intros A B.
apply description_rel_choice_imp_funct_choice.
exact (unique_choice A B).
exact (relational_choice A B).
Qed.
