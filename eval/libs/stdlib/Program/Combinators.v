From Hammer Require Import Hammer.











Require Import Coq.Program.Basics.
Require Export FunctionalExtensionality.

Open Scope program_scope.



Lemma compose_id_left : forall A B (f : A -> B), id ∘ f = f.
Proof. try hammer_hook "Combinators" "Combinators.compose_id_left". Undo.  
intros.
unfold id, compose.
symmetry. apply eta_expansion.
Qed.

Lemma compose_id_right : forall A B (f : A -> B), f ∘ id = f.
Proof. try hammer_hook "Combinators" "Combinators.compose_id_right". Undo.  
intros.
unfold id, compose.
symmetry ; apply eta_expansion.
Qed.

Lemma compose_assoc : forall A B C D (f : A -> B) (g : B -> C) (h : C -> D),
h ∘ g ∘ f = h ∘ (g ∘ f).
Proof. try hammer_hook "Combinators" "Combinators.compose_assoc". Undo.  
intros.
reflexivity.
Qed.

Hint Rewrite @compose_id_left @compose_id_right : core.
Hint Rewrite <- @compose_assoc : core.



Lemma flip_flip : forall A B C, @flip A B C ∘ flip = id.
Proof. try hammer_hook "Combinators" "Combinators.flip_flip". Undo.  
unfold flip, compose.
intros.
extensionality x ; extensionality y ; extensionality z.
reflexivity.
Qed.



Lemma prod_uncurry_curry : forall A B C, @prod_uncurry A B C ∘ prod_curry = id.
Proof. try hammer_hook "Combinators" "Combinators.prod_uncurry_curry". Undo.  
simpl ; intros.
unfold prod_uncurry, prod_curry, compose.
extensionality x ; extensionality y ; extensionality z.
reflexivity.
Qed.

Lemma prod_curry_uncurry : forall A B C, @prod_curry A B C ∘ prod_uncurry = id.
Proof. try hammer_hook "Combinators" "Combinators.prod_curry_uncurry". Undo.  
simpl ; intros.
unfold prod_uncurry, prod_curry, compose.
extensionality x ; extensionality p.
destruct p ; simpl ; reflexivity.
Qed.
