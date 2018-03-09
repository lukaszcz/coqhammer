From Hammer Require Import Hammer.









Require Export Relation_Definitions.
Require Export Relation_Operators.
Require Export Operators_Properties.

Lemma inverse_image_of_equivalence :
forall (A B:Type) (f:A -> B) (r:relation B),
equivalence B r -> equivalence A (fun x y:A => r (f x) (f y)).
Proof. hammer_hook "Relations" "Relations.inverse_image_of_equivalence". Restart. 
intros; split; elim H; red; auto.
intros _ equiv_trans _ x y z H0 H1; apply equiv_trans with (f y); assumption.
Qed.

Lemma inverse_image_of_eq :
forall (A B:Type) (f:A -> B), equivalence A (fun x y:A => f x = f y).
Proof. hammer_hook "Relations" "Relations.inverse_image_of_eq". Restart. 
split; red;
[   reflexivity
|   intros; transitivity (f y); assumption
|   intros; symmetry ; assumption ].
Qed.

