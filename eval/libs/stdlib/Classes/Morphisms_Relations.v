From Hammer Require Import Hammer.











Require Import Relation_Definitions.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Program.

Generalizable Variables A l.



Instance relation_conjunction_morphism : Proper (relation_equivalence (A:=A) ==>
relation_equivalence ==> relation_equivalence) relation_conjunction.
Proof. try hammer_hook "Morphisms_Relations" "Morphisms_Relations.relation_conjunction_morphism".   firstorder. Qed.

Instance relation_disjunction_morphism : Proper (relation_equivalence (A:=A) ==>
relation_equivalence ==> relation_equivalence) relation_disjunction.
Proof. try hammer_hook "Morphisms_Relations" "Morphisms_Relations.relation_disjunction_morphism".   firstorder. Qed.



Lemma predicate_equivalence_pointwise (l : Tlist) :
Proper (@predicate_equivalence l ==> pointwise_lifting iff l) id.
Proof. try hammer_hook "Morphisms_Relations" "Morphisms_Relations.predicate_equivalence_pointwise".   do 2 red. unfold predicate_equivalence. auto. Qed.

Lemma predicate_implication_pointwise (l : Tlist) :
Proper (@predicate_implication l ==> pointwise_lifting impl l) id.
Proof. try hammer_hook "Morphisms_Relations" "Morphisms_Relations.predicate_implication_pointwise".   do 2 red. unfold predicate_implication. auto. Qed.



Instance relation_equivalence_pointwise :
Proper (relation_equivalence ==> pointwise_relation A (pointwise_relation A iff)) id.
Proof. try hammer_hook "Morphisms_Relations" "Morphisms_Relations.relation_equivalence_pointwise".   intro. apply (predicate_equivalence_pointwise (Tcons A (Tcons A Tnil))). Qed.

Instance subrelation_pointwise :
Proper (subrelation ==> pointwise_relation A (pointwise_relation A impl)) id.
Proof. try hammer_hook "Morphisms_Relations" "Morphisms_Relations.subrelation_pointwise".   intro. apply (predicate_implication_pointwise (Tcons A (Tcons A Tnil))). Qed.


Lemma flip_pointwise_relation A (R : relation A) :
relation_equivalence (pointwise_relation A (flip R)) (flip (pointwise_relation A R)).
Proof. try hammer_hook "Morphisms_Relations" "Morphisms_Relations.flip_pointwise_relation".   intros. split; firstorder. Qed.
