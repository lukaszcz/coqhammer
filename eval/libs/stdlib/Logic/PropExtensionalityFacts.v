From Hammer Require Import Hammer.











Set Implicit Arguments.






Local Notation PropositionalExtensionality :=
(forall A B : Prop, (A <-> B) -> A = B).



Local Notation ProvablePropositionExtensionality :=
(forall A:Prop, A -> A = True).



Local Notation RefutablePropositionExtensionality :=
(forall A:Prop, ~A -> A = False).



Local Notation PredicateExtensionality :=
(forall (A:Type) (P Q : A -> Prop), (forall x, P x <-> Q x) -> P = Q).



Local Notation PropositionalFunctionalExtensionality :=
(forall (A:Type) (P Q : A -> Prop), (forall x, P x = Q x) -> P = Q).







Lemma PredExt_imp_PropExt : PredicateExtensionality -> PropositionalExtensionality.
Proof. hammer_hook "PropExtensionalityFacts" "PropExtensionalityFacts.PredExt_imp_PropExt". Restart. 
intros Ext A B Equiv.
change A with ((fun _ => A) I).
now rewrite Ext with (P := fun _ : True =>A) (Q := fun _ => B).
Qed.

Lemma PredExt_imp_PropFunExt : PredicateExtensionality -> PropositionalFunctionalExtensionality.
Proof. hammer_hook "PropExtensionalityFacts" "PropExtensionalityFacts.PredExt_imp_PropFunExt". Restart. 
intros Ext A P Q Eq. apply Ext. intros x. now rewrite (Eq x).
Qed.

Lemma PropExt_and_PropFunExt_imp_PredExt :
PropositionalExtensionality -> PropositionalFunctionalExtensionality -> PredicateExtensionality.
Proof. hammer_hook "PropExtensionalityFacts" "PropExtensionalityFacts.PropExt_and_PropFunExt_imp_PredExt". Restart. 
intros Ext FunExt A P Q Equiv.
apply FunExt. intros x. now apply Ext.
Qed.

Theorem PropExt_and_PropFunExt_iff_PredExt :
PropositionalExtensionality /\ PropositionalFunctionalExtensionality <-> PredicateExtensionality.
Proof. hammer_hook "PropExtensionalityFacts" "PropExtensionalityFacts.PropExt_and_PropFunExt_iff_PredExt". Restart. 
firstorder using PredExt_imp_PropExt, PredExt_imp_PropFunExt, PropExt_and_PropFunExt_imp_PredExt.
Qed.




Lemma PropExt_imp_ProvPropExt : PropositionalExtensionality -> ProvablePropositionExtensionality.
Proof. hammer_hook "PropExtensionalityFacts" "PropExtensionalityFacts.PropExt_imp_ProvPropExt". Restart. 
intros Ext A Ha; apply Ext; split; trivial.
Qed.




Lemma PropExt_imp_RefutPropExt : PropositionalExtensionality -> RefutablePropositionExtensionality.
Proof. hammer_hook "PropExtensionalityFacts" "PropExtensionalityFacts.PropExt_imp_RefutPropExt". Restart. 
intros Ext A Ha; apply Ext; split; easy.
Qed.
