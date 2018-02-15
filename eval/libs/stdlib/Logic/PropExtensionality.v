From Hammer Require Import Hammer.











Axiom propositional_extensionality :
forall (P Q : Prop), (P <-> Q) -> P = Q.

Require Import ClassicalFacts.

Theorem proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
Proof. hammer_hook "PropExtensionality" "PropExtensionality.proof_irrelevance". Restart. 
apply ext_prop_dep_proof_irrel_cic.
exact propositional_extensionality.
Qed.

